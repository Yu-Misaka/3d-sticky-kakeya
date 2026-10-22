#!/usr/bin/env python3
"""Audit and display the sticky theorem's compiled Lean dependencies."""

from __future__ import annotations

import hashlib
import html
import json
import re
import shutil
import subprocess
from collections import Counter, deque
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import quote

ROOT = Path(__file__).resolve().parents[2]
BLUEPRINT = ROOT / "blueprint"
REPORT = BLUEPRINT / "lean-dependencies.json"
RAW = BLUEPRINT / "build/lean-dependencies.jsonl"
EXTRACTOR = BLUEPRINT / "scripts/dependencies.lean"
THEOREM = "Kakeya.Assouad.PureWZ2Theorem5_2Unconditional"
EDGE_KINDS = ("value", "type", "structural")
REPORT_FORMAT = 3


def extractor_digest() -> str:
    return hashlib.sha256(EXTRACTOR.read_bytes() + b"\0" +
                          EXTRACTOR.with_name("audit.lean").read_bytes()).hexdigest()


def read_graph(path: Path) -> tuple[dict, dict[str, dict], list[str]]:
    with path.open() as stream:
        header = json.loads(next(stream))
        graph = {}
        boundary = None
        for line in stream:
            record = json.loads(line)
            if "boundary" in record:
                boundary = record["boundary"]
            else:
                name = record["name"]
                if name in graph:
                    raise ValueError(f"Duplicate dependency record: {name}")
                graph[name] = record
    if boundary is None:
        raise ValueError("Lean dependency extraction did not finish")
    for name, record in graph.items():
        for kind in EDGE_KINDS:
            missing = [dependency for dependency in record[kind] if dependency not in graph]
            if missing:
                raise ValueError(f"Unresolved {kind} dependencies of {name}: {sorted(missing)}")
    return header, graph, boundary


def walks(graph: dict[str, dict], start: str, stops: set[str] | None = None) -> dict:
    """Shortest witness paths; cycles and repeated edges do not duplicate work."""
    parents: dict[str, tuple[str, str] | None] = {start: None}
    pending = deque([start])
    while pending:
        name = pending.popleft()
        for kind in EDGE_KINDS:
            for dependency in sorted(graph[name][kind]):
                if dependency in parents:
                    continue
                parents[dependency] = (name, kind)
                if not stops or dependency not in stops:
                    pending.append(dependency)
    return parents


def witness(parents: dict, target: str) -> list[dict]:
    path = []
    while parents[target] is not None:
        source, kind = parents[target]
        path.append({"from": source, "to": target, "kind": kind})
        target = source
    return list(reversed(path))


def reduce_edges(edges: list[dict]) -> list[dict]:
    """Remove redundant display edges only when the projected graph is acyclic."""
    adjacency: dict[str, set[str]] = {}
    for edge in edges:
        adjacency.setdefault(edge["from"], set()).add(edge["to"])
    active, done = set(), set()

    def acyclic(node):
        if node in active:
            return False
        if node in done:
            return True
        active.add(node)
        if not all(acyclic(other) for other in adjacency.get(node, ())):
            return False
        active.remove(node)
        done.add(node)
        return True

    if not all(acyclic(node) for node in adjacency):
        return edges
    result = []
    for edge in edges:
        source, target = edge["from"], edge["to"]
        pending = list(adjacency[source] - {target})
        reached = set()
        while pending:
            node = pending.pop()
            if node in reached:
                continue
            reached.add(node)
            pending.extend(adjacency.get(node, ()))
        if target not in reached:
            result.append(edge)
    return result


def make_report(graph: dict[str, dict], records: list[dict], root: str,
                module_roots: list[str], boundary_count: int) -> dict:
    if root not in graph or graph[root]["kind"] != "theorem":
        raise ValueError("The dependency root must be a compiled theorem")
    parents = walks(graph, root)
    if set(parents) != graph.keys():
        raise ValueError("Dependency extraction contains declarations unreachable from the root")
    indexed = {record["name"]: record for record in records}
    if root not in indexed:
        raise ValueError("The dependency root must be linked from the blueprint")
    # Keep every reached blueprint declaration, including definitions and types.
    # Unlinked helpers are folded into witnessed edges; each displayed node has
    # a manuscript statement. Distinct Lean versions remain distinct nodes.
    selected = indexed.keys() & graph.keys()
    edges = []
    for name in sorted(selected):
        nearest = walks(graph, name, selected)
        for dependency in sorted(selected.intersection(nearest) - {name}):
            edges.append({"from": name, "to": dependency,
                          "path": witness(nearest, dependency)})
    edges = reduce_edges(edges)
    declarations = []
    for name, record in sorted(indexed.items()):
        declarations.append({
            "name": name, "kind": record["kind"], "module": record["module"],
            "line": record["line"], "axioms": record["axioms"],
            "reached": name in parents,
            "path": witness(parents, name) if name in parents else [],
            **{key: record[key] for key in ("is_proof", "is_proposition", "type", "definition", "expanded_type") if key in record},
        })
    evidence_names = set(selected)
    for path in [*(entry["path"] for entry in declarations), *(edge["path"] for edge in edges)]:
        for step in path:
            evidence_names.update((step["from"], step["to"]))
    evidence = {name: {key: graph[name][key] for key in ("kind", "module", "line")}
                for name in sorted(evidence_names)}
    return {
        "format": REPORT_FORMAT, "root": root, "module_roots": module_roots,
        "project_declarations": sum(record.get("scope") != "library" for record in graph.values()),
        "library_declarations": sum(record.get("scope") == "library" for record in graph.values()),
        "library_boundary": boundary_count,
        "kinds": dict(sorted(Counter(record["kind"] for record in graph.values()).items())),
        "declarations": declarations, "graph_nodes": sorted(selected), "edges": edges,
        "root_inputs": sorted(name for name in graph[root]["value"] if graph[name]["kind"] == "theorem"),
        "evidence": evidence,
    }


def save_report(records: list[dict], source_sha256: str) -> None:
    header, graph, boundary = read_graph(RAW)
    if header["root"] != THEOREM:
        raise ValueError("Unexpected Lean dependency root")
    report = make_report(graph, records, THEOREM, header["module_roots"], len(boundary))
    report.update(source_sha256=source_sha256, extractor_sha256=extractor_digest())
    REPORT.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    used = sum(entry["reached"] for entry in report["declarations"])
    print(f"Checked Lean dependencies: {report['project_declarations']} project declarations; "
          f"{used}/{len(records)} blueprint declarations reached.", flush=True)


def check_report(records: list[dict], source_sha256: str) -> dict:
    if not REPORT.is_file():
        raise ValueError("No proof dependency audit; run python blueprint/scripts/check.py --lean")
    report = json.loads(REPORT.read_text())
    if (report.get("format") != REPORT_FORMAT or report.get("root") != THEOREM
            or report.get("source_sha256") != source_sha256
            or report.get("extractor_sha256") != extractor_digest()):
        raise ValueError("Lean dependency audit is stale; run python blueprint/scripts/check.py --lean")
    expected = {record["name"]: record for record in records}
    if sorted(entry["name"] for entry in report["declarations"]) != sorted(expected):
        raise ValueError("Lean dependency audit differs from the blueprint declaration links")
    reached = {entry["name"] for entry in report["declarations"] if entry["reached"]}
    if report["graph_nodes"] != sorted(reached):
        raise ValueError("Displayed dependency nodes differ from the reached blueprint declarations")
    for entry in report["declarations"]:
        if any(entry.get(key) != expected[entry["name"]].get(key)
               for key in ("kind", "module", "line", "axioms", "is_proof", "is_proposition", "type", "definition", "expanded_type")):
            raise ValueError(f"Dependency metadata disagrees with Lean audit: {entry['name']}")
        if entry["reached"]:
            end = report["root"]
            for step in entry["path"]:
                if step["from"] != end or step["kind"] not in EDGE_KINDS:
                    raise ValueError(f"Invalid dependency witness: {entry['name']}")
                end = step["to"]
            if end != entry["name"]:
                raise ValueError(f"Incomplete dependency witness: {entry['name']}")
    for edge in report["edges"]:
        end = edge["from"]
        for step in edge["path"]:
            if step["from"] != end or step["kind"] not in EDGE_KINDS:
                raise ValueError("Invalid displayed dependency edge")
            end = step["to"]
        if end != edge["to"] or not edge["path"]:
            raise ValueError("Displayed dependency edge has no complete witness")
    return report


class PaperStatements(HTMLParser):
    """Read the already rendered blueprint, preserving its math and cross-links."""

    VOID = {"area", "base", "br", "col", "embed", "hr", "img", "input", "link",
            "meta", "param", "source", "track", "wbr"}

    def __init__(self, text: str, page_url: str | None = None):
        super().__init__(convert_charrefs=False)
        self.text = text
        self.page_url = page_url
        self.offsets = [0]
        for line in text.splitlines(keepends=True):
            self.offsets.append(self.offsets[-1] + len(line))
        self.depth = 0
        self.current = None
        self.captures = []
        self.head = ""
        self.statements: dict[str, dict] = {}
        self.feed(text)

    def source_offset(self) -> int:
        line, column = self.getpos()
        return self.offsets[line - 1] + column

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        classes = attrs.get("class", "").split()
        key = None
        if tag == "head":
            key = "head"
        if tag == "div" and attrs.get("id") and (
            "thm" in classes or any(cls.endswith("_thmwrapper") for cls in classes)
        ):
            self.current = {"depth": self.depth, "ref": "", "title": ""}
            if self.page_url:
                self.current["url"] = self.page_url + "#" + quote(attrs["id"], safe=":")
            self.statements[attrs["id"]] = self.current
        if self.current is not None:
            if any(cls.endswith("_thmcontent") for cls in classes):
                key = "content"
            for cls in classes:
                for suffix, field in (("_thmcaption", "caption"), ("_thmlabel", "ref"),
                                      ("_thmtitle", "title")):
                    if cls.endswith(suffix):
                        key = field
                        self.current["kind"] = cls.removesuffix(suffix)
            if "latex_link" in classes:
                self.current["url"] = attrs["href"]
        if key:
            self.captures.append((self.depth, key, self.source_offset() + len(self.get_starttag_text())))
        if tag not in self.VOID:
            self.depth += 1

    def handle_endtag(self, tag):
        if tag in self.VOID:
            return
        self.depth -= 1
        if self.captures and self.captures[-1][0] == self.depth:
            _, key, start = self.captures.pop()
            value = self.text[start:self.source_offset()].strip()
            if key == "head":
                self.head = value
            else:
                self.current[key] = value
        if self.current is not None and self.current["depth"] == self.depth:
            self.current = None


def statement_content(text: str, node_id: str, source_page: str = "index.html") -> str:
    """Give copies of a statement unique equation anchors for each Lean version."""
    local_ids = set(re.findall(r'(?<![\w:-])id="([^"]+)"', text))
    text = re.sub(r'(?<![\w:-])id="([^"]+)"', lambda match: f'id="{node_id}-{match[1]}"', text)
    return re.sub(r'(?<![\w:-])href="#([^"]+)"',
                  lambda match: f'href="#{node_id}-{match[1]}"' if match[1] in local_ids
                  else f'href="{source_page}#{match[1]}"', text)


def manuscript_statements(directory: Path) -> dict[str, dict]:
    """Include Remarks, which the upstream paper graph deliberately omits."""
    result = {}
    for page in sorted(directory.glob("chap-*.html")):
        result.update(PaperStatements(page.read_text(), page.name).statements)
    return result


def redirect_page(target: str, title: str) -> str:
    """A retired route that forwards to its replacement, keeping any fragment."""
    href = html.escape(target, quote=True)
    return (f'<!doctype html>\n<html lang="en"><head><meta charset="utf-8"><title>{html.escape(title)}</title>'
            f'<meta http-equiv="refresh" content="0; url={href}">'
            f'<script>location.replace({json.dumps(target)} + location.hash);</script></head>'
            f'<body><p>This page has moved to <a href="{href}">{html.escape(title)}</a>.</p></body></html>\n')


def write_site(site: Path, report: dict, paper_nodes: list[dict]) -> None:
    """Publish the reviewed atlas and its audits."""
    entries = {entry["name"]: entry for entry in report["declarations"]}
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()

    def source_link(name: str, label: str | None = None) -> str:
        from atlas_render import source_url
        metadata = report["evidence"].get(name, entries.get(name))
        url = source_url(metadata, revision)
        caption = html.escape(label) if label else f'<code>{html.escape(name)}</code>'
        return f'<a href="{html.escape(url, quote=True)}">{caption}</a>'

    def path_details(path: list[dict]) -> str:
        if not path:
            return ""
        steps = "".join(f'<li>{source_link(step["from"])} — {step["kind"]} → '
                        f'{source_link(step["to"])}</li>' for step in path)
        return f'<details><summary>Witness: {len(path)} references</summary><ol>{steps}</ol></details>'

    rows = []
    for node in paper_nodes:
        if node["kind"] == "remark" and not node["label"].startswith("rem:atlas-"):
            continue
        variants = []
        for name in node["lean"]:
            entry = entries[name]
            if entry["reached"]:
                status = "Used theorem" if entry["kind"] == "theorem" else "Used type / definition"
            else:
                status = "Proved, not used by this root" if entry["kind"] == "theorem" else "Not used by this root"
            link = "../lean/find/#doc/" + quote(name, safe=".")
            variants.append(f'<li><span class="usage">{status}</span> · {entry["kind"]}<br>'
                            f'<a href="{link}"><code>{html.escape(name)}</code></a>'
                            f'{path_details(entry["path"])}</li>')
        content = "<ul>" + "".join(variants) + "</ul>" if variants else "No Lean declaration linked; correspondence not audited."
        mark = ("Correspondence Remark" if node["kind"] == "remark" else
                "Definition" if node["kind"] == "definition" else
                "Marked complete" if node["proof_complete"] else "Not marked complete")
        rows.append(f'<tr id="{html.escape(node["label"], quote=True)}"><td><code>{html.escape(node["label"])}</code>'
                    f'<br>{html.escape(node["title"])}</td><td>{mark}</td><td>{content}</td></tr>')
    used = sum(entry["reached"] for entry in entries.values())
    unused_proofs = sum(not entry["reached"] and entry["kind"] == "theorem" for entry in entries.values())
    template = (BLUEPRINT / "templates/lean_dependency_audit.html").read_text()
    from atlas_render import sitebar
    substitutions = {
        "ROOT": html.escape(report["root"]),
        "COUNTS": f"{report['project_declarations']:,} project declarations inspected; {used}/{len(entries)} linked declarations reached; {unused_proofs} linked theorems proved but unused by this root.",
        "ROWS": "\n".join(rows), "SHA": html.escape(revision),
        # The witness of every graph edge is shown by the atlas and kept in lean-dependencies.json.
        "SITEBAR": sitebar("evidence"),
    }
    for name, text in substitutions.items():
        template = template.replace("{{" + name + "}}", text)
    paper = site / "blueprint/dep_graph_document.html"
    text = paper.read_text()
    (site / "blueprint/lean_dependency_audit.html").write_text(template)
    # The declaration-level graph is the unified atlas with every frame open.
    (site / "blueprint/lean_declarations.html").write_text(
        redirect_page("lean_dependencies.html", "the proof atlas"))
    (site / "blueprint/lean-dependencies.json").write_text(json.dumps(report, ensure_ascii=False) + "\n")
    from atlas_render import write_atlas
    write_atlas(site, report, paper_nodes, text)
    # The atlas has read plasTeX's statements; now give the manuscript the site's design.
    from manuscript import restyle_manuscript
    converted = restyle_manuscript(site / "blueprint")
    for theme in ("js", "styles"):
        shutil.rmtree(site / "blueprint" / theme, ignore_errors=True)
    (site / "blueprint/symbol-defs.svg").unlink(missing_ok=True)
    print(f"Restyled {converted} manuscript pages.", flush=True)
