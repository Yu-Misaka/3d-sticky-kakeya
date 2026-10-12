#!/usr/bin/env python3
"""Audit and display the sticky theorem's compiled Lean dependencies."""

from __future__ import annotations

import hashlib
import html
import json
import re
import subprocess
from collections import Counter, deque
from html.parser import HTMLParser
from importlib.resources import files
from pathlib import Path
from types import SimpleNamespace
from urllib.parse import quote

ROOT = Path(__file__).resolve().parents[2]
BLUEPRINT = ROOT / "blueprint"
REPORT = BLUEPRINT / "lean-dependencies.json"
RAW = BLUEPRINT / "build/lean-dependencies.jsonl"
EXTRACTOR = BLUEPRINT / "scripts/dependencies.lean"
THEOREM = "Kakeya.Assouad.PureWZ2Theorem5_2Unconditional"
EDGE_KINDS = ("value", "type", "structural")
REPORT_FORMAT = 2


def extractor_digest() -> str:
    return hashlib.sha256(EXTRACTOR.read_bytes()).hexdigest()


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
        })
    evidence_names = set(selected)
    for path in [*(entry["path"] for entry in declarations), *(edge["path"] for edge in edges)]:
        for step in path:
            evidence_names.update((step["from"], step["to"]))
    evidence = {name: {key: graph[name][key] for key in ("kind", "module", "line")}
                for name in sorted(evidence_names)}
    return {
        "format": REPORT_FORMAT, "root": root, "module_roots": module_roots,
        "project_declarations": len(graph), "library_boundary": boundary_count,
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
        if any(entry[key] != expected[entry["name"]][key] for key in ("kind", "module", "line", "axioms")):
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

    def __init__(self, text: str):
        super().__init__(convert_charrefs=False)
        self.text = text
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
        if tag == "div" and "thm" in classes:
            self.current = {"depth": self.depth, "ref": "", "title": ""}
            self.statements[attrs["id"]] = self.current
        if self.current is not None:
            if "thm_thmcontent" in classes:
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


def statement_content(text: str, node_id: str) -> str:
    """Give copies of a statement unique equation anchors for each Lean version."""
    text = re.sub(r'(?<![\w:-])id="([^"]+)"', lambda match: f'id="{node_id}-{match[1]}"', text)
    return re.sub(r'(?<![\w:-])href="#([^"]+)"', lambda match: f'href="#{node_id}-{match[1]}"', text)


def render_graph(report: dict, aliases: dict[str, list[str]], source_link, paper_html: str) -> str:
    """Use the installed default blueprint graph template and modal interactions."""
    from jinja2 import Template

    class GraphNode(SimpleNamespace):
        def __str__(self):
            return self.content

    paper = PaperStatements(paper_html)
    q = lambda text: json.dumps(text, ensure_ascii=False)
    dot = ['strict digraph { graph [bgcolor=transparent];',
           'node [penwidth=1.8]; edge [arrowhead=vee];']
    nodes = []
    groups: dict[str, list[str]] = {}
    for name in report["graph_nodes"]:
        labels = aliases.get(name, [])
        if not labels or any(label not in paper.statements for label in labels):
            raise ValueError(f"No rendered blueprint statement for {name}")
        groups.setdefault(labels[0], []).append(name)

    def role(name: str) -> str:
        if report["evidence"][name]["kind"] == "theorem":
            return "proof"
        return "definition" if paper.statements[aliases[name][0]]["kind"] == "definition" else "statement"

    for index, name in enumerate(report["graph_nodes"]):
        # Stable safe DOM IDs also support Lean names with punctuation.
        node_id = f"lean-{index}"
        labels = aliases[name]
        statement = paper.statements[labels[0]]
        label = labels[0].split(":", 1)[-1]
        if len(groups[labels[0]]) > 1:
            versions = [other for other in groups[labels[0]] if role(other) == role(name)]
            label += "\n" + role(name)
            if len(versions) > 1:
                label += f" {versions.index(name) + 1}"
        theorem = report["evidence"][name]["kind"] == "theorem"
        shape, color = ("ellipse", "#9CEC8B") if theorem else ("box", "#B0ECA3")
        dot.append(f'{q(node_id)} [label={q(label)}, shape={shape}, '
                   f'style=filled, color=green, fillcolor="{color}"];')
        content = statement_content(statement["content"], node_id)
        for other in labels[1:]:
            extra = paper.statements[other]
            content += (f'<p><a href="{html.escape(extra["url"], quote=True)}">'
                        f'{extra["caption"]} {extra["ref"]}: {extra["title"]}</a></p>'
                        + statement_content(extra["content"], node_id))
        status = {"proof": "Proved Lean theorem", "definition": "Lean definition / type",
                  "statement": "Lean statement interface"}[role(name)]
        link = "../lean/find/#doc/" + quote(name, safe=".")
        display_name = html.escape(name).replace(".", ".<wbr>").replace("_", "_<wbr>")
        content += (f'<p class="lean-version"><small>{status}: '
                    f'<a class="lean_decl" href="{link}"><code>{display_name}</code></a></small></p>'
                    f'<p>{source_link(name, "Lean source")} · '
                    f'<a href="{link}">Lean documentation</a> · '
                    f'<a href="lean_dependency_audit.html#{quote(labels[0], safe=":")}">'
                    'Version audit and paths</a></p>')
        nodes.append(GraphNode(id=node_id, thmName=statement["kind"], caption=statement["caption"],
                               ref=statement["ref"], title=statement["title"], content=content,
                               url=statement["url"]))
    ids = {name: node.id for name, node in zip(report["graph_nodes"], nodes)}
    for edge in report["edges"]:
        dot.append(f'{q(ids[edge["to"]])} -> {q(ids[edge["from"]])};')
    dot.append("}")

    template = files("plastexdepgraph").joinpath("templates/dep_graph.html").read_text()
    # Inherit the manuscript's MathJax setup, macros and styles along with its
    # rendered statements, without feeding that HTML back through Jinja.
    template = re.sub(r"<head>.*?</head>", "<head>{{ paper_head }}</head>", template, flags=re.S)
    # The upstream viewer embeds DOT in a JavaScript template literal. Use JSON
    # quoting so Lean declaration names cannot be interpreted as JavaScript.
    template = template.replace(".renderDot(`{{ dot.replace('\\n','') }}`)",
                                ".renderDot({{ dot_json }})")
    template = template.replace('<div class="content">', '<div class="content">\n'
                                '<nav aria-label="Dependency views">'
                                '<a href="lean_dependency_audit.html">Version audit and paths</a> · '
                                '<a href="dep_graph_document.html">Paper argument graph</a></nav>', 1)
    return Template(template).render(
        graph=SimpleNamespace(nodes=nodes), title="Lean dependencies",
        paper_head=re.sub(r"<title>.*?</title>", "<title>Lean proof dependencies</title>", paper.head, flags=re.S),
        config={"html5": {}},
        legend=[("Boxes", "definitions, types and statement interfaces"),
                ("Ellipses", "proved theorems and lemmas"),
                ("Green border", "the statement is formalized"),
                ("Green background", "the theorem's proof is formalized"),
                ("Light green background", "the definition or type is formalized"),
                ("Arrows", "from a dependency to the declaration using it; intermediate helpers are folded"),
                ("Scope", f"all {len(nodes)} reached blueprint declarations; "
                 '<a href="lean_dependency_audit.html">audit method and declaration versions</a>')],
        extra_modal_links=[],
        dot_json=json.dumps("\n".join(dot), ensure_ascii=False).replace("<", "\\u003c"),
    )


def write_site(site: Path, report: dict, paper_nodes: list[dict]) -> None:
    """Publish the default graph viewer and a separate version/witness audit."""
    entries = {entry["name"]: entry for entry in report["declarations"]}
    aliases: dict[str, list[str]] = {}
    for node in paper_nodes:
        for name in node["lean"]:
            aliases.setdefault(name, []).append(node["label"])
    edge_rows = []
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()

    def source_link(name: str, label: str | None = None) -> str:
        metadata = report["evidence"].get(name, entries.get(name))
        file = metadata["module"].replace(".", "/") + ".lean"
        url = f"https://github.com/Yu-Misaka/3d-sticky-kakeya/blob/{revision}/{quote(file)}"
        if metadata.get("line"):
            url += f"#L{metadata['line']}"
        caption = html.escape(label) if label else f'<code>{html.escape(name)}</code>'
        return f'<a href="{html.escape(url, quote=True)}">{caption}</a>'

    def path_details(path: list[dict]) -> str:
        if not path:
            return ""
        steps = "".join(f'<li>{source_link(step["from"])} — {step["kind"]} → '
                        f'{source_link(step["to"])}</li>' for step in path)
        return f'<details><summary>Witness: {len(path)} references</summary><ol>{steps}</ol></details>'

    for edge in report["edges"]:
        edge_rows.append(f'<li>{source_link(edge["to"])} → {source_link(edge["from"])}'
                         f'{path_details(edge["path"])}</li>')
    rows = []
    for node in paper_nodes:
        if node["kind"] == "remark":
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
        mark = ("Definition" if node["kind"] == "definition" else
                "Marked complete" if node["proof_complete"] else "Not marked complete")
        rows.append(f'<tr id="{html.escape(node["label"], quote=True)}"><td><code>{html.escape(node["label"])}</code>'
                    f'<br>{html.escape(node["title"])}</td><td>{mark}</td><td>{content}</td></tr>')
    used = sum(entry["reached"] for entry in entries.values())
    unused_proofs = sum(not entry["reached"] and entry["kind"] == "theorem" for entry in entries.values())
    template = (BLUEPRINT / "templates/lean_dependency_audit.html").read_text()
    substitutions = {
        "ROOT": html.escape(report["root"]),
        "COUNTS": f"{report['project_declarations']:,} project declarations inspected; {used}/{len(entries)} linked declarations reached; {unused_proofs} linked theorems proved but unused by this root.",
        "ROWS": "\n".join(rows), "EDGES": "\n".join(edge_rows),
        "SHA": html.escape(revision),
    }
    for name, text in substitutions.items():
        template = template.replace("{{" + name + "}}", text)
    paper = site / "blueprint/dep_graph_document.html"
    text = paper.read_text()
    (site / "blueprint/lean_dependency_audit.html").write_text(template)
    (site / "blueprint/lean_dependencies.html").write_text(render_graph(report, aliases, source_link, text))
    (site / "blueprint/lean-dependencies.json").write_text(json.dumps(report, ensure_ascii=False) + "\n")
    note = ('<p class="graph-audit-note">This graph follows the paper and manual completion marks. '
            '<a href="lean_dependencies.html">View the dependencies extracted from the Lean proof</a> '
            'and check which declaration versions are actually used.</p>')
    if 'class="graph-audit-note"' not in text:
        paper.write_text(text.replace('<div id="Legend">', note + '<div id="Legend">', 1))
