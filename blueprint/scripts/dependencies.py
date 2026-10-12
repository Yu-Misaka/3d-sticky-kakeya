#!/usr/bin/env python3
"""Audit and display the sticky theorem's compiled Lean dependencies."""

from __future__ import annotations

import hashlib
import html
import json
import subprocess
import textwrap
from collections import Counter, deque
from pathlib import Path
from urllib.parse import quote

ROOT = Path(__file__).resolve().parents[2]
BLUEPRINT = ROOT / "blueprint"
REPORT = BLUEPRINT / "lean-dependencies.json"
RAW = BLUEPRINT / "build/lean-dependencies.jsonl"
EXTRACTOR = BLUEPRINT / "scripts/dependencies.lean"
THEOREM = "Kakeya.Assouad.PureWZ2Theorem5_2Unconditional"
EDGE_KINDS = ("value", "type", "structural")


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
    # Keep exact Lean theorem names separate even when one paper node links several versions.
    selected = {name for name in indexed if name in graph and graph[name]["kind"] == "theorem"}
    selected.add(root)
    selected.update(name for name in graph[root]["value"] if graph[name]["kind"] == "theorem")
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
        "format": 1, "root": root, "module_roots": module_roots,
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
    if (report.get("format") != 1 or report.get("root") != THEOREM
            or report.get("source_sha256") != source_sha256
            or report.get("extractor_sha256") != extractor_digest()):
        raise ValueError("Lean dependency audit is stale; run python blueprint/scripts/check.py --lean")
    expected = {record["name"]: record for record in records}
    if sorted(entry["name"] for entry in report["declarations"]) != sorted(expected):
        raise ValueError("Lean dependency audit differs from the blueprint declaration links")
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


def write_site(site: Path, report: dict, paper_nodes: list[dict]) -> None:
    """Reuse the blueprint's Graphviz viewer and preserve the paper graph beside it."""
    entries = {entry["name"]: entry for entry in report["declarations"]}
    aliases: dict[str, list[str]] = {}
    for node in paper_nodes:
        for name in node["lean"]:
            aliases.setdefault(name, []).append(node["label"])
    q = lambda text: json.dumps(text, ensure_ascii=False)
    dot = ['digraph { rankdir=LR; graph [bgcolor="transparent", ranksep="0.6"];',
           'node [shape=box, style="rounded,filled", fillcolor="#e6f3e6", color="#56845c", fontname="sans-serif"];',
           'edge [color="#6b7787", arrowsize="0.7"];']
    assembly_dot = dot.copy()
    assembly_names = {report["root"], *report["root_inputs"]}
    for name in report["graph_nodes"]:
        short = name.rsplit(".", 1)[-1]
        caption = "\n".join([*aliases.get(name, []), *textwrap.wrap(short, width=38)])
        color = ", fillcolor=\"#b7dfbf\"" if name == report["root"] else ""
        line = (f'{q(name)} [label={q(caption)}, tooltip={q(name)}, '
                f'URL={q("../lean/find/#doc/" + quote(name, safe="."))}{color}];')
        dot.append(line)
        if name in assembly_names:
            assembly_dot.append(line)
    edge_rows = []
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()

    def source_link(name: str) -> str:
        metadata = report["evidence"].get(name, entries.get(name))
        file = metadata["module"].replace(".", "/") + ".lean"
        url = f"https://github.com/Yu-Misaka/3d-sticky-kakeya/blob/{revision}/{quote(file)}"
        if metadata.get("line"):
            url += f"#L{metadata['line']}"
        return f'<a href="{html.escape(url, quote=True)}"><code>{html.escape(name)}</code></a>'

    def path_details(path: list[dict]) -> str:
        if not path:
            return ""
        steps = "".join(f'<li>{source_link(step["from"])} — {step["kind"]} → '
                        f'{source_link(step["to"])}</li>' for step in path)
        return f'<details><summary>Witness: {len(path)} references</summary><ol>{steps}</ol></details>'

    for edge in report["edges"]:
        # Arrow direction matches the mathematical graph: dependency → consumer.
        dot.append(f'{q(edge["to"])} -> {q(edge["from"])};')
        edge_rows.append(f'<li>{source_link(edge["to"])} → {source_link(edge["from"])}'
                         f'{path_details(edge["path"])}</li>')
    dot.append("}")
    assembly_dot.extend(f'{q(name)} -> {q(report["root"])};' for name in report["root_inputs"])
    assembly_dot.append("}")
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
    template = (BLUEPRINT / "templates/lean_dependencies.html").read_text()
    substitutions = {
        "ROOT": html.escape(report["root"]),
        "COUNTS": f"{report['project_declarations']:,} project declarations inspected; {used}/{len(entries)} linked declarations reached; {unused_proofs} linked theorems proved but unused by this root.",
        "ROWS": "\n".join(rows), "EDGES": "\n".join(edge_rows),
        "DOT": json.dumps("\n".join(dot), ensure_ascii=False).replace("<", "\\u003c"),
        "ASSEMBLY_DOT": json.dumps("\n".join(assembly_dot), ensure_ascii=False).replace("<", "\\u003c"),
        "SHA": html.escape(revision),
    }
    for name, text in substitutions.items():
        template = template.replace("{{" + name + "}}", text)
    (site / "blueprint/lean_dependencies.html").write_text(template)
    (site / "blueprint/lean-dependencies.json").write_text(json.dumps(report, ensure_ascii=False) + "\n")
    paper = site / "blueprint/dep_graph_document.html"
    text = paper.read_text()
    note = ('<p class="graph-audit-note">This graph follows the paper and manual completion marks. '
            '<a href="lean_dependencies.html">View the dependencies extracted from the Lean proof</a> '
            'and check which declaration versions are actually used.</p>')
    if 'class="graph-audit-note"' not in text:
        paper.write_text(text.replace('<div id="Legend">', note + '<div id="Legend">', 1))
