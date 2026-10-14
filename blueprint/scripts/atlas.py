#!/usr/bin/env python3
"""Reconcile the expert roadmap with the compiled declaration graph.

Only kernel witness paths can produce solid edges. Expert edges never enter
the graph used for reachability. A missing correspondence, an unused proof and
a proposition interface remain distinct, including in the generated cards.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter, deque
from pathlib import Path

from dependencies import BLUEPRINT, EDGE_KINDS, REPORT, reduce_edges

EXPERT = BLUEPRINT / "expert-atlas.json"
MAPPING = BLUEPRINT / "atlas-mapping.json"
REMARKS = BLUEPRINT / "src/chapters/atlas-correspondence.tex"


def declaration_role(entry: dict) -> str:
    if entry["kind"] == "constructor":
        return "constructor"
    if entry["kind"] == "axiom":
        return "axiom"
    if entry.get("is_proof", entry["kind"] == "theorem"):
        return "proof"
    if entry.get("is_proposition", False):
        return "interface"
    return "definition"


def declaration_status(entry: dict) -> str:
    return ("used-" if entry["reached"] else "unused-") + declaration_role(entry)


def load_sources() -> tuple[dict, dict]:
    return json.loads(EXPERT.read_text()), json.loads(MAPPING.read_text())


def expert_connections(expert: dict) -> list[dict]:
    """Retain the unified source records and connections found only in a branch."""
    connections = [{**edge, "expert_view": "all", "expert_view_title": "Unified expert graph"}
                   for edge in expert["edges"]]
    pairs = {(edge["from"], edge["to"]) for edge in connections}
    for view in expert["views"]:
        for edge in view["edges"]:
            pair = (edge["from"], edge["to"])
            if pair not in pairs:
                pairs.add(pair)
                connections.append({**edge, "expert_view": view["id"],
                                    "expert_view_title": view["title"]})
    return connections


def validate_mapping(expert: dict, mapping: dict, paper_nodes: list[dict],
                     entries: dict[str, dict] | None = None) -> None:
    expert_ids = [node["id"] for node in expert["nodes"]]
    mapped_ids = [node["id"] for node in mapping["nodes"]]
    if len(set(expert_ids)) != len(expert_ids) or sorted(mapped_ids) != sorted(expert_ids):
        raise ValueError("Every expert node must have exactly one reviewed correspondence")
    labels = {node["label"]: node for node in paper_nodes}
    for node in mapping["nodes"]:
        if not node.get("remark", "").strip():
            raise ValueError(f"Missing correspondence Remark: {node['id']}")
        for label in node["labels"] + node["remarks"]:
            if label not in labels:
                raise ValueError(f"Unknown manuscript label for {node['id']}: {label}")
        if any(labels[label]["kind"] != "remark" for label in node["remarks"]):
            raise ValueError(f"A difference link is not a Remark: {node['id']}")
        if node["primary"] and node["primary"] not in node["lean"]:
            raise ValueError(f"Primary declaration is not among the reviewed versions: {node['id']}")
        if len(node["lean"]) != len(set(node["lean"])):
            raise ValueError(f"Duplicate Lean version: {node['id']}")
        if entries is not None:
            missing = set(node["lean"]) - entries.keys()
            if missing:
                raise ValueError(f"Unaudited Lean correspondence for {node['id']}: {sorted(missing)}")
    groups = mapping["external_groups"]
    group_ids = [group["id"] for group in groups]
    external_ids = [key for group in groups for key in group["nodes"]]
    expected_external = {node["id"] for node in expert["nodes"] if node["group"] == "external"}
    if len(set(group_ids)) != len(group_ids) or len(set(external_ids)) != len(external_ids):
        raise ValueError("External groups must have unique names and members")
    if set(external_ids) != expected_external:
        raise ValueError("Every expert External node must belong to exactly one framed group")
    for view in expert["views"]:
        if not set(view["nodes"]) <= set(expert_ids):
            raise ValueError(f"Unknown expert node in view {view['id']}")
    for edge in expert["edges"] + [e for view in expert["views"] for e in view["edges"]]:
        if not {edge["from"], edge["to"]} <= set(expert_ids):
            raise ValueError("Expert edge has an unknown endpoint")


class AuditedPaths:
    """Compose the existing kernel witnesses, including through visible nodes.

    The declaration report contracts unlinked helpers and, on a DAG, removes
    transitive edges. Neither operation changes reachability. Checking only
    its displayed edge pairs would incorrectly label transitive uses dashed.
    """

    def __init__(self, report: dict):
        self.nodes = set(report["graph_nodes"])
        self.adjacency = {name: [] for name in self.nodes}
        for edge in report["edges"]:
            if edge["from"] not in self.nodes or edge["to"] not in self.nodes:
                raise ValueError("Audited edge endpoint is outside the root closure")
            if not edge["path"]:
                raise ValueError("An actual dependency needs a nonempty kernel witness")
            end = edge["from"]
            for step in edge["path"]:
                if step["from"] != end or step["kind"] not in EDGE_KINDS:
                    raise ValueError("Invalid kernel witness in declaration graph")
                end = step["to"]
            if end != edge["to"]:
                raise ValueError("Incomplete kernel witness in declaration graph")
            self.adjacency[edge["from"]].append(edge)
        for edges in self.adjacency.values():
            edges.sort(key=lambda edge: (edge["to"], len(edge["path"])))
        self.cache = {}

    def walk(self, start: str, stops: set[str] | None = None) -> dict:
        if start not in self.nodes:
            return {}
        parents = {start: None}
        pending = deque([start])
        while pending:
            name = pending.popleft()
            for edge in self.adjacency[name]:
                target = edge["to"]
                if target in parents:
                    continue
                parents[target] = edge
                if stops is None or target not in stops:
                    pending.append(target)
        return parents

    @staticmethod
    def path(parents: dict, target: str) -> list[dict]:
        parts = []
        while parents[target] is not None:
            edge = parents[target]
            parts.append(edge["path"])
            target = edge["from"]
        return [step for part in reversed(parts) for step in part]

    def between(self, consumer: str | None, prerequisite: str | None) -> list[dict] | None:
        if not consumer or not prerequisite or consumer == prerequisite:
            return None
        if consumer not in self.cache:
            self.cache[consumer] = self.walk(consumer)
        parents = self.cache[consumer]
        return self.path(parents, prerequisite) if prerequisite in parents else None


def classify_expert_edge(edge: dict, nodes: dict[str, dict], paths: AuditedPaths) -> dict:
    source, target = nodes[edge["from"]], nodes[edge["to"]]
    prerequisite, consumer = source["primary"], target["primary"]
    result = {"from": edge["from"], "to": edge["to"],
              "expert_kind": edge["kind"], "expert_note": edge.get("note", ""),
              "expert_view": edge.get("expert_view", "all"),
              "expert_view_title": edge.get("expert_view_title", "Unified expert graph")}
    path = paths.between(consumer, prerequisite)
    if path:
        return {**result, "classification": "actual", "path": path,
                "reason": "A path of compiled kernel references supports this connection."}
    if not prerequisite or not consumer:
        reason = "At least one expert operation has no independently identified primary Lean declaration."
        kind = "unmapped"
    elif prerequisite == consumer:
        reason = "The two expert nodes share one Lean declaration; this is not a dependency of that declaration on itself."
        kind = "shared-declaration"
    elif prerequisite not in paths.nodes or consumer not in paths.nodes:
        reason = "At least one selected Lean version is not in the sticky root's dependency closure. No global nondependence claim is made about unused proofs."
        kind = "outside-root"
    else:
        reason = "Both selected versions are reached, but the consumer has no path to the prerequisite in the complete projected kernel graph."
        kind = "different-route"
    return {**result, "classification": kind, "path": [], "reason": reason}


def projected_edges(selected: list[str], nodes: dict[str, dict], paths: AuditedPaths) -> list[dict]:
    owners = {}
    for key in selected:
        primary = nodes[key]["primary"]
        if primary in paths.nodes:
            owners.setdefault(primary, []).append(key)
    stops = set(owners)
    edges = []
    for consumer, consumers in sorted(owners.items()):
        parents = paths.walk(consumer, stops)
        for prerequisite in sorted(stops.intersection(parents) - {consumer}):
            path = paths.path(parents, prerequisite)
            for source in owners[prerequisite]:
                for target in consumers:
                    edges.append({"from": source, "to": target, "kind": "actual", "path": path})
    return edges


def make_atlas(report: dict, expert: dict, mapping: dict, paper_nodes: list[dict]) -> dict:
    entries = {entry["name"]: entry for entry in report["declarations"]}
    validate_mapping(expert, mapping, paper_nodes, entries)
    reviewed = {node["id"]: node for node in mapping["nodes"]}
    aliases = {}
    for node in paper_nodes:
        if node["kind"] == "remark":
            continue
        for name in node["lean"]:
            aliases.setdefault(name, []).append(node["label"])
    for node in mapping["nodes"]:
        for name in node["lean"]:
            aliases.setdefault(name, node["labels"] or ["rem:atlas-" + node["id"]])

    def external_group(name):
        module = entries[name]["module"]
        return next((group["id"] for group in mapping["external_groups"]
                     if any(module.startswith(prefix)
                            for prefix in group["module_prefixes"])), None)

    nodes = {}
    for source in expert["nodes"]:
        match = reviewed[source["id"]]
        primary = match["primary"]
        group = next((group["id"] for group in mapping["external_groups"]
                      if source["id"] in group["nodes"]), None)
        nodes[source["id"]] = {**source, **match, "expert": True,
            "external_group": group,
            "status": declaration_status(entries[primary]) if primary else "unmatched",
            "versions": [{**entries[name], "status": declaration_status(entries[name])}
                         for name in match["lean"]]}
    represented = {node["primary"] for node in nodes.values() if node["primary"]}
    paper = {node["label"]: node for node in paper_nodes}
    for name in report["graph_nodes"]:
        if name in represented:
            continue
        labels = aliases.get(name, [])
        if not labels:
            raise ValueError(f"No mathematical correspondence for reached declaration {name}")
        primary_label = labels[0]
        entry = entries[name]
        key = "lean-" + hashlib.sha256(name.encode()).hexdigest()[:16]
        nodes[key] = {"id": key, "primary": name, "lean": [name], "expert": False,
                      "group": "external" if external_group(name) else "implementation",
                      "external_group": external_group(name), "origin": "Lean",
                      "title": paper[primary_label]["title"], "paper": primary_label,
                      "statement": "", "labels": labels, "remarks": [],
                      "remark": "This separately displayed Lean version is reached from the root. Its role and hypotheses are recorded below; sharing a paper label does not identify two declarations.",
                      "status": declaration_status(entry),
                      "versions": [{**entry, "status": declaration_status(entry)}]}
    paths = AuditedPaths(report)
    proposed = expert_connections(expert)
    classified = [classify_expert_edge(edge, nodes, paths) for edge in proposed]

    def view_data(key, title, description, selected, proposed):
        selected = list(dict.fromkeys(selected))
        actual = reduce_edges(projected_edges(selected, nodes, paths))
        comparisons = [classify_expert_edge(edge, nodes, paths) for edge in proposed]
        # Supported expert edges are already represented by a solid path. Only
        # unsupported conceptual links are overlaid, always with dashed strokes.
        dashed = [{**edge, "kind": "expert"} for edge in comparisons
                  if edge["classification"] != "actual"]
        # The expert sometimes records two categories for the same connection.
        # Keep both source records in the comparison table, but draw one arrow.
        displayed = {}
        for edge in actual + dashed:
            displayed.setdefault((edge["from"], edge["to"], edge["kind"]), edge)
        return {"id": key, "title": title, "description": description,
                "nodes": selected, "edges": list(displayed.values()), "comparisons": comparisons}

    views = [view_data(view["id"], view["title"], view["description"], view["nodes"],
                      [{**edge, "expert_view": view["id"], "expert_view_title": view["title"]}
                       for edge in view["edges"]])
             for view in expert["views"]]
    external = [key for key, node in nodes.items() if node["external_group"]]
    views.append(view_data("external", "External inputs, opened in Lean",
                          "The expert's black boxes and the reached project proofs behind them. Each branch stays inside the External frame; library leaves remain boundaries.",
                          external, [edge for edge in proposed
                                     if edge["from"] in external and edge["to"] in external]))
    views.append(view_data("all", "Unified proof atlas",
                          "All expert nodes and every reached linked Lean version. Conclusions sit above prerequisites. Colours identify branches, not completion.",
                          list(nodes), proposed))
    result = {"format": 1, "root": report["root"],
              "root_node": next(key for key, node in nodes.items() if node["primary"] == report["root"]),
              "source_sha256": report["source_sha256"],
              "extractor_sha256": report["extractor_sha256"],
              "nodes": list(nodes.values()), "views": views, "expert_edges": classified,
              "external_groups": mapping["external_groups"],
              "counts": {"expert_nodes": len(expert["nodes"]),
                         "lean_versions": len(report["graph_nodes"]),
                         "expert_edges": len(classified),
                         "expert_unified_edges": len(expert["edges"]),
                         "expert_branch_only_edges": len(classified) - len(expert["edges"]),
                         "classifications": dict(sorted(Counter(edge["classification"] for edge in classified).items())),
                         "node_statuses": dict(sorted(Counter(node["status"] for node in nodes.values() if node["expert"]).items()))}}
    return result


def tex_escape(text: str) -> str:
    replacements = {"\\": r"\textbackslash{}", "&": r"\&", "%": r"\%", "$": r"\$",
                    "#": r"\#", "_": r"\_", "{": r"\{", "}": r"\}",
                    "^": r"\textasciicircum{}", "~": r"\textasciitilde{}"}
    return "".join(replacements.get(char, char) for char in text)


def correspondence_tex(expert: dict, mapping: dict) -> str:
    text = [r"% Generated by blueprint/scripts/atlas.py --remarks from atlas-mapping.json.",
            r"% Edit the reviewed mapping, then regenerate this appendix.",
            r"\chapter{The expert atlas and its Lean correspondence}",
            r"\label{chap:atlas-correspondence}", "",
            "The expert atlas contributes a mathematical reading order and 102 named nodes.",
            "Its Lean blocks are uncompiled sketches. The following remarks record the",
            "reviewed correspondence, including interfaces and related specializations.",
            "They do not add proof-completion marks. The interactive atlas computes usage",
            "and solid edges from the compiled theorem; dashed edges are expert connections",
            "without a supporting path between the selected versions in that root's closure.",
            "The external inputs and their actual project dependencies are framed together.", ""]
    sources = {node["id"]: node for node in expert["nodes"]}
    for node in mapping["nodes"]:
        key = node["id"]
        text += [r"\begin{remark}[Expert node " + tex_escape(key) + "]",
                 r"\label{rem:atlas-" + key + "}"]
        if node["lean"]:
            text.append(r"\lean{" + ",".join(node["lean"]) + "}")
        text += [tex_escape(sources[key]["paper"] + ": " + sources[key]["title"]) + ".",
                 tex_escape(node["remark"])]
        references = list(dict.fromkeys(node["labels"] + node["remarks"]))
        if references:
            text.append("See " + ", ".join(r"\ref{" + label + "}" for label in references) + ".")
        text += [r"\end{remark}", ""]
    return "\n".join(text)


def check_correspondence(paper_nodes: list[dict], report: dict | None = None) -> dict | None:
    expert, mapping = load_sources()
    validate_mapping(expert, mapping, paper_nodes)
    if not REMARKS.is_file() or REMARKS.read_text() != correspondence_tex(expert, mapping):
        raise ValueError("Atlas Remarks are stale; run python blueprint/scripts/atlas.py --remarks")
    return make_atlas(report, expert, mapping, paper_nodes) if report is not None else None


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--remarks", action="store_true", help="regenerate the mathematical correspondence appendix")
    args = parser.parse_args()
    expert, mapping = load_sources()
    if args.remarks:
        REMARKS.write_text(correspondence_tex(expert, mapping))
        print(f"Wrote {len(mapping['nodes'])} correspondence Remarks.")
    else:
        from check import check_registry, inspect_content
        _, names, paper_nodes = inspect_content()
        check_registry(names, paper_nodes)
        atlas = check_correspondence(paper_nodes, json.loads(REPORT.read_text()))
        print(json.dumps(atlas["counts"], indent=2))
