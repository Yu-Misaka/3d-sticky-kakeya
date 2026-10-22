"""Write the proof atlas: its data and layouts, the home page, the node cards and the roadmap evidence."""

from __future__ import annotations

import hashlib
import html
import json
import re
import subprocess
import textwrap
from collections import Counter
from pathlib import Path
from urllib.parse import quote

from atlas import EXPERT, MAPPING, declaration_role, load_sources, make_atlas
from dependencies import (BLUEPRINT, REPORT, ROOT, PaperStatements,
                          manuscript_statements, redirect_page, statement_content)

PALETTE = {
    "setup": "Wolff setup",
    "plane": "Plane maps",
    "grains": "Grains",
    "regularity": "Slope regularity",
    "slope": "Nonsingular slope",
    "projection": "Twisted projections",
    "cinematic": "Twisted projections and cinematic curves",
    "radial": "Radial projections",
    "external": "External inputs",
    "api": "Definitions and operations",
    "implementation": "Additional Lean versions",
}
STATUS = {
    "used-proof": "Used Lean proof",
    "unused-proof": "Proved version · outside root",
    "used-interface": "Used proposition interface",
    "unused-interface": "Proposition interface · outside root",
    "used-definition": "Used definition / data",
    "unused-definition": "Definition / data · outside root",
    "used-constructor": "Used constructor · fields required",
    "unused-constructor": "Constructor · outside root",
    "unmatched": "No primary Lean correspondence",
}
def source_url(metadata: dict, revision: str) -> str:
    module = metadata["module"]
    if module.startswith("Mathlib."):
        packages = json.loads((ROOT / "lake-manifest.json").read_text())["packages"]
        revision = next(p["rev"] for p in packages if p["name"].strip("«»") == "mathlib")
        repository = "https://github.com/leanprover-community/mathlib4"
    else:
        repository = "https://github.com/Yu-Misaka/3d-sticky-kakeya"
    url = f"{repository}/blob/{revision}/{quote(module.replace('.', '/') + '.lean')}"
    return url + (f"#L{metadata['line']}" if metadata.get("line") else "")


DIFF_TITLE = {
    "agree": "Lean and roadmap agree",
    "lean-only": "Lean only",
    "detail": "Lean detail",
    "expert-route": "Roadmap only · different Lean route",
    "expert-unknown": "Roadmap only · not comparable",
}
# How each roadmap connection compares with the compiled proof.
CLASSIFICATION_TITLE = {
    "actual": "Lean path",
    "different-route": "Different Lean route",
    "outside-root": "Version outside the root",
    "shared-declaration": "Shared declaration",
    "unmapped": "No Lean match",
}


def plain(text: str) -> str:
    return re.sub(r"\\[a-zA-Z]+|[{}$]", "", text)


def node_heading(node: dict) -> tuple[str, str]:
    """A paper reference and a short summary; added Lean versions borrow their statement's."""
    heading = node.get("graph_heading", node["paper"])
    summary = node.get("graph_summary", node["title"])
    if not node["expert"]:
        summary, separator, reference = node["title"].partition("; ")
        heading = reference.replace(", ", " ", 1) if separator else summary
        if not separator:
            summary = ""
    return heading, summary


# Node boxes have a fixed width; Graphviz reads points, which the browser draws 1:1.
NODE_WIDTH = 216
HEADING_CHARS, SUMMARY_CHARS = 23, 30


def label_lines(node: dict) -> tuple[list[str], list[str]]:
    """At most two lines each of paper reference and summary, as drawn in a node box."""
    heading, summary = node_heading(node)
    heading, summary = plain(heading).strip().rstrip(":"), plain(summary).strip()
    heads = textwrap.wrap(heading, HEADING_CHARS, break_long_words=False) or [node["id"]]
    lines = textwrap.wrap(summary, SUMMARY_CHARS, break_long_words=False)
    for wrapped, width in ((heads, HEADING_CHARS), (lines, SUMMARY_CHARS)):
        if len(wrapped) > 2:
            del wrapped[2:]
            wrapped[1] = wrapped[1][:width - 1].rstrip(" ,;") + "…"
    return heads, lines


def node_size(key: str, nodes: dict[str, dict]) -> tuple[float, float]:
    if key.startswith("group-"):
        return NODE_WIDTH + 24, 70
    heads, lines = label_lines(nodes[key])
    return NODE_WIDTH, round(16 + 17 * len(heads) + 15.5 * len(lines), 1)


def layout_view(view: dict, nodes: dict[str, dict], groups: list[dict]) -> dict:
    """Lay out one view with Graphviz. The browser draws the boxes and splines.

    Returns node boxes [x, y, width, height], one cubic spline per edge in the
    order of view["edges"], and the frames of the External clusters, all with
    the origin at the top left.
    """
    q = json.dumps
    folded = {"group-" + group for group in view.get("collapsed", [])}
    dot = ['digraph atlas {',
           'graph [rankdir=BT, nodesep=0.28, ranksep=0.55, newrank=true, compound=true, pad=0.2];',
           'node [shape=box, fixedsize=true, label=""];', 'edge [arrowhead=none];']

    def draw(key):
        width, height = node_size(key, nodes)
        dot.append(f"{q(key)} [width={width / 72:.3f}, height={height / 72:.3f}];")

    external = [key for key in view["nodes"] if key in folded or nodes[key]["external_group"]]
    for key in view["nodes"]:
        if key not in external:
            draw(key)
    if external:
        # Space for the frame titles, which the browser writes.
        dot.append('subgraph cluster_external { graph [margin=18, label=" ", fontsize=22];')
        for key in external:
            if key in folded:
                draw(key)
        for group in groups:
            members = [key for key in external if key not in folded
                       and nodes[key]["external_group"] == group["id"]]
            if members:
                dot.append(f'subgraph cluster_{group["id"]} {{ graph [margin=12, label=" ", fontsize=18];')
                for key in members:
                    draw(key)
                dot.append("}")
        dot.append("}")
    for index, edge in enumerate(view["edges"]):
        weight = ", weight=0.3" if edge["kind"] != "actual" else ""
        dot.append(f'{q(edge["from"])} -> {q(edge["to"])} [id="e{index}"{weight}];')
    dot.append("}")
    text = "\n".join(dot)
    cache = BLUEPRINT / "build/atlas-layout"
    cache.mkdir(parents=True, exist_ok=True)
    cache_file = cache / (hashlib.sha256(text.encode()).hexdigest() + ".json")
    if not cache_file.is_file():
        result = subprocess.run(["dot", "-Tjson"], input=text, capture_output=True,
                                text=True, check=True, timeout=120)
        cache_file.write_text(result.stdout)
    raw = json.loads(cache_file.read_text())
    x0, y0, x1, y1 = map(float, raw["bb"].split(","))
    # A small margin keeps rounded boxes inside the drawing.
    margin = 8
    flip = lambda x, y: (round(x - x0 + margin), round(y1 - y + margin))
    boxes, clusters = {}, []
    for item in raw.get("objects", []):
        if item["name"].startswith("cluster_"):
            left, bottom, right, top = map(float, item["bb"].split(","))
            (ax, ay), (bx, by) = flip(left, top), flip(right, bottom)
            clusters.append({"id": item["name"].removeprefix("cluster_"), "x": ax, "y": ay, "w": bx - ax, "h": by - ay})
        elif "pos" in item:
            x, y = flip(*map(float, item["pos"].split(",")))
            width, height = float(item["width"]) * 72, float(item["height"]) * 72
            boxes[item["name"]] = [round(x - width / 2), round(y - height / 2), round(width, 1), round(height, 1)]
    splines = {}
    for item in raw.get("edges", []):
        points = [flip(*map(float, point.split(","))) for point in item["pos"].split()
                  if not point.startswith(("e,", "s,"))]
        path = f"M{points[0][0]},{points[0][1]}" + "".join(
            f"C{points[i][0]},{points[i][1]} {points[i + 1][0]},{points[i + 1][1]} {points[i + 2][0]},{points[i + 2][1]}"
            for i in range(1, len(points) - 2, 3))
        splines[int(item["id"][1:]) if "id" in item else item["_gvid"]] = path
    missing = set(view["nodes"]) - boxes.keys()
    if missing or len(splines) != len(view["edges"]):
        raise ValueError(f"Graphviz did not place every node and edge of {view['id']}")
    return {"w": round(x1 - x0 + 2 * margin), "h": round(y1 - y0 + 2 * margin), "nodes": {key: boxes[key] for key in view["nodes"]},
            "splines": [splines[i] for i in range(len(view["edges"]))], "clusters": clusters}


def expert_math_html(text: str) -> str:
    """Escape source text; MathJax renders its math without executing source HTML."""
    text = html.escape(text)
    for macro, tag in (("emph", "em"), ("textbf", "strong"), ("texttt", "code")):
        text = re.sub(r"\\" + macro + r"\{([^{}]*)\}", rf"<{tag}>\1</{tag}>", text)
    return "".join("<p>" + paragraph.replace("\n", " ") + "</p>" for paragraph in text.split("\n\n"))


def status_mark(status: str) -> str:
    """The node mark for a Lean status: shape for the role, filled when the root uses it."""
    if status == "unmatched":
        inner = '<rect class="mk-none" x="1.5" y="1.5" width="11" height="11" rx="2.5"/>'
    else:
        reached, role = status.split("-", 1)
        cls = "mk used" if reached == "used" else "mk off"
        inner = {"proof": f'<circle class="{cls}" cx="7" cy="7" r="4.1"/>',
                 "interface": f'<path class="{cls}" d="M7 2 12 7 7 12 2 7Z"/>',
                 "definition": f'<rect class="{cls}" x="3.4" y="3.4" width="7.2" height="7.2"/>'}.get(
            role, f'<path class="{cls}" d="M7 2.3 11.7 10.8 2.3 10.8Z"/>')
    return f'<svg class="mark" width="14" height="14" viewBox="0 0 14 14" aria-hidden="true">{inner}</svg>'


def sitebar(current: str) -> str:
    """The site bar, for pages under blueprint/ that are not Jinja templates."""
    from jinja2 import Environment, FileSystemLoader
    environment = Environment(loader=FileSystemLoader(BLUEPRINT / "templates"), autoescape=True)
    return environment.get_template("_sitebar.html").module.sitebar(current)


def connection_anchor(edge: dict) -> str:
    return f"connection-{edge['from']}-{edge['to']}"


def lean_only_anchor(edge: dict) -> str:
    return f"lean-only-{edge['from']}-{edge['to']}"


def audit_rows(atlas: dict) -> tuple[list[dict], list[dict]]:
    """Rows of the evidence page: every roadmap connection, and every Lean-only arrow."""
    drawn = {(edge["from"], edge["to"]) for view in atlas["views"] for edge in view["edges"]}
    seen = Counter()
    connections = []
    for edge in atlas["expert_edges"]:
        anchor = connection_anchor(edge)
        seen[anchor] += 1
        # The expert records two categories for a few connections; both rows stay.
        connections.append({**edge, "anchor": anchor if seen[anchor] == 1 else f"{anchor}-{seen[anchor]}",
                            "drawn": (edge["from"], edge["to"]) in drawn})
    lean_only = {}
    for view in atlas["views"]:
        for edge in view["edges"]:
            if edge["diff"] == "lean-only":
                row = lean_only.setdefault((edge["from"], edge["to"]),
                                           {**edge, "anchor": lean_only_anchor(edge), "views": []})
                row["views"].append(view["title"])
    return connections, list(lean_only.values())


def connection_records(atlas: dict) -> dict[str, dict]:
    """One record per drawn (from, to, kind): its class, reason, roadmap notes and evidence row."""
    notes: dict[tuple, list[str]] = {}
    for edge in atlas["expert_edges"]:
        notes.setdefault((edge["from"], edge["to"]), []).append(edge["expert_note"])
    records = {}
    for view in atlas["views"]:
        for edge in view["edges"]:
            key = f"{edge['from']}>{edge['to']}>{edge['kind']}"
            pair = (edge["from"], edge["to"])
            if key in records:
                continue
            anchor = (lean_only_anchor(edge) if edge["diff"] == "lean-only"
                      else connection_anchor(edge) if pair in notes else None)
            records[key] = {"diff": edge["diff"], "classification": edge.get("classification"),
                            "reason": edge.get("reason"), "notes": notes.get(pair, []),
                            "audit": "atlas-audit.html#" + anchor if anchor else None}
    return records


def layout_key(variant: str) -> str:
    """Whole-proof layouts: "all" folds every frame, "all-<group>" opens one, "all-full" opens all."""
    return {"collapsed": "all", "full": "all-full"}.get(variant, "all-" + variant.removeprefix("expand-"))


def atlas_links(data: dict) -> list[str]:
    """Links the atlas page builds from its data, checked with the site's other links."""
    links = [edge["audit"] for edge in data["connections"].values() if edge["audit"]]
    for node in data["nodes"]:
        links += [statement["url"] for statement in node["statements"]]
        links += [link["url"] for link in node["remark_links"]]
        links += [version["doc"] for version in node["versions"]]
    return links


def page_data(atlas: dict, nodes: dict[str, dict], cards: list[dict], evidence: dict, revision: str) -> dict:
    """Everything the atlas page draws: nodes and cards, layouts, connections and witnesses."""
    paths: dict[str, int] = {}
    table: list[list] = []

    def path_index(path):
        steps = [[step["from"], step["to"], step["kind"]] for step in path]
        key = json.dumps(steps)
        if key not in paths:
            paths[key] = len(table)
            table.append(steps)
        return paths[key]

    def drawn(edge, spline=None):
        record = {"from": edge["from"], "to": edge["to"], "kind": edge["kind"], "diff": edge["diff"]}
        if spline:
            record["d"] = spline
        if edge.get("path"):
            record["p"] = path_index(edge["path"])
        if "members" in edge:
            record["members"] = [[m["from"], m["to"], m["kind"], path_index(m["path"]) if m.get("path") else None]
                                 for m in edge["members"]]
        return record

    groups = atlas["external_groups"]
    sources = [(view["id"], view) for view in atlas["views"] if view["id"] != "all"]
    sources += [(layout_key(variant["id"]), variant) for variant in atlas["unified_variants"]]
    layouts = {}
    for key, view in sources:
        placed = layout_view(view, nodes, groups)
        layouts[key] = {"w": placed["w"], "h": placed["h"], "nodes": placed["nodes"], "clusters": placed["clusters"],
                        "edges": [drawn(edge, spline) for edge, spline in zip(view["edges"], placed["splines"])]}
    records = []
    for card in cards:
        heads, lines = label_lines(card)
        records.append({
            "id": card["id"], "group": card["group"], "expert": card["expert"], "origin": card.get("origin"),
            "paper": card["paper"], "title": card["title"], "source": card.get("source"),
            "heading": heads, "summary": lines, "full_heading": card["heading"].rstrip(":"),
            "status": card["status"], "primary": card["primary"], "external": card["external_group"],
            "remark": card["remark"], "labels": card["labels"],
            "statements": [{"heading": str(statement["heading"]), "url": statement["url"],
                            "html": str(statement["content"])} for statement in card["statements"]],
            "expert_html": str(card["expert_statement_html"]) if card["expert"] else "",
            "remark_links": [{"label": link["label"].removeprefix("rem:"), "url": link["url"]}
                             for link in card["remark_links"]],
            "versions": [{"name": version["name"], "kind": version["kind"], "role": version["role"],
                          "reached": version["reached"], "type": version.get("expanded_type") or version.get("type"),
                          "definition": version.get("definition"), "doc": version["doc_url"],
                          "src": version["source_url"], "p": path_index(version["path"]) if version["path"] else None}
                         for version in card["versions"]]})
    modules: dict[str, int] = {}
    located = {}
    for name in sorted({name for steps in table for step in steps for name in step[:2]}):
        metadata = evidence[name]
        located[name] = [modules.setdefault(metadata["module"], len(modules)), metadata.get("line")]
    packages = json.loads((ROOT / "lake-manifest.json").read_text())["packages"]
    return {"format": 1, "root": atlas["root"], "root_node": atlas["root_node"], "counts": atlas["counts"],
            "repository": "https://github.com/Yu-Misaka/3d-sticky-kakeya", "revision": revision,
            "mathlib_revision": next(p["rev"] for p in packages if p["name"].strip("«»") == "mathlib"),
            "views": [{"id": view["id"], "title": view["title"], "description": view["description"],
                       "count": len(view["nodes"])} for view in atlas["views"] if view["id"] != "all"],
            "groups": [{"id": group["id"], "title": group["title"]} for group in groups],
            "branches": PALETTE, "status": STATUS, "diff_titles": DIFF_TITLE,
            "nodes": records, "connections": connection_records(atlas), "layouts": layouts,
            "paths": table, "modules": list(modules), "sources": located}


def write_atlas(site: Path, report: dict, paper_nodes: list[dict], paper_html: str) -> None:
    from jinja2 import Environment, FileSystemLoader, select_autoescape
    from markupsafe import Markup

    expert, mapping = load_sources()
    environment = Environment(loader=FileSystemLoader(BLUEPRINT / "templates"),
                              autoescape=select_autoescape(["html"]))
    atlas = make_atlas(report, expert, mapping, paper_nodes)
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    atlas["provenance"] = {"expert_sources": expert["sources"], "revision": revision,
        "expert_sha256": hashlib.sha256(EXPERT.read_bytes()).hexdigest(),
        "mapping_sha256": hashlib.sha256(MAPPING.read_bytes()).hexdigest(),
        "declaration_report_sha256": hashlib.sha256(REPORT.read_bytes()).hexdigest()}
    nodes = {node["id"]: node for node in atlas["nodes"]}
    missing_groups = {node["group"] for node in nodes.values()} - PALETTE.keys()
    if missing_groups:
        raise ValueError(f"Expert branches have no presentation or filter: {sorted(missing_groups)}")
    entries = {entry["name"]: entry for entry in report["declarations"]}
    evidence = {**report["evidence"], **entries}
    paper = PaperStatements(paper_html)
    paper.statements.update(manuscript_statements(site / "blueprint"))

    def source_link(name):
        return '<a href="' + html.escape(source_url(evidence[name], revision), quote=True) + '"><code>' + html.escape(name) + '</code></a>'

    def path_html(path):
        if not path:
            return ""
        steps = "".join('<li>' + source_link(step["from"]) + ' <span class="reference-kind">' +
                        html.escape(step["kind"]) + '</span> → ' + source_link(step["to"]) + '</li>' for step in path)
        return '<details class="witness"><summary>Kernel witness · ' + str(len(path)) + ' references</summary><ol>' + steps + '</ol></details>'

    cards = []
    for node in atlas["nodes"]:
        card = {**node, "group_name": PALETTE.get(node["group"], PALETTE["api"]),
                "status_label": STATUS.get(node["status"], node["status"]), "statements": [],
                "expert_statement_html": Markup(expert_math_html(node["statement"])),
                "remark_links": [], "versions": []}
        for index, label in enumerate(node["labels"]):
            statement = paper.statements.get(label)
            if statement is None:
                raise ValueError(f"Atlas statement is absent from the rendered manuscript: {label}")
            content = statement_content(statement["content"], "atlas-" + node["id"] + "-" + str(index),
                                        statement.get("url", "index.html").split("#")[0])
            card["statements"].append({**statement, "content": Markup(content),
                "heading": Markup(" ".join(statement.get(key, "") for key in ("caption", "ref", "title"))),
                "url": statement.get("url", "index.html#" + quote(label, safe=":"))})
        for label in node["remarks"]:
            remark = paper.statements.get(label, {})
            card["remark_links"].append({"label": label,
                "url": remark.get("url", "index.html#" + quote(label, safe=":"))})
        for entry in node["versions"]:
            card["versions"].append({**entry, "status_label": STATUS.get(entry["status"], entry["status"]),
                "role": declaration_role(entry), "doc_url": "../lean/find/#doc/" + quote(entry["name"], safe="."),
                "source_url": source_url(entry, revision), "path_html": Markup(path_html(entry["path"]))})
        card["heading"] = plain(node_heading(node)[0])
        cards.append(card)
    destination = site / "blueprint"
    data = page_data(atlas, nodes, cards, evidence, revision)
    (destination / "atlas-view.json").write_text(json.dumps(data, ensure_ascii=False, separators=(",", ":")))
    branch_views = [view for view in atlas["views"] if view["id"] != "all"]
    (destination / "lean_dependencies.html").write_text(environment.get_template("atlas.html").render(
        atlas=atlas, views=branch_views, counts=atlas["counts"]))
    # The leanblueprint menu's historical graph route forwards to the reviewed
    # atlas. The generated paper DOT must not keep unaudited solid arrows.
    (destination / "dep_graph_document.html").write_text(
        redirect_page("lean_dependencies.html", "the proof atlas"))
    (destination / "atlas-cards.html").write_text(
        environment.get_template("atlas_cards.html").render(cards=cards))
    # The whole-proof variants are derived from the "all" view; their layouts
    # are in atlas-view.json and their witnesses are those of the "all" view.
    published = {key: value for key, value in atlas.items() if key != "unified_variants"}
    (destination / "atlas-dependencies.json").write_text(json.dumps(published, ensure_ascii=False) + "\n")

    def ends(row):
        heading = lambda key: plain(node_heading(nodes[key])[0]).strip().rstrip(":")
        return {"from_heading": heading(row["from"]), "to_heading": heading(row["to"]),
                "path_html": Markup(path_html(row["path"]))}

    connections, lean_only = audit_rows(atlas)
    # The expert's notes repeat the arrow before a colon; the table shows it already.
    connections = [{**row, **ends(row), "title": CLASSIFICATION_TITLE[row["classification"]],
                    "note": row["expert_note"].removeprefix(f"{row['from']} → {row['to']}: ")} for row in connections]
    lean_only = [{**row, **ends(row)} for row in lean_only]
    audit = environment.get_template("atlas_audit.html").render(
        atlas=atlas, connections=connections, lean_only=lean_only, counts=atlas["counts"],
        classifications=CLASSIFICATION_TITLE, diff_titles=DIFF_TITLE)
    (destination / "atlas-audit.html").write_text(audit)
    # The home page shows the theorem as the manuscript states it, and the atlas's own counts.
    root = paper.statements["thm:sticky"]
    order = ["used-proof", "used-interface", "used-definition", "used-constructor", "unused-proof",
             "unused-interface", "unused-definition", "unused-constructor", "unmatched"]
    statuses = atlas["counts"]["node_statuses"]
    tally = [(key, statuses[key]) for key in order if statuses.get(key)]
    (site / "index.html").write_text(environment.get_template("home.html").render(
        atlas=atlas, counts=atlas["counts"], views=branch_views, status=STATUS, diff_titles=DIFF_TITLE,
        node_tally=tally, marks={key: Markup(status_mark(key)) for key, _ in tally},
        edge_total=sum(atlas["counts"]["unified_diff"].values()),
        statement={**root, "content": Markup(statement_content(root["content"], "home", root["url"].split("#")[0]))}))
    print(f"Rendered atlas: {len(nodes)} display nodes, {len(branch_views)} views, "
          f"{len(expert['nodes'])} expert correspondences, {len(data['layouts'])} layouts.", flush=True)
