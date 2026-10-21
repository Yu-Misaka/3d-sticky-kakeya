"""Render the reviewed atlas using the expert's branch-and-card presentation."""

from __future__ import annotations

import hashlib
import html
import json
import re
import subprocess
import textwrap
import xml.etree.ElementTree as ET
from collections import Counter
from pathlib import Path
from urllib.parse import quote

from atlas import EXPERT, MAPPING, declaration_role, load_sources, make_atlas
from dependencies import (BLUEPRINT, REPORT, ROOT, PaperStatements,
                          manuscript_statements, redirect_page, statement_content)

PALETTE = {
    "setup": ("Wolff setup", "#e6eefb", "#56749c"),
    "plane": ("Plane maps", "#eaeafa", "#7874a5"),
    "grains": ("Grains", "#e6f3ec", "#578d75"),
    "regularity": ("Slope regularity", "#f0e9f8", "#8a6ca2"),
    "slope": ("Nonsingular slope", "#fff0df", "#b17b3f"),
    "projection": ("Twisted projections", "#e6f1f8", "#507f9d"),
    "cinematic": ("Twisted projections and cinematic curves", "#e6f1f8", "#507f9d"),
    "radial": ("Radial projections", "#eff3df", "#829358"),
    "external": ("External inputs", "#f0f2f6", "#7c8c9f"),
    "api": ("Definitions and operations", "#edf2f8", "#75889f"),
    "implementation": ("Additional Lean versions", "#eaf1f6", "#657d94"),
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
GRAPH_STATUS = {**STATUS, "used-proof": "Lean proof · used", "unused-proof": "Lean proof · outside root",
                "used-interface": "Prop interface · used", "unused-interface": "Prop interface · outside root",
                "used-definition": "Definition / data · used", "unused-definition": "Data · outside root"}


def edge_id(edge: dict) -> str:
    data = [edge["from"], edge["to"], edge.get("kind", "expert"), edge.get("path", [])]
    return "edge-" + hashlib.sha256(json.dumps(data, sort_keys=True).encode()).hexdigest()[:16]


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


# Graphviz strokes for each comparison class. Colour is never the only cue:
# the classes also differ in dash pattern or weight.
DIFF_STYLE = {
    "agree": {"style": "solid", "color": "#355572", "penwidth": "1.4"},
    "lean-only": {"style": "bold", "color": "#a3246f", "penwidth": "2.6"},
    "detail": {"style": "solid", "color": "#9eacbb", "penwidth": "0.9"},
    "expert-route": {"style": "dashed", "color": "#6f4aa8", "penwidth": "1.6"},
    "expert-unknown": {"style": "dotted", "color": "#a9b2bd", "penwidth": "1.1"},
}
DIFF_TITLE = {
    "agree": "Lean and roadmap agree",
    "lean-only": "Lean only",
    "detail": "Lean detail",
    "expert-route": "Roadmap only · different Lean route",
    "expert-unknown": "Roadmap only · not comparable",
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


def graph_label(node: dict, compact: bool = False) -> str:
    """Give paper references, summaries and Lean status distinct visual roles."""
    heading, summary = node_heading(node)

    def lines(text):
        return '<BR/>'.join(html.escape(line, quote=False) for line in
                           textwrap.wrap(plain(text), 29, break_long_words=False, break_on_hyphens=False))

    status = GRAPH_STATUS.get(node["status"], node["status"])
    rows = '<TR><TD><B>' + lines(heading) + '</B></TD></TR>'
    if compact:
        # The summary and status move to the tooltip and the details panel.
        return '<TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0" CELLPADDING="0">' + rows + '</TABLE>'
    if summary:
        rows += '<TR><TD>' + lines(summary) + '</TD></TR>'
    rows += ('<TR><TD CELLPADDING="3"><FONT POINT-SIZE="10" COLOR="#617389">' +
             html.escape(status, quote=False) + '</FONT></TD></TR>')
    return '<TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0" CELLPADDING="0">' + rows + '</TABLE>'


def drawn_id(edge: dict) -> str:
    return edge_id(edge) + ("-" + edge["diff"] if "members" in edge else "")


def edge_audit(edge: dict) -> str:
    """A folded edge links to the witness of its first member."""
    return "atlas-audit.html#" + edge_id(edge.get("members", [edge])[0])


def render_svg(view: dict, nodes: dict[str, dict], groups: list[dict], compact: bool = False) -> str:
    q = lambda value: json.dumps(value, ensure_ascii=False)
    titles = {group["id"]: group["title"] for group in groups}
    folded = {"group-" + group for group in view.get("collapsed", [])}
    sizes = Counter(node["external_group"] for node in nodes.values() if node["external_group"])
    dot = ['digraph atlas {',
           'graph [rankdir=BT, bgcolor="transparent", pad="0.25", nodesep="0.32", ranksep="0.65", compound=true, newrank=true];',
           'node [fontname="DejaVu Sans", fontsize=13, margin="0.16,0.10", penwidth=1.2];',
           'edge [arrowhead=vee, arrowsize=0.65, color="#355572", penwidth=1.3];']

    def draw_node(key):
        node = nodes[key]
        _, background, border = PALETTE.get(node["group"], PALETTE["api"])
        entry = next((v for v in node["versions"] if v["name"] == node["primary"]), None)
        shape = "ellipse" if entry and declaration_role(entry) == "proof" else "box"
        status = GRAPH_STATUS.get(node["status"], node["status"])
        tooltip = f"{node['id']} | {node['paper']}: {node['title']}. {status}. See the Remark for the scope of this version."
        attrs = {"id": f"{view['id']}-node-{key}", "class": "graphnode " + node["status"],
                 "shape": shape, "style": "filled" if shape == "ellipse" else "rounded,filled",
                 "fillcolor": background, "color": border, "fontcolor": "#243449",
                 "URL": "#node-" + key, "tooltip": tooltip}
        dot.append(q(key) + " [label=<" + graph_label(node, compact) + ">, " +
                   ", ".join(k + "=" + q(v) for k, v in attrs.items()) + "];")

    def draw_group(key):
        group = key.removeprefix("group-")
        label = ('<TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0" CELLPADDING="0"><TR><TD><B>' +
                 html.escape(titles[group], quote=False) + '</B></TD></TR><TR><TD CELLPADDING="3">'
                 '<FONT POINT-SIZE="10" COLOR="#617389">' + str(sizes[group]) +
                 ' nodes · click to open</FONT></TD></TR></TABLE>')
        attrs = {"id": f"{view['id']}-node-{key}", "class": "graphnode groupnode", "shape": "box3d",
                 "style": "filled", "fillcolor": "#ffffff", "color": "#7c8c9f", "fontcolor": "#243449",
                 "URL": "#group-" + group, "tooltip": titles[group] + ": folded External frame. Click to open it."}
        dot.append(q(key) + " [label=<" + label + ">, " +
                   ", ".join(k + "=" + q(v) for k, v in attrs.items()) + "];")

    external = [key for key in view["nodes"] if key in folded or nodes[key]["external_group"]]
    for key in view["nodes"]:
        if key not in external:
            draw_node(key)
    if external:
        dot += ['subgraph cluster_external {',
                'graph [label="External inputs · expanded Lean dependencies", labelloc=t, labeljust=l, '
                'fontname="DejaVu Sans", fontsize=14, color="#a0afc2", fontcolor="#526981", '
                'style="rounded,filled", fillcolor="#f5f7fb", margin=20];']
        for key in external:
            if key in folded:
                draw_group(key)
        for group in groups:
            members = [key for key in external if key not in folded
                       and nodes[key]["external_group"] == group["id"]]
            if not members:
                continue
            dot += [f'subgraph cluster_{group["id"]} {{',
                    'graph [id=' + q(view["id"] + '-external-' + group["id"]) +
                    ', label=' + q(group["title"]) + ', labelloc=t, labeljust=l, fontsize=11, style="rounded", margin=14];']
            for key in members:
                draw_node(key)
            dot.append("}")
        dot.append("}")
    for edge in view["edges"]:
        actual = edge["kind"] == "actual"
        members = edge.get("members", [])
        if len(members) > 1:
            label = f"{len(members)} connections folded into this arrow. Click to open the frame."
        elif actual:
            label = f"Lean kernel path: {len(edge['path'])} references. Click to open the witness."
        else:
            label = "Expert connection: " + edge["reason"]
        attrs = {"id": view["id"] + "-" + drawn_id(edge),
                 "class": "depedge " + edge["kind"] + " diff-" + edge["diff"],
                 "tooltip": DIFF_TITLE[edge["diff"]] + ". " + label,
                 "URL": edge_audit(edge), "target": "_blank", **DIFF_STYLE[edge["diff"]]}
        if not actual:
            attrs["weight"] = "0.3"
        dot.append(q(edge["from"]) + " -> " + q(edge["to"]) + " [" +
                   ", ".join(k + "=" + q(v) for k, v in attrs.items()) + "];")
    dot.append("}")
    dot_text = "\n".join(dot)
    cache = BLUEPRINT / "build/atlas-svg"
    cache.mkdir(parents=True, exist_ok=True)
    cache_file = cache / (hashlib.sha256(dot_text.encode()).hexdigest() + ".svg")
    if not cache_file.is_file():
        result = subprocess.run(["dot", "-Tsvg"], input=dot_text, capture_output=True,
                                text=True, check=True, timeout=120)
        cache_file.write_text(result.stdout)
    svg = ET.fromstring(cache_file.read_text())
    ns = "http://www.w3.org/2000/svg"
    ET.register_namespace("", ns)
    ET.register_namespace("xlink", "http://www.w3.org/1999/xlink")
    svg.attrib.update({"class": "depgraph", "data-view": view["id"], "role": "img",
                       "aria-label": view["title"], "id": "graph-" + view["id"]})
    svg.attrib.pop("width", None)
    svg.attrib.pop("height", None)
    edges = {view["id"] + "-" + drawn_id(edge): edge for edge in view["edges"]}
    for element in svg.iter():
        key = element.get("id", "")
        # Graphviz also emits graph0, clust1 and anchor IDs. All twelve SVGs
        # share one HTML document, so these generated IDs need a view prefix.
        if key and key != svg.get("id") and not key.startswith(view["id"] + "-"):
            element.set("id", view["id"] + "-" + key)
        group_prefix = view["id"] + "-external-"
        if key.startswith(group_prefix):
            element.set("data-external-group", key.removeprefix(group_prefix))
        prefix = view["id"] + "-node-"
        if key.startswith(prefix):
            node_key = key.removeprefix(prefix)
            if node_key in folded:
                group = node_key.removeprefix("group-")
                element.attrib.update({"data-node": node_key, "data-group": group, "tabindex": "0",
                                       "role": "button", "aria-label": "Open the External frame " + titles[group]})
            else:
                node = nodes[node_key]
                element.attrib.update({"data-node": node_key, "tabindex": "0", "role": "button",
                                       "aria-label": node["paper"] + ": " + node["title"],
                                       "data-heading": plain(node_heading(node)[0]),
                                       "data-title": plain(node["title"])})
                if node["external_group"]:
                    element.set("data-group", node["external_group"])
        if key in edges:
            edge = edges[key]
            element.attrib.update({"data-from": edge["from"], "data-to": edge["to"],
                                   "data-kind": edge["kind"], "data-diff": edge["diff"],
                                   "tabindex": "0", "role": "link", "data-audit": edge_audit(edge),
                                   "aria-label": DIFF_TITLE[edge["diff"]] + " edge " + edge["from"] + " to " + edge["to"]})
            if len(edge.get("members", [])) > 1:
                element.set("data-members", " ".join(
                    member["from"] + ">" + member["to"] + ">" + edge_id(member) for member in edge["members"]))
    return ET.tostring(svg, encoding="unicode")


def expert_math_html(text: str) -> str:
    """Escape source text; MathJax renders its math without executing source HTML."""
    text = html.escape(text)
    for macro, tag in (("emph", "em"), ("textbf", "strong"), ("texttt", "code")):
        text = re.sub(r"\\" + macro + r"\{([^{}]*)\}", rf"<{tag}>\1</{tag}>", text)
    return "".join("<p>" + paragraph.replace("\n", " ") + "</p>" for paragraph in text.split("\n\n"))


def write_atlas(site: Path, report: dict, paper_nodes: list[dict], paper_html: str) -> None:
    from jinja2 import Environment, FileSystemLoader, select_autoescape
    from markupsafe import Markup

    expert, mapping = load_sources()
    environment = Environment(loader=FileSystemLoader(BLUEPRINT / "templates"),
                              autoescape=select_autoescape(["html"]))
    template = environment.get_template("atlas.html")
    audit_template = environment.get_template("atlas_audit.html")
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
        card = {**node, "group_name": PALETTE.get(node["group"], PALETTE["api"])[0],
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
        card["search"] = " ".join(str(node.get(key, "")) for key in
                                  ("id", "title", "paper", "graph_heading", "graph_summary", "remark", "lean", "status")).lower()
        cards.append(card)
    groups = []
    for group in atlas["external_groups"]:
        members = [{"id": key, "heading": plain(node_heading(nodes[key])[0]),
                    "title": nodes[key]["primary"].rsplit(".", 1)[-1] if not nodes[key]["expert"]
                    else plain(nodes[key]["title"])}
                   for key in atlas["views"][-1]["nodes"] if nodes[key]["external_group"] == group["id"]]
        groups.append({**group, "members": members})
    # The unified graph is not embedded: its variants are separate files,
    # fetched when the dialog opens or a frame is opened.
    branch_views = [view for view in atlas["views"] if view["id"] != "all"]
    views = [{**view, "svg": Markup(render_svg(view, nodes, atlas["external_groups"]))} for view in branch_views]
    palette = {key: value for key, value in PALETTE.items() if any(node["group"] == key for node in nodes.values())}
    destination = site / "blueprint"
    for variant in atlas["unified_variants"]:
        svg = render_svg({**variant, "id": "map"}, nodes, atlas["external_groups"], compact=True)
        (destination / f"atlas-unified-{variant['id']}.svg").write_text(
            '<?xml version="1.0" encoding="UTF-8"?>\n' + svg)
    output = template.render(atlas=atlas, views=views, cards=cards, groups=groups, palette=palette,
                             status=STATUS, counts=atlas["counts"], diff_titles=DIFF_TITLE)
    (destination / "lean_dependencies.html").write_text(output)
    # The leanblueprint menu's historical graph route forwards to the reviewed
    # atlas. The generated paper DOT must not keep unaudited solid arrows.
    (destination / "dep_graph_document.html").write_text(
        redirect_page("lean_dependencies.html", "the proof atlas"))
    (destination / "atlas-cards.html").write_text(
        environment.get_template("atlas_cards.html").render(cards=cards))
    # The folded unified variants are derived from the "all" view and are
    # published as SVG files; repeating their witnesses would double the file.
    published = {key: value for key, value in atlas.items() if key != "unified_variants"}
    (destination / "atlas-dependencies.json").write_text(json.dumps(published, ensure_ascii=False) + "\n")

    actual_edges = {}
    for view in atlas["views"]:
        for edge in view["edges"]:
            actual_edges[edge_id(edge)] = edge
    edge_rows = []
    for key, edge in actual_edges.items():
        is_actual = edge["kind"] == "actual"
        edge_rows.append({"id": key, "from": edge["from"], "to": edge["to"], "diff": edge["diff"],
            "kind": DIFF_TITLE[edge["diff"]] + (" · compiled Lean path" if is_actual else " · " + edge["classification"]),
            "reason": "Each step below is a type, value, or structural reference in a compiled declaration." if is_actual else edge["reason"],
            "path_html": Markup(path_html(edge["path"]))})
    comparisons = [{**edge, "path_html": Markup(path_html(edge["path"]))} for edge in atlas["expert_edges"]]
    unified = {edge_id(edge) for edge in atlas["views"][-1]["edges"]}
    lean_only = [row for row in edge_rows if row["diff"] == "lean-only" and row["id"] in unified]
    audit = audit_template.render(atlas=atlas, edges=edge_rows, lean_only=lean_only,
                                 comparisons=comparisons, counts=atlas["counts"], diff_titles=DIFF_TITLE)
    (destination / "atlas-audit.html").write_text(audit)
    print(f"Rendered atlas: {len(nodes)} display nodes, {len(views)} views, "
          f"{len(expert['nodes'])} expert correspondences, framed external proofs.", flush=True)
