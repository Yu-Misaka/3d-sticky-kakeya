#!/usr/bin/env python3
"""Import the expert's *mathematical* atlas, without treating its sketches as Lean.

The committed JSON is a source snapshot. Building the site never needs the
untracked artifacts directory, and never executes or embeds its HTML/scripts.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from html.parser import HTMLParser
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


class ExpertHTML(HTMLParser):
    VOID = {"area", "base", "br", "col", "embed", "hr", "img", "input",
            "link", "meta", "param", "source", "track", "wbr"}

    def __init__(self, text: str):
        super().__init__(convert_charrefs=True)
        self.depth = 0
        self.cards = []
        self.views = []
        self.card = self.view = self.diagram = self.edge = None
        self.captures = []
        self.feed(text)

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        classes = attrs.get("class", "").split()
        if tag == "article" and "nodecard" in classes:
            self.card = {"id": attrs["id"].removeprefix("node-"),
                         "group": attrs["data-group"], "html_line": self.getpos()[0]}
            self.cards.append(self.card)
            self.card_depth = self.depth
        if tag == "section" and "graphview" in classes:
            self.view = {"id": attrs["id"].removeprefix("view-"), "title": "", "description": ""}
            self.view_depth = self.depth
        if tag == "svg" and "depgraph" in classes:
            self.diagram = {"id": attrs["data-view"], "nodes": [], "edges": []}
            if self.view is not None:
                self.diagram.update(self.view)
            else:
                self.diagram.update(title="Unified dependency graph", description="All branches and external inputs.")
            self.views.append(self.diagram)
            self.diagram_depth = self.depth
        if self.diagram is not None and "graphnode" in classes:
            self.diagram["nodes"].append(attrs["data-node"])
        if self.diagram is not None and "edgegroup" in classes:
            self.edge = {"from": attrs["data-from"], "to": attrs["data-to"],
                         "kind": attrs["data-kind"]}
            self.diagram["edges"].append(self.edge)
        target = key = None
        if self.card is not None:
            if "mathsvg" in classes:
                self.card["statement"] = attrs["aria-label"]
            if tag == "h3":
                target, key = self.card, "paper"
            for cls, field in (("subtitle", "title"), ("source", "source"),
                               ("origin", "origin"), ("note", "note")):
                if cls in classes:
                    target, key = self.card, field
        elif self.view is not None and self.diagram is None:
            if tag == "h2":
                target, key = self.view, "title"
            elif tag == "p" and not self.view["description"]:
                target, key = self.view, "description"
        if tag == "title" and self.diagram is not None and self.edge is not None:
            target, key = self.edge, "note"
        if key is not None:
            self.captures.append((self.depth, target, key, []))
        if tag not in self.VOID:
            self.depth += 1

    def handle_data(self, data):
        for _, _, _, chunks in self.captures:
            chunks.append(data)

    def handle_endtag(self, tag):
        if tag in self.VOID:
            return
        self.depth -= 1
        while self.captures and self.captures[-1][0] == self.depth:
            _, target, key, chunks = self.captures.pop()
            target[key] = "".join(chunks).strip()
        if self.card is not None and self.depth == self.card_depth:
            self.card = None
        if self.diagram is not None and self.depth == self.diagram_depth:
            self.diagram = self.edge = None
        if self.view is not None and self.depth == self.view_depth:
            self.view = None


def import_atlas(html_file: Path, tex_file: Path) -> dict:
    parsed = ExpertHTML(html_file.read_text())
    tex = tex_file.read_text()
    ids = [card["id"] for card in parsed.cards]
    if len(ids) != len(set(ids)) or not ids:
        raise ValueError("Missing or duplicate expert nodes")
    for card in parsed.cards:
        for field in ("paper", "title", "statement", "source", "origin"):
            if not card.get(field):
                raise ValueError(f"Missing {field} in {card['id']}")
        marker = "\\hypertarget{node-" + card["id"] + "}{}"
        if tex.count(marker) != 1:
            raise ValueError(f"Missing or duplicate TeX counterpart: {card['id']}")
        card["tex_line"] = tex[:tex.index(marker)].count("\n") + 1
        # Cross-check the accessible math against the companion TeX, instead of
        # extracting the expert's rendered equation SVGs or its pseudocode.
        block = tex.split(marker, 1)[1].split("\\end{tcolorbox}", 1)[0]
        statement = block.split("\\textbf{Mathematical statement.} ", 1)[1]
        statement = statement.split("\\smallskip\\textbf{Lean statement sketch.}", 1)[0].strip()
        if re.sub(r"\s+", " ", statement) != re.sub(r"\s+", " ", card["statement"]):
            raise ValueError(f"HTML/TeX mathematical statement differs: {card['id']}")
    all_view = next(view for view in parsed.views if view["id"] == "all")
    if set(all_view["nodes"]) != set(ids):
        raise ValueError("Unified expert graph does not contain exactly the catalogue")
    for view in parsed.views:
        if not set(view["nodes"]) <= set(ids):
            raise ValueError(f"Unknown expert node in {view['id']}")
        for edge in view["edges"]:
            if not {edge["from"], edge["to"]} <= set(view["nodes"]):
                raise ValueError(f"Expert edge has missing endpoints: {edge}")
    return {"format": 1, "description": "Expert mathematical roadmap; all original Lean blocks are uncompiled pseudocode and are intentionally excluded.",
            "sources": [{"file": path.name, "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
                        for path in (html_file, tex_file)],
            "nodes": parsed.cards, "edges": all_view["edges"],
            "views": [view for view in parsed.views if view["id"] != "all"]}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--html", type=Path, default=ROOT / "artifacts/wz2_theorem_5_2_dependency_atlas.html")
    parser.add_argument("--tex", type=Path, default=ROOT / "artifacts/wz2_theorem_5_2_dependency_atlas.tex")
    parser.add_argument("--output", type=Path, default=ROOT / "blueprint/expert-atlas.json")
    args = parser.parse_args()
    data = import_atlas(args.html, args.tex)
    args.output.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n")
    print(f"Imported {len(data['nodes'])} expert nodes and {len(data['edges'])} proposed edges; no Lean sketches imported.")
