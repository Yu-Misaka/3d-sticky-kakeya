"""The expert roadmap must not manufacture Lean proofs or dependency paths."""

import copy
import json
import shutil
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import atlas
import atlas_render


def edge(consumer, prerequisite, kind="value"):
    return {"from": consumer, "to": prerequisite,
            "path": [{"from": consumer, "to": prerequisite, "kind": kind}]}


def expert_edge(source, target):
    return {"from": source, "to": target, "kind": "core", "note": "Expert mathematical input"}


def entry(name, *, kind="theorem", reached=True, is_proof=True, is_proposition=False):
    return {"name": name, "kind": kind, "reached": reached, "is_proof": is_proof,
            "is_proposition": is_proposition, "type": "True", "definition": None,
            "module": "Example", "line": 1, "axioms": [], "path": []}


class AtlasEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.report = {"graph_nodes": ["Root", "Middle", "Leaf", "Signature"],
                       "edges": [edge("Root", "Middle"), edge("Middle", "Leaf"),
                                 edge("Root", "Signature", "type")]}
        self.paths = atlas.AuditedPaths(self.report)
        self.nodes = {"A": {"primary": "Leaf"}, "B": {"primary": "Root"},
                      "C": {"primary": "Signature"}, "Unused": {"primary": "UnusedProof"},
                      "Missing": {"primary": None}, "Alias": {"primary": "Root"}}

    def test_transitive_use_is_solid_even_when_the_display_edge_was_reduced(self):
        result = atlas.classify_expert_edge(expert_edge("A", "B"), self.nodes, self.paths)
        self.assertEqual(result["classification"], "actual")
        self.assertEqual(result["path"], [edge("Root", "Middle")["path"][0],
                                          edge("Middle", "Leaf")["path"][0]])

    def test_expert_edges_cannot_be_used_as_reachability_evidence(self):
        # The expert can connect Leaf -> Signature -> Root, but the stored
        # Signature has no reference to Leaf. That first edge must stay dashed.
        proposed = [expert_edge("A", "C"), expert_edge("C", "B")]
        results = [atlas.classify_expert_edge(e, self.nodes, self.paths) for e in proposed]
        self.assertEqual([r["classification"] for r in results], ["different-route", "actual"])
        self.assertEqual(results[0]["path"], [])
        self.assertEqual(results[1]["path"][0]["kind"], "type")

    def test_dependency_direction_is_not_reversed(self):
        forward = atlas.classify_expert_edge(expert_edge("A", "B"), self.nodes, self.paths)
        backward = atlas.classify_expert_edge(expert_edge("B", "A"), self.nodes, self.paths)
        self.assertEqual(forward["classification"], "actual")
        self.assertEqual(backward["classification"], "different-route")

    def test_missing_correspondence_unused_proof_and_alias_have_distinct_reasons(self):
        expected = {"Missing": "unmapped", "Unused": "outside-root", "Alias": "shared-declaration"}
        for source, classification in expected.items():
            with self.subTest(source=source):
                result = atlas.classify_expert_edge(expert_edge(source, "B"), self.nodes, self.paths)
                self.assertEqual(result["classification"], classification)
                self.assertEqual(result["path"], [])

    def test_a_local_view_preserves_the_path_through_omitted_declarations(self):
        projected = atlas.projected_edges(["A", "B"], self.nodes, self.paths)
        self.assertEqual(len(projected), 1)
        self.assertEqual((projected[0]["from"], projected[0]["to"]), ("A", "B"))
        self.assertEqual(len(projected[0]["path"]), 2)
        aliases = atlas.projected_edges(["B", "Alias"], self.nodes, self.paths)
        self.assertEqual(aliases, [])

    def test_witnesses_must_be_nonempty_contiguous_kernel_paths(self):
        for path in ([], [{"from": "SomeoneElse", "to": "Leaf", "kind": "value"}],
                     [{"from": "Root", "to": "Leaf", "kind": "expert"}]):
            report = {"graph_nodes": ["Root", "Leaf"], "edges": [{"from": "Root", "to": "Leaf", "path": path}]}
            with self.subTest(path=path), self.assertRaises(ValueError):
                atlas.AuditedPaths(report)

    def test_prop_definition_and_constructor_are_not_certified_as_proofs(self):
        interface = entry("Statement", kind="definition", is_proof=False, is_proposition=True)
        proof_def = entry("proof", kind="definition", is_proof=True)
        constructor = entry("Statement.mk", kind="constructor", is_proof=True)
        unused = entry("Unused", reached=False)
        self.assertEqual(atlas.declaration_status(interface), "used-interface")
        self.assertEqual(atlas.declaration_status(proof_def), "used-proof")
        self.assertEqual(atlas.declaration_role(constructor), "constructor")
        self.assertEqual(atlas.declaration_status(unused), "unused-proof")


class AtlasCorrespondenceTests(unittest.TestCase):
    def setUp(self):
        self.expert = {"nodes": [{"id": "E", "group": "external"}], "edges": [], "views": []}
        self.mapping = {"nodes": [{"id": "E", "primary": "Lemma", "lean": ["Lemma"],
                                    "labels": ["thm:lemma"], "remarks": ["rem:scope"],
                                    "remark": "The actual theorem has additional hypotheses."}],
                        "external_groups": [{"id": "external", "nodes": ["E"], "module_prefixes": []}]}
        self.paper = [{"label": "thm:lemma", "kind": "theorem"}, {"label": "rem:scope", "kind": "remark"}]

    def test_every_expert_node_and_lean_version_must_be_accounted_for(self):
        atlas.validate_mapping(self.expert, self.mapping, self.paper, {"Lemma": entry("Lemma")})
        with self.assertRaisesRegex(ValueError, "Unaudited"):
            atlas.validate_mapping(self.expert, self.mapping, self.paper, {})
        duplicate = copy.deepcopy(self.mapping)
        duplicate["nodes"].append(duplicate["nodes"][0])
        with self.assertRaisesRegex(ValueError, "exactly one"):
            atlas.validate_mapping(self.expert, duplicate, self.paper)

    def test_external_inputs_cannot_silently_fall_outside_the_frame(self):
        self.mapping["external_groups"][0]["nodes"] = []
        with self.assertRaisesRegex(ValueError, "Every expert External"):
            atlas.validate_mapping(self.expert, self.mapping, self.paper)

    def test_a_difference_must_have_a_real_remark_and_valid_references(self):
        self.mapping["nodes"][0]["remarks"] = ["thm:lemma"]
        with self.assertRaisesRegex(ValueError, "not a Remark"):
            atlas.validate_mapping(self.expert, self.mapping, self.paper)

    def test_expert_html_is_never_inserted_as_executable_markup(self):
        rendered = atlas_render.expert_math_html('<script>alert(1)</script> $x<y$ \\emph{retained}')
        self.assertNotIn('<script>', rendered)
        self.assertIn('&lt;script&gt;', rendered)
        self.assertIn('$x&lt;y$', rendered)
        self.assertIn('<em>retained</em>', rendered)

    def test_mathjax_parameter_macros_survive_template_compilation(self):
        from jinja2 import Environment, FileSystemLoader
        environment = Environment(loader=FileSystemLoader(atlas.BLUEPRINT / "templates"))
        rendered = environment.get_template("atlas.html").render(
            atlas={"root": "Root", "root_node": "N1", "nodes": []}, views=[], counts={})
        self.assertIn('Ncov:', rendered)
        self.assertIn('{#1}(#2)', rendered)

    def test_checked_in_sources_cover_the_complete_expert_catalogue(self):
        import check
        expert, mapping = atlas.load_sources()
        atlas.validate_mapping(expert, mapping, check.inspect_content()[2])
        self.assertEqual(atlas.REMARKS.read_text(), atlas.correspondence_tex(expert, mapping))
        self.assertTrue({node['group'] for node in expert['nodes']} <= atlas_render.PALETTE.keys())
        self.assertTrue(all("statement" in node and "sketch" not in node for node in expert["nodes"]))
        self.assertEqual(len(expert["sources"]), 2)
        combined = atlas.make_atlas(json.loads(atlas.REPORT.read_text()), expert, mapping,
                                    check.inspect_content()[2])
        self.assertEqual(sum(e["expert_view"] == "all" for e in combined["expert_edges"]),
                         len(expert["edges"]))
        all_source_edges = expert["edges"] + [e for view in expert["views"] for e in view["edges"]]
        self.assertEqual({(e["from"], e["to"]) for e in combined["expert_edges"]},
                         {(e["from"], e["to"]) for e in all_source_edges})
        for view in combined["views"]:
            connections = [(e["from"], e["to"], e["kind"]) for e in view["edges"]]
            self.assertEqual(len(connections), len(set(connections)), view["id"])


class EdgeComparisonTests(unittest.TestCase):
    def setUp(self):
        def node(key, expert=True, group=None):
            return {"id": key, "expert": expert, "external_group": group}
        self.nodes = {key: node(key) for key in "ABCD"}
        self.nodes.update({"L": node("L", expert=False), "X1": node("X1", False, "box"),
                           "X2": node("X2", False, "box"), "Y": node("Y", group="single")})
        # The roadmap connects A to C only through B, and says nothing about D.
        self.reach = atlas.expert_reach([expert_edge("A", "B"), expert_edge("B", "C")])

    def diff(self, source, target, kind="actual", classification="actual"):
        return atlas.edge_diff({"from": source, "to": target, "kind": kind,
                                "classification": classification}, self.nodes, self.reach)

    def test_a_longer_roadmap_path_counts_as_agreement(self):
        self.assertEqual(self.diff("A", "B"), "agree")
        self.assertEqual(self.diff("A", "C"), "agree")

    def test_lean_only_requires_no_roadmap_path_in_that_direction(self):
        self.assertEqual(self.diff("A", "D"), "lean-only")
        self.assertEqual(self.diff("C", "A"), "lean-only")

    def test_an_added_lean_version_cannot_be_compared(self):
        self.assertEqual(self.diff("L", "A"), "detail")
        self.assertEqual(self.diff("A", "X1"), "detail")

    def test_roadmap_only_edges_separate_a_different_route_from_no_comparison(self):
        self.assertEqual(self.diff("D", "A", "expert", "different-route"), "expert-route")
        for reason in ("unmapped", "outside-root", "shared-declaration"):
            self.assertEqual(self.diff("D", "A", "expert", reason), "expert-unknown")

    def test_folding_a_frame_keeps_every_member_edge_and_its_class(self):
        def drawn(source, target, diff, kind="actual"):
            return {"from": source, "to": target, "kind": kind, "diff": diff, "path": []}
        view = {"id": "all", "title": "All", "description": "", "nodes": ["A", "X1", "X2", "Y", "L"],
                "edges": [drawn("X1", "A", "detail"), drawn("X2", "A", "detail"),
                          drawn("X1", "X2", "detail"), drawn("Y", "A", "expert-unknown", "expert"),
                          drawn("L", "X2", "detail")]}
        groups = atlas.collapsible_groups(view, self.nodes)
        self.assertEqual(groups, ["box"], "a one-node frame is not folded")
        folded = atlas.collapse_view(view, self.nodes, groups, "collapsed", "Folded")
        self.assertEqual(folded["nodes"], ["A", "group-box", "Y", "L"])
        arrows = {(e["from"], e["to"]): e for e in folded["edges"]}
        self.assertEqual(set(arrows), {("group-box", "A"), ("Y", "A"), ("L", "group-box")})
        self.assertEqual(len(arrows[("group-box", "A")]["members"]), 2)
        members = sum(len(e.get("members", [e])) for e in folded["edges"])
        self.assertEqual(members, len(view["edges"]) - 1, "only the edge inside the frame disappears")
        self.assertEqual(atlas.collapse_view(view, self.nodes, [], "full", "Full")["edges"], view["edges"])

    def test_checked_in_unified_variants_lose_no_connection(self):
        import check
        expert, mapping = atlas.load_sources()
        combined = atlas.make_atlas(json.loads(atlas.REPORT.read_text()), expert, mapping,
                                    check.inspect_content()[2])
        unified = combined["views"][-1]
        nodes = {node["id"]: node for node in combined["nodes"]}
        inside = sum(1 for e in unified["edges"] if nodes[e["from"]]["external_group"]
                     and nodes[e["from"]]["external_group"] == nodes[e["to"]]["external_group"])
        variants = {variant["id"]: variant for variant in combined["unified_variants"]}
        self.assertEqual(variants["full"]["edges"], unified["edges"])
        groups = atlas.collapsible_groups(unified, nodes)
        self.assertEqual(set(variants), {"collapsed", "full", *("expand-" + g for g in groups)})
        for variant in variants.values():
            for diff in atlas.DIFF_CLASSES:
                kept = sum(len(e.get("members", [e])) for e in variant["edges"] if e["diff"] == diff)
                total = sum(e["diff"] == diff for e in unified["edges"])
                self.assertLessEqual(kept, total, (variant["id"], diff))
                if diff != "detail":
                    self.assertEqual(kept, total, (variant["id"], diff))
        folded = sum(len(e.get("members", [e])) for e in variants["collapsed"]["edges"])
        self.assertEqual(folded + inside, len(unified["edges"]))


class EvidenceAnchorTests(unittest.TestCase):
    def test_every_arrow_link_reaches_a_row_of_the_evidence_page(self):
        import check
        expert, mapping = atlas.load_sources()
        combined = atlas.make_atlas(json.loads(atlas.REPORT.read_text()), expert, mapping,
                                    check.inspect_content()[2])
        connections, lean_only = atlas_render.audit_rows(combined)
        anchors = [row["anchor"] for row in connections + lean_only]
        self.assertEqual(len(anchors), len(set(anchors)))
        self.assertEqual(len(connections), len(combined["expert_edges"]), "every roadmap connection has a row")
        records = atlas_render.connection_records(combined)
        for key, record in records.items():
            if record["audit"]:
                self.assertIn(record["audit"].removeprefix("atlas-audit.html#"), anchors, key)
        drawn_lean_only = {(e["from"], e["to"]) for view in combined["views"] for e in view["edges"]
                           if e["diff"] == "lean-only"}
        self.assertEqual({(row["from"], row["to"]) for row in lean_only}, drawn_lean_only)
        # Roadmap connections whose Lean path runs through other displayed nodes have no arrow of their own.
        self.assertTrue(any(row["classification"] == "actual" and not row["drawn"] for row in connections))
        for record in records.values():
            if record["diff"] in ("expert-route", "expert-unknown"):
                self.assertTrue(record["audit"] and record["reason"] and record["notes"])


class AtlasPageTests(unittest.TestCase):
    def render(self, name, **context):
        from jinja2 import Environment, FileSystemLoader
        environment = Environment(loader=FileSystemLoader(atlas.BLUEPRINT / "templates"), autoescape=True)
        return environment.get_template(name).render(**context)

    def test_the_atlas_page_is_a_shell_and_the_cards_page_holds_the_cards(self):
        card = {"id": "N1", "group": "setup", "group_name": "Setup", "origin": "WZ2", "paper": "Lemma 1",
                "title": "A lemma", "status": "used-proof", "status_label": "Used",
                "statements": [], "remark": "Scope.", "remark_links": [], "expert": True, "versions": [],
                "external_group": None, "heading": "Lemma 1", "primary": "Example.lemma"}
        views = [{"id": "overview", "title": "Core proof DAG", "nodes": ["N1"]}]
        page = self.render("atlas.html", atlas={"root": "Root", "root_node": "N1", "nodes": [card]},
                           views=views, counts={})
        self.assertNotIn('Scope.', page, "cards are stored once, in atlas-cards.html")
        self.assertEqual(page.count('id="node-N1"'), 1, "the no-script index keeps the node anchor")
        self.assertIn('href="atlas-cards.html#node-N1"', page)
        self.assertIn('data-view="overview"', page)
        self.assertIn('data-view="all"', page)
        self.assertIn('../assets/atlas.js', page)
        cards = self.render("atlas_cards.html", cards=[card])
        self.assertEqual(cards.count('id="node-N1"'), 1)
        self.assertIn('Scope.', cards)
        self.assertIn('lean_dependencies.html#node-N1', cards)

    def test_long_labels_keep_two_lines_and_mark_the_cut(self):
        node = {"id": "N", "expert": True, "paper": "P", "title": "T", "graph_heading": "WZ2 Lemma 7.12",
                "graph_summary": "A summary long enough to need more than two lines in a node box here"}
        heads, lines = atlas_render.label_lines(node)
        self.assertEqual(heads, ["WZ2 Lemma 7.12"])
        self.assertEqual(len(lines), 2)
        self.assertTrue(lines[1].endswith("…"))
        self.assertTrue(all(len(line) <= atlas_render.SUMMARY_CHARS for line in lines))


@unittest.skipUnless(shutil.which("dot"), "Graphviz is needed to lay out a view")
class AtlasLayoutTests(unittest.TestCase):
    def node(self, key, external=None):
        return {"id": key, "primary": key, "group": "external" if external else "setup", "external_group": external,
                "title": "A statement", "paper": "Theorem " + key, "expert": True, "status": "used-proof",
                "versions": [entry(key)]}

    def test_every_node_edge_and_frame_is_placed(self):
        nodes = {"A": self.node("A"), "B": self.node("B", "input"), "C": self.node("C", "input"), "D": self.node("D")}
        view = {"id": "test", "nodes": ["A", "B", "C", "D"],
                "edges": [{"from": "B", "to": "A", "kind": "actual", "diff": "detail"},
                          {"from": "C", "to": "B", "kind": "actual", "diff": "detail"},
                          {"from": "D", "to": "A", "kind": "expert", "diff": "expert-route"}]}
        placed = atlas_render.layout_view(view, nodes, [{"id": "input", "title": "External test"}])
        self.assertEqual(set(placed["nodes"]), set(view["nodes"]))
        self.assertEqual(len(placed["splines"]), len(view["edges"]))
        self.assertTrue(all(spline.startswith("M") and "C" in spline for spline in placed["splines"]))
        self.assertEqual({cluster["id"] for cluster in placed["clusters"]}, {"external", "input"})
        frame = next(c for c in placed["clusters"] if c["id"] == "input")
        for key in ("B", "C"):
            x, y, w, h = placed["nodes"][key]
            self.assertTrue(frame["x"] <= x and x + w <= frame["x"] + frame["w"], key)
            self.assertTrue(frame["y"] <= y and y + h <= frame["y"] + frame["h"], key)
        for x, y, w, h in placed["nodes"].values():
            self.assertTrue(0 <= x and x + w <= placed["w"] and 0 <= y and y + h <= placed["h"])
        # Conclusions sit above their prerequisites.
        self.assertLess(placed["nodes"]["A"][1], placed["nodes"]["B"][1])

    def test_a_folded_frame_is_one_box(self):
        nodes = {"A": self.node("A"), "B": self.node("B", "input")}
        member = {"from": "B", "to": "A", "kind": "actual", "diff": "detail", "path": edge("A", "B")["path"]}
        view = {"id": "map", "nodes": ["A", "group-input"], "collapsed": ["input"],
                "edges": [{**member, "from": "group-input", "members": [member]}]}
        placed = atlas_render.layout_view(view, nodes, [{"id": "input", "title": "External test"}])
        self.assertEqual(set(placed["nodes"]), {"A", "group-input"})
        self.assertGreater(placed["nodes"]["group-input"][2], placed["nodes"]["A"][2])
        self.assertEqual([c["id"] for c in placed["clusters"]], ["external"], "a folded frame draws no inner cluster")


class ManuscriptTests(unittest.TestCase):
    PAGE = """<!DOCTYPE html><html><head><meta name="generator" content="plasTeX" /><title>Chapter</title>
<link rel="next" href="chap-next.html" title="Next chapter" /><link rel="stylesheet" href="styles/theme-white.css" /></head>
<body><header><h1 id="doc_title">Old title</h1></header><div class="wrapper"><nav class="toc"><ul class="sub-toc-0">
<li class=" active current"><a href="chap-test.html"><span class="toc_ref">1</span> <span class="toc_entry">Test chapter</span></a>
<ul class="sub-toc-1"><li><a href="chap-test.html#s1"><span class="toc_ref">1.1</span> <span class="toc_entry">A section</span></a></li></ul></li>
<li><a href="dep_graph_document.html">Dependency graph</a></li></ul></nav>
<div class="content"><div class="content-wrapper"><div class="main-text"><h1 id="chap:test">1 Test chapter</h1>
<div class="theorem_thmwrapper theorem-style-plain" id="thm:t"><div class="theorem_thmheading">
<span class="theorem_thmcaption">Theorem</span><span class="theorem_thmlabel">1.1</span><span class="theorem_thmtitle">Test</span>
<div class="thm_header_extras"> ✓ </div><div class="thm_header_hidden_extras"><a class="icon proof" href="chap-test.html#thm:t">#</a>
<button class="modal">u</button><div class="modal-container"><div class="modal-content"><header><h1>Uses</h1></header>
<ul class="uses"><li><a href="chap-test.html#def:d">Definition 1.0</a></li></ul></div></div>
<button class="modal lean">L</button><div class="modal-container"><div class="modal-content"><header><h1>Lean declarations</h1></header>
<ul class="uses"><li><a href="../lean/find/#doc/Example.statement" class="lean_decl">Example.statement</a></li>
<li><a href="../lean/find/#doc/Example.proof" class="lean_decl">Example.proof</a></li></ul></div></div></div></div>
<div class="theorem_thmcontent"><p>A statement.</p></div></div>
<div class="proof_wrapper" id="a01"><div class="proof_heading"><span class="proof_caption">Proof</span><span class="expand-proof">▶</span></div>
<div class="proof_content"><p>An argument.</p></div></div>
</div></div></div></div><nav class="prev_up_next"></nav><script src="js/plastex.js"></script></body></html>"""

    def test_a_plastex_page_keeps_its_content_and_gains_labelled_badges(self):
        import manuscript
        from jinja2 import Environment, FileSystemLoader
        from markupsafe import Markup
        from bs4 import BeautifulSoup
        environment = Environment(loader=FileSystemLoader(atlas.BLUEPRINT / "templates"), autoescape=True)
        environment.filters["markup"] = Markup
        soup = BeautifulSoup(self.PAGE, "html.parser")
        chapters = manuscript.chapter_list(soup)
        self.assertEqual([c["title"] for c in chapters], ["Test chapter"], "the paper graph route is not a chapter")
        nodes = manuscript.atlas_nodes({"nodes": [
            {"id": "Other", "labels": ["thm:t"], "primary": "Example.other", "expert": True},
            {"id": "Match", "labels": ["thm:t"], "primary": "Example.proof", "expert": False}]})
        page = manuscript.restyle_page(self.PAGE, "chap-test.html", chapters, nodes,
                                       environment.get_template("manuscript.html"))
        self.assertFalse(manuscript.is_plastex(page), "a converted page is not converted twice")
        result = BeautifulSoup(page, "html.parser")
        self.assertIsNotNone(result.find(id="thm:t"))
        self.assertIsNotNone(result.find(id="chap:test"))
        self.assertIn("A statement.", page)
        self.assertEqual(result.select_one("a.badge.atlas")["href"], "lean_dependencies.html#node-Match",
                         "the node anchored at a linked declaration is preferred")
        lean = result.select_one("details.pop.lean")
        self.assertIn("ok", lean["class"])
        self.assertEqual([a["href"] for a in lean.select("a")],
                         ["../lean/find/#doc/Example.statement", "../lean/find/#doc/Example.proof"])
        uses = [pop for pop in result.select("details.pop") if "lean" not in pop["class"]][0]
        self.assertIn("not Lean dependencies", uses.get_text())
        proof = result.find(id="a01")
        self.assertEqual(proof.name, "details")
        self.assertIn("An argument.", proof.get_text())
        self.assertNotIn("modal", page)
        self.assertNotIn("styles/theme-white.css", page)
        self.assertNotIn("js/plastex.js", page)
        self.assertIn('href="chap-next.html"', page)
        self.assertIn('aria-current="page"', page)


if __name__ == "__main__":
    unittest.main()
