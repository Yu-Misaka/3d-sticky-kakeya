"""The expert roadmap must not manufacture Lean proofs or dependency paths."""

import copy
import json
import shutil
import sys
import unittest
import xml.etree.ElementTree as ET
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
        template = environment.get_template("atlas.html")
        rendered = template.render(atlas={"root": "Root"}, views=[], cards=[], palette={}, status={},
                                   counts={"expert_nodes": 0, "expert_edges": 0, "lean_versions": 0})
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


@unittest.skipUnless(shutil.which("dot"), "Graphviz is needed to check rendered evidence styles")
class AtlasSVGTests(unittest.TestCase):
    def test_actual_and_expert_strokes_and_external_frame_survive_svg_rendering(self):
        def node(key, group, external=None):
            return {"id": key, "primary": key, "group": group, "external_group": external,
                    "title": "A mathematical statement", "paper": "Theorem " + key,
                    "expert": True, "status": "used-proof", "versions": [entry(key)]}
        nodes = {"A": node("A", "setup"), "B": node("B", "external", "input"),
                 "C": node("C", "plane")}
        view = {"id": "test", "title": "Evidence styles", "nodes": ["A", "B", "C"],
                "edges": [{"from": "B", "to": "A", "kind": "actual", "path": edge("A", "B")["path"]},
                          {"from": "C", "to": "A", "kind": "expert", "path": [], "reason": "No supporting path"}]}
        svg = ET.fromstring(atlas_render.render_svg(view, nodes, [{"id": "input", "title": "External test"}]))
        groups = list(svg.iter('{http://www.w3.org/2000/svg}g'))
        actual = next(g for g in groups if g.get('data-kind') == 'actual')
        expert = next(g for g in groups if g.get('data-kind') == 'expert')
        self.assertFalse(any(p.get('stroke-dasharray') for p in actual.iter('{http://www.w3.org/2000/svg}path')))
        self.assertTrue(any(p.get('stroke-dasharray') for p in expert.iter('{http://www.w3.org/2000/svg}path')))
        self.assertTrue(any('External inputs' in (e.text or '') for e in svg.iter()))
        self.assertEqual([g.get('data-external-group') for g in groups if g.get('data-external-group')], ['input'])
        self.assertTrue(actual.get('data-audit').startswith('atlas-audit.html#edge-'))
        self.assertEqual({g.get('data-node') for g in groups if g.get('data-node')}, {'A', 'B', 'C'})
        other = ET.fromstring(atlas_render.render_svg({**view, "id": "other"}, nodes,
                              [{"id": "input", "title": "External test"}]))
        ids = [element.get('id') for drawing in (svg, other)
               for element in drawing.iter() if element.get('id')]
        self.assertEqual(len(ids), len(set(ids)))


if __name__ == "__main__":
    unittest.main()
