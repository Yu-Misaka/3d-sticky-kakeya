"""Dependency extraction must distinguish proofs, signatures, and unused versions."""

import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import dependencies as deps


def declaration(name, kind="theorem", types=(), values=(), structural=()):
    return {"name": name, "kind": kind, "module": "Example", "line": 1,
            "type": list(types), "value": list(values), "structural": list(structural)}


def registry_record(name, kind="theorem"):
    return {"name": name, "kind": kind, "module": "Example", "line": 1, "axioms": []}


class DependencyGraphTests(unittest.TestCase):
    def test_proof_path_survives_hidden_helpers_and_inductive_cycles(self):
        graph = {row["name"]: row for row in [
            declaration("Root", types=["Statement"], values=["Helper"]),
            declaration("Statement", "inductive", structural=["Ctor"]),
            declaration("Ctor", "constructor", types=["Statement"]),
            declaration("Helper", "opaque", values=["Used"]),
            declaration("Used"),
        ]}
        report = deps.make_report(graph, [registry_record("Root"), registry_record("Used"),
                                         registry_record("UnusedSameType"),
                                         registry_record("Statement", "inductive")],
                                  "Root", ["Example"], 0)
        entries = {row["name"]: row for row in report["declarations"]}
        self.assertTrue(entries["Statement"]["reached"])
        self.assertNotIn("Statement", report["graph_nodes"])
        self.assertFalse(entries["UnusedSameType"]["reached"])
        self.assertEqual(entries["UnusedSameType"]["kind"], "theorem")
        self.assertEqual(entries["Used"]["path"], [
            {"from": "Root", "to": "Helper", "kind": "value"},
            {"from": "Helper", "to": "Used", "kind": "value"},
        ])
        self.assertEqual(report["edges"][0]["path"], entries["Used"]["path"])

    def test_reduction_keeps_the_nonredundant_dependency_chain(self):
        edges = [{"from": "Root", "to": "Middle"}, {"from": "Middle", "to": "Leaf"},
                 {"from": "Root", "to": "Leaf"}]
        self.assertEqual(deps.reduce_edges(edges), edges[:2])

    def test_cyclic_projection_is_not_incorrectly_reduced(self):
        edges = [{"from": "A", "to": "B"}, {"from": "B", "to": "A"}]
        self.assertEqual(deps.reduce_edges(edges), edges)

    def test_an_unfinished_or_incomplete_extraction_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            file = Path(tmp) / "graph.jsonl"
            header = json.dumps({"root": "Root", "module_roots": ["Example"]})
            record = json.dumps(declaration("Root", values=["Missing"]))
            file.write_text(header + "\n" + record + "\n")
            with self.assertRaisesRegex(ValueError, "did not finish"):
                deps.read_graph(file)
            file.write_text(header + "\n" + record + '\n{"boundary": []}\n')
            with self.assertRaisesRegex(ValueError, "Unresolved"):
                deps.read_graph(file)


@unittest.skipUnless(shutil.which("lake"), "Lean is needed for the metaprogram regression")
class LeanExtractionTests(unittest.TestCase):
    def test_private_and_opaque_bodies_are_followed_without_including_an_unused_proof(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "graph.jsonl"
            fixture = Path(tmp) / "Fixture.lean"
            fixture.write_text("import Lean\n" + deps.EXTRACTOR.read_text() + "\n" + '''
namespace DependencyFixture
def Statement : Prop := True
private theorem used : Statement := True.intro
theorem unusedSameType : Statement := True.intro
opaque opaqueProof : Statement := used
structure Box where
  proof : Statement
def box : Box := ⟨used⟩
theorem projectionProof : Statement := box.proof
theorem endpoint : Statement ∧ Statement := ⟨opaqueProof, projectionProof⟩
end DependencyFixture
run_cmd do
  BlueprintDependencies.collect ``DependencyFixture.endpoint #[(← getEnv).mainModule]
''' + "    " + json.dumps(str(output)) + "\n")
            result = subprocess.run(["lake", "env", "lean", str(fixture)], cwd=deps.ROOT,
                                    capture_output=True, text=True, timeout=90)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            header, graph, boundary = deps.read_graph(output)
            root = graph[header["root"]]
            self.assertEqual(root["type"], ["DependencyFixture.Statement"])
            self.assertEqual(root["value"], ["DependencyFixture.Statement",
                                            "DependencyFixture.opaqueProof",
                                            "DependencyFixture.projectionProof"])
            self.assertEqual(graph["DependencyFixture.opaqueProof"]["kind"], "opaque")
            private_name = graph["DependencyFixture.opaqueProof"]["value"][0]
            self.assertTrue(private_name.startswith("_private."))
            self.assertEqual(graph[private_name]["kind"], "theorem")
            self.assertIn("DependencyFixture.Box", graph)
            self.assertIn("DependencyFixture.Box.mk", graph["DependencyFixture.Box"]["structural"])
            self.assertEqual(graph["DependencyFixture.Box.mk"]["structural"], ["DependencyFixture.Box"])
            self.assertNotIn("DependencyFixture.unusedSameType", graph)
            self.assertIn("True.intro", boundary)


if __name__ == "__main__":
    unittest.main()
