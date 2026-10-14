"""Dependency extraction must distinguish proofs, signatures, and unused versions."""

import json
import os
import re
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
        self.assertEqual(set(report["graph_nodes"]), {"Root", "Statement", "Used"})
        self.assertFalse(entries["UnusedSameType"]["reached"])
        self.assertEqual(entries["UnusedSameType"]["kind"], "theorem")
        self.assertEqual(entries["Used"]["path"], [
            {"from": "Root", "to": "Helper", "kind": "value"},
            {"from": "Helper", "to": "Used", "kind": "value"},
        ])
        proof_edge = next(edge for edge in report["edges"]
                          if edge["from"] == "Root" and edge["to"] == "Used")
        self.assertEqual(proof_edge["path"], entries["Used"]["path"])
        statement_edge = next(edge for edge in report["edges"] if edge["to"] == "Statement")
        self.assertEqual(statement_edge["path"], [{"from": "Root", "to": "Statement", "kind": "type"}])

    def test_definitions_are_kept_and_unlinked_assembly_steps_are_folded(self):
        graph = {row["name"]: row for row in [
            declaration("Root", types=["Conclusion"], values=["Assembly"]),
            declaration("Conclusion", "definition", types=["Objects"]),
            declaration("Objects", "inductive"),
            declaration("Assembly", types=["Conclusion"], values=["Proof"]),
            declaration("Proof", types=["Conclusion"]),
        ]}
        records = [registry_record("Root"), registry_record("Conclusion", "definition"),
                   registry_record("Objects", "inductive"), registry_record("Proof"),
                   registry_record("UnusedDefinition", "definition"), registry_record("UnusedProof")]
        report = deps.make_report(graph, records, "Root", ["Example"], 0)
        self.assertEqual(report["graph_nodes"], ["Conclusion", "Objects", "Proof", "Root"])
        self.assertEqual({(edge["from"], edge["to"]) for edge in report["edges"]},
                         {("Root", "Proof"), ("Proof", "Conclusion"), ("Conclusion", "Objects")})
        proof_edge = next(edge for edge in report["edges"] if edge["from"] == "Root")
        self.assertEqual(proof_edge["path"], [
            {"from": "Root", "to": "Assembly", "kind": "value"},
            {"from": "Assembly", "to": "Proof", "kind": "value"},
        ])
        self.assertEqual(report["evidence"]["Objects"]["kind"], "inductive")

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


class ManuscriptPopupTests(unittest.TestCase):
    PAPER = r'''<!doctype html><html><head>
<title>Dependency graph</title>
<script>MathJax = {tex: {macros: {R: "\\mathbb{R}"}}};</script>
<script src="mathjax.js"></script><link rel="stylesheet" href="styles/theme.css" />
</head><body><div id="statements"><div class="thm" id="thm:bound">
<div class="thm_thmheading"><span class="theorem_thmcaption">Theorem</span>
<span class="theorem_thmlabel">2.3</span>
<span class="theorem_thmtitle">A bound on \(\R\)</span></div>
<div class="thm_thmcontent"><p>Every <em>nonempty</em> set satisfies<br /> the bound.</p>
<div class="displaymath" id="bound-equation">\[ |E| \geq \delta^\varepsilon. \]</div>
<p>See <a href="#bound-equation">the bound</a> and
<a href="chapter.html#def:sets">Definition 2.1</a>.</p></div>
<a class="latex_link" href="chapter.html#thm:bound">LaTeX</a>
</div></div></body></html>'''

    def test_versions_reuse_natural_statements_math_config_and_cross_references(self):
        report = {"graph_nodes": ["Bound", "Bound.proof"], "edges": [],
                  "evidence": {"Bound": {"kind": "definition"}, "Bound.proof": {"kind": "theorem"}}}
        aliases = {name: ["thm:bound"] for name in report["graph_nodes"]}
        rendered = deps.render_graph(report, aliases, self.PAPER)
        self.assertIn('macros: {R: "\\\\mathbb{R}"}', rendered)
        self.assertIn('<script src="mathjax.js"></script>', rendered)
        self.assertEqual(rendered.count(r'\[ |E| \geq \delta^\varepsilon. \]'), 2)
        self.assertEqual(rendered.count('Every <em>nonempty</em> set'), 2)
        for index in range(2):
            self.assertIn(f'id="lean-{index}-bound-equation"', rendered)
            self.assertIn(f'href="#lean-{index}-bound-equation"', rendered)
        self.assertNotIn('id="bound-equation"', rendered)
        self.assertEqual(rendered.count('href="chapter.html#def:sets"'), 2)
        self.assertEqual(rendered.count('href="chapter.html#thm:bound"'), 2)
        statements = deps.PaperStatements(rendered).statements
        for index, name in enumerate(report["graph_nodes"]):
            content = statements[f"lean-{index}"]["content"]
            self.assertNotIn('Lean', content)
            self.assertNotIn('Version audit and paths', content)
            # Each version has exactly one Lean action; all three actions are
            # adjacent inline links after the statement, as in the paper graph.
            link = f'../lean/find/#doc/{name}'
            self.assertEqual(rendered.count(f'href="{link}"'), 1)
            self.assertRegex(rendered,
                r'<a class="latex_link" href="chapter.html#thm:bound">LaTeX</a>\s*'
                rf'<a class="lean_link lean_decl" href="{re.escape(link)}">Lean</a>\s*'
                r'<a class="issue_link audit_link" href="lean_dependency_audit.html#thm:bound">'
                r'Version audit and paths</a>')
        for removed in ('Proved Lean theorem:', 'Lean statement interface:',
                        'Lean source', 'Lean documentation', 'lean-version'):
            self.assertNotIn(removed, rendered)

    def test_missing_manuscript_statement_does_not_silently_become_a_code_only_popup(self):
        report = {"graph_nodes": ["Unknown"], "edges": []}
        with self.assertRaisesRegex(ValueError, "No rendered blueprint statement for Unknown"):
            deps.render_graph(report, {"Unknown": ["thm:missing"]}, self.PAPER)

    def test_chapter_remarks_keep_their_actual_page_and_content(self):
        source = '''<div class="remark_thmwrapper theorem-style-remark" id="rem:scope">
<div class="remark_thmheading"><span class="remark_thmcaption">Remark</span>
<span class="remark_thmlabel">3.4</span><span class="remark_thmtitle">Scope</span></div>
<div class="remark_thmcontent"><p>An interface is not its proof.</p></div></div>'''
        statement = deps.PaperStatements(source, "chap-test.html").statements["rem:scope"]
        self.assertEqual(statement["url"], "chap-test.html#rem:scope")
        self.assertEqual(statement["kind"], "remark")
        self.assertIn("An interface is not its proof.", statement["content"])

    def test_copying_equations_does_not_invent_cross_statement_anchors(self):
        content = '<div id="eq">x</div><a href="#eq">Equation</a><a href="#other">Other statement</a>'
        rendered = deps.statement_content(content, "copy", "chap-test.html")
        self.assertIn('id="copy-eq"', rendered)
        self.assertIn('href="#copy-eq"', rendered)
        self.assertIn('href="chap-test.html#other"', rendered)
        self.assertNotIn('href="#copy-other"', rendered)


@unittest.skipUnless(shutil.which("lake"), "Lean is needed for the metaprogram regression")
class LeanExtractionTests(unittest.TestCase):
    def test_compiled_prop_interface_proof_definition_and_constructor_are_distinct(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            payload = directory / "AtlasFixture.lean"
            payload.write_text('''namespace AtlasFixture
def Statement : Prop := True
def proofValue : Statement := True.intro
theorem proved : Statement := proofValue
inductive RequiresInput : Prop where
  | make (input : False) : RequiresInput
end AtlasFixture
''')
            compiled = subprocess.run(["lake", "env", "lean", "--root=" + tmp,
                                       "-o", str(directory / "AtlasFixture.olean"), str(payload)],
                                      cwd=deps.ROOT, capture_output=True, text=True, timeout=90)
            self.assertEqual(compiled.returncode, 0, compiled.stdout + compiled.stderr)
            probe = directory / "Probe.lean"
            probe.write_text("import AtlasFixture\nimport Lean\n" +
                             deps.EXTRACTOR.with_name("audit.lean").read_text() + '''
run_cmd blueprintAudit #[``AtlasFixture.Statement, ``AtlasFixture.proofValue,
  ``AtlasFixture.proved, ``AtlasFixture.RequiresInput, ``AtlasFixture.RequiresInput.make]
''')
            configured_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"],
                                                       cwd=deps.ROOT, text=True).strip()
            # Keep Lake's pinned compiler on PATH while prepending the fixture
            # *after* Lake configures LEAN_PATH. Calling an ambient `lean`
            # shim here can resolve a different toolchain or block on setup.
            result = subprocess.run(["lake", "env", "env",
                                     "LEAN_PATH=" + tmp + os.pathsep + configured_path,
                                     "lean", str(probe)], cwd=deps.ROOT,
                                    capture_output=True, text=True, timeout=90)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            records = {r["name"]: r for line in result.stdout.splitlines() if line.startswith("BLUEPRINT ")
                       for r in [json.loads(line.removeprefix("BLUEPRINT "))]}
            statement = records["AtlasFixture.Statement"]
            self.assertTrue(statement["is_proposition"])
            self.assertFalse(statement["is_proof"])
            self.assertEqual(statement["definition"], "True")
            proof = records["AtlasFixture.proofValue"]
            self.assertTrue(proof["is_proof"])
            self.assertFalse(proof["is_proposition"])
            self.assertEqual(proof["expanded_type"], "True")
            constructor = records["AtlasFixture.RequiresInput.make"]
            self.assertEqual(constructor["kind"], "constructor")
            self.assertTrue(constructor["is_proof"])
            self.assertIn("False", constructor["type"])

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
