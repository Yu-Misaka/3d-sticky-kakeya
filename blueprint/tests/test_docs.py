"""Regression checks for documentation cache invalidation and declaration links."""

import json
import sqlite3
import subprocess
import sys
import tempfile
import unittest
from html.parser import HTMLParser
from pathlib import Path
from unittest.mock import call, patch
from urllib.parse import urljoin

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import docs
import check


class DocumentationCacheTests(unittest.TestCase):
    def setUp(self):
        self.enterContext(patch.object(docs, "compatibility_digest", return_value="config"))
        self.enterContext(patch.object(docs, "stabilize_unicode_order"))

    def test_changed_environment_discards_database_and_pages_together(self):
        with tempfile.TemporaryDirectory() as tmp:
            build = Path(tmp)
            for relative in ("doc/Old.html", "doc-data/Old.doc", "api-docs.db",
                             "api-docs.db-wal", "doc-manifest.json", "lib/lean/Documentation.olean"):
                path = build / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("old build")
            stamp = build / "blueprint-docs.json"
            stamp.write_text(json.dumps({"inputs": "old", "compatibility": "old config"}))
            with patch.object(docs, "DOC_BUILD", build), patch.object(docs, "STAMP", stamp), \
                 patch.object(docs, "input_digest", return_value="new"), \
                 patch.object(docs, "check_docbuild_config"):
                self.assertTrue(docs.prepare_docs())
            self.assertFalse((build / "doc").exists())
            self.assertFalse((build / "doc-data").exists())
            self.assertFalse((build / "api-docs.db").exists())
            self.assertFalse((build / "api-docs.db-wal").exists())
            self.assertFalse(stamp.exists())
            self.assertTrue((build / "lib/lean/Documentation.olean").is_file())

    def test_source_edits_retain_dependency_database_and_module_traces(self):
        with tempfile.TemporaryDirectory() as tmp:
            build = Path(tmp)
            for relative in ("doc/Documentation.html", "doc/Old.html", "doc-manifest.json",
                             "doc/declarations/declaration-data.bmp", "doc-data/Mathlib.doc",
                             "doc-data/Mathlib.doc.trace", "doc-data/core-Init.doc",
                             "doc-data/Example.doc", "doc-data/Example.doc.trace",
                             "doc-data/references.json", "doc-data/references.json.trace",
                             "doc-data/declaration-data-Old.bmp", "doc-data/backrefs-Old.json",
                             "doc-data/Documentation--library.docs_built",
                             "doc-data/Documentation--library.docs_built.trace",
                             "doc-data/Documentation--library.docsHeader_built"):
                path = build / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("cached output")
            database_path = build / "api-docs.db"
            with sqlite3.connect(database_path) as database:
                database.execute("CREATE TABLE modules (name TEXT, source_url TEXT)")
                database.execute("INSERT INTO modules VALUES ('Mathlib', 'https://example.org/Mathlib.lean')")
            stamp = build / "blueprint-docs.json"
            stamp.write_text(json.dumps({"inputs": "old", "compatibility": "config"}))
            with patch.object(docs, "DOC_BUILD", build), patch.object(docs, "STAMP", stamp), \
                 patch.object(docs, "BUILD", build / "logs"), \
                 patch.object(docs, "input_digest", return_value="new"), \
                 patch.object(docs, "check_docbuild_config"), \
                 patch.object(docs, "run_logged") as run, patch.object(docs, "finish_docs") as finish:
                docs.build_docs()
                run.assert_called_once()
                finish.assert_called_once()
            self.assertFalse(stamp.exists())
            self.assertFalse((build / "doc").exists())
            self.assertFalse((build / "doc-manifest.json").exists())
            self.assertFalse(list((build / "doc-data").glob("*.docs_built*")))
            self.assertFalse(list((build / "doc-data").glob("*.docsHeader_built*")))
            self.assertFalse(list((build / "doc-data").glob("declaration-data-*.bmp")))
            self.assertFalse(list((build / "doc-data").glob("backrefs-*.json")))
            for relative in ("doc-data/Mathlib.doc", "doc-data/Mathlib.doc.trace",
                             "doc-data/core-Init.doc", "doc-data/Example.doc", "doc-data/Example.doc.trace",
                             "doc-data/references.json", "doc-data/references.json.trace"):
                self.assertEqual((build / relative).read_text(), "cached output")
            with sqlite3.connect(database_path) as database:
                self.assertEqual(database.execute("SELECT name FROM modules").fetchall(), [("Mathlib",)])

    def test_legacy_cache_compares_its_revision_configuration(self):
        with tempfile.TemporaryDirectory() as tmp:
            build = Path(tmp)
            stamp = build / "blueprint-docs.json"
            revision = "a" * 40
            stamp.write_text(json.dumps({"inputs": "old", "revision": revision}))
            with patch.object(docs, "DOC_BUILD", build), patch.object(docs, "STAMP", stamp), \
                 patch.object(docs, "cache_complete", return_value=True), \
                 patch.object(docs, "input_digest", return_value="new"), \
                 patch.object(docs, "check_docbuild_config"), \
                 patch.object(docs, "prune_removed_modules") as prune, \
                 patch.object(docs, "compatibility_digest", return_value="config") as digest:
                self.assertTrue(docs.prepare_docs())
                self.assertEqual(digest.call_args_list, [call(revision), call()])
                prune.assert_called_once_with()
            self.assertFalse(stamp.exists())

    def test_text_only_changes_reuse_matching_documentation(self):
        with tempfile.TemporaryDirectory() as tmp:
            build = Path(tmp)
            stamp = build / "blueprint-docs.json"
            stamp.write_text(json.dumps({"inputs": "same"}))
            for relative in ("doc-manifest.json", "doc/Documentation.html",
                             "doc/declarations/declaration-data.bmp"):
                path = build / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("cached output")
            database = build / "api-docs.db"
            database.write_text("cached data")
            with patch.object(docs, "DOC_BUILD", build), patch.object(docs, "STAMP", stamp), \
                 patch.object(docs, "input_digest", return_value="same"), \
                 patch.object(docs, "check_docbuild_config"), \
                 patch.object(docs, "run_logged") as run, \
                 patch.object(docs, "finish_docs") as finish:
                docs.build_docs()
                docs.check_fresh_docs()
                run.assert_not_called()
                finish.assert_called_once_with()
            self.assertEqual(database.read_text(), "cached data")

    def test_missing_database_invalidates_otherwise_matching_cache(self):
        with tempfile.TemporaryDirectory() as tmp:
            build = Path(tmp)
            stamp = build / "blueprint-docs.json"
            stamp.write_text(json.dumps({"inputs": "same"}))
            (build / "doc-data").mkdir()
            (build / "doc-data/Example.doc").touch()
            with patch.object(docs, "DOC_BUILD", build), patch.object(docs, "STAMP", stamp), \
                 patch.object(docs, "input_digest", return_value="same"), \
                 patch.object(docs, "check_docbuild_config"):
                self.assertTrue(docs.prepare_docs())
            self.assertFalse(stamp.exists())
            self.assertFalse((build / "doc-data").exists())

    def test_reuse_rejects_changed_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            stamp = Path(tmp) / "blueprint-docs.json"
            stamp.write_text(json.dumps({"inputs": "old"}))
            with patch.object(docs, "STAMP", stamp), \
                 patch.object(docs, "input_digest", return_value="new"):
                with self.assertRaisesRegex(ValueError, "stale"):
                    docs.check_fresh_docs()

    def test_cache_misses_build_before_validation(self):
        for cached in (None, '{"inputs": "old"}', '{"inputs": "same"}', '{', '[]'):
            with self.subTest(stamp=cached), tempfile.TemporaryDirectory() as tmp:
                build = Path(tmp)
                stamp = build / "blueprint-docs.json"
                if cached is not None:
                    stamp.write_text(cached)
                for relative in ("api-docs.db", "doc-manifest.json", "doc/Documentation.html",
                                 "doc/declarations/declaration-data.bmp"):
                    path = build / relative
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text("cached output")
                if cached == '{"inputs": "same"}':
                    # Even a matching stamp cannot reuse an incomplete cache.
                    (build / "api-docs.db").unlink()
                events = []
                with patch.object(docs, "DOC_BUILD", build), patch.object(docs, "STAMP", stamp), \
                     patch.object(docs, "BUILD", build / "logs"), \
                     patch.object(docs, "input_digest", return_value="same"), \
                     patch.object(docs, "check_docbuild_config"), \
                     patch.object(docs, "run_logged", side_effect=lambda *_: events.append("build")) as run, \
                     patch.object(docs, "finish_docs", side_effect=lambda: events.append("validate")):
                    docs.build_docs()
                run.assert_called_once_with(
                    ["lake", "--no-cache", "-d", "docbuild", "build", "Documentation:docs"],
                    build / "logs/docgen.log",
                )
                self.assertEqual(events, ["build", "validate"])
                self.assertFalse(stamp.exists())

    def test_failed_build_cannot_leave_a_valid_stamp(self):
        with tempfile.TemporaryDirectory() as tmp:
            build = Path(tmp)
            stamp = build / "blueprint-docs.json"
            stamp.write_text(json.dumps({"inputs": "old"}))
            with patch.object(docs, "DOC_BUILD", build), patch.object(docs, "STAMP", stamp), \
                 patch.object(docs, "BUILD", build / "logs"), \
                 patch.object(docs, "input_digest", return_value="new"), \
                 patch.object(docs, "check_docbuild_config"), \
                 patch.object(docs, "run_logged", side_effect=ValueError("build failed")), \
                 patch.object(docs, "finish_docs") as finish:
                with self.assertRaisesRegex(ValueError, "build failed"):
                    docs.build_docs()
                finish.assert_not_called()
            self.assertFalse(stamp.exists())

    def test_failed_incremental_build_cannot_leave_a_valid_stamp(self):
        with tempfile.TemporaryDirectory() as tmp:
            build = Path(tmp)
            stamp = build / "blueprint-docs.json"
            stamp.write_text(json.dumps({"inputs": "old", "compatibility": "config"}))
            with patch.object(docs, "DOC_BUILD", build), patch.object(docs, "STAMP", stamp), \
                 patch.object(docs, "BUILD", build / "logs"), \
                 patch.object(docs, "cache_complete", return_value=True), \
                 patch.object(docs, "input_digest", return_value="new"), \
                 patch.object(docs, "check_docbuild_config"), \
                 patch.object(docs, "prune_removed_modules"), \
                 patch.object(docs, "run_logged", side_effect=ValueError("build failed")), \
                 patch.object(docs, "finish_docs") as finish:
                with self.assertRaisesRegex(ValueError, "build failed"):
                    docs.build_docs()
                finish.assert_not_called()
            self.assertFalse(stamp.exists())

    def test_reused_documentation_is_validated_and_source_links_are_refreshed(self):
        with tempfile.TemporaryDirectory() as tmp:
            build = Path(tmp)
            page = build / "doc/Example.html"
            page.parent.mkdir()
            old_revision, revision = "a" * 40, "b" * 40
            source = f'{docs.REPOSITORY}/blob/{old_revision}/Example.lean'
            page.write_text(f'<div id="Example.result"><a href="{source}">source</a></div>')
            for relative in ("index.html", "Documentation.html", "find/index.html", "find/find.js",
                             "search.html", "search.js", "declaration-data.js", "style.css"):
                path = page.parent / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("cached output")
            index = page.parent / "declarations/declaration-data.bmp"
            index.parent.mkdir()
            index.write_text(json.dumps({
                "modules": {"Example": {"url": "./Example.html"}},
                "declarations": {"Example.result": {"docLink": "./Example.html#Example.result",
                                                     "sourceLink": source}},
            }))
            stamp = build / "blueprint-docs.json"
            stamp.write_text(json.dumps({"inputs": "same", "revision": old_revision}))
            records = [{"name": "Example.result", "module": "Example"}]
            validate_cached = docs.validate_documentation
            with patch.object(docs, "STAMP", stamp), patch.object(docs, "DOCS", page.parent), \
                 patch.object(docs, "input_digest", return_value="same"), \
                 patch.object(docs, "check_docbuild_config"), \
                 patch.object(docs, "cache_complete", return_value=True), \
                 patch.object(docs, "inspect_content", return_value=("", [], [])), \
                 patch.object(docs, "check_registry", return_value=records), \
                 patch.object(docs, "lean_modules", return_value=["Example"]), \
                 patch.object(docs, "validate_documentation", \
                              side_effect=lambda rows: validate_cached(rows, page.parent)) as validate, \
                 patch.object(docs.subprocess, "check_output", return_value=revision), \
                 patch.object(docs, "run_logged") as run:
                docs.build_docs()
                run.assert_not_called()
                validate.assert_called_once_with(records)
            self.assertIn(f"/blob/{revision}/", page.read_text())
            self.assertNotIn(old_revision, page.read_text())
            self.assertIn(f"/blob/{revision}/", index.read_text())
            self.assertEqual(json.loads(stamp.read_text()),
                             {"inputs": "same", "revision": revision, "compatibility": "config"})


class DocumentationFingerprintTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.inputs = (
            "Main.lean", "lean-toolchain", "lakefile.toml", "lake-manifest.json",
            "docbuild/lean-toolchain", "docbuild/lakefile.toml",
            "docbuild/lake-manifest.json", "docbuild/Documentation.lean",
        )
        for name in (*self.inputs, "blueprint/src/content.tex", "blueprint/site-src/index.html"):
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("original input\n")
        subprocess.run(["git", "init", "--quiet", str(self.root)], check=True)
        subprocess.run(["git", "-C", str(self.root), "add", "."], check=True)
        self.enterContext(patch.object(check, "ROOT", self.root))
        self.enterContext(patch.object(docs, "ROOT", self.root))
        self.enterContext(patch.object(docs, "DOCBUILD", self.root / "docbuild"))

    def test_manuscript_and_web_changes_keep_the_cache_key(self):
        original = docs.input_digest()
        for name in ("blueprint/src/content.tex", "blueprint/site-src/index.html"):
            (self.root / name).write_text("updated page\n")
        (self.root / "blueprint/src/new.tex").write_text("new chapter\n")
        self.assertEqual(docs.input_digest(), original)

    def test_lean_and_documentation_inputs_change_the_cache_key(self):
        original = docs.input_digest()
        for name in self.inputs:
            with self.subTest(input=name):
                path = self.root / name
                content = path.read_text()
                path.write_text("changed input\n")
                self.assertNotEqual(docs.input_digest(), original)
                path.write_text(content)
        (self.root / "New.lean").write_text("new Lean source\n")
        self.assertNotEqual(docs.input_digest(), original)

    def test_source_edits_and_import_changes_keep_environment_compatible(self):
        original = docs.compatibility_digest()
        for name in ("Main.lean", "docbuild/Documentation.lean"):
            (self.root / name).write_text("changed Lean source\n")
        (self.root / "New.lean").write_text("new module\n")
        self.assertEqual(docs.compatibility_digest(), original)

    def test_deleted_tracked_lean_source_changes_fingerprint(self):
        original = docs.input_digest()
        (self.root / "Main.lean").unlink()
        self.assertNotEqual(docs.input_digest(), original)

    def test_build_configuration_changes_environment_compatibility(self):
        original = docs.compatibility_digest()
        for name in docs.CONFIG_INPUTS:
            with self.subTest(input=name):
                path = self.root / name
                content = path.read_bytes() if path.exists() else None
                path.write_text("changed build environment\n")
                self.assertNotEqual(docs.compatibility_digest(), original)
                if content is None:
                    path.unlink()
                else:
                    path.write_bytes(content)

    def test_legacy_revision_digest_detects_configuration_changes(self):
        subprocess.run(["git", "-C", str(self.root), "-c", "user.name=Docs test",
                        "-c", "user.email=docs@example.org", "commit", "--quiet", "-m", "fixture"],
                       check=True)
        revision = subprocess.check_output(["git", "-C", str(self.root), "rev-parse", "HEAD"],
                                           text=True).strip()
        original = docs.compatibility_digest()
        self.assertEqual(docs.compatibility_digest(revision), original)
        (self.root / "Main.lean").write_text("new source\n")
        self.assertEqual(docs.compatibility_digest(revision), docs.compatibility_digest())
        (self.root / "docbuild/lakefile.toml").write_text("new generator config\n")
        self.assertEqual(docs.compatibility_digest(revision), original)
        self.assertNotEqual(docs.compatibility_digest(revision), docs.compatibility_digest())
        self.assertIsNone(docs.compatibility_digest("a" * 40))
        self.assertIsNone(docs.compatibility_digest("HEAD"))


class UnicodeInputOrderTests(unittest.TestCase):
    def test_restored_archive_order_is_preserved_and_patch_is_idempotent(self):
        with tempfile.TemporaryDirectory() as tmp:
            package = Path(tmp)
            sources = package / "UnicodeCLib"
            sources.mkdir()
            for name in ("basic.c", "case.c", "prop.c", "script.c"):
                (sources / name).write_text("C source")
            config = package / "lakefile.lean"
            config.write_text(docs.UNICODE_LOOP + "\n    original body\n")
            trace = package / ".lake/build/lib/libunicodeclib.a.trace"
            trace.parent.mkdir(parents=True)
            order = ["prop", "case", "script", "basic"]
            trace.write_text(json.dumps({"inputs": [["objs", [
                [f"/old/runner/UnicodeCLib/{name}.o", "hash"] for name in order
            ]]]}))
            original_trace = trace.read_text()
            with patch.object(docs, "UNICODE_PACKAGE", package):
                docs.stabilize_unicode_order()
                patched = config.read_text()
                self.assertIn('#["prop.c", "case.c", "script.c", "basic.c"]', patched)
                self.assertIn("for file in ordered do\n    original body", patched)
                self.assertEqual(trace.read_text(), original_trace)
                docs.stabilize_unicode_order()
                self.assertEqual(config.read_text(), patched)

    def test_cold_or_invalid_trace_uses_sorted_sources(self):
        for content in (None, "{", '{"inputs": []}',
                        '{"inputs": [["objs", [["missing.o", "hash"]]]]}'):
            with self.subTest(trace=content), tempfile.TemporaryDirectory() as tmp:
                package = Path(tmp)
                (package / "UnicodeCLib").mkdir()
                for name in ("z.c", "a.c"):
                    (package / "UnicodeCLib" / name).touch()
                (package / "lakefile.lean").write_text(docs.UNICODE_LOOP)
                if content is not None:
                    trace = package / ".lake/build/lib/libunicodeclib.a.trace"
                    trace.parent.mkdir(parents=True)
                    trace.write_text(content)
                with patch.object(docs, "UNICODE_PACKAGE", package):
                    docs.stabilize_unicode_order()
                self.assertIn('#["a.c", "z.c"]', (package / "lakefile.lean").read_text())


class RemovedModuleTests(unittest.TestCase):
    def test_removed_module_rows_and_markers_are_pruned_with_foreign_keys(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            build = root / "build"
            (build / "doc-data").mkdir(parents=True)
            present = root / "Example/Present.lean"
            present.parent.mkdir()
            present.touch()
            for module in ("Example.Removed", "Example.Present", "Mathlib.Remote"):
                for suffix in (".doc", ".doc.hash", ".doc.trace"):
                    (build / "doc-data" / f"{module}{suffix}").write_text("marker")
            with sqlite3.connect(build / "api-docs.db") as database:
                database.execute("PRAGMA foreign_keys = ON")
                database.execute("CREATE TABLE modules (name TEXT PRIMARY KEY, source_url TEXT)")
                database.execute("CREATE TABLE declarations (name TEXT, module_name TEXT "
                                 "REFERENCES modules(name) ON DELETE CASCADE)")
                for module, source in (
                    ("Example.Removed", f"{docs.REPOSITORY}/blob/{'a' * 40}/Example/Removed.lean"),
                    ("Example.Present", f"{docs.REPOSITORY}/blob/{'a' * 40}/Example/Present.lean"),
                    ("Mathlib.Remote", "https://github.com/leanprover-community/mathlib4/blob/old/Remote.lean"),
                ):
                    database.execute("INSERT INTO modules VALUES (?, ?)", (module, source))
                    database.execute("INSERT INTO declarations VALUES (?, ?)", (module + ".result", module))
            with patch.object(docs, "ROOT", root), patch.object(docs, "DOC_BUILD", build):
                docs.prune_removed_modules()
            with sqlite3.connect(build / "api-docs.db") as database:
                self.assertEqual(database.execute("SELECT name FROM modules ORDER BY name").fetchall(),
                                 [("Example.Present",), ("Mathlib.Remote",)])
                self.assertEqual(database.execute("SELECT COUNT(*) FROM declarations").fetchone(), (2,))
            self.assertFalse(list((build / "doc-data").glob("Example.Removed.doc*")))
            self.assertEqual(len(list((build / "doc-data").glob("Example.Present.doc*"))), 3)
            self.assertEqual(len(list((build / "doc-data").glob("Mathlib.Remote.doc*"))), 3)

class DeclarationLinkTests(unittest.TestCase):
    def validate_fixture(self, link: str, html: str):
        record = {"name": "Example.result", "module": "Example.Main"}
        index = {
            "modules": {"Example.Main": {"url": "./Example/Main.html"}},
            "declarations": {"Example.result": {"docLink": link}},
        }
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            page = root / "Example/Main.html"
            page.parent.mkdir()
            page.write_text(html)
            with patch.object(docs, "documentation_index", return_value=index), \
                 patch.object(docs, "lean_modules", return_value=["Example.Main"]):
                return docs.validate_documentation([record], root)

    def test_docgen_relative_url_reaches_exact_anchor(self):
        self.validate_fixture("./Example/Main.html#Example.result", '<div id="Example.result"></div>')

    def test_missing_anchor_fails_even_when_name_is_indexed(self):
        with self.assertRaisesRegex(ValueError, "Missing declaration anchor"):
            self.validate_fixture("./Example/Main.html#Example.result", '<div id="Example.other"></div>')

    def test_wrong_module_cannot_satisfy_a_blueprint_link(self):
        with self.assertRaisesRegex(ValueError, "unexpected page"):
            self.validate_fixture("./Example/Other.html#Example.result", '<div id="Example.result"></div>')


class PublishedHtmlTests(unittest.TestCase):
    def parsed(self, text):
        events = []

        class Document(HTMLParser):
            def handle_starttag(self, tag, attrs):
                attrs = [(key, urljoin("https://example.org/project/lean/Example/Main.html", value)
                          if key in ("href", "src") else value) for key, value in attrs]
                events.append((tag, attrs))

            def handle_data(self, data):
                events.append(data)

        Document().feed(text)
        return events

    def test_shorter_urls_and_quotes_preserve_text_and_attributes(self):
        original = '''<div id="Example.result" class="decl theorem"><a
          href=".././Example/Main.html#Example.result">result</a>
          <a href=".././Example/Other.html?q=x&amp;y=z#Example.other">other</a>
          <a href=".././find/#doc/Example.result">find</a>
          <a href="https://github.com/example/repo/blob/abc/Main.lean">source</a>
          <pre><code>  ∀ x, f x = x\n    a &lt; b</code></pre>
          <span title="a &quot;quoted&quot; value">x</span></div>'''
        compact = docs.compact_html(original, "Example/Main.html")
        self.assertLess(len(compact), len(original))
        self.assertIn('href=#Example.result', compact)
        self.assertIn('href=../find/#doc/Example.result', compact)
        self.assertEqual(self.parsed(compact), self.parsed(original))

    def test_scripts_styles_and_literal_html_are_preserved(self):
        original = '''<script>const s = '<a href=".././Other.html">';</script>
        <style>a::after { content: 'href=".././Other.html"' }</style>
        <textarea><a href=".././Other.html"></textarea>
        <!-- <a href=".././Other.html"> -->
        <p title='literal > <a href=".././Other.html">'>href=".././Other.html"</p>'''
        self.assertEqual(docs.compact_html(original, "Example/Main.html"), original)

    def test_self_closing_tags_keep_their_attribute_values(self):
        for original in ('<img src=".././image.svg"/>', '<img src=".././image.svg" />',
                         '<img class="icon" src=../image.svg/>'):
            compact = docs.compact_html(original, "Example/Main.html")
            self.assertEqual(self.parsed(compact), self.parsed(original))


if __name__ == "__main__":
    unittest.main()
