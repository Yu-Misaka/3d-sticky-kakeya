"""Regression checks for documentation cache invalidation and declaration links."""

import json
import sys
import tempfile
import unittest
from html.parser import HTMLParser
from pathlib import Path
from unittest.mock import patch
from urllib.parse import urljoin

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import docs


class DocumentationCacheTests(unittest.TestCase):
    def test_changed_inputs_discard_database_and_pages_together(self):
        with tempfile.TemporaryDirectory() as tmp:
            build = Path(tmp)
            for relative in ("doc/Old.html", "doc-data/Old.doc", "api-docs.db",
                             "api-docs.db-wal", "doc-manifest.json", "lib/lean/Documentation.olean"):
                path = build / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("old build")
            stamp = build / "blueprint-docs.json"
            stamp.write_text(json.dumps({"inputs": "old"}))
            with patch.object(docs, "DOC_BUILD", build), patch.object(docs, "STAMP", stamp), \
                 patch.object(docs, "input_digest", return_value="new"), \
                 patch.object(docs, "check_docbuild_config"):
                docs.prepare_docs()
            self.assertFalse((build / "doc").exists())
            self.assertFalse((build / "doc-data").exists())
            self.assertFalse((build / "api-docs.db").exists())
            self.assertFalse((build / "api-docs.db-wal").exists())
            self.assertFalse(stamp.exists())
            self.assertTrue((build / "lib/lean/Documentation.olean").is_file())

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
                 patch.object(docs, "check_docbuild_config"):
                docs.prepare_docs()
                docs.check_fresh_docs()
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
                docs.prepare_docs()
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
