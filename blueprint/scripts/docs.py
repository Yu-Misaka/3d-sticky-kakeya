#!/usr/bin/env python3
"""Build and validate standard doc-gen4 documentation for the blueprint."""

from __future__ import annotations

import argparse
import hashlib
import html
import json
import posixpath
import re
import shutil
import subprocess
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urlsplit, urlunsplit

from check import (BUILD, ROOT, check_docbuild_config, check_registry,
                   inspect_content, lean_modules, run_logged, source_digest)

DOCBUILD = ROOT / "docbuild"
DOC_BUILD = DOCBUILD / ".lake/build"
DOCS = DOC_BUILD / "doc"
STAMP = DOC_BUILD / "blueprint-docs.json"
REPOSITORY = "https://github.com/Yu-Misaka/3d-sticky-kakeya"
HTML_PART = re.compile(
    r"(?P<raw><!--.*?-->|<(?P<rawtag>script|style|textarea|title)\b[^>]*>"
    r".*?</(?P=rawtag)\s*>)"
    r'''|(?P<tag><[a-z](?:[^<>"']|"[^"]*"|'[^']*')*>)''', re.I | re.S,
)
ATTRIBUTE = re.compile(
    r'''(?P<name>\s[\w:-]+)\s*=\s*(?:"(?P<value>[^"]*)"|(?P<other>'[^']*'|[^\s>]+))'''
)
UNQUOTED = re.compile(r"[^\s\"'`=<>]+\Z")


def compact_html(text: str, page: str) -> str:
    """Shorten equivalent HTML syntax, preserving text and every link target.

    Full dependency documentation exceeds Pages' size limit as emitted by
    doc-gen4. Its root-relative links repeat long directory prefixes millions
    of times. Use the shortest relative path and omit optional attribute quotes
    in the published copy, leaving the generator's cache unchanged.
    """
    parent = posixpath.dirname(page) or "."
    shortened: dict[str, str] = {}

    def attribute(match: re.Match) -> str:
        name, value = match["name"], match["value"]
        if value is None:
            return match[0]
        if name.strip().lower() in ("href", "src") and value.startswith(("./", "../")):
            if value not in shortened:
                link = urlsplit(html.unescape(value))
                target = posixpath.normpath(posixpath.join(parent, link.path))
                path = "" if target == page and link.fragment else posixpath.relpath(target, parent)
                if link.path.endswith("/") and path and not path.endswith("/"):
                    path += "/"
                updated = html.escape(urlunsplit(("", "", path, link.query, link.fragment)),
                                      quote=False).replace('"', "&quot;")
                shortened[value] = updated if len(updated) < len(value) else value
            value = shortened[value]
        if UNQUOTED.fullmatch(value):
            rendered = value
            # Do not let a self-closing slash become part of this value.
            if match.string.endswith("/>") and match.end() == len(match.string) - 2:
                rendered += " "
        else:
            rendered = f'"{value}"'
        return f"{name}={rendered}"

    def part(match: re.Match) -> str:
        if match["raw"] is not None:
            return match[0]
        return ATTRIBUTE.sub(attribute, match["tag"])

    return HTML_PART.sub(part, text)


def copy_documentation(destination: Path) -> None:
    def copy_file(source: str, target: str) -> str:
        path = Path(source)
        if path.suffix == ".html":
            Path(target).write_text(compact_html(path.read_text(), path.relative_to(DOCS).as_posix()))
            return target
        return shutil.copy2(source, target)

    shutil.copytree(DOCS, destination, copy_function=copy_file)


def input_digest() -> str:
    digest = hashlib.sha256(source_digest().encode())
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "Documentation.lean"):
        digest.update((DOCBUILD / name).read_bytes())
    return digest.hexdigest()


def cache_complete() -> bool:
    return all((DOC_BUILD / name).is_file() for name in (
        "api-docs.db", "doc-manifest.json", "doc/Documentation.html",
        "doc/declarations/declaration-data.bmp",
    ))


def prepare_docs() -> None:
    check_docbuild_config()
    previous = json.loads(STAMP.read_text()) if STAMP.is_file() else {}
    if previous.get("inputs") != input_digest() or not cache_complete():
        # doc-gen4's database and markers form one cache. Discard them together
        # when inputs change, so deleted declarations or empty marker files
        # cannot leave stale documentation in a restored cache.
        for name in ("doc", "doc-data"):
            path = DOC_BUILD / name
            if path.exists():
                shutil.rmtree(path)
        for pattern in ("api-docs.db*", "doc-manifest.json", "blueprint-docs.json"):
            for path in DOC_BUILD.glob(pattern):
                path.unlink()
        print("Documentation inputs changed or cache is incomplete; rebuilding doc-gen4 data.", flush=True)
    else:
        print("Reusing doc-gen4 data for unchanged Lean sources.", flush=True)


class Anchors(HTMLParser):
    def __init__(self, path: Path):
        super().__init__()
        self.ids: set[str] = set()
        self.feed(path.read_text())

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        for key, value in attrs:
            if value is not None and (key == "id" or (tag == "a" and key == "name")):
                self.ids.add(value)


def documentation_index(root: Path = DOCS) -> dict:
    for relative in ("index.html", "Documentation.html", "find/index.html", "find/find.js",
                     "search.html", "search.js", "declaration-data.js", "style.css",
                     "declarations/declaration-data.bmp"):
        if not (root / relative).is_file():
            raise ValueError(f"Missing doc-gen4 output: {root / relative}")
    index = json.loads((root / "declarations/declaration-data.bmp").read_text())
    if not index.get("declarations") or not index.get("modules"):
        raise ValueError("doc-gen4 returned an empty declaration or module index")
    return index


def validate_documentation(records: list[dict], root: Path = DOCS) -> dict:
    index = documentation_index(root)
    for module in lean_modules():
        if module not in index["modules"]:
            raise ValueError(f"Documentation is missing a blueprint module: {module}")
    # Check every generated module's page, then the exact anchors of all links
    # from the blueprint. Avoid loading thousands of large HTML pages at once.
    for module, data in index["modules"].items():
        path = unquote(urlsplit(data["url"]).path)
        if not (root / path).is_file():
            raise ValueError(f"Documentation index points to a missing module page: {module}")
    anchors: dict[Path, set[str]] = {}
    for record in records:
        name = record["name"]
        data = index["declarations"].get(name)
        if data is None:
            raise ValueError(f"Declaration absent from doc-gen4's search index: {name}")
        link = urlsplit(data["docLink"])
        path = Path(unquote(link.path)).as_posix()
        expected = record["module"].replace(".", "/") + ".html"
        if path != expected or unquote(link.fragment) != name:
            raise ValueError(f"doc-gen4 resolved {name} to an unexpected page: {data['docLink']}")
        target = root / path
        if target not in anchors:
            anchors[target] = Anchors(target).ids
        if name not in anchors[target]:
            raise ValueError(f"Missing declaration anchor: {path}#{name}")
    print(f"Checked doc-gen4: {len(index['modules'])} module pages, "
          f"{len(index['declarations'])} indexed declarations, {len(records)} declaration links.", flush=True)
    return index


def refresh_source_links() -> str:
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    if not re.fullmatch(r"[0-9a-f]{40,64}", revision):
        raise ValueError("Cannot determine the source revision")
    old_link = re.compile(re.escape(REPOSITORY) + r"/blob/[0-9a-f]{40,64}/")
    for pattern in ("**/*.html", "declarations/*.bmp"):
        for path in DOCS.glob(pattern):
            text = path.read_text()
            updated = old_link.sub(f"{REPOSITORY}/blob/{revision}/", text)
            if updated != text:
                path.write_text(updated)
    return revision


def finish_docs() -> None:
    _, names, nodes = inspect_content()
    records = check_registry(names, nodes)
    validate_documentation(records)
    # For a text-only commit the compiled declarations are unchanged, but the
    # source buttons should still point to this site's actual checkout.
    revision = refresh_source_links()
    STAMP.write_text(json.dumps({"inputs": input_digest(), "revision": revision}, indent=2) + "\n")


def check_fresh_docs() -> None:
    if not STAMP.is_file() or json.loads(STAMP.read_text()).get("inputs") != input_digest() \
            or not cache_complete():
        raise ValueError("Documentation is missing or stale; build with python blueprint/scripts/build.py")


def build_docs() -> None:
    prepare_docs()
    BUILD.mkdir(exist_ok=True)
    run_logged(["lake", "--no-cache", "-d", "docbuild", "build", "Documentation:docs"],
               BUILD / "docgen.log")
    finish_docs()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("prepare", "check", "build"))
    args = parser.parse_args()
    try:
        {"prepare": prepare_docs, "check": finish_docs, "build": build_docs}[args.command]()
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"Documentation check failed: {error}\n")
