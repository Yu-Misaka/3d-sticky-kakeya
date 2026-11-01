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
import sqlite3
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
CONFIG_INPUTS = (
    "lean-toolchain", "lakefile.toml", "lakefile.lean", "lake-manifest.json",
    "docbuild/lean-toolchain", "docbuild/lakefile.toml", "docbuild/lake-manifest.json",
)
UNICODE_PACKAGE = ROOT / ".lake/packages/UnicodeBasic"
UNICODE_LOOP = '  for file in (← (pkg.dir / "UnicodeCLib").readDir) do'
UNICODE_ORDER = re.compile(
    r"  -- blueprint: stable UnicodeCLib input order\n.*?"
    r"  -- blueprint: end stable UnicodeCLib input order", re.S,
)
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


def compatibility_digest(revision: str | None = None) -> str | None:
    """Separate source edits from changes to the generator's build environment.

    Legacy stamps only record the git revision. Read that revision's config to
    migrate compatible v3 caches without trusting an unrelated database. CI
    fetches history for this comparison; unavailable history means a rebuild.
    """
    if revision is not None:
        if not re.fullmatch(r"[0-9a-f]{40,64}", revision):
            return None
        commit = subprocess.run(["git", "cat-file", "-e", f"{revision}^{{commit}}"],
                                cwd=ROOT, capture_output=True)
        if commit.returncode:
            return None
    digest = hashlib.sha256()
    for name in CONFIG_INPUTS:
        if revision is None:
            path = ROOT / name
            content = path.read_bytes() if path.is_file() else None
        else:
            result = subprocess.run(["git", "show", f"{revision}:{name}"],
                                    cwd=ROOT, capture_output=True)
            content = result.stdout if result.returncode == 0 else None
        digest.update(name.encode() + b"\0")
        digest.update(b"missing\0" if content is None else hashlib.sha256(content).digest())
    return digest.hexdigest()


def cache_complete() -> bool:
    return all((DOC_BUILD / name).is_file() for name in (
        "api-docs.db", "doc-manifest.json", "doc/Documentation.html",
        "doc/declarations/declaration-data.bmp",
    ))


def cache_stamp() -> dict:
    try:
        stamp = json.loads(STAMP.read_text())
    except (FileNotFoundError, json.JSONDecodeError):
        return {}
    return stamp if isinstance(stamp, dict) else {}


def cached_inputs() -> str | None:
    inputs = cache_stamp().get("inputs")
    return inputs if isinstance(inputs, str) else None


def stabilize_unicode_order() -> None:
    """Keep UnicodeBasic's object order stable across restored filesystems.

    Preserve the archive's recorded order, including for pre-fix caches. A
    cold build starts in lexical order. Only the ignored package checkout is
    patched; the pinned source files and dependency manifests stay intact.
    """
    config = UNICODE_PACKAGE / "lakefile.lean"
    source = config.read_text()
    if UNICODE_LOOP not in source and not UNICODE_ORDER.search(source):
        # A newer upstream version may already sort its inputs.
        if '.readDir).qsort (·.fileName < ·.fileName)' in source:
            return
        raise ValueError("Cannot stabilize UnicodeBasic's UnicodeCLib input order")
    names = sorted(path.name for path in (UNICODE_PACKAGE / "UnicodeCLib").glob("*.c"))
    order = names
    trace = UNICODE_PACKAGE / ".lake/build/lib/libunicodeclib.a.trace"
    try:
        inputs = json.loads(trace.read_text())["inputs"]
        objects = next(value for key, value in inputs if key == "objs")
        recorded = [Path(path).with_suffix(".c").name for path, _ in objects]
        if len(recorded) == len(names) and set(recorded) == set(names):
            order = recorded
    except (FileNotFoundError, json.JSONDecodeError, KeyError, TypeError, ValueError, StopIteration):
        pass
    literal = ", ".join(json.dumps(name) for name in order)
    loop = (
        "  -- blueprint: stable UnicodeCLib input order\n"
        f"  let sourceOrder : Array String := #[{literal}]\n"
        '  let sources ← (pkg.dir / "UnicodeCLib").readDir\n'
        "  let ordered := sources.qsort fun a b =>\n"
        "    let i := sourceOrder.idxOf a.fileName\n"
        "    let j := sourceOrder.idxOf b.fileName\n"
        "    i < j || (i == j && a.fileName < b.fileName)\n"
        "  -- blueprint: end stable UnicodeCLib input order\n"
        "  for file in ordered do"
    )
    if UNICODE_LOOP in source:
        updated = source.replace(UNICODE_LOOP, loop, 1)
    else:
        updated = UNICODE_ORDER.sub(lambda _: loop.rsplit("\n", 1)[0], source, count=1)
    if updated != source:
        config.write_text(updated)
        print(f"Stabilized UnicodeCLib inputs: {', '.join(order)}.", flush=True)


def prune_removed_modules() -> None:
    """Delete removed project modules before doc-gen4 replaces changed ones."""
    prefix = REPOSITORY + "/blob/"
    with sqlite3.connect(DOC_BUILD / "api-docs.db") as database:
        database.execute("PRAGMA foreign_keys = ON")
        modules = database.execute("SELECT name, source_url FROM modules").fetchall()
        for module, url in modules:
            if not isinstance(url, str) or not url.startswith(prefix):
                continue
            revision, separator, relative = url[len(prefix):].partition("/")
            if not separator or not re.fullmatch(r"[0-9a-f]{40,64}", revision):
                continue
            source = ROOT / unquote(relative)
            if source.suffix == ".lean" and not source.is_file():
                database.execute("DELETE FROM modules WHERE name = ?", (module,))
                # A later reintroduction must not reuse this module's marker.
                for path in (DOC_BUILD / "doc-data").glob(f"{module}.doc*"):
                    path.unlink()
                print(f"Removed obsolete documentation module: {module}.", flush=True)


def clear_rendered_docs() -> None:
    """Discard render outputs, including disk data merged into the search index."""
    path = DOC_BUILD / "doc"
    if path.exists():
        shutil.rmtree(path)
    (DOC_BUILD / "doc-manifest.json").unlink(missing_ok=True)
    for pattern in ("*.docs_built*", "*.docsHeader_built*",
                    "declaration-data-*.bmp", "backrefs-*.json"):
        for path in (DOC_BUILD / "doc-data").glob(pattern):
            path.unlink()


def prepare_docs() -> bool:
    """Prepare the cache and return whether doc-gen4 needs to run."""
    check_docbuild_config()
    stamp = cache_stamp()
    complete = cache_complete()
    if stamp.get("inputs") == input_digest() and complete:
        print("Reusing validated documentation for unchanged inputs; skipping doc-gen4/Lake.", flush=True)
        return False
    compatible = stamp.get("compatibility")
    if compatible is None and isinstance(stamp.get("revision"), str):
        compatible = compatibility_digest(stamp["revision"])
    if complete and isinstance(stamp.get("inputs"), str) and compatible == compatibility_digest():
        # The upstream single-module writer deletes that module's old rows in
        # a transaction, including removed declarations. Preserve its database
        # and docInfo markers so Lake only reprocesses affected imports.
        STAMP.unlink(missing_ok=True)
        prune_removed_modules()
        clear_rendered_docs()
        print("Documentation sources changed; updating module data incrementally and regenerating HTML/indexes.", flush=True)
    else:
        # An unknown/incompatible environment or incomplete database cannot
        # safely retain docInfo's empty marker files.
        for name in ("doc", "doc-data"):
            path = DOC_BUILD / name
            if path.exists():
                shutil.rmtree(path)
        for pattern in ("api-docs.db*", "doc-manifest.json", "blueprint-docs.json"):
            for path in DOC_BUILD.glob(pattern):
                path.unlink()
        print("Documentation environment changed or cache is incomplete; rebuilding doc-gen4 data.", flush=True)
    return True


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
    STAMP.write_text(json.dumps({"inputs": input_digest(), "revision": revision,
                                "compatibility": compatibility_digest()}, indent=2) + "\n")


def check_fresh_docs() -> None:
    if cached_inputs() != input_digest() or not cache_complete():
        raise ValueError("Documentation is missing or stale; build with python blueprint/scripts/build.py")


def build_docs() -> None:
    # UnicodeBasic's unsorted C inputs can invalidate Lake's traces on another
    # runner. A complete cache with matching source inputs needs no Lake call.
    if prepare_docs():
        stabilize_unicode_order()
        BUILD.mkdir(exist_ok=True)
        run_logged(["lake", "--no-cache", "-d", "docbuild", "build", "Documentation:docs"],
                   BUILD / "docgen.log")
    finish_docs()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("prepare", "check", "build", "fingerprint"))
    args = parser.parse_args()
    try:
        if args.command == "fingerprint":
            print(input_digest())
        else:
            {"prepare": prepare_docs, "check": finish_docs, "build": build_docs}[args.command]()
    except (OSError, ValueError, KeyError, sqlite3.Error, subprocess.CalledProcessError) as error:
        parser.exit(1, f"Documentation check failed: {error}\n")
