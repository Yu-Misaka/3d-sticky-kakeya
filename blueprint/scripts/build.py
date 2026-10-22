#!/usr/bin/env python3
"""Build and validate the complete GitHub Pages artifact in blueprint/site."""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urlsplit

from check import (BLUEPRINT, BUILD, audit_with_lean, check_docbuild_config,
                   check_registry, inspect_content, run_logged, source_digest)
from docs import build_docs, check_fresh_docs, copy_documentation, validate_documentation
from dependencies import check_report, write_site

SITE = BLUEPRINT / "site"


class Links(HTMLParser):
    def __init__(self, text: str):
        super().__init__()
        self.links: list[str] = []
        self.ids: set[str] = set()
        self.feed(text)

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        for name, value in attrs:
            if value is None:
                continue
            if name in ("href", "src", "xlink:href", "data-audit"):
                self.links.append(value)
            if name == "id" or (tag == "a" and name == "name"):
                self.ids.add(value)


def validate_site(records: list[dict]) -> None:
    report = check_report(records, source_digest())
    from atlas import check_correspondence
    _, _, manuscript_nodes = inspect_content()
    check_correspondence(manuscript_nodes, report)
    existing = {record["name"] for record in records}
    extra = [{"name": name, **report["evidence"][name]}
             for name in report["graph_nodes"] if name not in existing]
    index = validate_documentation([*records, *extra], SITE / "lean")
    names = index["declarations"]
    # doc-gen4's module index and all blueprint declaration anchors are checked
    # above. Keep this pass focused on the manuscript and the site's navigation.
    files = [*SITE.glob("*.html"), *(SITE / "blueprint").rglob("*.html")]
    pages = {path: Links(path.read_text()) for path in files}
    # The atlas draws its cards and arrows from data; check those links as the page's own.
    from atlas_render import atlas_links
    atlas_page = SITE / "blueprint/lean_dependencies.html"
    pages[atlas_page].links += atlas_links(json.loads((SITE / "blueprint/atlas-view.json").read_text()))
    errors = []
    for page, document in pages.items():
        for link in document.links:
            parsed = urlsplit(link)
            if parsed.scheme or parsed.netloc or not link:
                continue
            target = (page.parent / unquote(parsed.path)).resolve() if parsed.path else page
            if target.is_dir():
                target /= "index.html"
            if not target.is_relative_to(SITE) or not target.is_file():
                errors.append(f"{page.relative_to(SITE)}: missing {link}")
                continue
            fragment = unquote(parsed.fragment)
            if fragment.startswith("doc/") and target == SITE / "lean/find/index.html":
                if fragment[4:] not in names:
                    errors.append(f"Unknown declaration: {fragment[4:]}")
            elif fragment and target in pages and fragment not in pages[target].ids:
                errors.append(f"{page.relative_to(SITE)}: missing anchor {link}")
    if errors:
        raise ValueError("Broken site links:\n" + "\n".join(errors[:30]))
    print(f"Checked local links and anchors in {len(pages)} HTML pages.")
    sizes = [path.stat().st_size for path in SITE.rglob("*") if path.is_file()]
    # Include tar headers and padding rather than relying on compressed size.
    artifact_size = sum(512 + ((size + 511) // 512) * 512 for size in sizes)
    if artifact_size >= 1_000_000_000:
        raise ValueError(f"Pages artifact exceeds 1 GB: approximately {artifact_size:,} bytes")
    print(f"Pages artifact: {sum(sizes) / 1_000_000:.1f} MB of files, "
          f"approximately {artifact_size / 1_000_000:.1f} MB with tar overhead.")


def make_site(reuse_docs: bool = False) -> None:
    _, names, nodes = inspect_content()
    check_docbuild_config()
    if not reuse_docs:
        audit_with_lean(names)
    records = check_registry(names, nodes)
    if reuse_docs:
        check_fresh_docs()
    else:
        build_docs()
    BUILD.mkdir(exist_ok=True)
    run_logged(["leanblueprint", "pdf"], BUILD / "pdf.log")
    pdf_log = (BLUEPRINT / "print/print.log").read_text()
    if re.search(r"(?:Reference|Citation).*undefined|There were undefined references", pdf_log):
        raise ValueError("Unresolved PDF references; see blueprint/print/print.log")
    if "Overfull \\hbox" in pdf_log or "Overfull \\vbox" in pdf_log:
        raise ValueError("PDF content exceeds its margins; see blueprint/print/print.log")
    # Avoid retaining obsolete chapter pages or cross-reference state.
    web = BLUEPRINT / "web"
    if web.exists():
        shutil.rmtree(web)
    for path in (BLUEPRINT / "src").glob("*.paux"):
        path.unlink()
    web_log = run_logged(["leanblueprint", "web"], BUILD / "web.log")
    if re.search(r"unrecognized (?:command|environment)|undefined (?:reference|citation)", web_log, re.I):
        raise ValueError("Unresolved HTML commands or references; see blueprint/build/web.log")
    if not (web / "index.html").is_file():
        raise ValueError("The HTML build did not produce an index")
    if SITE.exists():
        shutil.rmtree(SITE)
    shutil.copytree(BLUEPRINT / "site-src", SITE)
    shutil.copytree(web, SITE / "blueprint")
    copy_documentation(SITE / "lean")
    shutil.copy2(BLUEPRINT / "print/print.pdf", SITE / "blueprint.pdf")
    (SITE / ".nojekyll").touch()
    write_site(SITE, check_report(records, source_digest()), nodes)
    validate_site(records)
    print(f"Site ready: {SITE}\nServe with: python -m http.server 8000 --directory blueprint/site")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-site", action="store_true", help="check an existing site without recompiling")
    parser.add_argument("--reuse-docs", action="store_true",
                        help="reuse already audited Lean and doc-gen4 output with matching inputs")
    args = parser.parse_args()
    try:
        if args.check_site:
            _, names, nodes = inspect_content()
            validate_site(check_registry(names, nodes))
        else:
            make_site(reuse_docs=args.reuse_docs)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"Blueprint build failed: {error}\n")
