#!/usr/bin/env python3
"""Build and validate the complete GitHub Pages artifact in blueprint/site."""

from __future__ import annotations

import argparse
import html
import json
import re
import shutil
import subprocess
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import quote, unquote, urlsplit

from check import BLUEPRINT, BUILD, ROOT, check_registry, inspect_content, run_logged

SITE = BLUEPRINT / "site"
REPOSITORY = "https://github.com/Yu-Misaka/3d-sticky-kakeya"


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
            if name in ("href", "src"):
                self.links.append(value)
            if name == "id" or (tag == "a" and name == "name"):
                self.ids.add(value)


def validate_site(names: set[str]) -> None:
    pages = {path: Links(path.read_text()) for path in SITE.rglob("*.html")}
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


def make_site() -> None:
    _, names, nodes = inspect_content()
    records = check_registry(names, nodes)
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
    shutil.copy2(BLUEPRINT / "print/print.pdf", SITE / "blueprint.pdf")
    (SITE / ".nojekyll").touch()
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    if not re.fullmatch(r"[0-9a-f]{40,64}", revision):
        raise ValueError("Cannot determine a source revision")
    source_links = [
        {"name": record["name"], "kind": record["kind"],
         "file": record["file"], "line": record["line"],
         "url": f"{REPOSITORY}/blob/{revision}/{quote(record['file'])}#L{record['line']}"}
        for record in records
    ]
    (SITE / "declarations.json").write_text(json.dumps(source_links, ensure_ascii=False) + "\n")
    # The fallback source list also works without JavaScript.
    finder = SITE / "lean/find/index.html"
    links = "\n".join(
        f'<li><a href="{html.escape(record["url"])}">'
        f'{html.escape(record["name"])}</a></li>' for record in source_links
    )
    finder.write_text(finder.read_text().replace("<!-- DECLARATION_LINKS -->", links))
    validate_site(set(names))
    print(f"Site ready: {SITE}\nServe with: python -m http.server 8000 --directory blueprint/site")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-site", action="store_true", help="check an existing site without recompiling")
    args = parser.parse_args()
    try:
        if args.check_site:
            _, names, _ = inspect_content()
            validate_site(set(names))
        else:
            make_site()
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"Blueprint build failed: {error}\n")
