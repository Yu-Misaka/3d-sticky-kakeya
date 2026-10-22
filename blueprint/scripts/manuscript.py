#!/usr/bin/env python3
"""Give the plasTeX manuscript the site's design.

plasTeX writes the statements, proofs and cross-references. This pass keeps
that content and every anchor in it, and replaces the theme around it: the
site bar, a chapter list, and plain labelled badges instead of the theme's
icon popups. A theorem's badges list its Lean declarations, the results it
cites (its TeX \\uses, which are not Lean dependencies), and its node in the
proof atlas. Pages that have already been converted are left alone.
"""

from __future__ import annotations

import json
from pathlib import Path

from bs4 import BeautifulSoup

from dependencies import BLUEPRINT


def is_plastex(text: str) -> bool:
    return 'name="generator" content="plasTeX"' in text


def chapter_list(soup: BeautifulSoup) -> list[dict]:
    """Chapters with their sections, from the theme's navigation tree."""
    chapters = []
    for item in soup.select("nav.toc > ul.sub-toc-0 > li"):
        link = item.find("a")
        if not link or "dep_graph" in link["href"]:
            continue
        ref = link.select_one(".toc_ref")
        sections = [{"href": a["href"], "ref": a.select_one(".toc_ref").get_text(strip=True) if a.select_one(".toc_ref") else "",
                     "title": a.select_one(".toc_entry").get_text(" ", strip=True)}
                    for a in item.select("ul.sub-toc-1 > li > a") if a.select_one(".toc_entry")]
        chapters.append({"href": link["href"], "ref": ref.get_text(strip=True) if ref else "",
                         "title": link.select_one(".toc_entry").get_text(" ", strip=True), "sections": sections})
    return chapters


def atlas_nodes(view: dict) -> dict[str, list[dict]]:
    """Manuscript labels and the atlas nodes that show them."""
    nodes: dict[str, list[dict]] = {}
    for node in view["nodes"]:
        for label in node["labels"]:
            nodes.setdefault(label, []).append(node)
        # Each correspondence Remark of the generated appendix belongs to one node.
        nodes.setdefault("rem:atlas-" + node["id"], []).append(node)
    return nodes


def atlas_node(label: str, declarations: list[str], nodes: dict[str, list[dict]]) -> str | None:
    """The node for a statement: the one anchored at its declaration, else the roadmap's own."""
    candidates = nodes.get(label, [])
    for node in candidates:
        if node["primary"] in declarations:
            return node["id"]
    return next((node["id"] for node in candidates if node["expert"]), candidates[0]["id"] if candidates else None)


def badge(soup: BeautifulSoup, label: str, title: str, links: list[tuple[str, str]], heading: str,
          classes: str = "") -> BeautifulSoup:
    """A badge that opens a short list of links; a details element, so it works without JavaScript."""
    box = soup.new_tag("details", attrs={"class": "pop " + classes})
    summary = soup.new_tag("summary", attrs={"class": "badge", "title": title})
    summary.string = label
    panel = soup.new_tag("div", attrs={"class": "pop-panel"})
    caption = soup.new_tag("p")
    caption.string = heading
    listing = soup.new_tag("ul")
    for href, text in links:
        item = soup.new_tag("li")
        anchor = soup.new_tag("a", href=href)
        anchor.string = text
        item.append(anchor)
        listing.append(item)
    panel.extend([caption, listing])
    box.extend([summary, panel])
    return box


def restyle_statements(soup: BeautifulSoup, nodes: dict[str, list[dict]]) -> None:
    for wrapper in soup.select("div[id]"):
        if not any(cls.endswith("_thmwrapper") for cls in wrapper.get("class", [])):
            continue
        head = next((child for child in wrapper.find_all("div", recursive=False)
                     if any(cls.endswith("_thmheading") for cls in child.get("class", []))), None)
        if head is None:
            continue
        extras = head.select_one(".thm_header_extras")
        hidden = head.select_one(".thm_header_hidden_extras")
        marked = bool(extras and "✓" in extras.get_text())
        declarations, uses = [], []
        if hidden:
            declarations = [(a["href"], a.get_text(strip=True)) for a in hidden.select("a.lean_decl")]
            for container in hidden.select(".modal-container"):
                title = container.find("h1")
                if title and title.get_text(strip=True) == "Uses":
                    uses = [(a["href"], a.get_text(" ", strip=True)) for a in container.select("ul.uses a")]
        for tag in (extras, hidden):
            if tag:
                tag.decompose()
        tools = soup.new_tag("span", attrs={"class": "badges"})
        permalink = soup.new_tag("a", href="#" + wrapper["id"], attrs={"class": "permalink", "aria-label": "Link to this result"})
        permalink.string = "#"
        tools.append(permalink)
        if declarations:
            tools.append(badge(soup, ("✓ " if marked else "") + f"Lean · {len(declarations)}",
                               "Marked \\leanok in the manuscript. Show the linked Lean declarations." if marked
                               else "Show the linked Lean declarations.",
                               declarations, "Linked Lean declarations", "lean" + (" ok" if marked else "")))
        if uses:
            tools.append(badge(soup, f"Uses · {len(uses)}", "Results this statement cites in the manuscript (its TeX \\uses). These are not Lean dependencies.",
                               uses, "Cited in the manuscript, not Lean dependencies"))
        node = atlas_node(wrapper["id"], [text for _, text in declarations], nodes)
        if node:
            link = soup.new_tag("a", href="lean_dependencies.html#node-" + node,
                                attrs={"class": "badge atlas", "title": "Show this result in the proof atlas"})
            link.string = "Atlas →"
            tools.append(link)
        head.append(tools)


def restyle_proofs(soup: BeautifulSoup) -> None:
    """Proofs fold under their caption, closed, as plasTeX's theme had them."""
    for wrapper in soup.select("div.proof_wrapper"):
        caption = wrapper.select_one(".proof_caption")
        content = wrapper.select_one(".proof_content")
        if content is None:
            continue
        proof = soup.new_tag("details", attrs={"class": "proof"})
        if wrapper.get("id"):
            proof["id"] = wrapper["id"]
        summary = soup.new_tag("summary")
        summary.string = caption.get_text(" ", strip=True) if caption else "Proof"
        proof.append(summary)
        proof.append(content.extract())
        wrapper.replace_with(proof)


def restyle_page(text: str, name: str, chapters: list[dict], nodes: dict[str, list[dict]], template) -> str:
    soup = BeautifulSoup(text, "html.parser")
    main = soup.select_one(".main-text")
    if main is None:
        raise ValueError(f"{name}: plasTeX page without its main text")
    restyle_statements(soup, nodes)
    restyle_proofs(soup)
    contents = soup.select_one("nav.local_toc")
    links = {rel: soup.find("link", rel=rel) for rel in ("prev", "next")}
    neighbours = {rel: {"href": link["href"], "title": link.get("title", "")} for rel, link in links.items() if link}
    title = soup.title.get_text(strip=True) if soup.title else "Manuscript"
    return template.render(title=title, page=name, chapters=chapters, neighbours=neighbours,
                           main="".join(str(child) for child in main.contents),
                           contents=str(contents) if contents else "")


def restyle_manuscript(directory: Path) -> int:
    """Convert every plasTeX page in the blueprint directory; return how many were converted."""
    from jinja2 import Environment, FileSystemLoader, select_autoescape
    from markupsafe import Markup

    environment = Environment(loader=FileSystemLoader(BLUEPRINT / "templates"), autoescape=select_autoescape(["html"]))
    environment.filters["markup"] = Markup
    template = environment.get_template("manuscript.html")
    pages = {path: path.read_text() for path in sorted(directory.glob("*.html"))}
    pages = {path: text for path, text in pages.items() if is_plastex(text)}
    if not pages:
        return 0
    index = directory / "index.html"
    chapters = chapter_list(BeautifulSoup(pages.get(index) or next(iter(pages.values())), "html.parser"))
    nodes = atlas_nodes(json.loads((directory / "atlas-view.json").read_text()))
    for path, text in pages.items():
        path.write_text(restyle_page(text, path.name, chapters, nodes, template))
    return len(pages)
