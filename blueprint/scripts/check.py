#!/usr/bin/env python3
"""Check blueprint references; optionally rebuild and audit them in Lean."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BLUEPRINT = ROOT / "blueprint"
SRC = BLUEPRINT / "src"
BUILD = BLUEPRINT / "build"
REGISTRY = BLUEPRINT / "lean-declarations.json"
KINDS = "theorem|proposition|lemma|corollary|definition|remark|proof"
ENVIRONMENT = re.compile(
    rf"\\begin\{{({KINDS})\}}(?:\[([^\n]*?)\])?(.*?)\\end\{{\1\}}",
    re.S,
)
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def uncomment(text: str) -> str:
    return re.sub(r"(?<!\\)%[^\n]*", "", text)


def command_args(text: str, command: str) -> list[str]:
    return re.findall(r"\\" + command + r"(?:\[[^\]]*\])?\{([^{}]+)\}", text)


def comma_args(text: str, command: str) -> list[str]:
    return [item.strip() for arg in command_args(text, command)
            for item in arg.split(",") if item.strip()]


def expand(path: Path, stack: tuple[Path, ...] = ()) -> str:
    if path in stack:
        raise ValueError(f"Recursive input: {path.relative_to(ROOT)}")
    text = uncomment(path.read_text())

    def include(match: re.Match[str]) -> str:
        relative = Path(match[1])
        if not relative.suffix:
            relative = relative.with_suffix(".tex")
        target = SRC / relative
        if not target.is_file():
            raise ValueError(f"Missing input {relative} in {path.relative_to(ROOT)}")
        return expand(target, (*stack, path))

    return re.sub(r"\\input\{([^{}]+)\}", include, text)


def inspect_content() -> tuple[str, list[str], list[dict]]:
    text = expand(SRC / "content.tex")
    # Check both entry points and their macros as well as the common content.
    expand(SRC / "web.tex")
    expand(SRC / "print.tex")
    labels = command_args(text, "label")
    duplicates = sorted({label for label in labels if labels.count(label) > 1})
    if duplicates:
        raise ValueError(f"Duplicate labels: {', '.join(duplicates)}")
    references = {arg.strip() for cmd in ("ref", "eqref", "pageref", "uses", "proves")
                  for arg in comma_args(text, cmd)}
    missing = sorted(references - set(labels))
    if missing:
        raise ValueError(f"Undefined labels: {', '.join(missing)}")
    bibliography = (SRC / "references.bib").read_text()
    bibkeys = set(re.findall(r"@\w+\s*\{\s*([^,\s]+)", bibliography))
    missing = sorted(set(comma_args(text, "cite")) - bibkeys)
    if missing:
        raise ValueError(f"Undefined citations: {', '.join(missing)}")

    names = sorted(set(comma_args(text, "lean")))
    nodes: list[dict] = []
    previous = None
    for match in ENVIRONMENT.finditer(text):
        kind, title, body = match.groups()
        if kind == "proof":
            targets = comma_args(body, "proves")
            if not targets and previous:
                targets = [previous["label"]]
            for target in targets:
                node = next((node for node in nodes if node["label"] == target), None)
                if node is None:
                    raise ValueError(f"Proof target is not a preceding statement: {target}")
                node["proof_complete"] = r"\leanok" in body or r"\mathlibok" in body
                node["uses"] += comma_args(body, "uses")
                node["lean"] += comma_args(body, "lean")
            continue
        node_labels = command_args(body, "label")
        if not node_labels:
            raise ValueError(f"Unlabelled {kind}: {title or body[:60]}")
        node = {"label": node_labels[0], "kind": kind, "title": title or "",
                "lean": comma_args(body, "lean"), "uses": comma_args(body, "uses"),
                "statement_complete": r"\leanok" in body or r"\mathlibok" in body,
                "proof_complete": False}
        nodes.append(node)
        if kind not in ("remark", "definition"):
            previous = node

    graph = {node["label"]: node["uses"] for node in nodes}

    def visit(label: str, active: tuple[str, ...], seen: set[str]) -> None:
        if label in active:
            raise ValueError("Dependency cycle: " + " -> ".join((*active, label)))
        if label in seen:
            return
        for dependency in graph.get(label, []):
            visit(dependency, (*active, label), seen)
        seen.add(label)

    seen: set[str] = set()
    for label in graph:
        visit(label, (), seen)
    return text, names, nodes


def source_digest() -> str:
    """Bind the audit to all project Lean sources and the dependency lock file."""
    result = subprocess.run(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z", "--",
         "*.lean", "lean-toolchain", "lake-manifest.json", "lakefile.toml", "lakefile.lean"],
        cwd=ROOT, check=True, capture_output=True,
    )
    paths = sorted({name.decode() for name in result.stdout.split(b"\0")
                    if name and not name.startswith(b"blueprint/")})
    digest = hashlib.sha256()
    for name in paths:
        digest.update(name.encode() + b"\0")
        digest.update(hashlib.sha256((ROOT / name).read_bytes()).digest())
    return digest.hexdigest()


def run_logged(args: list[str], log: Path) -> str:
    print(f"Running {args[0]} {' '.join(args[1:4])} (log: {log.relative_to(ROOT)})", flush=True)
    with log.open("w") as output:
        result = subprocess.run(args, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
    text = log.read_text()
    if result.returncode:
        print("\n".join(text.splitlines()[-35:]), file=sys.stderr)
        raise ValueError(f"Command failed; see {log.relative_to(ROOT)}")
    return text


def audit_with_lean(names: list[str]) -> None:
    modules = [line.strip() for line in (BLUEPRINT / "lean-imports.txt").read_text().splitlines()
               if line.strip() and not line.lstrip().startswith("#")]
    if not modules or any(not re.fullmatch(r"[\w.]+", module) for module in modules):
        raise ValueError("Invalid module list in blueprint/lean-imports.txt")
    BUILD.mkdir(exist_ok=True)
    run_logged(["lake", "build", *modules], BUILD / "lake-build.log")
    source = "\n".join(f"import {module}" for module in modules)
    source += "\nimport Lean\n\n" + (BLUEPRINT / "scripts" / "audit.lean").read_text()
    source += "\nrun_cmd blueprintAudit #[\n"
    source += ",\n".join("  " + json.dumps(name, ensure_ascii=False) + ".toName" for name in names)
    source += "\n]\n"
    probe = BUILD / "CheckDeclarations.lean"
    probe.write_text(source)
    output = run_logged(["lake", "env", "lean", str(probe)], BUILD / "lean-audit.log")
    records = [json.loads(line.removeprefix("BLUEPRINT "))
               for line in output.splitlines() if line.startswith("BLUEPRINT ")]
    if sorted(record["name"] for record in records) != names:
        raise ValueError("Lean did not return exactly the requested declarations")
    for record in records:
        record["file"] = record["module"].replace(".", "/") + ".lean"
        unexpected = set(record["axioms"]) - ALLOWED_AXIOMS
        if unexpected:
            raise ValueError(f"Unexpected axioms for {record['name']}: {sorted(unexpected)}")
    registry = {"format": 1, "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
                "source_sha256": source_digest(), "declarations": records}
    REGISTRY.write_text(json.dumps(registry, ensure_ascii=False, indent=2) + "\n")


def check_registry(names: list[str], nodes: list[dict]) -> list[dict]:
    if not REGISTRY.is_file():
        raise ValueError("No declaration registry; run this script with --lean")
    registry = json.loads(REGISTRY.read_text())
    if registry["toolchain"] != (ROOT / "lean-toolchain").read_text().strip():
        raise ValueError("Lean toolchain changed; regenerate the registry with --lean")
    if registry["source_sha256"] != source_digest():
        raise ValueError("Lean sources changed since the audit; regenerate the registry with --lean")
    records = registry["declarations"]
    indexed = {record["name"]: record for record in records}
    if len(indexed) != len(records) or sorted(indexed) != names:
        raise ValueError("Declaration registry differs from the TeX links; regenerate it with --lean")
    for record in records:
        source = ROOT / record["file"]
        if not source.is_file():
            raise ValueError(f"Missing Lean source: {record['file']}")
        lines = source.read_text().splitlines()
        line = record["line"]
        short = record["name"].rsplit(".", 1)[-1]
        if line < 1 or line > len(lines) or short not in lines[line - 1]:
            raise ValueError(f"Source position no longer matches {record['name']}; run --lean")
        if set(record["axioms"]) - ALLOWED_AXIOMS:
            raise ValueError(f"Unexpected axioms in registry: {record['name']}")
    for node in nodes:
        if node["proof_complete"] and not any(
            indexed[name]["kind"] == "theorem" for name in node["lean"]
        ):
            raise ValueError(f"Completed proof has no linked theorem: {node['label']}")
    return records


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", action="store_true", help="build imports and regenerate the Lean audit")
    parser.add_argument("--content-only", action="store_true", help="lint the manuscript before the first Lean audit")
    args = parser.parse_args()
    try:
        _, names, nodes = inspect_content()
        if args.lean:
            audit_with_lean(names)
        if not args.content_only:
            check_registry(names, nodes)
        BUILD.mkdir(exist_ok=True)
        (BUILD / "statements.json").write_text(json.dumps(nodes, ensure_ascii=False, indent=2) + "\n")
        statements = sum(node["kind"] != "remark" for node in nodes)
        remarks = len(nodes) - statements
        proofs = sum(node["proof_complete"] for node in nodes)
        print(f"Checked {statements} statements, {remarks} remarks, {len(names)} Lean links; "
              f"{proofs} proofs marked complete.")
        return 0
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as error:
        print(f"Blueprint check failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
