# Sticky Kakeya blueprint

The blueprint follows the proof through Wang–Zahl's finite sticky estimate, Theorem 5.2 of *The Assouad dimension of Kakeya sets in ℝ³*. It includes the structural argument from *Sticky Kakeya sets and the sticky Kakeya conjecture* and the supporting projection, Furstenberg, cinematic, multilinear, and hairbrush estimates. The later general Kakeya and Assouad reductions are outside its scope.

The mathematical text is in English. [The correspondence chapter](src/chapters/correspondence.tex) identifies the manuscript versions and numbering. Remarks next to the relevant results distinguish corrections, normalizations, weaker interfaces, and propositions whose general paper formulation is not marked as fully proved. The downloaded papers themselves are not included in the repository.

The supplied `wz2_theorem_5_2_dependency_atlas.tex` is a mathematical
reading guide. Its Lean snippets are pseudocode, not declaration names or
evidence of formalization. The introduction maps the main route, and the
correspondence chapter records the WZ1-to-WZ2 transfers. Intermediate nodes
expose normalized refinement losses, the AD exponent gap, parameter
freezing, cinematic mass-to-area comparison, uniform parameter coarsening,
and finite telescoping. The Section 7 account keeps the actual Lean
replication deficit and the explicit parameter-Frostman hypotheses.
These additions change the mathematical graph; the compiled dependency
graph continues to follow audited Lean declarations and proof terms.

## Build and read locally

On Ubuntu/Debian, install the system dependencies:

```sh
sudo apt-get update
sudo apt-get install -y --no-install-recommends \
  python3-venv python3-dev build-essential pkg-config \
  texlive-xetex texlive-latex-extra texlive-fonts-recommended \
  latexmk ghostscript dvisvgm poppler-utils graphviz libgraphviz-dev
```

Install [Elan](https://github.com/leanprover/elan) so that `lake` uses the
version pinned in `lean-toolchain`. From the repository root, using Python 3.12:

```sh
python3 -m venv .venv-blueprint
source .venv-blueprint/bin/activate
python -m pip install -r blueprint/requirements.txt
lake exe cache get
python blueprint/scripts/build.py
python -m http.server 8000 --directory blueprint/site
```

Open <http://localhost:8000>. The complete site contains the HTML manuscript,
interactive dependency graph, PDF, and standard **doc-gen4 Lean documentation**
under `/lean/`. Declaration links open their rendered Lean types and docstrings;
doc-gen4 provides module navigation, declaration search, and source buttons.
MathJax loads from a CDN. The PDF is also available directly at
`blueprint/print/print.pdf`.

The documentation entry page includes the full Lean statement of the sticky
theorem, checked against `PureWZ2/Core.lean`. Doc-gen4 omits long automatically
generated equations; the source buttons provide the full bodies of other
proposition-valued definitions when their Equations section is abbreviated.

The full build compiles and audits the Lean imports, generates doc-gen4
documentation, then runs `leanblueprint pdf` before `leanblueprint web` so that
both editions use the same bibliography. It checks labels, citations, graph
dependencies, PDF margins, doc-gen4's module index, and the exact documentation
anchors for every blueprint declaration. Build logs are kept under
`blueprint/build/`; generated output is ignored by Git.

The first documentation build also processes the imported Mathlib and Lean
libraries. Subsequent builds reuse compiled artifacts and documentation data.
After a successful full build, a text-only edit can be previewed with:

```sh
python blueprint/scripts/build.py --reuse-docs
```

This shortcut fails if Lean or documentation inputs changed. Actions always
runs the Lean audit before assembling the site.

## Documentation build

[docbuild](../docbuild/lakefile.toml) is a separate Lake project, following the
doc-gen4 setup. Its toolchain matches the parent project; doc-gen4 and all its
dependencies are pinned by [its manifest](../docbuild/lake-manifest.json).
It shares `.lake/packages` with the parent without adding doc-gen4 to the
mathematical library's dependencies.

[Documentation.lean](../docbuild/Documentation.lean) imports every module in
[lean-imports.txt](lean-imports.txt), including the closed sticky theorem.
The generated documentation includes these modules **and their full transitive
dependencies**, together with Lean's core libraries. This scope follows the
sticky blueprint. It does not claim to compile the later general Kakeya
development or the repository's unrelated comparison targets.

Actions uses the same full build command as local development:

```sh
python blueprint/scripts/build.py
```

For debugging, its individual build steps are:

```sh
python blueprint/scripts/check.py --lean
python blueprint/scripts/docs.py prepare
lake --no-cache -d docbuild build Documentation:docs
python blueprint/scripts/docs.py check
python blueprint/scripts/build.py --reuse-docs
```

`--no-cache` here disables Lake's optional Reservoir download; the local Lake
artifacts, Mathlib cache, and Actions cache are still used. The raw doc-gen4 site
is `docbuild/.lake/build/doc/`. Publication copies it to `blueprint/site/lean/`,
shortening equivalent relative URLs and omitting optional HTML attribute quotes
to fit GitHub Pages' 1 GB limit. All module pages, declaration text, and search
data are retained. The build checks the final size before uploading.
The preparation step invalidates doc-gen4's database and generated pages when
their inputs change, preventing stale declarations from surviving a cache
restore. For unchanged Lean inputs, source buttons are refreshed to the current
commit while documentation data is reused.

When updating Lean, update both `lean-toolchain` files and the doc-gen4 revision
in `docbuild/lakefile.toml`. Then refresh the nested manifest deliberately:

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake -d docbuild update MyLeanRepo doc-gen4
```

Commit both manifests and check that shared dependency revisions agree. Ordinary
builds use the committed lock files and do not run `lake update`.

## Write a statement

Edit the chapters listed in [src/content.tex](src/content.tex). Add bibliography entries to [src/references.bib](src/references.bib). Keep mathematical notation shared between print and web in [src/macros/common.tex](src/macros/common.tex).

Brace arguments when applying an accent to a macro: write `\overline{\T}`. The unbraced form can work in LaTeX while failing after plasTeX expands it for MathJax.

A typical node looks like this:

```tex
\begin{theorem}[A descriptive name; Paper, Theorem 3.2]
\label{thm:descriptive-name}
\lean{Namespace.statement,Namespace.proof}
\leanok
\uses{def:relevant-definition}
State the hypotheses, quantifier order, and conclusion here.
\end{theorem}
\begin{proof}
\uses{lem:first-input,prop:second-input}
\leanok
Give the mathematical argument or a useful outline here.
\end{proof}
```

Each `\label` must be unique. `\uses` records mathematical dependencies; `\proves{thm:descriptive-name}` attaches a proof that appears later in the text. Use theorem labels rather than chapter labels for dependency edges.

Place `\leanok` in the statement only when its displayed formulation is faithfully represented in Lean, and in the proof only when the corresponding proof is formalized. A proposition-valued definition is a statement, not a proof. A theorem taking other proof inputs establishes an implication; its hypotheses must remain visible. When a Lean result is a normalized or restricted version of a paper theorem, state that version explicitly or leave the broader paper node unmarked. An unmarked node may still link to useful partial work.

Use a mathematical remark to explain a changed exponent, missing hypothesis, different parameter range, or altered conclusion. Distinguish an actual inconsistency from an equivalent normalization. Avoid replacing a paper statement by an implementation helper just because the helper has a convenient name.

## Verify Lean references

The committed [lean-declarations.json](lean-declarations.json) is generated from Lean, not from a regular-expression guess at namespaces. It records defining modules, source positions, declaration kinds, and transitive axioms. A hash binds it to the project Lean sources, toolchain, and dependency lock file.

To regenerate it, with the project's Lean toolchain and dependencies installed:

```sh
python blueprint/scripts/check.py --lean
```

This builds the modules in [lean-imports.txt](lean-imports.txt), resolves every
`\lean{...}` name in the compiled Lean environment, and rejects axiom dependencies
other than `propext`, `Classical.choice`, and `Quot.sound`. In particular, it
rejects `sorryAx`. When a new reference is not already exposed by those imports,
add its module to both `lean-imports.txt` and `docbuild/Documentation.lean` in
the same order. The check also verifies that these entry points and the two
projects' dependency versions agree. Commit the regenerated JSON along with
the text changes.

For text changes that preserve the linked declarations and Lean sources, the faster check is sufficient:

```sh
python blueprint/scripts/check.py
```

The audit establishes declaration existence and axiom dependencies. Comparing a mathematical statement with its Lean type still requires reading both. The manuscript's completion marks are deliberately more conservative than a list of existing declarations.

## Expert roadmap and actual Lean dependencies

The homepage opens the **proof atlas** at `blueprint/lean_dependencies.html`.
Its branch navigation, readable diagrams, unified zoomable graph and node cards
follow the expert atlas supplied in `artifacts/`. The historical
`blueprint/dep_graph_document.html` route opens the same reviewed atlas, so the
published paper-graph route does not retain unaudited solid arrows.

The two sources remain separate:

- `expert-atlas.json` is a reproducible snapshot of all 102 expert nodes, 237
  unified-graph records and ten branch views. It preserves natural-language
  statements, source locations and source hashes. Original Lean sketches,
  scripts and rendered equation SVGs are not imported. Five further connections
  occur only in the branch views; the combined atlas and audit include them too.
- `atlas-mapping.json` records each node's reviewed manuscript references,
  actual Lean versions, selected graph anchor and correspondence Remark.
  A null anchor records a grouped operation or a missing independent match;
  related declarations do not silently become a proof of that operation.
- `lean-declarations.json` and `lean-dependencies.json` are generated by Lean.
  The latter starts at `Kakeya.Assouad.PureWZ2Theorem5_2Unconditional` and
  follows stored kernel references, not source imports or the expert graph.

To replace the expert snapshot deliberately:

```sh
python blueprint/scripts/import_expert.py --html artifacts/wz2_theorem_5_2_dependency_atlas.html --tex artifacts/wz2_theorem_5_2_dependency_atlas.tex
```

The importer cross-checks every mathematical statement between the supplied
HTML and TeX. Normal builds use the committed snapshot and do not need the
untracked `artifacts` directory. Review all changed mappings after an import.
Every expert node must have exactly one mapping and a nonempty Remark.

Edit correspondence text in `atlas-mapping.json`, then regenerate the appendix:

```sh
python blueprint/scripts/atlas.py --remarks
python blueprint/scripts/check.py --lean
```

The generated `src/chapters/atlas-correspondence.tex` carries the real Lean
links into the declaration audit and records differences in the PDF and HTML
manuscript. It adds no `\leanok` marks. New modules must still be exposed by
both `lean-imports.txt` and `docbuild/Documentation.lean`. A correspondence
change that adds no new Lean links can use the lightweight check instead.

### Line styles and evidence

**Solid arrows** have nonempty witness paths in the compiled declaration
graph. Types, proof or definition bodies, private helpers, structure
projections and inductive/recursor data are distinguished at every step.
Unlinked intermediate helpers can be folded. Reachability is checked through
other displayed nodes too: a transitive use is not labelled unsupported merely
because a direct edge was removed from a diagram.

**Dashed arrows** preserve expert connections without such a path between the
selected versions in the sticky root's closure. The comparison distinguishes
an unassigned endpoint, a version outside the root, two cards sharing one Lean
declaration, and two reached declarations connected differently in the code.
For unused proofs it makes no assertion of global nondependence. The expert
edges never enter the graph used to calculate actual reachability.

The former expert categories (proof input, API, assembly and provenance) are
retained as source metadata, not as competing stroke styles. Supported expert
connections may appear as a sequence of solid edges rather than a redundant
shortcut. Every recorded connection is retained in the audit table.

The classifier uses Lean's type information to distinguish a definition of a
proposition from a proof-valued declaration. Constructors are labelled as
constructors requiring their fields, not as independent existence proofs.
Each version separately records whether the root reaches it. A proved
implication keeps its hypotheses visible; neither proof status nor reachability
certifies equivalence to the expert's natural-language formulation.

The **External** view opens the implemented multilinear, cinematic, radial,
incidence and projection inputs inside labelled frames. Their reached,
blueprint-linked implementation declarations are grouped by the reviewed
module boundaries. Shared mathematical definitions can remain in the main
argument. Lean and Mathlib are library boundaries; explicitly linked Mathlib
inputs are retained as terminal nodes with witnessed incoming references.
Group buttons bring each framed input into view at a readable scale; the
unified graph initially focuses the root theorem or the selected node.

Click an arrow for its complete source-linked witness. The separate
`blueprint/atlas-audit.html` compares all expert connections and explains every
line in every view. `blueprint/atlas-dependencies.json` contains the generated
atlas, paths and source fingerprints. The declaration-level graph remains
available at `blueprint/lean_declarations.html`, with the version table at
`blueprint/lean_dependency_audit.html`.

The extractor's non-`module` driver loads imported private bodies. Missing
referenced declarations fail the audit. The full direct graph is written to
the ignored `blueprint/build/lean-dependencies.jsonl`; committed reports retain
the displayed graph and kernel witnesses. The extractor and classifier are
fingerprinted together, and all Lean sources and dependency locks are bound
to the source digest.

These are syntactic dependencies of stored declarations. An argument or let
binding that remains in the proof term still counts. Reachability is not a
proof of minimal logical necessity. The manuscript's `\uses` and `\leanok`
annotations retain their mathematical and editorial meanings; atlas branch
colours never promote those completion marks.

## Publish with GitHub Pages

The [Blueprint workflow](../.github/workflows/blueprint.yml) builds the same
artifact on pull requests and relevant pushes to `main`, including changes to
Lean sources, toolchains, and Lake manifests. Every run compiles the blueprint
imports, audits the declarations, and builds doc-gen4 before publishing the
combined artifact. The workflow installs the tools, runs the tests and the
single full build command above, then uploads the site. Only `main` deploys.
New pushes cancel an older run on the same branch. Lean and doc-gen4 use their
default concurrency; the workflow does not override their thread counts.

The cache covers `.lake` and `docbuild/.lake`, keyed by platform, toolchain,
dependency manifests, and commit, with reuse from compatible earlier commits.
A cache hit never skips the Lean build or declaration audit. Documentation
content is additionally checked against a digest of its inputs.

To enable publication, choose **Settings → Pages → Build and deployment → Source: GitHub Actions** in the repository. Push the commit to `main` or run the **Blueprint** workflow manually. Its deployment target is <https://yu-misaka.github.io/3d-sticky-kakeya/>. The Pages setting and a successful deployment are required before that address is available.

The workflow uses pinned action revisions, a read-only build job, and a separate Pages deployment job. There is no publishing step in the local build command.
