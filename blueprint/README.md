# Sticky Kakeya blueprint

The blueprint follows the proof through Wang–Zahl's finite sticky estimate, Theorem 5.2 of *The Assouad dimension of Kakeya sets in ℝ³*. It includes the structural argument from *Sticky Kakeya sets and the sticky Kakeya conjecture* and the supporting projection, Furstenberg, cinematic, multilinear, and hairbrush estimates. The later general Kakeya and Assouad reductions are outside its scope.

The mathematical text is in English. [The correspondence chapter](src/chapters/correspondence.tex) identifies the manuscript versions and numbering. Remarks next to the relevant results distinguish corrections, normalizations, weaker interfaces, and propositions whose general paper formulation is not marked as fully proved. The downloaded papers themselves are not included in the repository.

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

The usual leanblueprint route `lean/find/#doc/Namespace.declaration` is handled
by doc-gen4 itself and opens the declaration's documentation page. Its source
button links to the corresponding GitHub source. The previous custom
source-only resolver has been removed.

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
