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

From the repository root, using Python 3.12:

```sh
python3 -m venv .venv-blueprint
source .venv-blueprint/bin/activate
python -m pip install -r blueprint/requirements.txt
python blueprint/scripts/build.py
python -m http.server 8000 --directory blueprint/site
```

Open <http://localhost:8000>. The complete site contains the HTML manuscript, interactive dependency graph, PDF, and source declaration index. MathJax loads from a CDN. The PDF is also available directly at `blueprint/print/print.pdf`.

The build runs `leanblueprint pdf` before `leanblueprint web`, so that both editions use the same bibliography. It checks labels, citations, graph dependencies, the audited source references, PDF margins, and the site's local links. Build logs and a statement inventory are kept under `blueprint/build/`. Generated output is ignored by Git.

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

This builds the modules in [lean-imports.txt](lean-imports.txt), resolves every `\lean{...}` name in the compiled Lean environment, and rejects axiom dependencies other than `propext`, `Classical.choice`, and `Quot.sound`. In particular, it rejects `sorryAx`. When a new reference is not already exposed by those imports, add its module to `lean-imports.txt` first. Commit the regenerated JSON along with the text changes.

For text changes that preserve the linked declarations and Lean sources, the faster check is sufficient:

```sh
python blueprint/scripts/check.py
```

The audit establishes declaration existence and axiom dependencies. Comparing a mathematical statement with its Lean type still requires reading both. The manuscript's completion marks are deliberately more conservative than a list of existing declarations.

Source links use the usual leanblueprint route `lean/find/#doc/Namespace.declaration`. The small resolver sends readers to the precise GitHub source line at the site build's commit. This supplies working declaration links without generating documentation for the entire imported library.

## Publish with GitHub Pages

The [Blueprint workflow](../.github/workflows/blueprint.yml) builds the same artifact on pull requests and on relevant pushes to `main`. Only `main` deploys. It checks the committed Lean audit without rebuilding the large Lean project in every documentation job. If Lean sources have changed, regenerate the audit locally first.

To enable publication, choose **Settings → Pages → Build and deployment → Source: GitHub Actions** in the repository. Push the commit to `main` or run the **Blueprint** workflow manually. Its deployment target is <https://yu-misaka.github.io/3d-sticky-kakeya/>. The Pages setting and a successful deployment are required before that address is available.

The workflow uses pinned action revisions, a read-only build job, and a separate Pages deployment job. There is no publishing step in the local build command.
