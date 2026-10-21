# Langevin proof document

Open `dist/index.html` directly in a browser. It is a single self-contained file:
the mathematical typesetting, fonts, exact Lean excerpts, complete source files,
and interactions all work offline.

`index.html`, `main_theorem.html`, and `beginner_guide.html` in this directory
are shortcuts to that finished document. The editable fragments live under
`templates/` with `.html.inc` extensions; they are build inputs, not pages to
open. Running the builder also recreates the shortcuts, including their section
anchors and a visible link if automatic redirection is disabled.

The main theorem states both fully constructed Gaussian ULA bounds, with the
exact theorem headers from `CanonicalULA.lean`. The analytic argument develops
through definitions, lemmas, and the shared proof in `HilbertDalalyan.lean`.
The historical Euclidean wrappers are explained in a separate compatibility
chapter and retained in the complete-source appendix. Each proof step sits beside its source lines, and
the full declaration follows every proof, initially unfolded. On narrow screens,
each Lean box follows its mathematical step. The small toolbar switches to
mathematics only, folds repeated code, or prints the document. Step links can be
bookmarked; full modules at the end can be copied or saved.

The front of the document states the main theorem explicitly, with both
step-size regimes, its assumptions, the meaning of the error terms, and a proof
roadmap. Direct links lead to the full theorem proofs; expandable sections show
the constructed reference properties and the exact Lean theorem statements.
The shared analytic interface explicitly displays its reference argument;
the canonical endpoints discharge it and use the true initial Wasserstein
distance. These two levels are identified separately throughout the document.

The Lean notes assume no prior Lean experience. Every statement has a note
explaining its parameters and hypotheses, every proof block has explanations
of its individual source lines, and every section explains its surrounding
module context. Expanded notes span the document width for easier reading.
The beginner guide explains types, goals, `have`, `let`, `:=`, function
application, affine maps, `simp [line]`, `simpa`, and other recurring syntax.
Each note includes a local table of typing shortcuts for its Unicode symbols.
Use **Open Lean notes** to expand all notes together, or open one at a time.
The HTML keeps all explanations offline; optional reference links open the
official Lean documentation and extension abbreviation table.

Regenerate from the repository root after changing source or annotations:

```sh
python3 UnadjustedLangevin/exposition/build_document.py
python3 UnadjustedLangevin/exposition/verify_document.py
```

Building needs Python 3 and Node.js; no package installation or network access
is needed. `vendor/katex/` contains the typesetter, its license, and only the
WOFF2 fonts used in the generated file. The builder renders mathematics before
writing HTML, so malformed formulas fail the build.

`notes_analytic.json`, `notes_probability.json`, and `notes_assembly.json` hold
the mathematical statements and source ranges. The builder checks that every
declaration is present and every nonblank proof-body line is covered exactly
once, in order. The verifier compares all displayed and embedded Lean source
with the actual repository files, checks hashes and links, and rejects external
resources. Lean sources are read directly, never copied into the annotations.

Optional browser verification uses Playwright and an installed Chromium or
Google Chrome:

```sh
node UnadjustedLangevin/exposition/verify_browser.cjs
```

Set `NODE_PATH` to your Playwright package directory if it is not on Node’s
module path. This checks the reading modes, folding, step and module links,
downloads, offline fonts, and layouts from 320 to 1440 pixels.

The original multi-view teaching interface and its generated source archive
have been replaced. The existing `dist/index.html` entry path is retained.
