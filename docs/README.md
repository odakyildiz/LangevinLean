# Parallel proof documentation

The project homepage links to four theorem overviews, with the particle LSI
analogue linked as a footnote from IPLA:

- [ULA under Strong Convexity](../UnadjustedLangevin/exposition/index.html)
- [ULA under LSI](../UnadjustedLangevin/LSI/exposition/index.html)
- [IPLA under Strong Convexity](../IPLA/exposition/index.html)
- [Proximal algorithms](../ProximalLangevin/exposition/index.html)
- [IPLA under LSI](../IPLA/LSI/exposition/index.html)

Every overview states its results with all assumptions beside the exact Lean
headers, provides verification commands, and has a logical proof diagram whose
boxes open HTML proof pages. Its searchable directory includes every Lean
subfile, import module, and kernel audit in that development. The LSI extensions
have their own directories and detailed mathematical arguments. Their complete Lean endpoints derive the Gaussian interpolation calculus and
moment bounds from smoothness, the target LSI, and finite initial KL. Output
finiteness is included in the convergence conclusions.

Mathematical labels in the proof diagrams are written in LaTeX and typeset with
the same vendored KaTeX used by the statements. Typesetting is generated locally,
so diagram formulas and proof links work offline without browser-side rendering.
The downloadable IPLA SVG also embeds its mathematical fonts.

Every overview, supporting module page, and archived proof document identifies
its paper references and publication status near the top. Full citations include
all authors, the title, publication venue, year, volume and pages, and paper links.
The IPLA LSI proof and corrected proximal proofs are explicitly unpublished;
the IPLA overview also identifies its unpublished independent-dimension extension.
Background papers are distinguished from sources of the displayed result.
The shared metadata and notice styles are authored in `references.py`.

`modules/` mirrors the Lean source paths. Each module page contains an authored
mathematical statement and proof beside the full corresponding Lean declarations,
links to imported proofs and users, the complete module context, and a downloadable
LaTeX exposition under `latex/`. The generated IPLA standalone bundle links to the
proof of each included source module in HTML; its LaTeX export gathers all those
mathematical statements and proofs into one document in dependency order.
LaTeX exports use `fontspec` and can be compiled with XeLaTeX or LuaLaTeX.

Each Lean statement, proof excerpt, and full-module block has a **Copy Lean**
button. It copies the displayed source as plain text, preserving indentation and
Unicode while excluding line numbers. Copy controls also work when reading local
files, with a selection-based fallback if the browser denies Clipboard API access.

The original long teaching documents and paper audits remain available from
“Further reading”: ULA at `UnadjustedLangevin/exposition/dist/index.html`, IPLA at
`IPLA/exposition/proof.html`, and proximal algorithms at
`ProximalLangevin/exposition/proof.html`. Their existing deep links remain useful.
The LSI source-by-source archives are now `LSI/exposition/proof.html` within ULA
and IPLA. Old section anchors are redirected from their overview automatically.

## Edit and regenerate

The authored module statements and proofs live in each library's
`exposition/module_notes.json`. Each step names the local declarations it explains;
Lean code is read from the source at generation time. `site_content.py` contains
the standalone theorem statements and logical diagrams; `entropy_content.py`
contains the detailed entropy arguments and their formal scope. `assets/site.css` and
`assets/site.js` provide the common layout and reading controls.

From the repository root, with Python 3 and Node.js on `PATH`:

```sh
python3 docs/build_site.py
python3 docs/verify_site.py
```

The builder requires mathematical explanations for every native local declaration,
rejects unrecognized declaration references, and fails on malformed LaTeX formulas.
KaTeX and fonts are vendored; no network or package installation is required.
The verifier checks the complete source inventory, hashes of authoring inputs and
outputs, every displayed source line, full declaration coverage, all local HTML
destinations and anchors, diagram destinations, and LaTeX exports. It checks
documentation integrity; the mathematical proof is checked by Lean:

```sh
lake build
lake env lean UnadjustedLangevin/Check.lean
lake env lean IPLA/Check.lean
lake env lean ProximalLangevin/Check.lean
lake env lean UnadjustedLangevin/LSI/Check.lean
lake env lean IPLA/LSI/Check.lean
```

`python3 docs/build_site.py --check` independently rerenders the entire site and
fails if any generated file is stale. `bash scripts/check-local.sh` runs these
checks locally alongside the Lean builds, axiom audits, and legacy exposition
checks. The repository contains no GitHub Actions workflows.

All generated HTML carries `noindex, nofollow, noarchive` metadata, including
module pages and archived expositions. Publication uses the existing `gh-pages`
branch with `.nojekyll`; generation and verification run locally.

Optional browser QA, with Playwright and Chromium or Google Chrome installed:

```sh
node docs/verify_browser.cjs
node docs/verify_copy.cjs
```

It checks all five overviews and representative module proofs at desktop,
375 px, and 320 px widths, reading modes, search, diagram navigation, LaTeX
downloads, old section links, and offline `file://` reading. Screenshots and a
JSON report are written to a temporary directory. Set `NODE_PATH` if Playwright
is installed outside Node's usual module search path.
The separate copy check compares clipboard payloads against the Lean sources and
checks Unicode, indentation, local files, clipboard rejection fallbacks, and
focus and selection restoration. Its clipboard stubs leave the system clipboard
untouched.

Open `../index.html` directly, or serve the repository root with
`python3 -m http.server 8000 --bind 127.0.0.1`. Pages, mathematics, fonts, source
excerpts, navigation, search, and reading modes all work from local files.
