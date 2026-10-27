# Parallel proof documentation

The project homepage links to the theorem overviews below; the particle LSI
analogue is also linked as a footnote from IPLA:

- [ULA under Strong Convexity](../UnadjustedLangevin/exposition/index.html)
- [ULA under LSI](../UnadjustedLangevin/LSI/exposition/index.html)
- [IPLA under Strong Convexity](../IPLA/exposition/index.html)
- [Proximal algorithms](../ProximalLangevin/exposition/index.html)
- [IPLA under LSI](../IPLA/LSI/exposition/index.html)
- [Kinetic Langevin](../KineticLangevin/exposition/index.html)
- [KIPLMC](../KIPLMC/exposition/index.html)
- [PBGSO: paper theorems and new discretisation bounds](../PBGSO/exposition/index.html)
- [Latent diffusion: assumptions, results and exact Lean statements](../LatentDiffusion/exposition/index.html)

Latent diffusion has a source-derived overview and complete declaration pages,
with variational identities, marginal optimizers, particle error bounds and
explicit accuracy choices. Its continuous decay results retain explicit analytic
bridges. The [source audit](../LatentDiffusion/exposition/source_audit.md) records
remaining gaps, corrected minibatch scaling and the time-zero density obstruction.

PBGSO is a separate source-based development with all eight source results
and both new method bounds verified under explicit source interpretations. It proves the general independent-map framework, actual Brownian/Itô
integration, original local stationary product laws, primitive linear-growth
optimal law contraction across original sources, the appendix criteria and
continuous/discrete volume assertions. A2 is interpreted as an actual stationary
weak frozen SDE, not a generator-only identity. Source A1 supplies canonical
full-system strong existence and same-driver uniqueness; actual Wiener-path
transport derives the law comparison without a common-source frozen strong
solver or ambient sample-measure separability.

Both actual additive particle methods have new time-uniform square-root-step
parameter bounds for every iteration under an explicit positive small-step
threshold. Source A3 constructs their contracting empirical metric; physical
noise, Gaussian coupling, raw/L² coordinates, uniform reference moments and
local errors are derived. Constants may depend on the fixed particle count.
The numerical assumptions N1–N3 separately state global force Lipschitz
regularity, the original initial/A3/A5 data, and an actual canonical L² frozen
target trajectory. No numerical contraction or uniform moment bound is
assumed. The explicit endpoints are `FullyUniformMomentum.explicit_parameter_bound`
and `FullyUniformHigherOrder.explicit_parameter_bound`; each also has an
`explicit_discretization_bound` for the full raw state. Their metric constants
are numeric (`sqrt(lower_N)/2` and `2*sqrt(upper_N)`), and the force/cloud,
zero-origin and local-error arithmetic expansions are proved. Older
existential statements remain corollaries, and finite-horizon results remain
available. The sharp original raw particle interaction and parameter arguments use computed local Brownian
noise, genuine stopping and actual reference variance. The constant-diffusion source2 branch is also proved across arbitrary original
sources under the explicitly independent ordinary finite signed-work reading
of universal A3. The broader extended-negative-work interpretation is outside
this convention; a proved dissipative cubic/P₂ witness records the difference.
Natural independent reference clouds and the complete physical pair are
constructed. Source A4/A5 derive stationary-target comparison work without
that universal finite-work convention. Exact assumptions accompany every Lean header. The source audit
also distinguishes the verified HOL Gaussian covariance from its incorrect
exact-linear-flow claim and records the improper full-space TV prior. PBGSO
has no complete proof PDF or published-report claim.

The two kinetic developments prove convergence bounds for the continuous
kinetic equations and the discrete Gaussian samplers. Kinetic Langevin includes Gibbs stationarity, the KLMC and
Hessian-corrected KLMC2 Wasserstein bounds, and explicit accuracy guarantees.
KIPLMC includes KIPLD convergence in the original time variable, parameter
root-mean-square error bounds for both Gaussian samplers, concentration about
the maximum marginal likelihood estimator, the change of variables relating
the algorithms, and the analytic logistic example. KIPLMC1 reuses the shared exponential integrator; KIPLMC2 has
its own checked OBABO contraction and direct sampling-error proof.

The source audits preserve every statement and identify the supplied draft's
corrections. In particular, KLMC2 retains the exact $\sqrt{p^2+2p}$ moment
factor for all dimensions, uses $p\ge2$ for the printed coarser formula, and
proves the stronger inverse-step-square tail. The complete comparison includes
the stochastic Hessian-difference terms omitted from the displayed source proof.
The iteration count stated after omission of the exponential tail also needs the factor
$\sqrt{\kappa/\rho}$, with $\kappa=M/m$ and
$\rho=\kappa_2=(M_2/m^{3/2})^{2/3}+\kappa p^{-1/3}$; the printed form is
valid under $\rho\ge\kappa$, or after using $\max(\kappa,\rho)$.
The proved accuracy guarantee includes every exponential tail term; its
iteration count is stated separately from the formula obtained by dropping
that term.
The continuous equations have Brownian coordinate processes with the stated
joint laws and solutions continuous in L² on each finite time interval. A separate almost-surely continuous
sample-path modification theorem is not asserted. Empirical experiment results
remain observations, separate from the analytic guarantees.

Run `python3 scripts/verify-kinetic-coverage.py --require-complete` to require
every convergence theorem and required supporting proof. The verifier checks the declarations proving each convergence statement
and the supporting results required by that proof.

The seven established overviews state their results with all assumptions beside the exact Lean
headers, provides verification commands, and has a logical proof diagram whose
boxes open HTML proof pages. Its searchable directory includes every Lean
subfile, import module, and kernel audit in that development. The LSI extensions
have their own directories and detailed mathematical arguments. PBGSO's main
page states four main paper theorems and the two final numerical bounds as
Theorem New A and Theorem New B. Each mathematical row sits beside its exact
Lean statement, with expandable shared context. The paper’s state/gradient
notation is retained. A1–A5, added R1–R3, and numerical N1–N3 have their own
paired statements; orange marks added conditions and blue marks explicit
solution interpretations. Each theorem states which conditions it uses.
All numerical constants are expanded mathematically, including both positive
and zero position-dimension cloud constants and the proved primitive zero-force
radius. No unknown coordinate-map norm is left in the displayed bounds.
Standalone entry files contain actual assumption contexts and theorem
declarations with short checked proofs, rather than only `#check` commands.
Their Mathlib-only exports place exact readable contracts before the complete
proof appendix. Verification instructions precede a linked proof roadmap at
the end. The separate
[technical page](../PBGSO/exposition/technical.html) retains intermediate results,
the eight-result correspondence ledger, assumption inventory and declaration
directory. The LSI convergence theorems derive the Gaussian interpolation identities and
moment bounds from smoothness, the target LSI, and finite initial KL. Output
finiteness is included in the convergence conclusions.

Mathematical labels in the proof diagrams are written in LaTeX and typeset with
the same vendored KaTeX used by the statements. Typesetting is generated locally,
so diagram formulas and proof links work offline without browser-side rendering.
The downloadable IPLA SVG also embeds its mathematical fonts.

Each established-report overview, supporting module page, and archived proof document identifies
its paper references and publication status near the top. Full citations include
all authors, the title, publication venue, year, volume and pages, and paper links.
The IPLA LSI proof and corrected proximal proofs are explicitly unpublished;
the IPLA overview also identifies its unpublished independent-dimension extension.
Background papers are distinguished from sources of the displayed result.
The kinetic pages identify their published sources and the corrected proofs
checked here. The shared metadata and notice styles are authored in `references.py`.

For the established reports, `modules/` mirrors the Lean source paths. Each module page contains an authored
mathematical statement and proof beside the full corresponding Lean declarations,
links to imported proofs and users, the complete module context, and a downloadable
LaTeX exposition under `latex/`. The generated IPLA standalone bundle links to the
proof of each included source module in HTML; its LaTeX export gathers all those
mathematical statements and proofs into one document in dependency order.
The seven established theorem overviews each link to a mathematical proof report at
`pdf/<library>/FullProof.pdf`. IPLA's strongly convex and LSI treatments have
separate reports. Each report contains its theorem statements, detailed argument,
and its own supporting proofs in dependency order. Shared results are proved once
in their owning report and cited by exact section or subsection at their use sites.
The report order is ULA-SC, ULA-LSI, IPLA-SC, IPLA-LSI, Proximal, Kinetic, KIPLMC.
The corresponding complete LaTeX source is at `latex/<library>/FullProof.tex`.
Every overview and module page offers a corporate-author BibTeX citation, with
copy and download controls. Individual entries and `all-reports.bib` are generated
under `bib/`; their content revision identifies the report edition. Module pages
also identify their exact report section when the module belongs to a report.
The project homepage offers a separate project-level citation. Individual proof
boxes have no separate PDF downloads. The PDFs use ordinary mathematical
notation and paper-style exposition throughout: source paths, declaration names,
tactics and implementation commentary belong to the website's paired reading
view. The mathematical proofs retain the formal development's logical order,
including intermediate inequalities, integrability and limiting arguments.
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
the standalone theorem statements and logical diagrams; `classical_proofs.py`
contains the detailed strongly convex ULA, IPLA and proximal overview arguments.
`entropy_content.py`
contains the detailed entropy arguments and their formal scope. `kinetic_content.py`
and `kinetic_overviews.py` contain the two kinetic paper arguments, exact theorem
statements, and diagrams; their source correspondence is recorded in each
development's `exposition/reference_audit.json`. `assets/site.css` and
`assets/site.js` provide the common layout and reading controls.

`pbgso_overview.py` authors PBGSO's statement-only main page and its roadmap;
`assets/pbgso.css` supplies its assumption colours and responsive roadmap layout.
`build_pbgso.py` generates that overview, the technical catalog and complete declaration
pages under `PBGSO/exposition/`, using the shared layout and mathematical
typesetting. It reads every Lean file, shared context, theorem header and full
structure/definition contract directly into `assumption_inventory.json`.
`scripts/verify-pbgso.py` checks those exact excerpts and assumptions, source
audit coverage, local links and regeneration. PBGSO stays outside the published
PDF report catalog and its bibliography/numbering system.
`python3 scripts/verify-pbgso.py --require-complete` is the separate strict
coverage check for all eight source results, both actual method bounds and
required bridges. Its completed ledger uses the explicit SDE meaning of A2 and
ordinary finite signed-work convention for constant-diffusion source2; the
broader extended-negative interpretation is outside that correspondence.

`build_latent_diffusion.py` generates the latent-diffusion overview, complete
proof pages, verbatim line-numbered manuscript views, exact source inventory
and imported theorem checks. Its first part states all 19 paper results and
their corrections; its second part separately lists New Assumptions and New
Theorems. Each source result records its formal status. It is integrated
into `build_site.py` and its input/output manifest. Run
`python3 docs/build_latent_diffusion.py --check` to check regeneration, exact source
excerpts, complete theorem headers, local links and mathematical typesetting;
`lake env lean LatentDiffusion/exposition/statement_checks.lean` checks the displayed
results against their imported Lean proof types.
`python3 scripts/verify-latent-diffusion.py` additionally checks the source audit
and unresolved coverage statuses, and runs
`python3 docs/test_latent_diffusion_landing.py` to check all 19 source cards,
exact citations, original TeX, and separation/order of the two parts. These
checks do not certify complete source coverage.
This development stays outside
the published PDF report catalog, and its source coverage remains partial.

`AverageLMC` is contribution 09 after latent diffusion. Its paired overview,
module atlas and source audit are authored in
`average_content.py` and `AverageLMC/exposition/module_notes.json`. The
`--require-resolved` coverage gate checks the main sampling theorems; the audit
records broader auxiliary coverage separately. It does not assert literal full-paper coverage. Its
PDF report is built with the shared report catalog and cites shared proofs.

Keep each mathematical statement and proof self-contained in ordinary notation.
Use dry mathematical language: state the hypotheses, define each quantity,
and explain each inference. Include the inequalities, integrability conditions,
and limiting arguments needed to justify the conclusion. Avoid metaphors,
invented terminology, and descriptions of what a proof accomplishes in place
of the proof itself. Use the same notation throughout an argument.
Put source correspondence and implementation details in explicitly marked
`<p class="formal-note">...</p>` elements. These remain available in the paired
web view and are omitted from mathematical reading mode and LaTeX exports.
The exporter removes only marked notes; it never guesses which mathematical
sentences to discard. Equations are protected before HTML parsing, including
strict inequalities containing a literal less-than sign. The reader checks
reject source identifiers and implementation commentary in the mathematical
prose. Changing a declaration's name is never a substitute for explaining its
mathematical statement, hypotheses and proof.

Typography and colours follow odakyildiz.com: Latin Modern prose, a neutral
background, and dark-red links. The four font styles and their licenses are
bundled in `assets/fonts/`. Current pages use the shared assets; standalone
archives embed the fonts through `theme.py` so they remain readable offline.
Keep code in its monospace font and retain contrast in both light and dark
themes when changing the palette.

From the repository root, with Python 3 and Node.js on `PATH`:

```sh
python3 docs/build_site.py
python3 docs/build_pdfs.py
python3 docs/test_paper_prose.py
python3 docs/verify_exposition.py
python3 docs/verify_site.py
python3 scripts/verify-pbgso.py
```

The builder requires mathematical explanations for every native local declaration,
rejects unrecognized declaration references, and fails on malformed LaTeX formulas.
KaTeX and web fonts are vendored; building HTML requires no network or package installation.
Building PDFs additionally requires XeLaTeX (or `--engine lualatex`), the standard
TeX packages used in the exports, and `pdfinfo`. The PDF builder compiles only
the complete `FullProof.tex` documents, keeps compiler scratch files outside the repository,
and rebuilds documents when their sources change. Its manifest records source
and PDF hashes and page counts. `python3 docs/build_pdfs.py --check` checks the
committed PDFs without requiring a TeX installation.
The verifier checks the complete source inventory, hashes of authoring inputs and
outputs, every displayed source line, full declaration coverage, all local HTML
destinations and anchors, diagram destinations, and the complete PDF/LaTeX volumes.
The dependency inventory in `full_proofs.json` records each proof's unique report
owner, numbered sections, declaration-to-subsection mapping, earlier-report
dependencies, and content revision. `report_links.py` resolves authored citation
markers and indexes explicit earlier-result uses in the corresponding proofs.
`verify_report_citations.py` checks these destinations, bibliography entries,
report ownership and use-site citations; `--pdf` also checks the final PDF's named
destinations and author metadata using pypdf.
It also verifies PDF coverage and hashes against the current LaTeX sources. It checks
documentation integrity; the mathematical proof is checked by Lean:

```sh
lake build
lake env lean UnadjustedLangevin/Check.lean
lake env lean IPLA/Check.lean
lake env lean ProximalLangevin/Check.lean
lake env lean UnadjustedLangevin/LSI/Check.lean
lake env lean IPLA/LSI/Check.lean
lake env lean KineticLangevin/Check.lean
lake env lean KIPLMC/Check.lean
lake env lean PBGSO/Check.lean
lake env lean LatentDiffusion/Check.lean
lake env lean AverageLMC/Check.lean
python3 scripts/verify-average-lmc-coverage.py --require-resolved
python3 scripts/verify-kinetic-coverage.py --require-complete
```

`python3 docs/build_site.py --check` independently rerenders the entire site and
fails if any generated file is stale. `bash scripts/check-local.sh` runs these
checks locally alongside the Lean builds, axiom audits, and legacy exposition
checks. The repository contains no GitHub Actions workflows.

All generated HTML carries `noindex, nofollow, noarchive` metadata, including
module pages and archived expositions. Publication uses the existing `gh-pages`
branch with `.nojekyll`; generation and verification run locally.
The repository owner approved publication of the reviewed kinetic and KIPLMC
pages with their documented scope qualifications on 23 October 2026. The `papers/`
directory stays on `main` and must be excluded from every publication. Use
`python3 scripts/prepare-publication.py /tmp/langevin-publication-review` after
verification and committing the review snapshot. It exports committed files to
a new directory, excludes `papers/`, and never changes a branch or publishes.
Check that no files under `papers/` are tracked on `gh-pages` before any approved
publication update.

Optional browser QA, with Playwright and Chromium or Google Chrome installed:

```sh
node docs/verify_browser.cjs
node docs/verify_copy.cjs
node docs/verify_theme.cjs
```

It checks all seven overviews and representative module proofs at desktop,
375 px, and 320 px widths, reading modes, search, diagram navigation, LaTeX
downloads, old section links, and offline `file://` reading. Screenshots and a
JSON report are written to a temporary directory. Set `NODE_PATH` if Playwright
is installed outside Node's usual module search path.
The separate copy check compares clipboard payloads against the Lean sources and
checks Unicode, indentation, local files, clipboard rejection fallbacks, and
focus and selection restoration. Its clipboard stubs leave the system clipboard
untouched.

Proof diagrams use native HTML cards so equations retain their normal typesetting
on phones and tablets. Cards reflow into two columns and then one column.
A separate SVG layer draws only dependency paths and adapts when cards resize;
all labels and equations stay in HTML. On phones, numbered “Uses” links replace
the connecting paths and identify each exact prerequisite. The separate
downloadable SVG remains available.

Every page and archived exposition offers a Theme selector. System follows the
device's light/dark preference, including changes while a page is open. Light and
Dark override it and persist in local storage across pages; selecting System
restores automatic behavior. If storage is unavailable, the selector still works
for the current page. Archives embed the shared theme assets for offline use.
The theme browser check covers these behaviors, label contrast and clipping at
phone, tablet and desktop widths, local files, source dialogs, and print styling.

Open `../index.html` directly, or serve the repository root with
`python3 -m http.server 8000 --bind 127.0.0.1`. Pages, mathematics, fonts, source
excerpts, navigation, search, and reading modes all work from local files.
