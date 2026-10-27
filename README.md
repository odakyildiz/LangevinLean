# LangevinLean

Lean formalizations of unadjusted Langevin (ULA), interacting particle Langevin
(IPLA), proximal particle algorithms, kinetic Langevin, kinetic interacting
particle Langevin Monte Carlo (KIPLMC), and a general particle-based stochastic
optimisation framework (PBGSO), latent diffusion, and average-smoothness LMC. Mathematical statements and proofs are
paired with the exact Lean declarations, including every supporting subfile.
The shared theory is organized for reuse by further methods.

Open the [documentation homepage](index.html), then choose strongly convex ULA,
ULA under LSI, strongly convex IPLA, proximal algorithms, kinetic Langevin,
KIPLMC, PBGSO, latent diffusion, or average-smoothness LMC. The established overviews pair mathematical results with Lean,
verification commands, and proof diagrams linking to detailed HTML proof pages.
They have module pages and downloadable LaTeX expositions. PBGSO's main page
pairs its four main paper theorems and final discretisation bounds New A and
New B with exact Lean statements. A1–A5, added R1–R3 and numerical N1–N3 are
stated separately using the paper’s notation. The page expands all numerical
constants, colours added conditions, provides readable standalone declarations
and ends with a linked roadmap. Its separate technical catalog retains the
source-based declaration pages and exact assumption notes.
Relative links and bundled mathematical typesetting work offline after cloning;
no website account or documentation build is needed to read the pages.

## Clone and compile

Install Git and **elan**, Lean's toolchain manager, on the destination machine:

```sh
git clone https://github.com/odakyildiz/LangevinLean.git
cd LangevinLean
lake exe cache get
lake build
```

Elan reads [lean-toolchain](lean-toolchain); Lake reads the committed
[lake-manifest.json](lake-manifest.json). These pin Lean to `v4.35.0-rc3` and
Mathlib to its matching release and exact dependency commits. The first build
requires internet access to download those dependencies. The multi-gigabyte
`.lake/` directory is deliberately excluded from Git and recreated locally.

Check the theorem dependencies and compile the standalone IPLA theorem:

```sh
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
lake env lean IPLA/Standalone.lean
```

[IPLA/Standalone.lean](IPLA/Standalone.lean) contains its local definitions,
assumptions, and proofs in one file and imports only Mathlib. It can also be
compiled in another project using the same pinned Lean/Mathlib versions.

After the first clone, update on the other machine with:

```sh
git pull --ff-only
lake exe cache get
lake build
```

## Read the exposition

Open [index.html](index.html) directly in a browser, or serve the repository:

```sh
python3 -m http.server 8000 --bind 127.0.0.1
```

Then visit `http://127.0.0.1:8000/`. Serve the repository root so links from
exposition pages to `.lean` files retain their relative paths. The committed
HTML includes the offline fonts, formula rendering, and source viewers.

- **ULA under Strong Convexity:** [theorem, workflow, and proof diagram](UnadjustedLangevin/exposition/index.html),
  [library guide](UnadjustedLangevin/README.md), and
  [convergence theorem](UnadjustedLangevin/CanonicalULA.lean).
- **ULA under LSI:** [detailed mathematical argument, Lean scope, and proof diagram](UnadjustedLangevin/LSI/exposition/index.html),
  with a downloadable LaTeX proof and [source-by-source archive](UnadjustedLangevin/LSI/exposition/proof.html).
- **IPLA under Strong Convexity:** [theorem, workflow, and proof diagram](IPLA/exposition/index.html),
  [statement and assumption correspondence](IPLA/exposition/README.md),
  [final theorem](IPLA/Theorem.lean), and
  [standalone Lean file](IPLA/Standalone.lean).
  Its [LSI analogue](IPLA/LSI/exposition/index.html) has a separate full page,
  linked as a footnote from the IPLA theorem page.
- **Proximal algorithms:** [three main bounds, workflow, and proof diagram](ProximalLangevin/exposition/index.html),
  [detailed proofs and v3 paper audit](ProximalLangevin/exposition/proof.html),
  and [scope and module guide](ProximalLangevin/README.md). Corrected MYIPLA,
  PIPGLA and MYPGD distributional bounds and corrected mean-field results are proved;
  the ledger identifies remaining results.
- **Kinetic Langevin:** [continuous mixing, KLMC, and KLMC2 proofs](KineticLangevin/exposition/index.html),
  including the distributions of Brownian integral solutions, Gibbs stationarity,
  correlated Gaussian samplers, and both unconditional Wasserstein bounds.
  The [source coverage audit](KineticLangevin/exposition/reference_audit.json)
  records every source result and the corrections required by the supplied draft.
- **KIPLMC:** [diffusion, both particle sampler bounds, and concentration](KIPLMC/exposition/index.html).
  KIPLMC1 calls the shared kinetic exponential integrator; KIPLMC2 calls the
  shared OBABO composition. Parameter root-mean-square error bounds for the Gaussian chains,
  exact changes of time variable, concentration about the maximum marginal
  likelihood estimator, and explicit iteration counts for a specified accuracy
  are proved. The [source coverage audit](KIPLMC/exposition/reference_audit.json)
  distinguishes the analytic statements from the empirical experiments.
- **Latent diffusion:** [assumptions, mathematical results and exact Lean statements](LatentDiffusion/exposition/index.html),
  with [source coverage, added regularity and corrections](LatentDiffusion/exposition/source_audit.md).
  The development proves variational identities, marginal optimizer results,
  interacting-particle error estimates and explicit accuracy choices. Continuous
  decay retains explicit analytic bridges; the audit records corrected minibatch
  scaling and the obstruction to universal density regularity at time zero.
  Incomplete source-proof statuses and remaining analytic obligations are explicit.
- **Average smoothness LMC (contribution 09):** [sampling proofs](AverageLMC/exposition/index.html),
  following latent diffusion on the homepage. LMC, decreasing-step, Laplacian LMC
  and control-variate SGLD bounds retain the source hypotheses and constants.
  [Separate counterexample pages](AverageLMC/exposition/mistakes.html) record
  verified manuscript mistakes; the [source audit](AverageLMC/exposition/reference_audit.json)
  distinguishes this review scope from broader auxiliary coverage.
- **PBGSO:** [general framework, assumptions and exact theorem statements](PBGSO/exposition/index.html),
  [scope and module guide](PBGSO/README.md), and
  [audit of all eight numbered source results](PBGSO/exposition/source_audit.md).
  The general independent-map optimiser/sampler framework, all eight source
  results and new actual M-MFPO/HOL-MYPGD time-uniform bounds are proved under
  explicit assumptions. Actual Brownian integration, local stopping,
  original stationary product laws, optimal-law contraction and sharp original
  particle/parameter bounds are verified. Both methods construct their raw/L²
  coordinates, physical Gaussian noise, exact restarts and uniform reference
  moments. The discretisation term is D*sqrt(h) for every iteration under an
  explicit positive small-step threshold, with constants allowed to depend
  on fixed N. The explicit headline endpoints are
  `FullyUniformMomentum.explicit_parameter_bound` and
  `FullyUniformHigherOrder.explicit_parameter_bound`; each also certifies the
  full raw-state error through `explicit_discretization_bound`. The proved metric
  comparison constants are `sqrt(lower_N)/2` and `2*sqrt(upper_N)`,
  and cloud dimensions, force origins and local coefficients have proved
  arithmetic expansions. No numerical contraction or uniform moment bound is
  assumed. Older existential endpoints remain corollaries. Source A2 means
  actual stationary weak frozen SDE invariance;
  constant-diffusion source2 uses the independent ordinary finite signed-work
  reading of universal A3. The broader extended-negative-work interpretation
  is outside that convention. Original interacting-solution existence and
  synchronous initialization remain explicit for general particle bounds.
  The page records these assumptions, critical-point rather than minimizer
  targets, smoothing bias, the improper full-space TV prior and the printed
  HOL coefficient defect. `python3 scripts/verify-pbgso.py` checks documentation
  fidelity; `python3 scripts/verify-pbgso.py --require-complete` also checks all
  eight source results, both method bounds and required bridges under the
  audit file’s stated source interpretations. The readable
  [New A](standalone/PBGSO/NewA.lean), [New B](standalone/PBGSO/NewB.lean) and
  [paper theorem](standalone/PBGSO/PaperTheorems.lean) entries state complete
  assumptions and conclusions with short checked proofs.
  `python3 scripts/check-pbgso-standalone.py --output /tmp/pbgso-standalone --check`
  exports each complete Mathlib-only proof closure with the readable contracts
  first, then compiles it with this project’s compiled modules excluded.

The two kinetic developments prove convergence of the continuous processes
and the Gaussian samplers under the displayed assumptions. The supplied Dalalyan–Riou-Durand draft needs explicit corrections:
the unshifted continuous prefactor is $\sqrt{2}$; the second-order local proof
uses a stationary reference; and the comparison must retain fresh stochastic
Hessian-difference terms. KLMC2 retains $\sqrt{p^2+2p}$ in every dimension,
including $p=1$; the printed coarser simplification is checked with $p\ge2$
stated explicitly. The sharper inverse-step-square tail is also proved.
The audits preserve the source statements and explain these differences.
The draft's iteration count obtained by omitting the exponential tail needs a factor
$\sqrt{\kappa/\rho}$, where $\kappa=M/m$ and
$\rho=\kappa_2=(M_2/m^{3/2})^{2/3}+\kappa p^{-1/3}$; its printed form is
justified when $\rho\ge\kappa$, or with $\rho$ replaced by
$\max(\kappa,\rho)$. The proved accuracy guarantee retains the exponential tail and states its
iteration count separately.

The continuous equations have solutions continuous in L² on each finite time
interval, driven by Brownian coordinate processes with the stated joint laws.
The proof establishes their integral equations, independence properties,
distributions at fixed times, and stationarity.
A separate almost-surely continuous sample-path modification theorem is not
asserted. The numerical convergence bounds use the actual Gaussian Markov laws.

Verify the source correspondence and the presence of each convergence theorem
and its supporting results with:

```sh
python3 scripts/verify-kinetic-coverage.py
python3 scripts/verify-kinetic-coverage.py --require-complete
```

The strict command rejects a missing convergence theorem or supporting result.
It checks the declarations proving the distributional conclusions.

## Repository structure and reuse

The [ULA proof under LSI](UnadjustedLangevin/LSI/exposition/index.html) follows
[Vempala–Wibisono (2019), Theorem 2](https://proceedings.neurips.cc/paper_files/paper/2019/file/65a99bb7a3115fdede20da98b08a370f-Paper.pdf):
for $0<h\le\alpha/(4L^2)$, the KL bound is
$H_\nu(\rho_k)\le e^{-\alpha hk}H_\nu(\rho_0)+8hnL^2/\alpha$.
The theorem `ULA.LSI.ula_kl_bound` in
[UnconditionalTheorem.lean](UnadjustedLangevin/LSI/UnconditionalTheorem.lean)
proves this bound from differentiability, Lipschitz gradient, LSI, the step
restriction, and finite initial KL. Its conclusion includes finite KL at every
Gaussian ULA iterate. The proof derives $\alpha\le L$, bounds the gradient
second moment by the initial entropy, constructs the density at positive
times, and proves its weak equation and entropy derivative. A bound on
entropy at small positive times gives the initial value for integration. The
gradient estimate follows from an exponential moment and the entropy
variational inequality. The offline pages and downloadable
LaTeX explain these arguments beside their exact Lean declarations.

The [IPLA entropy extension](IPLA/LSI/exposition/index.html) derives a general
particle bound from the actual lifted Gibbs target's LSI constant $\beta_N$.
When that target has the admissible constant $N\alpha$, the per-particle KL
bias is $(8\gamma L^2/\alpha)(d_x+d_\theta/N)$ and the contraction factor is
$e^{-\alpha\gamma k}$. The theorem for finite initial KL derives the required interpolation estimates. A pair-target LSI is not substituted for the lifted-target
hypothesis, and parameter KL is controlled by the full joint entropy.

| Location | Purpose |
| --- | --- |
| [`UnadjustedLangevin/`](UnadjustedLangevin/README.md) | Reusable analysis, Gaussian and Brownian constructions, Gibbs measures and stationarity, transport estimates, and the ULA convergence theorem. |
| [`UnadjustedLangevin/Analysis/`](UnadjustedLangevin/Analysis/) | Shared smoothness estimates; convexity support is in [`StrongConvexity.lean`](UnadjustedLangevin/StrongConvexity.lean). |
| [`UnadjustedLangevin/LSI/`](UnadjustedLangevin/LSI/README.md) | KL/Fisher calculus, Gaussian interpolation laws, and the full ULA entropy theorem under LSI. |
| [`IPLA/`](IPLA/exposition/README.md) | Lifted particle geometry, identification of IPLA with ULA, the parameter marginal and its log-concavity and concentration, and the final IPLA theorem. |
| [`IPLA/LSI/`](IPLA/LSI/README.md) | Particle entropy bounds from finite initial KL, exact normalization and parameter KL projection under a lifted-target LSI. |
| [`ProximalLangevin/`](ProximalLangevin/README.md) | Proximal minimizers, corrected MYIPLA/PIPGLA/MYPGD convergence, constructed mean-field limits, and a version-specific audit of arXiv:2406.14292v3. |
| [`KineticLangevin/`](KineticLangevin/exposition/README.md) | Kinetic convergence and Gibbs stationarity, Cholesky Gaussian sampling, KLMC/KLMC2 Wasserstein bounds, iteration counts for a specified accuracy, and comparison with the source paper. |
| [`KIPLMC/`](KIPLMC/exposition/README.md) | KIPLD convergence, KIPLMC1/KIPLMC2 parameter root-mean-square error bounds, changes of variables for the diffusion and algorithms, target concentration, and the analytic logistic example. |
| [`LatentDiffusion/`](LatentDiffusion/exposition/index.html) | All 19 corrected source results under explicit added regularity: actual density/KL identities, product transport and entropy calculus, classical-flow convergence, constructed mean-field and particle equations, and full-batch RMS error; separate new theory and accuracy choices. |
| [`PBGSO/`](PBGSO/README.md) | General optimiser/sampler framework, actual predictable Brownian integration and continuous adapted modifications, stationary product laws and optimal law contraction, source appendix criteria and fully constructed additive particle numerical bounds; original raw stationarity via actual Wiener-path transfer and primitive linear-growth optimal law contraction across sources; constant-diffusion contraction uses the explicit ordinary finite signed-work A3 convention; actual independent reference clouds and physical particle/reference pairing are constructed. |
| [`AverageLMC/`](AverageLMC/README.md) | Average-smoothness LMC, decreasing-step, Laplacian LMC and control-variate SGLD proofs, with separate checked manuscript counterexamples. |
| `papers/` | Reference manuscripts retained on `main`; excluded from all publication exports and from `gh-pages`. |
| [`IPLA/Standalone.lean`](IPLA/Standalone.lean) | Generated single-file version of the IPLA theorem and its dependencies, importing only Mathlib. |
| [`UnadjustedLangevin/exposition/`](UnadjustedLangevin/exposition/index.html), [`IPLA/exposition/`](IPLA/exposition/index.html), [`ProximalLangevin/exposition/`](ProximalLangevin/exposition/index.html) | Standard overviews, theorem statements, verification commands, and linked proof diagrams. |
| [`docs/`](docs/README.md) | Module statements and proofs, mathematical LaTeX exports, shared renderer, and documentation integrity checks. |

The dependency runs from IPLA to `UnadjustedLangevin`; the ULA library has no
IPLA imports. IPLA applies the existing ULA estimate to its lifted potential,
then uses the parameter projection and concentration bound. The particle state
has dimension `dθ + N * dx`, with independent parameter and latent dimensions.

Future sampling methods can have their own top-level library and exposition,
importing the shared ULA analysis and probability modules as needed. Keep each
method's geometry, algorithm identification, and method-specific estimates in
that method's directory; extend the common layer when a result is useful to
more than one method. Add the library to [lakefile.toml](lakefile.toml), its
theorem audits, and a link from the documentation homepage.

## Local checks and publication

Run all proof and exposition checks locally before pushing or publishing:

```sh
bash scripts/check-local.sh
python3 scripts/verify-kinetic-coverage.py --require-complete
```

This builds all six Lean libraries, runs the eight theorem dependency audits,
checks all four proof documents and the complete module proof atlas, and compiles
the IPLA standalone in isolation with only Mathlib available. The standalone verifier refreshes its committed
diagnostic reports; review any changes before committing.

The repository has no GitHub Actions workflow files. Keep verification local
to avoid paid hosted-runner use; do not add remote build, release, or dependency
update workflows without an explicit request.

Develop and review on `main`. The repository owner approved publication of the
reviewed kinetic Langevin and KIPLMC pages with their documented scope
qualifications on 23 October 2026. Publish locally verified snapshots to `gh-pages` at
`/ (root)`, retaining `noindex, nofollow, noarchive` metadata on every HTML page,
the publication's `robots.txt`, and `.nojekyll`. [index.html](index.html) is the
entry point. GitHub Pages handles serving the already generated static files;
Lean compilation and documentation generation run locally.

Do not publish `papers/` or merge `main` wholesale into `gh-pages`. After local
verification and a committed review snapshot, a publication export can be
prepared in a new directory outside the checkout:

```sh
python3 scripts/prepare-publication.py /tmp/langevin-publication-review
```

This exports committed files with `papers/` excluded. It never changes a branch
or publishes a site. Publication retains the documented initialization, dimension,
continuous-model, and full-paper coverage qualifications.

## Regenerate and verify documentation

Reading the committed pages needs only a browser. Regeneration needs Python 3
and Node.js; the formula typesetter is vendored, so no npm installation is needed.

```sh
python3 docs/build_site.py
python3 docs/verify_site.py
```

The hand-authored `exposition/module_notes.json` files explain every native
declaration and probability instance. The common builder rejects missing
modules, missing explanations, and malformed formulas. The verifier compares
all excerpts against Lean, checks source/input/output hashes, validates local
HTML links and diagram destinations, and checks every LaTeX export. See the
[documentation guide](docs/README.md) for the file structure and reading controls.

To regenerate the extended teaching documents, reference audits, and standalone
IPLA artifact as well:

```sh
python3 UnadjustedLangevin/exposition/build_document.py
python3 UnadjustedLangevin/exposition/verify_document.py
python3 IPLA/build_artifacts.py
python3 IPLA/verify.py
python3 ProximalLangevin/exposition/build_document.py
python3 ProximalLangevin/exposition/verify_document.py
python3 UnadjustedLangevin/LSI/exposition/build_document.py
python3 UnadjustedLangevin/LSI/exposition/verify_document.py
python3 IPLA/LSI/exposition/build_document.py
python3 IPLA/LSI/exposition/verify_document.py
python3 docs/build_site.py
python3 docs/verify_site.py
```

The verifiers compare embedded Lean source and theorem statements with the
repository files. The IPLA verifier also compiles the standalone file with the
project's local compiled modules excluded. Commit regenerated artifacts alongside
their sources so another machine receives matching proofs and exposition.
