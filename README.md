# LangevinLean

An early research project for Lean formalizations of sampling algorithms,
starting with strongly convex unadjusted Langevin (ULA) and interacting particle
Langevin (IPLA). Mathematical exposition links directly to the Lean sources.
The shared theory is organized for reuse by further methods as they are added.

Open the [documentation homepage](index.html), then follow the ULA or IPLA links.
The IPLA main page includes a clickable proof diagram and an embedded source
viewer. Relative links and bundled mathematical typesetting work after cloning;
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

- **ULA:** [proof document](UnadjustedLangevin/exposition/dist/index.html),
  [library guide](UnadjustedLangevin/README.md), and
  [canonical theorem](UnadjustedLangevin/CanonicalULA.lean).
- **IPLA:** [statement, proof diagram, and source viewer](IPLA/exposition/index.html),
  [statement and assumption correspondence](IPLA/exposition/README.md),
  [final theorem](IPLA/Theorem.lean), and
  [standalone Lean file](IPLA/Standalone.lean).
- **Proximal algorithms:** [proofs and v3 paper audit](ProximalLangevin/exposition/index.html)
  and [scope and module guide](ProximalLangevin/README.md). Corrected MYIPLA,
  PIPGLA and MYPGD actual-law bounds and corrected mean-field results are proved;
  the ledger identifies remaining results.

## Repository structure and reuse

The [ULA proof under LSI](UnadjustedLangevin/LSI/exposition/index.html) follows
[Vempala–Wibisono (2019), Theorem 2](https://proceedings.neurips.cc/paper_files/paper/2019/file/65a99bb7a3115fdede20da98b08a370f-Paper.pdf):
for $0<h\le\alpha/(4L^2)$, the KL bound is
$H_\nu(\rho_k)\le e^{-\alpha hk}H_\nu(\rho_0)+8hnL^2/\alpha$.
The Lean endpoint `ULA.LSI.ula_kl_bound_of_interpolation` is **conditional** on
explicit density, interpolation, and moment hypotheses, including
$\alpha\le L$. The guide identifies the remaining analytic work needed for a
complete proof from only the published LSI and smoothness assumptions. The
offline proof page explains every LSI declaration beside its exact Lean source
and compares the argument with the paper; the [module guide](UnadjustedLangevin/LSI/README.md)
lists the remaining obligations and build instructions.

The [IPLA entropy extension](IPLA/LSI/exposition/index.html) derives a general
particle bound from the actual lifted Gibbs target's LSI constant $\beta_N$.
When that target has the admissible constant $N\alpha$, the per-particle KL
bias is $(8\gamma L^2/\alpha)(d_x+d_\theta/N)$ and the contraction factor is
$e^{-\alpha\gamma k}$. This conclusion retains the shared interpolation
assumptions. A pair-target LSI is not substituted for the lifted-target
hypothesis, and parameter KL is controlled by the full joint entropy.

| Location | Purpose |
| --- | --- |
| [`UnadjustedLangevin/`](UnadjustedLangevin/README.md) | Reusable analysis, Gaussian and Brownian constructions, Gibbs measures and stationarity, transport estimates, and the ULA convergence theorem. |
| [`UnadjustedLangevin/Analysis/`](UnadjustedLangevin/Analysis/) | Shared smoothness estimates; convexity support is in [`StrongConvexity.lean`](UnadjustedLangevin/StrongConvexity.lean). |
| [`UnadjustedLangevin/LSI/`](UnadjustedLangevin/LSI/README.md) | KL/Fisher calculus, Gaussian interpolation laws, and conditional ULA entropy bounds under LSI. |
| [`IPLA/`](IPLA/exposition/README.md) | Lifted particle geometry, identification of IPLA with ULA, the parameter marginal and its log-concavity and concentration, and the final IPLA theorem. |
| [`IPLA/LSI/`](IPLA/LSI/README.md) | Conditional particle entropy bounds, exact normalization and parameter KL projection under a lifted-target LSI. |
| [`ProximalLangevin/`](ProximalLangevin/README.md) | Actual proximal minimizers, corrected MYIPLA/PIPGLA/MYPGD convergence, constructed mean-field limits, and a version-specific audit of arXiv:2406.14292v3. |
| [`IPLA/Standalone.lean`](IPLA/Standalone.lean) | Generated single-file version of the IPLA theorem and its dependencies, importing only Mathlib. |
| [`UnadjustedLangevin/exposition/`](UnadjustedLangevin/exposition/dist/index.html), [`IPLA/exposition/`](IPLA/exposition/index.html) | Offline exposition, source viewers, and verification reports. |

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
```

This builds all three Lean libraries, runs the five theorem dependency audits,
checks all four proof documents, and compiles the IPLA standalone in isolation
with only Mathlib available. The standalone verifier refreshes its committed
diagnostic reports; review any changes before committing.

The repository has no GitHub Actions workflow files. Keep verification local
to avoid paid hosted-runner use; do not add remote build, release, or dependency
update workflows without an explicit request.

Develop on `main`. Publish a locally verified snapshot to `gh-pages` at
`/ (root)`, retaining `noindex, nofollow, noarchive` metadata on every HTML page,
the publication's `robots.txt`, and `.nojekyll`. [index.html](index.html) is the
entry point. GitHub Pages handles serving the already generated static files;
Lean compilation and documentation generation run locally.

## Regenerate and verify documentation

Reading the committed pages needs only a browser. Regeneration needs Python 3
and Node.js; the formula typesetter is vendored, so no npm installation is needed.

```sh
python3 UnadjustedLangevin/exposition/build_document.py
python3 UnadjustedLangevin/exposition/verify_document.py
python3 IPLA/build_artifacts.py
python3 IPLA/verify.py
```

The verifiers compare embedded Lean source and theorem statements with the
repository files. The IPLA verifier also compiles the standalone file with the
project's local compiled modules excluded. Commit regenerated artifacts alongside
their sources so another machine receives matching proofs and exposition.
