# LangevinLean

Lean formalizations of strongly convex unadjusted Langevin (ULA) and interacting
particle Langevin (IPLA), with offline mathematical exposition linked to the
Lean source. The project also includes gradient descent and a convexity tutorial.

Open the [documentation homepage](index.html), then follow the ULA or IPLA links.
The IPLA main page includes a clickable proof diagram and an embedded source
viewer. Relative links and bundled mathematical typesetting work after cloning;
no website account or documentation build is needed to read the pages.

## Clone and compile

Install Git and **elan**, Lean's toolchain manager, on the destination machine.
Use the URL of your hosted repository in place of `REPOSITORY_URL`:

```sh
git clone REPOSITORY_URL LangevinLean
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

The ULA library proves the shared sampling estimates and Gibbs stationarity.
IPLA reuses that library and adds particle geometry and parameter concentration.
The final IPLA theorem allows independent parameter and latent dimensions.

## Connect a remote repository

Create an empty repository named `LangevinLean` on your chosen Git host, without
an initial README or other files. Then run these commands in this checkout,
replacing `REPOSITORY_URL` with its SSH or HTTPS URL:

```sh
git remote add origin REPOSITORY_URL
git push -u origin main
```

You can then use the clone and pull commands above on another machine.
The repository includes a read-only GitHub Actions workflow for the Lean build,
the theorem audits, and the exposition checks. Website deployment is separate:
if you enable GitHub Pages, serve `main` at `/ (root)` to use
[index.html](index.html) as the homepage. The checked-in `.nojekyll` preserves
the static directory layout and source links.

For a transfer before choosing a host, generate a Git bundle after committing:

```sh
git bundle create LangevinLean.bundle main
```

Copy `LangevinLean.bundle` to the destination machine, then run:

```sh
git clone --branch main LangevinLean.bundle LangevinLean
cd LangevinLean
lake exe cache get
lake build
```

The bundle includes Git history, Lean sources, and exposition. It is a snapshot;
to receive future updates with `git pull`, connect the hosted remote there using
`git remote set-url origin REPOSITORY_URL`.

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

## Related developments

- **Learn Lean through convexity:** [`ConvexityTutorial/README.md`](ConvexityTutorial/README.md)
  describes a separate sequence of short optimization proofs, explained from
  the first syntax conventions onward. Open its
  [tutorial webpage](ConvexityTutorial/site/index.html).

- **Interacting particle Langevin:** [`IPLA/exposition/index.html`](IPLA/exposition/index.html)
  maps the strongly convex IPLA theorem for independent parameter and latent
  dimensions to its Lean statement and audits every assumption against U_y(θ,x).
  [`IPLA/Standalone.lean`](IPLA/Standalone.lean) compiles using only Mathlib.
  Gibbs stationarity, the canonical Brownian reference, and sharp marginal
  concentration are proved from the original potential assumptions.
- **Gradient descent:** [`GradientDescent/README.txt`](GradientDescent/README.txt)
  describes the convergence library and its existing exposition.
- **Unadjusted Langevin:** [`UnadjustedLangevin/README.md`](UnadjustedLangevin/README.md)
  describes the complete strongly convex Gaussian ULA theorem, both sharp
  step-size regimes, the actual algorithm-law identification, and its kernel
  checks.
- **Langevin proof document:** [`UnadjustedLangevin/exposition/dist/index.html`](UnadjustedLangevin/exposition/dist/index.html)
  develops the argument sequentially, with Lean beside every proof step and the
  complete declaration repeated after each proof. It opens offline as one file.

## Recorded learning direction — 14 October 2026

The ULA development is too demanding as a first Lean project: it introduces
probability, analysis, and substantial library machinery alongside the proof
language. Keep it as an advanced reference. Use the separate convexity tutorial
for learning Lean through short, rigorous optimization facts. Assume mathematical
maturity, but no knowledge of Lean; explain every code piece and syntax convention
when it first appears. Match the mathematical reasoning to the source and show
the current goal and available assumptions at each proof step.
