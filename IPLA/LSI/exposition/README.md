# IPLA entropy proof page

Open [index.html](index.html) for the general theorem, the per-particle
specialization, parameter-marginal consequences, and the complete proof beside
its exact Lean declarations. The source-by-source archive is [proof.html](proof.html).
These pages work offline; the archive includes every local
source dependency, formula rendering, source search, and copy/save controls.

This derivation is developed in this repository using its shared ULA entropy
theorem. There is no IPLA reference paper attached to this result. The
assumption audit identifies the actual lifted-target LSI hypothesis and the
analytic interpolation conditions retained by the formalization.

The authoring inputs are `chapters.json` and `reference_audit.json`. The shared
renderer, stylesheet, controls and verifier live in
`UnadjustedLangevin/LSI/exposition/`; these are reused rather than copied.

Regenerate and verify from the repository root:

```sh
python3 -B IPLA/LSI/exposition/build_document.py
python3 -B IPLA/LSI/exposition/verify_document.py
python3 -B docs/build_site.py
python3 -B docs/verify_site.py
```

Building requires Python 3, Node.js and the existing vendored KaTeX. No
network connection or package installation is needed. The verifier checks all
displayed and embedded source, explanation coverage, hashes, formulas, local
links and offline resources. Compile and audit the mathematics separately:

```sh
lake build UnadjustedLangevin IPLA +IPLA.LSI.Check
lake env lean IPLA/LSI/Check.lean
```
