# IPLA entropy proof pages

Open [index.html](index.html) for the standalone lifted-target LSI theorem,
the per-particle specialization, parameter-marginal consequence, and detailed
mathematics beside Lean. The [source archive](proof.html) includes every local
dependency and retains the older interpolation-data interfaces as reusable
lemmas. The main normalized entropy theorem is
`particle_kl_bound_linear_lsi_of_finite_kl` in `IPLA/LSI/UnconditionalTheorem.lean`.

The theorem assumes differentiability, a Lipschitz gradient, an LSI for the
normalized joint particle Gibbs measure, the stated positive step restriction, and finite
initial joint KL. Density construction, entropy differentiation, the bound at the initial
time, gradient moments, and the inequality between LSI and smoothness constants are proved in the shared ULA
argument. A pair-target LSI is not substituted for the lifted-target premise.

These pages work offline. Their authoring inputs are `chapters.json` and
`reference_audit.json`; the common renderer, stylesheet, controls, and verifier
live in `UnadjustedLangevin/LSI/exposition/`.

Regenerate and verify locally from the repository root:

```sh
python3 -B IPLA/LSI/exposition/build_document.py
python3 -B IPLA/LSI/exposition/verify_document.py
python3 -B docs/build_site.py
python3 -B docs/verify_site.py
```

Building requires Python 3, Node.js, and the existing vendored KaTeX. No
network connection or package installation is needed for page generation.
The verifier checks exact displayed and embedded source, explanation
coverage, hashes, formulas, local links, and offline resources. Compile and
audit the mathematics separately:

```sh
lake build UnadjustedLangevin IPLA +IPLA.LSI.Check
lake env lean IPLA/LSI/Check.lean
```

No GitHub workflow or hosted runner is used by this process.
