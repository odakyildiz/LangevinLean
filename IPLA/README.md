# Interacting particle Langevin algorithm

The library has a strongly convex transport theorem and a separate
[LSI entropy extension](LSI/exposition/index.html). The latter states a general
bound using the joint particle target's LSI constant and derives the
per-particle specialization. Its assumptions are differentiability, a Lipschitz
gradient, an LSI for that target, the stated step restriction, and finite initial
joint KL. The shared ULA theorem proves the interpolation properties used in
the argument. Its [module guide](LSI/README.md) records the assumptions.

## Strongly convex theorem

The strongly convex result is `IPLA.theorem1` in [Theorem.lean](Theorem.lean). It proves
the general-dimension extension of equation (34) of
[arXiv:2409.07101v2](https://arxiv.org/html/2409.07101v2), using its Appendix B
proof with independent parameter dimension `dθ` and latent dimension `dx`.
There is no equality, ordering, or padding requirement between the dimensions;
both may be zero. Setting `dθ = dx = d` recovers the printed equation.
The smoothness constant bounds the same potential as in Appendix B, including
a prior when one is present. Standard notation is used throughout:
`U y (pair θ x)`, with fixed observed data `y`, parameter `θ`, and latent `x`.

The only potential assumptions are differentiability, joint positive strong
convexity of `U y`, and a globally Lipschitz joint gradient. The theorem specifies
the actual independent Gaussian IPLA recursion and a square-integrable
initialization. It does not accept a reference process, Gibbs stationarity,
marginal log-concavity, a concentration estimate, or finite transport as extra
hypotheses. All of those facts are proved. The marginal maximizer exists and
is unique under the same potential assumptions.

Read the [offline exposition](exposition/index.html) or its
[statement and assumption audit](exposition/README.md). It gives the exact
mathematical statement, a coefficient-by-coefficient correspondence with Lean,
the smoothness assumptions on the source's Φ and Ψ potentials, and a list of
the proof steps and files. The
exposition includes the final declaration copied directly from the source;
the module pages give the corresponding mathematical proofs.

For the rescaled state, the dimension is `dθ + N*dx`, proved explicitly by
`IPLA.finrank_state` in [Geometry.lean](Geometry.lean). There is one shared
parameter block and `N` latent blocks. The bound has equilibrium
radius `sqrt (2*dθ/(N*m))` and discretization term
`(33/20)*(L/m)*sqrt (dx + dθ/N)*sqrt γ`. Neither coefficient replaces one
dimension by the other.

The final proof directly applies
`ULA.Hilbert.dalalyan_of_gaussian_innovations` from
[GaussianULA.lean](../UnadjustedLangevin/GaussianULA.lean) to the lifted chain.
That shared ULA module also derives finite initial transport from the
initialization and Gibbs moments. Contraction, local error, Brownian reference
construction, and Gibbs stationarity all stay in `UnadjustedLangevin`.
The distributional identity `laws_eq_ulaLawStep` transfers ULA's output-finiteness result to
the IPLA law before projection. IPLA adds the lifted geometry, algorithm
identification, exact parameter marginal, Prékopa theorem, and
parameter concentration. The small compatibility export modules contain no
separate ULA proofs.

## Compile

```sh
lake build IPLA
lake env lean IPLA/Check.lean
lake env lean IPLA/Standalone.lean
```

[Standalone.lean](Standalone.lean) contains every local definition, assumption,
and proof needed by the final theorem. It imports only Mathlib. Copy this one
file into a project with Mathlib `v4.35.0-rc3` and Lean
`leanprover/lean4:v4.35.0-rc3`, then run:

```sh
lake env lean Standalone.lean
```

The file prints the complete final theorem type and its kernel dependencies.
The permitted axiom dependencies are exactly the usual `propext`,
`Classical.choice`, and `Quot.sound`; there are no added mathematical axioms
or proof placeholders.

## Regenerate and independently check

```sh
python3 IPLA/build_artifacts.py
python3 IPLA/verify.py
```

The builder creates the standalone source and offline HTML from current
sources. The verifier checks source hashes, exact declaration correspondence,
every final theorem binder against the complete hypothesis list, the
independent dimensions and exact dimension factors, then copies only the standalone
source to a fresh folder and compiles with this project's compiled modules
removed from `LEAN_PATH`. Results are saved in
[verification.json](exposition/verification.json) and
[standalone-check.txt](exposition/standalone-check.txt).

The HTML generator uses vendored KaTeX for offline mathematical typesetting.
Python 3 and Node.js suffice; no download is needed.
