# Strongly convex interacting particle Langevin algorithm

The main result is `IPLA.theorem1` in [Theorem.lean](Theorem.lean). It proves
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
the source's Φ/Ψ smoothness issue, and a file-level proof roadmap. The
exposition includes the final declaration copied directly from the source;
it does not reproduce the proof.

For the rescaled state, the dimension is `dθ + N*dx`. The bound has equilibrium
radius `sqrt (2*dθ/(N*m))` and discretization term
`(33/20)*(L/m)*sqrt (dx + dθ/N)*sqrt γ`. Neither coefficient replaces one
dimension by the other.

The analytic ULA argument is reused from `UnadjustedLangevin`, including
contraction, local error, finite transport, Brownian reference construction,
and the now-proved Gibbs stationarity theorem. IPLA adds the lifted geometry,
algorithm law identification, the exact parameter marginal, the proved
Prékopa theorem, and sharp parameter concentration.

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
