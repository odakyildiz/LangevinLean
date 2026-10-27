# Latent diffusion

Lean development and source audit for *Training Latent Diffusion Models with
Interacting Particle Algorithms*. The [statement page](exposition/index.html)
exposes the exact assumptions; the [source audit](exposition/source_audit.md)
and [coverage ledger](exposition/reference_audit.json) distinguish proved,
conditional, corrected and unverified manuscript claims.

The main page follows the PBGSO statement/Lean layout. Part I states A1–A4,
the additional formalization domains, all 19 main and supplementary source
results, and the corrections. Every result links to a verbatim, line-numbered
view of the supplied paper. Part II separately lists **New Assumptions N1–N7**
and **New Theorems**, with their exact Lean contracts and contributions.

The finite-dimensional theory proves existence and uniqueness of the actual
heterogeneous marginal optimizer from differentiable jointly strongly convex
potentials, sharp parameter quadratic growth, and variational optimality on the
finite-KL domain. `Density.lean` proves the actual log-density integral/KL
identity from explicit normalization and entropy-integrability hypotheses.
Continuous-time free-energy, posterior-KL and parameter decay
retain explicit first-order transport and entropy-dissipation hypotheses.
These hypotheses have not been derived from the source's raw smoothness
assumptions. The literal all-initial-laws density requirement at time zero is
refuted for nonatomic reference measures. Full Wasserstein/PDE reconstruction
and the experimental neural-network assumptions are not claimed.

`SourceCalculus.lean` proves actual parameter and density-direction first
variations of the free-energy integral from explicit common-neighborhood
domination and integrability. `SourceResults.lean` proves the corrected Cauchy
minimizing-sequence argument, normalized-metric cancellation, scalar geodesic
first-order/quadratic-growth steps, tilted-density penalty/evidence identities,
and the corrected finite uniform-time estimator. These proofs do not establish
Wasserstein displacement convexity, de Bruijn integration by parts, or the
intended SDE construction. Each source card distinguishes these checked steps
from the remaining application obligations.

`LatentDiffusion.particle_oracle_parameter_bound` in `MainResults.lean`
bounds the actual parameter RMS error of the lifted pointwise Euler recursion:

$$
E_n\le(1-mh/2)^nR_0+\frac2m\sqrt{\frac VK}
+\frac Lm\left[hG+\frac43W\sqrt h\right]+\sqrt{\frac{h\sigma^2}{m}},
\qquad K=MN.
$$

The hypotheses include stable step size, heterogeneous joint convexity and
Lipschitz gradients, an integral reference with drift/noise moment bounds,
zero cross moments of finite-particle residuals, and centered orthogonal oracle
innovations. The reference and these stochastic hypotheses must be supplied
for an application. Its fixed target parameter must be identified with the
tilted optimizer to obtain an inference guarantee to that optimizer.
The printed minibatch algorithm's temperature is separately
audited and is not silently covered by this theorem.

`Accuracy.budget_le_epsilon` gives explicit particle count, step size and
logarithmic burn-in criteria allocating $\varepsilon/5$ to each of the five terms.
Interpreting these as complexity rates requires the constants to remain bounded
independently of particle count and step size. `Marginal.lean` also proves the
one-sided model-bias estimate $\sqrt{2(\delta+\varepsilon)/m}$ for approximate tilted optimizers.
“New” means new relative to the supplied manuscript, not a literature priority
claim.

Run from the repository root:

```sh
python3 docs/build_latent_diffusion.py --check
python3 docs/test_latent_diffusion_landing.py
python3 scripts/verify-latent-diffusion.py
python3 scripts/verify-latent-diffusion.py --lean
```

The default verifier checks source hashes, all 19 result environments and four
displayed assumptions, declaration mappings, absence of proof placeholders or
custom axioms, exact generated statements, and paper-before-new-theory layout.
`--lean` additionally builds the
library, checks the displayed declarations, and audits every public theorem's transitive
logical axioms. It permits only `propext`, `Classical.choice`, and `Quot.sound`.

```sh
python3 scripts/verify-latent-diffusion.py --require-source-complete
```

This last command is intentionally expected to fail while source claims retain
open analytic bridges or require corrections. Passing the ordinary verifier
certifies documentation fidelity and the stated checks, not complete recovery
of every manuscript theorem from its original assumptions.
