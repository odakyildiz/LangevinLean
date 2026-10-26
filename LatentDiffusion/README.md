# Latent diffusion

Lean development and source audit for *Training Latent Diffusion Models with
Interacting Particle Algorithms*. The [statement page](exposition/index.html)
exposes the exact assumptions; the [source audit](exposition/source_audit.md)
and [coverage ledger](exposition/reference_audit.json) distinguish proved,
conditional, corrected and unverified manuscript claims.

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

`LatentDiffusion.particle_oracle_parameter_bound` in `MainResults.lean`
bounds the actual parameter RMS error of the lifted pointwise Euler recursion:

```text
E_n ≤ (1 − mh/2)^n R0 + (2/m) √(V/K)
      + (L/m) [hG + (4/3) W √h] + √(h σ²/m),    K = M N.
```

The hypotheses include stable step size, heterogeneous joint convexity and
Lipschitz gradients, an integral reference with drift/noise moment bounds,
zero cross moments of finite-particle residuals, and centered orthogonal oracle
innovations. The reference and these stochastic hypotheses must be supplied
for an application. The printed minibatch algorithm's temperature is separately
audited and is not silently covered by this theorem.

`Accuracy.budget_le_epsilon` gives explicit particle count, step size and
logarithmic burn-in criteria allocating ε/5 to each of the five terms.
Interpreting these as complexity rates requires the constants to remain bounded
independently of particle count and step size. `Marginal.lean` also proves the
one-sided model-bias estimate √(2(δ+ε)/m) for approximate tilted optimizers.
“New” means new relative to the supplied manuscript, not a literature priority
claim.

Run from the repository root:

```sh
python3 docs/build_latent_diffusion.py --check
python3 scripts/verify-latent-diffusion.py
python3 scripts/verify-latent-diffusion.py --lean
```

The default verifier checks source hashes, all 19 result environments and four
displayed assumptions, declaration mappings, absence of proof placeholders or
custom axioms, and exact generated statements. `--lean` additionally builds the
library, checks the displayed declarations, and audits every public theorem's transitive
logical axioms. It permits only `propext`, `Classical.choice`, and `Quot.sound`.

```sh
python3 scripts/verify-latent-diffusion.py --require-source-complete
```

This last command is intentionally expected to fail while source claims retain
open analytic bridges or require corrections. Passing the ordinary verifier
certifies documentation fidelity and the stated checks, not complete recovery
of every manuscript theorem from its original assumptions.
