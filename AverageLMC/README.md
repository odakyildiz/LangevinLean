# Langevin Monte Carlo with average smoothness

**Incomplete formalization. The exact full-paper request cannot be completed:
the supplied Gaussian design proposition is false.**

The authoritative source is
`papers/Average_LMC/Arxiv_version_May_26.tex`, titled *Improved Guarantees for
Langevin Monte Carlo with Average Smoothness*, by Arnak S. Dalalyan and Avetik
Karagulyan. The [standard proof overview](exposition/index.html) pairs the
checked results with exact Lean statements, module proofs, and LaTeX exports.
The [source audit](exposition/reference_audit.json) preserves the manuscript's
statements and records their individual status.

## Obstruction to the exact printed proposition

In Proposition 2 (`prop:glm-constants`), take `n = p`, identity covariance,
`g₁(t) = t² − sin(t)` and `gᵢ(t) = t²` for `i > 1`. All components are convex,
infinitely differentiable, and satisfy `|gᵢ''| + |gᵢ'''| ≤ 4`. The resulting
potential is

$$f(\theta)=\sum_{i=1}^p(X_i^\top\theta)^2-\sin(X_1^\top\theta).$$

The Hessian's derivative at zero in direction `X₁ / ‖X₁‖` implies
`M₂ ≥ ‖X₁‖³`. For a standard Gaussian vector `Z` in dimension `p`, its squared
norm has mean `p` and variance `2p`. Chebyshev gives
`Pr(‖Z‖² < p/2) ≤ 8/p`. Thus, for any constant `C ≥ 0`, if `p > 16` and
`p > 8C²`, then

$$\Pr(\|Z\|^3\le Cp)<\frac12.$$

The table requires `M₂√p ≤ Cn√p`, equivalently `M₂ ≤ Cp` in this setting,
with `C` depending only on the fixed derivative bound `C_g = 4`.
Its asserted probability of at least one half is impossible uniformly in
dimension. This is a counterexample to a numbered proposition, rather than
only an error in its proof. It does not disprove the sampler convergence
theorems. The exact Lean scope of the counterexample is documented in the
module pages and audit.

## Checked components

- Exact coordinate Taylor supremum and global gradient seminorm definitions,
  their comparisons, and the actual Hessian, Laplacian and C³ trace condition.
- The gradient-step lemma and deterministic smooth-descent inequality under
  the paper's differentiability, strong convexity and gradient smoothness
  assumptions.
- Conditional scalar constant-step and variable-step bounds, including the
  exact ceiling warmup and iteration envelope of Proposition 1. Their
  stochastic recurrence is an explicit premise, and remains unproved for
  actual LMC laws.
- The GLM obstruction and the actual Gaussian probability estimates described
  above, using the existing exact fourth-moment theorem.

No new actual-law LMC, Laplacian-smooth LMC, SGLD, or GLM upper-bound endpoint
is claimed. There are no proof holes or new axioms in these modules.

## Verification

```sh
lake build AverageLMC
lake env lean AverageLMC/Check.lean
python3 scripts/verify-average-lmc-coverage.py
python3 docs/build_site.py --check
python3 docs/verify_site.py
```

The following completion gate deliberately fails while required endpoints
remain unproved or a source statement is refuted:

```sh
python3 scripts/verify-average-lmc-coverage.py --require-complete
```

Passing the ordinary integrity checks does not certify full-paper coverage.
This work is for review on `main`; it does not publish or update `gh-pages`.
