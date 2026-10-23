# Langevin Monte Carlo with average smoothness

[**Mistakes in the supplied manuscript and separate counterexample pages**](exposition/mistakes.html)

The reference is *Improved Guarantees for Langevin Monte Carlo with Average Smoothness*, by Arnak S. Dalalyan and Avetik Karagulyan, supplied as `papers/Average_LMC/Arxiv_version_May_26.tex`. The [proof overview](exposition/index.html) uses the repository's paired mathematics and exact Lean template. Every module has a complete proof page and downloadable LaTeX exposition.

The review scope is the three main sampling theorems, the decreasing-step proposition, the supporting SGLD proposition, and verified source mistakes. The [source audit](exposition/reference_audit.json) preserves all 12 numbered results and all 78 labels, including broader auxiliary statements whose full standalone generality is outside this scope.

## Main sampling statements

- **Theorem 1 (`th:1`):** the actual Gaussian LMC one-step bound with the exact coordinate-average smoothness and signed score correction, and its exponential constant-step convergence estimate.
- **Proposition 1 (`prop:VSS`):** the actual decreasing-step chain with the literal warmup ceiling, positive-part schedule and accuracy iteration count.
- **Theorem 2 (`th:3`):** the actual LMC bound under precisely C³ regularity and the stated gradient-of-Laplacian condition, with persistent error `(2 M_infinity sqrt(M_av) + M_Delta) h sqrt(p) / m`.
- **Theorem 3 (`th:sgld`) and Proposition 3 (`prop:th:sgld`):** the actual independent Gaussian/uniform-index control-variate SGLD law, exact estimator variance, component RMS recurrence and printed constant-step error bound.

The constants are defined from the actual potentials. The main endpoints derive their recurrences, Gibbs stationarity, Gaussian freshness, coordinate smoothing, moments and gradient-generator estimate. They introduce no Hessian Lipschitz assumption, C⁴ regularity or convexity assumption on individual SGLD components. Extended-nonnegative main bounds cover every probability initialization. The local signed-energy formula uses its finite-transport interpretation; bounded initial errors in the variable-step statement themselves provide the required finiteness.

## Separate source mistakes

- [The isotropic GLM Hessian entry in Proposition 2](exposition/counterexamples/glm-hessian.html) fails for a smooth convex quadratic-plus-sine potential at `n = p`.
- [The empirical fourth-moment event in its proof](exposition/counterexamples/glm-fourth-moment.html) fails in a direction chosen parallel to a Gaussian design row.
- [An intermediate SGLD transient comparison](exposition/counterexamples/sgld-transient.html) fails under only the immediately stated one-third step restriction.

Each page links its checked Lean certificate. The last example concerns an intermediate implication, not the main SGLD bound or its later stricter step choice. Unfinished auxiliary coverage is recorded as such, never presented as a counterexample. Literal full-paper proof coverage remains false because the source contains a false numbered proposition.

## Verification

```sh
lake build AverageLMC
lake env lean AverageLMC/Check.lean
python3 scripts/verify-average-lmc-coverage.py --require-resolved
python3 docs/build_site.py --check
python3 docs/verify_site.py
```

`--require-resolved` checks the main-theorem and counterexample review scope. The separate `--require-complete` flag rejects any false or uncovered source result. The kernel audits use only Lean's standard `propext`, `Classical.choice` and `Quot.sound` axioms; no proof holes or added axioms are permitted.

This work is for review on `main`. It does not update `gh-pages`.
