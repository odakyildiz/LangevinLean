# Langevin Monte Carlo with average smoothness

The reference is *Improved Guarantees for Langevin Monte Carlo with Average Smoothness*, by Arnak S. Dalalyan and Avetik Karagulyan, supplied as `papers/Average_LMC/Arxiv_version_May_26.tex`. The [proof overview](exposition/index.html) uses the repository's paired mathematics and exact Lean template. Every module has a complete proof page and downloadable LaTeX exposition.

The review scope is the three main sampling theorems, the decreasing-step proposition and the supporting SGLD proposition. The [source audit](exposition/reference_audit.json) preserves all 12 numbered results and all 78 labels, including broader auxiliary statements whose full standalone generality is outside this scope.

## Main sampling statements

- **Theorem 1 (`th:1`):** the actual Gaussian LMC one-step bound with the exact coordinate-average smoothness and signed score correction, and its exponential constant-step convergence estimate.
- **Proposition 1 (`prop:VSS`):** the actual decreasing-step chain with the literal warmup ceiling, positive-part schedule and accuracy iteration count.
- **Theorem 2 (`th:3`):** the actual LMC bound under precisely $C^3$ regularity and the stated gradient-of-Laplacian condition, with persistent error $\bigl(2M_\infty\sqrt{M_{\mathrm{av}}}+M_\Delta\bigr)h\sqrt p/m$.
- **Theorem 3 (`th:sgld`) and Proposition 3 (`prop:th:sgld`):** the actual independent Gaussian/uniform-index control-variate SGLD law, exact estimator variance, component RMS recurrence and printed constant-step error bound.

The constants are defined from the actual potentials. The main endpoints derive their recurrences, Gibbs stationarity, Gaussian freshness, coordinate smoothing, moments and gradient-generator estimate. They introduce no Hessian Lipschitz assumption, $C^4$ regularity or convexity assumption on individual SGLD components. Extended-nonnegative main bounds cover every probability initialization. The local signed-energy formula uses its finite-transport interpretation; bounded initial errors in the variable-step statement themselves provide the required finiteness.

The source inventory records broader auxiliary statements separately. Their full standalone generality is outside the main sampling theorem scope, so literal full-paper proof coverage is not claimed.

## Verification

```sh
lake build AverageLMC
lake env lean AverageLMC/Check.lean
python3 scripts/verify-average-lmc-coverage.py --require-resolved
python3 docs/build_site.py --check
python3 docs/verify_site.py
```

`--require-resolved` checks the main sampling theorem scope. The separate `--require-complete` flag requires every source result to be covered. The kernel audits use only Lean's standard `propext`, `Classical.choice` and `Quot.sound` axioms; no proof holes or added axioms are permitted.

This work is for review on `main`. It does not update `gh-pages`.
