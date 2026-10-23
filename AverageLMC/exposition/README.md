# Average-smoothness LMC source audit

The reference is the supplied source
[`Arxiv_version_May_26.tex`](../../papers/Average_LMC/Arxiv_version_May_26.tex),
**Improved Guarantees for Langevin Monte Carlo with Average Smoothness**.
The exact source hash and a statement-by-statement coverage report appear in
[`reference_audit.json`](reference_audit.json).

Full formalization under exactly the paper's hypotheses is impossible: the
numbered GLM proposition asserts a false isotropic Hessian-Lipschitz estimate
when its only dimension/sample restriction is `p ≤ n`.

Take `n = p`, `g₁(t) = t² − sin t`, and `gᵢ(t) = t²` for `i > 1`.
Every component is smooth and convex, its second derivative is at least one,
and `|gᵢ″| + |gᵢ‴| ≤ 4`. Writing `a = X₁`, the full potential has Hessian

```
H(θ) = 2 Σᵢ Xᵢ Xᵢᵀ + sin(aᵀθ) aaᵀ.
```

Its Hessian Lipschitz constant is at least `‖a‖³`, whereas the isotropic table
requires it to be at most `C n = C p`, with `C` depending only on the fixed
component bound. A standard Gaussian row has squared norm of order `p`.
For every proposed `C ≥ 0`, choosing `p > 16` and `p > 8 C²` makes the
probability of `‖a‖³ ≤ C p` strictly less than one half. Thus the claimed
simultaneous table event cannot have probability at least one half.
The same example exposes the false uniform fourth-moment event in that
proposition's proof. It does not refute every other result in the paper.

`AverageLMC/GLMObstruction.lean` proves the exact component derivative formulas,
the uniform derivative bound, and the cubic lower bound for the explicit
rank-one sinusoidal Hessian. `AverageLMC/GaussianObstruction.lean` proves the
Gaussian norm probability obstruction from exact norm moments. Consult those
sources for the precise checked theorem statements; the audit distinguishes
these certificates from the remaining unproved analytic sampling results.

The source's local/global LMC theorems, Laplacian theorem, Gaussian perturbation
lemma, SGLD law inequalities, and all remaining probabilistic GLM estimates are
not advertised as completed merely because scalar recurrence consequences or
counterexample components compile. Repairing the sample-size assumptions or
changing a bound would produce a different theorem.

Only `main` is intended for review. This work does not request or perform a
`gh-pages` update.
