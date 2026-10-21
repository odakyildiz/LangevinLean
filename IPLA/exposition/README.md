# IPLA with the joint potential U_y(θ,x)

The final theorem proves the strongly convex IPLA bound from the original
joint-potential assumptions. **θ denotes the parameter, x the latent variable,
and y fixed observed data.** Strong convexity and gradient Lipschitz continuity
are assumed only for the same joint function U_y(θ,x). The stationary reference,
Gibbs invariance, marginal strong convexity, and concentration are proved facts,
not additional hypotheses in `IPLA.theorem1`.

The [main exposition page](index.html#proof-map) includes a clickable proof
diagram and an offline Lean source viewer. Each box opens the relevant result,
and the source library links every Lean file used by the final theorem.
The diagram is also available as a [standalone SVG](proof-map.svg).

The source is [Theorem 1, equation (34), and Appendix B of
arXiv:2409.07101v2](https://arxiv.org/html/2409.07101v2).
Its forcing parameter b corresponds to θ here; its latent FEM state u corresponds
to x. Both have dimension d=n_u in the printed theorem. The formalization proves
its extension to independent dimensions d_θ and d_x by the same Appendix B
argument: the rescaled state has dimension d_θ+Nd_x, and concentration concerns
only the d_θ-dimensional parameter marginal. No equality, ordering, embedding,
or padding assumption relates d_θ and d_x. Setting d_θ=d_x=d recovers the
printed equation (34). The source also uses θ for a different fixed
model index; that fixed index is absorbed into U_y here.

## Mathematical statement

Let \(\theta\in\mathbb R^{d_\theta}\) and
\(x\in\mathbb R^{d_x}\), where d_θ and d_x are independent nonnegative integers. Fix observed data y and define

\[
 U_y(\theta,x)=-\log p_\theta(x,y),\qquad
 \ell_y(\theta)=\int_{\mathbb R^{d_x}}e^{-U_y(\theta,x)}\,dx.
\]

A parameter prior can be included in U_y. Without a prior, a maximizer of ℓ_y
is a marginal maximum-likelihood estimator. With a prior included, it is a
marginal MAP estimator. The predicate `IsMarginalMaximizer` therefore describes
the center without requiring a particular statistical interpretation. It means
a maximizer of the actual integral over x. It does not mean the parameter
coordinate of the joint minimizer.

Assume U_y is differentiable, m-strongly convex jointly in (θ,x), and has a
globally L-Lipschitz joint gradient. Let m>0, N≥1, and
0<γ≤2/(m+L). Let the initialization have a finite second moment.
The Gaussian IPLA recursion is

\[
\begin{aligned}
\theta_{k+1}
 &=\theta_k-\frac\gamma N\sum_{i=1}^N\nabla_\theta U_y(\theta_k,x_k^i)
     +\sqrt{2\gamma/N}\,\xi_{k+1}^0,\\
x_{k+1}^i
 &=x_k^i-\gamma\nabla_x U_y(\theta_k,x_k^i)
     +\sqrt{2\gamma}\,\xi_{k+1}^i.
\end{aligned}
\]

The innovations are independent standard Gaussian vectors and are independent
of the initialization. The parameter innovation ξ⁰ has dimension d_θ and
each latent innovation ξⁱ has dimension d_x. `noise k` in Lean is the innovation for transition
k→k+1. There are no regularity assumptions in the observed data y.

Use the rescaled state and lifted potential

\[
 z_k=(\theta_k,x_k^1/\sqrt N,\ldots,x_k^N/\sqrt N),\qquad
 U_{N,y}(\theta,p_1,\ldots,p_N)
   =\sum_{i=1}^N U_y(\theta,\sqrt Np_i).
\]

Thus \(z_k\in\mathbb R^{d_\theta+Nd_x}\); the two coordinate blocks
retain their own dimensions. Let ν_k be the law of z_k, and let

\[
 \pi_N(dz)=Z_N^{-1}e^{-U_{N,y}(z)}\,dz.
\]

The normalization Z_N is positive and finite. There is a unique maximizer θ⋆
of ℓ_y. For every integer k≥0, the final theorem proves

\[
\boxed{
\left(\mathbb E\|\theta_k-\theta^\star\|^2\right)^{1/2}
\leq
\sqrt{\frac{2d_\theta}{Nm}}
+(1-m\gamma)^k W_2(\nu_0,\pi_N)
+\frac{33}{20}\frac Lm
  \sqrt{d_x+\frac{d_\theta}{N}}\sqrt\gamma .
}
\]

The coefficient 33/20 is exactly 1.65. The initial transport distance is finite
as a consequence of the stated second moments. For fixed N and γ, the first
and last terms give the error floor appearing in the paper.

## Exact joint assumptions

The potential assumptions in the final declaration are exactly

```lean
{Data : Type*} (U : Data → Joint dθ dx → ℝ) (y : Data)
(hdiff : Differentiable ℝ (U y))
(hsc : StrongConvexOn Set.univ m (U y))
(hLip : LipschitzWith L (gradient (U y)))
(hm : 0 < m)
```

Here `Joint dθ dx = EuclideanSpace ℝ (Fin dθ ⊕ Fin dx)`. The `Sum.inl`
coordinates form θ and the `Sum.inr` coordinates form x, and
`U y (pair θ x)` is U_y(θ,x). Mathlib's convention for
strong convexity has the quadratic coefficient m/2.

There is one joint strong-convexity binder and one joint gradient-Lipschitz
binder. There are no separate assumptions about either coordinate block,
the lifted potential, or the negative log marginal. No Hessian, C² regularity,
quadratic potential, or Gaussian statistical model is assumed. The inequality
m≤L is derived whenever the Euclidean space is nontrivial. The final theorem
also covers zero-dimensional blocks. If d_θ=0, the parameter RMS error is
zero. The proof applies the shared ULA theorem whenever the total state
space is nontrivial and proves the completely zero-dimensional case directly.
No dimension-positivity premise is hidden in the final declaration.

## Object and coefficient correspondence

| Mathematical object | Lean representation | Verified meaning |
| --- | --- | --- |
| Fixed observation y | `y : Data` | All assumptions use the fixed slice `U y`. |
| Pair (θ,x) | `Joint dθ dx`, `pair θ x` | Parameter first, latent state second. |
| Rescaled state z | `State N dθ dx` | Euclidean coordinates indexed by `Fin dθ ⊕ (Fin N × Fin dx)`. |
| Parameter coordinate | `parameterCLM z` | `Sum.inl` coordinates, operator norm at most one. |
| Physical particle x_i | `Real.sqrt N • block z i` | Exactly reverses the particle rescaling. |
| Lifted potential U_{N,y} | `potential (U y)` | The defined sum of N copies of U_y. |
| Physical IPLA updates | `scaledUpdate_parameter`, `scaledUpdate_particle` | Both drift and Gaussian noise factors agree with the displayed recursion. |
| Pointwise algorithm | `scaledChain` | Iterates precisely that scaled update. |
| L² algorithm | `lpChain` | `lpChain_coe` gives almost-everywhere equality to the pointwise recursion. |
| ν_k | `laws P (U y) … k` | `laws_eq_scaledChain` gives the pointwise chain law. |
| ULA identification | `laws_eq_ulaLawStep` | Actual IPLA law equals iterated ULA for U_{N,y}, step γ/N. |
| π_N | `gibbsTarget (U y)` | The actual normalized density, definitionally the Gibbs measure of `potential (U y)`. |
| Parameter marginal of π_N | `marginalTarget N (U y)` | Its density is proportional to ℓ_y(θ)^N, proved by `gibbsTarget_parameter_marginal`. |
| θ⋆ | `θStar` and `IsMarginalMaximizer (U y) θStar` | A maximizer of the latent integral; existence and uniqueness are derived. |
| Initial W₂ | `ULA.wasserstein2Real (P.map initial) (gibbsTarget (U y))` | The genuine coupling infimum for the rescaled state. |
| RMS error | The square root of the law integral in `theorem1` | Finite second moment is proved before converting extended quantities to real numbers. |

The substitutions into the shared Dalalyan theorem are exact:

| ULA quantity | IPLA substitution | Lean justification |
| --- | --- | --- |
| Dimension D | d_θ+Nd_x | Cardinality of the actual coordinate index set. |
| Strong-convexity constant | Nm | `potential_strongConvex`. |
| Gradient Lipschitz constant | NL | `potential_gradient_lipschitz`. |
| Step h | γ/N | `laws_eq_ulaLawStep`. |
| 1−(Nm)h | 1−mγ | Arithmetic identity in `theorem1`. |
| (NL)/(Nm) | L/m | Cancellation with N>0. |
| √(hD) | √(d_x+d_θ/N)√γ | `scaled_bias_eq`, an equality. |
| h≤2/(Nm+NL) | γ≤2/(m+L) | `scaled_step_iff`, a proved equivalence. |
| Parameter equilibrium RMS | √(2d_θ/(Nm)) | `gibbsTarget_parameter_concentration`, proved from the original joint assumptions. |

Thus every coefficient and measure has an explicit Lean counterpart in the
general-dimension bound. With d_θ=d_x=d, the last factor becomes
√(d+d/N)=√(((N+1)d)/N), and the radius becomes √(2d/(Nm)); these are exactly
the coefficients in equation (34). The source proof needs only the total
dimension d_θ+Nd_x for ULA and the parameter dimension d_θ for concentration.
The initial W₂ is for the scaled state, as in Appendix B; using
the unscaled state would change the theorem. The source orders its joint pair
as (u,b), while Lean uses (θ,x); this is only a coordinate permutation.

There is one necessary source clarification. The printed Theorem 1 defines L
using Φ, the potential without the parameter prior, whereas Appendix B applies
L-smoothness to Ψ, the potential including that prior. Here L bounds the gradient
of the same U_y that drives the algorithm. This matches Appendix B and the
corrected quantitative theorem; a bound for Φ alone would not justify applying
that same constant to Ψ. The formalization therefore does not claim that those
two different printed potentials have the same smoothness constant.

## Complete assumption audit

| Item | Status in the final theorem |
| --- | --- |
| Joint differentiability, positive strong convexity, and gradient L-Lipschitz continuity | The three displayed assumptions on U_y. |
| N≥1; independent natural dimensions d_θ,d_x; m>0; 0<γ≤2/(m+L) | The algorithm's dimensions and numerical regime. There is no relation between d_θ and d_x. |
| Independent standard Gaussian innovations, independent of initialization | The three fields of `GaussianInnovations`, specifying the algorithm. |
| Square-integrable realization of the initialization | `initial : Lp (State N dθ dx) 2 P`; this is the finite-initial-moment regime of the bound. |
| Square-integrable innovations | Their L² representation; standard Gaussian laws ensure finite moments. |
| A chosen marginal maximizer θ⋆ | The center is named with `IsMarginalMaximizer`; `existsUnique_marginalMaximizer` proves there is exactly one. |
| Finite initial W₂ | Derived from initialization and Gibbs second moments; no `hfinite` binder. |
| Gibbs normalization and finite moments | Derived from joint strong convexity. |
| Gibbs score second moment | Derived using differentiability and gradient Lipschitz continuity, with no Hessian. |
| Independent Brownian source and continuous Langevin solution | Constructed in the shared ULA library. |
| Gibbs invariance of that solution | Proved in `lp_langevin_gibbs_stationary`; no stationarity binder. |
| Reference and initial coupling family | Constructed for arbitrary finite-cost couplings in the shared ULA theorem; no reference-family binder. |
| Marginal preservation of strong log-concavity | Proved using the finite-dimensional Prékopa theorem. |
| Sharp equilibrium parameter concentration | Proved in `gibbsTarget_parameter_concentration`; no concentration binder. |
| Output finite transport and finite projected moment | Derived before taking real-valued Wasserstein distance and RMS. |

Finite W₂ and an L² initialization describe the same moment regime here:
`initial_memLp_of_finite_transport` proves the implication from finite W₂,
and `wasserstein2_ne_top_of_memLp` proves the converse when the target has its
derived second moment. The theorem's L² representation therefore adds no
independent analytical integrability requirement beyond the source's finite-W₂
initialization. Every extra premise of the earlier conditional endpoint has
been removed from the final theorem declaration.

## Main proof steps and files

This is a file-level roadmap; the proof is contained in the Lean sources.

1. `IPLA/Geometry.lean` and `IPLA/Dynamics.lean` derive the lifted constants,
   gradient blocks, and both physical IPLA updates from U_y. `IPLA/ULAAdapter.lean`
   identifies the actual Gaussian IPLA laws with the shared ULA law.
2. `UnadjustedLangevin/CanonicalULA.lean` supplies the complete Dalalyan estimate
   for that law. It reuses the earlier ULA contraction, local-error recurrence,
   transport infimum, Gibbs normalization, and score estimates. Its canonical
   Brownian source and all initial coupling extensions are constructed.
3. `UnadjustedLangevin/GibbsStationarity.lean` proves that the constructed
   Langevin solution has Gibbs law at every time, using exactly invariant
   Metropolis approximations, vanishing rejection cost, Euler convergence,
   and a coupling limit. `BrownianSegmentsGlobal.lean` identifies the analytic
   reference segments with that global solution.
4. `IPLA/MarginalConcentration.lean` computes the parameter marginal exactly,
   including all Jacobians and normalizers. `PrekopaLeindler.lean` proves the
   one-dimensional integral inequality by monotone transport;
   `PrekopaTensorization.lean` extends it to finite dimensions.
   `StrongLogConcavity.lean` derives m-strong convexity of −log ℓ_y and the
   unique maximizer. These are conclusions, not additional potential assumptions.
5. `UnadjustedLangevin/GibbsConcentration.lean` proves the dimension-sharp
   second-moment bound by dilation for a continuous strongly convex potential
   about its mode. `IPLA/Concentration.lean` applies it to −N log ℓ_y and gets
   the radius √(2d_θ/(Nm)).
6. `IPLA/Theorem.lean` applies ULA at the exact scaled constants, uses the
   proved concentration theorem, and projects to θ with a norm-one map.

The ULA proof is reused as a shared library. The special IPLA geometry and
marginal argument are separate modules; the ULA convergence theorem is not
reproved for a different statistical model.

## What the generator argument establishes

`UnadjustedLangevin/Generator.lean` integrates the Langevin generator against
the actual Gibbs density using compact C² test functions. `GeneratorDirichlet.lean`
proves the Dirichlet identity, symmetry, and dissipativity, and
`FokkerPlanck.lean` proves the constant Gibbs weak forward solution. These facts
use first-order assumptions on U_y, with no Hessian of the potential.

An integrated generator identity by itself does not identify the law of a
constructed stochastic solution. That identification is now proved separately
by the Metropolis and Euler limit argument in `GibbsStationarity.lean`. Thus the
requested generator verification is present, and the process-stationarity gap
is also closed by a theorem about the actual constructed Langevin solution.

## Standalone compilation and audit

[Standalone.lean](../Standalone.lean) contains every local definition and proof
in the final theorem's dependency closure and imports only Mathlib. The exact
final declaration is copied directly from `IPLA/Theorem.lean` into this page
below. It includes the full hypothesis list; the proof body is omitted here.

```sh
lake env lean IPLA/Standalone.lean
```

The pinned environment is Lean `leanprover/lean4:v4.35.0-rc3` with Mathlib
`v4.35.0-rc3`. `IPLA/verify.py` copies this one file to a fresh directory and
compiles with the project's compiled modules excluded. It checks the source
hashes, exact statement equality, and every top-level binder against the
complete expected hypothesis list. It also checks the independent dimensions
and exact dimension factors, absence of extra analytical premises and
placeholders, and the final axiom dependencies. The allowed dependencies are
only `propext`, `Classical.choice`, and `Quot.sound`.

See the [machine-readable audit](verification.json),
[complete compiler output](standalone-check.txt), and
[source manifest](source_manifest.json). Regenerate with
`python3 IPLA/build_artifacts.py`, then run `python3 IPLA/verify.py`.
