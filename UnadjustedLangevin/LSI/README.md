# Unadjusted Langevin under LSI

The [theorem overview](exposition/index.html) presents the standalone result,
its proof diagram, mathematical proof and Lean statement. The
[source-by-source proof](exposition/proof.html) pairs every LSI declaration with
detailed mathematics and exact Lean. Both pages work offline; the overview also
provides a LaTeX download.

The final theorem is `ULA.LSI.ula_kl_bound` in
[UnconditionalTheorem.lean](UnconditionalTheorem.lean). For a normalized Gibbs
target $\nu(dx)=Z^{-1}e^{-U(x)}dx$, differentiable $U$ with an $L$-Lipschitz
gradient, target LSI with constant $\alpha>0$, and finite initial KL, it proves

$$
0<h\le\frac{\alpha}{4L^2}
\quad\Longrightarrow\quad
H_\nu(\rho_k)\le e^{-\alpha hk}H_\nu(\rho_0)
 +\frac{8hdL^2}{\alpha}.
$$

Here $L>0$, $d=\dim E$, and $\rho_k$ is the law of the actual independent-Gaussian
ULA update $X_{k+1}=X_k-h\nabla U(X_k)+\sqrt{2h}Z_k$. Convexity is not assumed.
The zero-dimensional case follows from uniqueness of the probability law.
This is the discrete KL estimate in
[Vempala–Wibisono (2019), Theorem 2](https://www.cs.yale.edu/homes/wibisono/VW19.pdf).

The theorem does not request an interpolation path, weak equation, entropy
regularity, Fisher bound, initial score moment, entropy-cost coupling,
compatibility inequality or recurrence. These conclusions are proved from the
stated assumptions. Earlier conditional interfaces in
[Theorem.lean](Theorem.lean),
[RegularizedTheorem.lean](RegularizedTheorem.lean) and
[InterpolationData.lean](InterpolationData.lean) remain available with their
hypotheses explicit.

## The proof

The normalization is $2\alpha H_\nu(\rho)\le I_\nu(\rho)$. `IsLogSobolev`
tests positive $C^1$ normalized relative densities, using Mathlib's extended KL
and the squared relative score. The actual positive-time Gaussian density is
proved to belong to this class; its Fisher information is proved finite before
LSI is used to obtain finite KL.

The proof has the following steps:

1. [Compatibility.lean](Compatibility.lean) derives $\alpha\le L$ in positive
   dimension using bounded exponential and sinusoidal tests and the Gibbs
   integration-by-parts identity.
2. [EntropyMoment.lean](EntropyMoment.lean) integrates the directional
   score moment-generating function against a Gaussian measure and uses the entropy variational inequality to prove score
   integrability and $G_\mu\le4L H_\nu(\mu)+2dL$. The variational inequality applies because the relevant exponential
   score moment is finite. Thus finite relative entropy implies the required
   second moment of the gradient.
3. [InterpolationDensity.lean](InterpolationDensity.lean) and
   [GaussianEntropy.lean](GaussianEntropy.lean) construct the positive
   Gaussian-mixture density, prove that its relative density is $C^1$, express
   its score as a conditional mean, and prove finiteness of its Fisher information. [GaussianDrift.lean](GaussianDrift.lean) proves the exact
   displacement and frozen gradient-error energies.
4. [GaussianTimeDerivative.lean](GaussianTimeDerivative.lean) differentiates
   the mixture density in time and proves spacetime $L^1$ estimates.
   [GaussianWeakEquation.lean](GaussianWeakEquation.lean) proves the
   weak equation on the whole space for bounded $C^1$ tests with finite gradient energy.
   [GaussianMeasurability.lean](GaussianMeasurability.lean) and
   [GaussianEnergyIntegrability.lean](GaussianEnergyIntegrability.lean) provide
   the measurable score field and compact-time energy estimates.
5. [BoundedLog.lean](BoundedLog.lean),
   [EntropyChainRule.lean](EntropyChainRule.lean) and
   [GaussianEntropyIdentity.lean](GaussianEntropyIdentity.lean) apply bounded
   smooth log tests, commute time and space integration, and pass two dominated
   limits. They prove local absolute continuity and the almost-everywhere derivative of
   entropy. [GaussianScorePairing.lean](GaussianScorePairing.lean) and
   [GaussianEntropyProduction.lean](GaussianEntropyProduction.lean) identify
   the integral of the score against the interpolation error and prove
   $H'\le-3I/4+L^2(t^2G_0+2td)$.
6. [GibbsInterpolationBound.lean](GibbsInterpolationBound.lean),
   [EntropyEndpoint.lean](EntropyEndpoint.lean) and
   [InitialEntropy.lean](InitialEntropy.lean) bound entropy at positive times by a continuous function whose initial
   value is the initial entropy. The proof uses data processing and a
   pointwise bound on the density obtained by applying the interpolation to
   the Gibbs measure. This provides the initial value when integrating the
   entropy inequality, even for an initial distribution with only finite KL.
7. [IntegratedEntropy.lean](IntegratedEntropy.lean) integrates the a.e.
   inequality and sends the positive starting time to zero using this continuous upper bound.
   The one-step coefficient is $6$.
   [DiscreteEntropy.lean](DiscreteEntropy.lean) sums the recurrence for the
   bound with coefficient $8$, and
   [UnconditionalTheorem.lean](UnconditionalTheorem.lean) proves finiteness at
   each iterate and applies the recurrence.

[ConditionalDrift.lean](ConditionalDrift.lean) and
[GradientMoment.lean](GradientMoment.lean) also retain independently useful
conditional-mean and transport-coupling estimates. The final theorem uses the
joint Gaussian error and the direct entropy moment argument.

## Local verification

From the repository root:

```sh
lake exe cache get
lake build UnadjustedLangevin IPLA +UnadjustedLangevin.LSI.Check
lake env lean UnadjustedLangevin/LSI/Check.lean
./scripts/check-local.sh
```

The [exposition build guide](exposition/README.md) describes the offline HTML,
LaTeX and exact-source checks. GitHub workflows are not used. Publishing is a
separate manual step.
