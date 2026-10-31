# Particle-based Generalised Stochastic Optimisation

This library formalizes the general optimiser–sampler framework in the local
PBGSO paper by Jiechen Jackie Zhang and O. Deniz Akyildiz. The observation,
optimiser response, sampler drift/diffusion, projections and augmented spaces
are independent inputs. No common potential, MMLE objective or equality of
parameter and sampler dimensions is required. The mean-field optimiser has no
thermal noise; the finite-particle optimiser is random through its empirical
observations.

Read the [mathematical overview](exposition/index.html), the
[source audit](exposition/source_audit.md), the
[coverage ledger](exposition/reference_audit.json), and the
[exact assumption inventory](exposition/assumption_inventory.json).
The overview pairs each mathematical assumption and theorem with its exact
Lean statement. It uses the paper’s optimiser state $\vartheta$, sampler $Z$,
mean observation $G_\nu$, and numerical coordinates. A1–A5, extra assumptions
R1–R3, and numerical assumptions N1–N3 are stated separately, with additions
and solution interpretations marked before the theorems. Shared Lean context
is available beside each statement. Each proof page retains the full source.

## Source results and current scope

- **Stationarity:** the original local stochastic equation and integral
  optimiser ODE give the literal stationary product law. A2 means an actual
  stationary weak frozen **SDE** realization on some probability space,
  retaining all auxiliary variables. A1 supplies one full-system canonical
  strong solution with independent initial/Wiener inputs and same-driver
  pathwise uniqueness. The actual probability map and local-noise transport
  derive the comparison on the original source. No common-source frozen strong
  solver, global drift moment or energy conclusion is assumed.
- **Mean-field law contraction:** the primitive linear-growth A1(ii) branch
  derives global moments, actual stochastic realization and the true optimal
  initial Wasserstein factor across original sources. The constant-diffusion
  A1(i) branch is also proved across arbitrary original sources under the
  **ordinary finite signed-integral reading of universal A3**. The named
  `FiniteCouplingWork` domain is independent of the conditional inequality.
  Extended-negative-work A3 is outside this convention; an actual strongly
  dissipative cubic/$\mathcal P_2$ witness shows the distinction is substantive. Source
  A4/A5 derive target-comparison work without universal finite work.
- **Particle interaction:** original raw local particle/copy equations give
  the sharp source RMS floor, using actual computed Brownian noise, genuine
  stopping, original reference variance/N and Fatou. There is no global drift
  $L^2$, energy or iid interacting-law premise. Independent reference copies,
  product Brownian drivers, physical diffusion columns and complete natural
  physical particle/reference packing are constructed. The final source3
  client bounds the original native interacting solution on the independent
  whole-seed product; its existence and synchronous initial $L^2$ remain explicit.
  Mean-field A1 does not assert arbitrary interacting-system existence.
- **Parameter error:** actual parameter projection and $L^2$ triangles give the
  source relaxation-plus-particle bound and a joint time/population limit.
  Natural constant-noise target comparisons derive positive work from A4/A5;
  their optimal-law factor is proved. The final original-native parameter
  clients construct all physical process assembly internally in both A1
  branches. A natural family of original equations proves the joint limit
  without assuming any final estimate.
- **Appendix criteria and volume:** the separate small-gain criterion has its
  actual minimum matrix eigenvalue; the canonical projected criterion derives
  its metrics and generalized spectral rates; the heavy-ball source threshold
  gives full law monotonicity. Continuous signed determinant one follows from
  the source $C^1$ force and actual globally defined original ODE trajectories,
  with differentiable flow dependence proved. Actual ODE uniqueness derives the
  flow inverse, and Jacobian change of variables proves literal continuous
  Lebesgue measure preservation. The discrete original BAB
  determinant assertion is also proved.

All eight source statements and both actual method bounds are verified under
these explicit source interpretations. The strict verifier checks that ledger;
a documentation-fidelity check alone is not a completion certificate. In
particular, extended-negative signed-work A3 is outside the constant-branch
convention, and A2 means actual frozen SDE invariance.

## New bounds for the two actual methods

`FullyUniformMomentum.explicit_parameter_bound` and
`FullyUniformHigherOrder.explicit_parameter_bound` prove time-uniform
parameter bounds for the actual M-MFPO/OBABO and printed HOL-MYPGD particle
maps. Their `explicit_discretization_bound` theorems also bound the full raw
state error, in the maximum of the four component $L^2$ norms. Each parameter
bound combines the source continuous-time relaxation and particle floor with
$D_j\sqrt h$ for **every iteration**, when $0<h\le h_{\star,j}$. The coefficient
and positive threshold are explicit functions of the data, independent of
iteration count, step size and time horizon. They may depend on fixed $N$;
no uniform-in-$N$ discretization claim is made.

The construction derives the contracting empirical metric from source A3,
exact Picard restarts and their contraction, uniform continuous-reference
moments, actual Gaussian one-step errors and the absorbed recurrence.
No numerical contractivity, local-error estimate, uniform moment estimate,
reference-law identity or final recurrence is an assumption.

The main page states the numerical assumptions before the bounds:

- **N1:** independent globally jointly Lipschitz forces on the paper’s
  finite-dimensional optimiser and Euclidean sampler spaces. Write $F_x$ for
  the sampler force, to preserve the paper’s $G_\nu$ for the population mean
  observation; Lean calls these two independent forces `D.F` and `D.G`.
- **N2:** positive population, deterministic optimiser initial state, an
  independent i.i.d. $\mathcal P_2$ sampler cloud and physical Brownian drivers, source
  A3 with positive rate, A5, and zero mean observation at the target.
- **N3:** an actual norm-continuous $L^2$ frozen invariant trajectory on the
  target law times the canonical Brownian source. It starts at the initial
  projection, solves the physical frozen integral equation and preserves its
  law at every time. This is stronger than the weak frozen-SDE interpretation
  of A2 used for Theorem 1; the numerical endpoint takes it explicitly.

M-MFPO assumes $\gamma\ge0$; HOL assumes $\alpha>0$ and $\gamma\ge0$.
No common potential or higher force derivatives are required. The target is
an actual stationary zero-observation target. It is an objective critical
point when the gradient identity and frozen position marginal match that
objective. The uniform error proof does not assume
a numerical invariant law.

### Explicit numerical constants

Let $d=Nd_x$. For positive position dimension, the standard Euclidean cloud
map has norm 1 and inverse norm $\sqrt N$. Thus the actual force constants are

$$
\begin{aligned}
L_F&=2\ell_F,&L_x&=2\sqrt N\,\ell_x,\\
f_0&=\|F(0,0)\|,&g_0&=\sqrt N\,\|F_x(0,0)\|,\\
b_\circ&=\max\{f_0,g_0\}.
\end{aligned}
$$

For $d_x=0$, the proved alternatives are $L_F=\ell_F$, $L_x=0$.
`CloudEncodingConstants` proves both cases. `UniformOriginConstants` proves
that $f_0$ and $g_0$ are exactly the actual lifted zero-force norms and that the
full raw drift at zero has norm $b_\circ$ for each method. No coordinate-map norm or
unspecified zero-state process radius remains in the constants.

For M-MFPO, the local coefficients have the following closed formulas:

$$
\begin{aligned}
L_M&=2\max\{L_F,L_x\},&K_M&=L_M+\gamma+1,\\
\Xi_M&=\sqrt d,&\beta_M&=\sqrt\gamma\sqrt{2d},\\
T_M&=b_\circ+K_Me^{K_M+1}(b_\circ+\beta_M)+\beta_M,\\
c_{0,M}&=\left(\frac{\gamma+1}{2}+\frac{L_M}{4}\right)b_\circ
 +\left(\frac{L_M}{2}+\sqrt\gamma+\frac{3\gamma\sqrt\gamma}{2}\right)\sqrt d
 +\frac{2K_MT_M}{3},\\
c_{1,M}&=\frac{\gamma^2+\gamma+L_M}{2}
 +\left(\frac{\gamma+1}{2}+\frac{L_M}{4}\right)L_M
 +\frac{2K_M^2e^{K_M+1}}{3}.
\end{aligned}
$$

For HOL-MYPGD, all coefficient and Gaussian remainder budgets are explicit:

$$
\begin{aligned}
K_H&=4(L_F+L_x+1+2\gamma+\alpha),&\beta_H&=\sqrt\alpha\sqrt{2d},\\
r_{12}&=\frac{\gamma^2}{2\alpha},&r_{13}&=\frac\gamma2,\\
r_{22}&=\frac{\gamma^2}{2},&r_{23}&=\frac{\gamma\alpha}{2},\\
r_{32}&=\frac{2\gamma^3}{\alpha}+\frac{\gamma^3}{2}+\frac{\gamma\alpha}{2},\\
r_{33}&=\frac{3\gamma^2}{2}+\frac{\alpha^2}{2}+\frac{\alpha\gamma^2}{2},\\
A_H&=\frac{1+\gamma}{2}[g_0+2L_x+L_x(f_0+2L_F)]
 +r_{12}+r_{22}+r_{32}+r_{13}+r_{23}+r_{33}+L_x(f_0+2L_F),\\
N_H&=\sqrt{2\alpha}\left(\frac{3\gamma}{2}+\alpha+r_{33}\right),\\
T_H&=b_\circ+K_He^{K_H+1}(b_\circ+\beta_H)+\beta_H,\\
c_{0,H}&=A_H+\sqrt d\,N_H+\frac{8K_HT_H}{3},\\
c_{1,H}&=A_H+\frac{8K_H^2e^{K_H+1}}{3}.
\end{aligned}
$$

`UniformConstantExpansions` proves equality of these arithmetic expressions
with the exact coefficients in the local-error proofs; no consistency budget
or error bound is supplied as a premise.

For either method $j\in\{M,H\}$, let $\underline\lambda,\overline\lambda$ be the certified source
quadratic comparisons. The metric and remaining constants are

$$
\begin{aligned}
\underline d_N&=\underline\lambda\min\{1,N^{-1}\},&
\overline d_N&=\overline\lambda\max\{1,N^{-1}\},\\
m_N&=\frac{\sqrt{\underline d_N}}2,&U_N&=2\sqrt{\overline d_N},\\
S_j&=U_Ne^{K_j+1}(b_\circ+\beta_j),\\
R_j&=U_N\|y_0\|+\frac{S_j}{1-e^{-\rho}}+S_j,\\
a_j&=U_Nc_{0,j},&b_j&=\frac{U_Nc_{1,j}}{m_N},\\
D_j&=\frac{4(a_j+b_jR_j)}{\rho m_N},\\
h_{\star,j}&=\min\left\{1,\rho^{-1},\left(\frac{\rho}{4(b_j+1)}\right)^2\right\}.
\end{aligned}
$$

Here $\|y_0\|$ is the raw maximum-component $L^2$ norm of the common initial
phase. `MethodMetricComparisons` derives a metric factor $C$ from A3 with
$m_N\|y\|\le\|Cy\|\le U_N\|y\|$. Since $N$ is positive,
$m_N=\frac12\sqrt{\underline\lambda/N}$ and $U_N=2\sqrt{\overline\lambda}$. Both constants are
numeric comparisons; no unknown operator norm enters the final bound.
The proof derives the radius $R_j$ by restarting the actual continuous flow
and absorbs the one-step defects using the explicit positive step threshold.

The earlier existential `FullyUniformMomentum.numerical_parameter_bound` and
`FullyUniformHigherOrder.parameter_bound` remain as corollaries. The
`FullyConstructedMomentum` and `FullyConstructedHigherOrder` finite-horizon
estimates also remain supporting results. The latter’s `original_parameter_bound`
adds $L\varepsilon/m$ from actual coupled original/surrogate target observations
and positive gradient monotonicity. The same bias argument can accompany the
uniform theorem; a model-specific smoothing coupling radius remains explicit.

Two source limitations are recorded separately: the printed HOL coefficients
are not the exact full force-free linear flow (an exact nonzero defect is
proved), although their printed Gaussian covariance is the verified kernel
Gram covariance; and the displayed full-space image-TV prior is improper along
constant-image translations. Repairing that illustrative model is not an
additional generic-method proof obligation.

## Compile and verify

From the repository root:

```sh
lake build PBGSO
lake env lean PBGSO/Check.lean
python3 scripts/verify-pbgso.py
python3 scripts/verify-pbgso.py --require-complete
python3 docs/build_site.py --check
```

`Check.lean` prints the logical axioms of all public theorem/lemma declarations.
The expected logical dependencies are `propext`, `Classical.choice` and
`Quot.sound`; no custom axiom or admitted proof is permitted. The normal
verifier checks all source hashes, exact statement/context copies, assumption
inventories and local links. `--require-complete` additionally requires all
eight source results, both actual method bounds and required bridges to be
verified under the audit file’s explicit source interpretations.

Regenerate the site with `python3 docs/build_site.py`; the bundled Node runtime
must be on PATH for local math rendering. Existing repository-wide static and
citation checks also apply.

## Standalone verification

The reader-facing entry files
[`NewA.lean`](../standalone/PBGSO/NewA.lean),
[`NewB.lean`](../standalone/PBGSO/NewB.lean), and
[`PaperTheorems.lean`](../standalone/PBGSO/PaperTheorems.lean) contain actual
theorem declarations, their complete variable and assumption contexts, and
short proofs applying the checked library. Both new theorem entries also display their primitive
force records, exact numerical constants, closed arithmetic expansions and
checked constant identities. Readers can inspect the statements without
opening the proof closure. These files import the proof library and serve as
**repository checks**:

```sh
lake build PBGSO
python3 scripts/check-pbgso-standalone.py --check
```

To generate genuinely self-contained local proofs, export the complete
transitive source closure into one Mathlib-only file per entry point and check
it with the repository's compiled modules excluded:

```sh
python3 scripts/check-pbgso-standalone.py --output /tmp/pbgso-standalone --check
```

The output directory must be new or empty. It receives `NewA.lean`, `NewB.lean`,
`PaperTheorems.lean`, the pinned `lean-toolchain`, exact source hashes in
`manifest.json`, and full Lean output in `*.check.txt`. Each exported file
begins with an exact reader-facing assumption/statement preview, followed by
every local definition and proof used by its endpoints. The actual theorem
declarations compile after their dependencies at the end, as Lean requires;
only Mathlib is imported. The script checks each file in a fresh directory with
all original project oleans removed from `LEAN_PATH`, and rejects placeholders,
custom axioms and unexpected logical dependencies. The manifest also hashes the exact reader-facing entry; the
export does not strengthen its statements.

To export only one numerical theorem, use `--endpoint new-a` or
`--endpoint new-b`; `--endpoint paper` selects the original paper endpoints.
For example:

```sh
python3 scripts/check-pbgso-standalone.py --endpoint new-a --output /tmp/pbgso-new-a --check
```

These commands run offline once the repository's pinned Lean toolchain and
Mathlib dependencies are prepared; the script never installs or fetches them.
An exported `.lean` file can also be copied into a separate project with Lean
`leanprover/lean4:v4.35.0-rc3` and Mathlib `v4.35.0-rc3`, then checked with
`lake env lean NewA.lean` (or the other filename). The analytic hypotheses
remain visible in the exact theorem types. New A and New B are the time-uniform
implementation-to-target bounds described above; the paper entry
retains the finite signed-work convention, actual A1/A2 solution assumptions,
original interacting-solution existence and synchronous initial conditions.

## Entry points

- `Framework`, `PaperTheorems`, `WeakContraction`, `LawContraction`,
  `ProductTransport`: independent primitive maps, joint monotonicity, weak
  equations, genuine couplings and actual product-law Wasserstein identities.
- `FilteredBrownian`, `ClosedStepIntegration`, `PredictableStepDensity`,
  `PredictableCurveIntegral`, `RawDiffusionIntegral`: actual finite Brownian
  sums and Hilbert completion, predictable density, martingales, weighted
  increments and raw spatial sections. `ProductLpSections` derives section
  measurability on arbitrary sigma-finite sample measures from the field's
  own countable spatial dependence; ambient measure separability is unnecessary.
- `AdaptedBrownianModification`, `BrownianDriverPathLaw`, `BrownianPathDriver`,
  `RawLocalIntegral`, `RawPathSolutionTransfer`: actual continuous Brownian
  modifications, input-path probabilities, genuine local integrals and
  cross-source strong-solution law transfer.
- `RawLinearGrowthState`, `RawSamplerGrowth`,
  `RawSamplerGrowthArbitraryLaw`: primitive growth, derived original moments
  and actual optimal-law contraction. `NaturalFiniteWorkArbitraryLaw` gives
  the constant-diffusion branch under the explicit finite signed-work
  convention; `RawConstantNoisePositiveLaw` also exposes a one-sided-work
  sufficient criterion.
- `RawParticleInteraction`, `RawParticleParameter`, `RawIndependentCopies`,
  `RawReferenceCloud`: original raw particle bounds and independent reference
  constructions. `RawConstructedParticleCopy`, `RawConstructedParticleBounds`,
  `RawConstructedParticleParameter` and `RawConstructedParticleJointLimit`
  instantiate the actual physical reference/pair construction and conclude
  the source bounds and joint limit on the original native equations.
- `SeparatedSchur`, `SmallGainSpectrum`, `CanonicalProjectedCriterion`,
  `HypocoerciveCriterion`, `FlowSourceRegularity`, `ContinuousFlowMeasure`,
  `DiscreteVolume`: the
  appendix sufficient criteria and continuous/discrete volume results.
- `FullyUniformMomentum`, `FullyUniformHigherOrder`: final time-uniform
  implementation-to-target bounds. `ImplementationMetric`, `EmpiricalMetric`
  and `MetricFactor` construct the actual contracting raw metric from A3.
  `UniformIntegralMoments`, `UniformDiscrete`, `UniformStepSize` derive uniform
  moments and all-iteration error absorption. `MomentumUniform*` and
  `HOLUniform*`/`HOLRestart*` derive actual scheme errors and Brownian coupling.
  `MethodMetricComparisons` proves numeric raw-metric comparisons;
  `CloudEncodingConstants`, `UniformOriginConstants` and
  `UniformConstantExpansions` remove coordinate-norm, origin and arithmetic
  ambiguity from the displayed constants. Earlier finite-horizon results remain
  available in `FullyConstructed*`.

The generated proof catalog covers every module and every complete declaration;
this entry-point list is not a substitute for its exact assumptions.
