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
The overview copies theorem signatures from the current Lean sources. Each
proof page includes its complete source and the shared context of every result.

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
  dissipative cubic/P₂ witness shows the distinction is substantive. Source
  A4/A5 derive target-comparison work without universal finite work.
- **Particle interaction:** original raw local particle/copy equations give
  the sharp source RMS floor, using actual computed Brownian noise, genuine
  stopping, original reference variance/N and Fatou. There is no global drift
  L², energy or iid interacting-law premise. Independent reference copies,
  product Brownian drivers, physical diffusion columns and complete natural
  physical particle/reference packing are constructed. The final source3
  client bounds the original native interacting solution on the independent
  whole-seed product; its existence and synchronous initial L² remain explicit.
  Mean-field A1 does not assert arbitrary interacting-system existence.
- **Parameter error:** actual parameter projection and L² triangles give the
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
  the source C¹ force and actual globally defined original ODE trajectories,
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

`FullyUniformMomentum.numerical_parameter_bound` and
`FullyUniformHigherOrder.parameter_bound` prove time-uniform parameter bounds
for the actual M-MFPO/OBABO and printed HOL-MYPGD particle maps. Each combines
the source continuous-time relaxation and particle floor with `D*sqrt(h)` for
**every iteration**, whenever `0 < h <= h_max`. Both `D` and the explicit
positive threshold are independent of the run length and step size. They may
depend on the fixed population N; no uniform-in-N discretization claim is made.

The construction derives the contracting empirical metric from source A3,
exact Picard restarts and their contraction, uniform continuous-reference
moments, actual Gaussian one-step errors and the final absorbed recurrence.
No numerical contractivity, local-error estimate, uniform moment estimate,
reference-law identity or error recurrence is an input to the final endpoints.
If the proved affine metric local error is `h*sqrt(h)*(a+b*norm(C*z))`, the
verified constants are

```
U_C = sqrt(upper_N)*norm(P)
m_C = sqrt(lower_N)/(norm(P.inverse)+1)
S = U_C*exp(K+1)*(norm(f(0))+beta)
R = U_C*norm(z0) + S/(1-exp(-rho)) + S
D = 4*(a+b*R)/(rho*m_C)
h_max = min(1, 1/rho, (rho/(4*(b+1)))^2)
```

Here P is the proved raw-to-physical coordinate equivalence, lower_N/upper_N
are the empirical source metric comparisons, and a=U_C*c0, b=U_C*c1/m_C.
The proof constructs C from A3 and shows
`m_C*norm(z) <= norm(C*z) <= U_C*norm(z)`; the final constants use only
the primitive data and proved coordinate norms.
`K` is a certified global drift Lipschitz constant, `beta` is the actual
Brownian L² increment radius, and a,b are explicit proved coefficients.
The exact functions and final bounds are linked from the overview.

The assumptions are independent globally jointly Lipschitz forces,
finite-dimensional optimiser and Euclidean sampler coordinates, positive
particle count, standard flattened Euclidean cloud encoding, P₂ initial and
target laws, positive source A3, uniform reference observation variance, and an
actual norm-continuous L² frozen invariant trajectory on the stationary law
times the canonical Brownian source with zero target mean observation.
The frozen trajectory starts at the initial-coordinate projection, solves the
physical-input integral equation and preserves the target law at every time.
The endpoint takes this realization explicitly, rather than deriving it from
an abstract invariant law. M-MFPO uses `gamma >= 0`; HOL uses `alpha > 0` and
`gamma >= 0`. No common force potential or higher force derivatives are added.
The target is a stationary critical point. The uniform coupling estimate does
not require existence of a numerical invariant law.

The earlier `FullyConstructedMomentum` and `FullyConstructedHigherOrder`
finite-horizon estimates remain as supporting results. The latter's
`original_parameter_bound` adds `L*epsilon/m` from actual coupled original and
surrogate target observations and positive gradient monotonicity. That bias
argument can also be combined with the new uniform theorem; a model-specific
smoothing coupling radius remains an explicit separate requirement.

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

The compact entry files
[`NewA.lean`](../standalone/PBGSO/NewA.lean),
[`NewB.lean`](../standalone/PBGSO/NewB.lean), and
[`PaperTheorems.lean`](../standalone/PBGSO/PaperTheorems.lean) print the exact
final theorem contracts and audit their logical axioms. They import the proof
library and are **repository checks**, rather than self-contained proof files:

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
contains every local definition, assumption and proof used by its endpoints;
only Mathlib is imported. The script checks each file in a fresh directory with
all original project oleans removed from `LEAN_PATH`, and rejects unexpected
axioms. No theorem is renamed or strengthened.

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
  The earlier finite-horizon results remain available in `FullyConstructed*`.

The generated proof catalog covers every module and every complete declaration;
this entry-point list is not a substitute for its exact assumptions.
