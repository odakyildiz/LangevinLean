import PBGSO.FullyUniformHigherOrder
import PBGSO.UniformConstantExpansions

/-!
# Theorem New B: actual time-uniform HOL-MYPGD bound

This is a reader-facing, checked theorem file. Primitive force assumptions,
all ambient variables, the source assumptions, explicit constants and final
inequalities are stated below; the proofs only apply the checked library.

`A` is the optimiser position space; `J` indexes each sampler's position
and Brownian coordinates. `N` is the positive particle count. The full
sampler state also includes its two auxiliary coordinates.
`Geo`/`Geometry` is the source positive quadratic metric; A3 is the original
full optimiser/sampler joint-monotonicity inequality, not a numerical
contraction condition. `Variance` and `hVariance` state A5 for the actual
constructed mean-field solution, not for a supplied comparison process.

The frozen target assumption is an actual norm-continuous L² solution of
the frozen integral SDE on target-law × canonical Brownian space, initialized
by the first projection and preserving the target law. This is more explicit
than an abstract weak invariant-law premise; it is kept visible below.

All metric factors, original interacting dynamics, correlated physical
Gaussian innovations, local defects, moments and numerical stability are
constructed. Constants and the positive maximum step are independent of
iteration count, step size and time horizon, for fixed N. The full-state
norm below is the maximum of the four component L² norms. No error recurrence
or final estimate is assumed. No common potential or higher derivative of
the forces is needed. The target is stationary with zero mean observation.
It is an objective critical point when the gradient identity and frozen
position marginal match that objective.

Mathlib-only export, with these same contracts FIRST and full proofs afterward:
  python3 scripts/check-pbgso-standalone.py --endpoint new-b --output /tmp/pbgso-new-b --check
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal InnerProductSpace RealInnerProductSpace
namespace PBGSO.Standalone.NewB
open PBGSO.Methods PBGSO.ImplementationDynamics PBGSO.FullyConstructedHigherOrder

variable {A J : Type*} {N : ℕ}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [Fintype J] [DecidableEq J]

/-- Exactly the extra primitive numerical assumptions: positive population
and two independent globally jointly Lipschitz forces. Neither a common
potential nor a numerical contraction/error estimate is a field. -/
structure IndependentForces where
  positive_particles : 0 < N
  F : A → EuclideanSpace ℝ J → A
  G : A → EuclideanSpace ℝ J → EuclideanSpace ℝ J
  lF : ℝ≥0
  lG : ℝ≥0
  F_lipschitz : ∀ θ θ' x x',
    ‖F θ x - F θ' x'‖ ≤ (lF : ℝ) * (‖θ - θ'‖ + ‖x - x'‖)
  G_lipschitz : ∀ θ θ' x x',
    ‖G θ x - G θ' x'‖ ≤ (lG : ℝ) * (‖θ - θ'‖ + ‖x - x'‖)

/-- The standard Euclidean cloud encoding is a definition, not an extra
compatibility hypothesis. -/
def IndependentForces.data (forces : IndependentForces (A := A) (J := J) (N := N)) :
    ParticleForceData A (EuclideanSpace ℝ J) (EuclideanSpace ℝ (Fin N × J)) N where
  nonempty := forces.positive_particles
  F := forces.F
  G := forces.G
  parameterLip := forces.lF
  samplerLip := forces.lG
  parameter_bound := forces.F_lipschitz
  sampler_bound := forces.G_lipschitz
  cloud := euclideanParticleEncoding N J

variable (forces : IndependentForces (A := A) (J := J) (N := N))

private theorem input_continuous (α : ℝ) : Continuous (input (J := J) α) :=
  samplerBrownianInput_continuous _ _ _ _ _

private theorem input_zero (α : ℝ) : input (J := J) α 0 = 0 :=
  samplerBrownianInput_zero _ _ _ _ _

variable (α γ : ℝ) (Geo : TwistedGeometry A (HigherOrderSampler (EuclideanSpace ℝ J)))
  (μ : Measure (HigherOrderSampler (EuclideanSpace ℝ J))) [IsProbabilityMeasure μ]
  (hμ : MemLp (fun z : HigherOrderSampler (EuclideanSpace ℝ J) ↦ z) 2 μ) (a : A)
  (Variance : ℝ)
  (hVariance : ∀ r, 0 ≤ r →
    (∫ z, ‖(sourceModel (forces.data) α γ).observation
      ((sourceModel (forces.data) α γ).parameter (AdditiveCanonical.optimizer
        (ULA.CanonicalBrownian.vectorProbability J) (higherOrderForceDynamics (forces.data) α γ)
        μ hμ a (input α) (input_continuous α) (input_zero α) r))
      ((sourceModel (forces.data) α γ).position z) -
      (sourceModel (forces.data) α γ).meanGradient (AdditiveCanonical.law
        (ULA.CanonicalBrownian.vectorProbability J) (higherOrderForceDynamics (forces.data) α γ)
        μ hμ a (input α) (input_continuous α) (input_zero α) r)
        (AdditiveCanonical.optimizer (ULA.CanonicalBrownian.vectorProbability J)
          (higherOrderForceDynamics (forces.data) α γ) μ hμ a
          (input α) (input_continuous α) (input_zero α) r)‖ ^ 2
      ∂AdditiveCanonical.law (ULA.CanonicalBrownian.vectorProbability J)
        (higherOrderForceDynamics (forces.data) α γ) μ hμ a
        (input α) (input_continuous α) (input_zero α) r) ≤ Variance)



/-! ## Explicit data-only constants
The following definitions repeat the exact library formulas. Cross-references
are qualified to make the correspondence directly inspectable. -/
/-- Coercivity of the constructed source metric in raw HOL coordinates. -/
def metricCoercivity : ℝ := Real.sqrt (EmpiricalMetric.lower N Geo) / 2

/-- Data-only upper norm bound for the constructed metric factor. -/
def metricUpper : ℝ := 2 * Real.sqrt (EmpiricalMetric.upper N Geo)

/-- State-independent part of the proved local Gaussian error. -/
def localConstant0 : ℝ :=
  let Q := ParticleNoiseSpace.probability (J := J) μ N
  holUniformLocalConstant0 (Fin N × J) α γ (forces.data).meanLip (forces.data).samplerForceLip
    ‖(forces.data).meanForceLp Q 0 0‖ ‖(forces.data).samplerForceLp Q 0 0‖
    ‖holDrift ((forces.data).meanForceLp Q) ((forces.data).samplerForceLp Q) α γ 0‖

/-- Linear initial-state part of the proved local Gaussian error. -/
def localConstant1 : ℝ :=
  let Q := ParticleNoiseSpace.probability (J := J) μ N
  holUniformLocalConstant1 α γ (forces.data).meanLip (forces.data).samplerForceLip
    ‖(forces.data).meanForceLp Q 0 0‖ ‖(forces.data).samplerForceLp Q 0 0‖

/-- Actual Brownian increment radius, including every particle coordinate. -/
def noiseRadius : ℝ := holUniformNoiseRadius (Fin N × J) α

/-- Explicit one-unit exact-flow radius when started at zero. -/
def zeroStartRadius : ℝ :=
  let Q := ParticleNoiseSpace.probability (J := J) μ N
  UniformIntegral.radius (holDriftGlobalLip (forces.data).meanLip (forces.data).samplerForceLip α γ)
    ‖holDrift ((forces.data).meanForceLp Q) ((forces.data).samplerForceLp Q) α γ 0‖
    (PBGSO.FullyUniformHigherOrder.noiseRadius (N := N) (J := J) α) 0

/-- Data-only transformed zero-start radius `S`. -/
def zeroStartMoment : ℝ := PBGSO.FullyUniformHigherOrder.metricUpper (N := N) Geo * PBGSO.FullyUniformHigherOrder.zeroStartRadius (forces.data) α γ μ

/-- Uniform exact-reference radius, derived by contraction and unit restarts. -/
def referenceRadius (ρ : ℝ) : ℝ :=
  let S := PBGSO.FullyUniformHigherOrder.zeroStartMoment (forces.data) α γ Geo μ
  PBGSO.FullyUniformHigherOrder.metricUpper (N := N) Geo * ‖initial (forces.data) α γ Geo μ hμ a Variance hVariance‖ +
    S / (1 - Real.exp (-ρ)) + S

/-- Linear-radius coefficient absorbed by exact-flow dissipation. -/
def radiusGrowth : ℝ :=
  PBGSO.FullyUniformHigherOrder.metricUpper (N := N) Geo * PBGSO.FullyUniformHigherOrder.localConstant1 (forces.data) α γ μ / PBGSO.FullyUniformHigherOrder.metricCoercivity (N := N) Geo

/-- Explicit time-uniform discretisation coefficient, independent of `h,n`. -/
def discretizationConstant (ρ : ℝ) : ℝ :=
  (4 * (PBGSO.FullyUniformHigherOrder.metricUpper (N := N) Geo * PBGSO.FullyUniformHigherOrder.localConstant0 (forces.data) α γ μ +
    PBGSO.FullyUniformHigherOrder.radiusGrowth (forces.data) α γ Geo μ * PBGSO.FullyUniformHigherOrder.referenceRadius (forces.data) α γ Geo μ hμ a Variance hVariance ρ) / ρ) /
      PBGSO.FullyUniformHigherOrder.metricCoercivity (N := N) Geo

/-- Explicit positive upper step size, with no hidden error or radius premise. -/
def maximumStep (ρ : ℝ) : ℝ := UniformStep.maximumStep ρ (PBGSO.FullyUniformHigherOrder.radiusGrowth (forces.data) α γ Geo μ)


/-- The displayed copied formulas are definitionally the exact constants in
the library theorem. This check detects drift between the readable contract
and the implementation without assuming any error bound. -/
theorem constants_match_source (ρ : ℝ) :
    metricCoercivity (N := N) Geo = PBGSO.FullyUniformHigherOrder.metricCoercivity (N := N) Geo ∧
    metricUpper (N := N) Geo = PBGSO.FullyUniformHigherOrder.metricUpper (N := N) Geo ∧
    discretizationConstant (forces := forces) (γ := γ) (μ := μ) (α := α) (Geo := Geo) (hμ := hμ) (a := a) (Variance := Variance) (hVariance := hVariance) (ρ := ρ) = PBGSO.FullyUniformHigherOrder.discretizationConstant (forces.data) α γ Geo μ hμ a Variance hVariance ρ ∧
    maximumStep (forces := forces) (γ := γ) (μ := μ) (α := α) (Geo := Geo) (ρ := ρ) = PBGSO.FullyUniformHigherOrder.maximumStep (forces.data) α γ Geo μ ρ := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Closed arithmetic for the local coefficients
The identities here connect these arithmetic expressions to the exact
coefficients referenced above. No local-error premise is supplied. -/
namespace LocalErrorFormulas
def holExpandedGrowthConstant (α γ LF LG fzero gzero : ℝ) : ℝ :=
  ((1 + γ) / 2) * (gzero + 2 * LG + LG * (fzero + 2 * LF)) +
    (γ ^ 2 / (2 * α) + γ ^ 2 / 2 +
      2 * γ ^ 3 / α + γ ^ 3 / 2 + γ * α / 2) +
    (γ / 2 + γ * α / 2 + 3 * γ ^ 2 / 2 + α ^ 2 / 2 + α * γ ^ 2 / 2) +
    LG * (fzero + 2 * LF)

def holExpandedNoiseConstant (α γ : ℝ) : ℝ :=
  Real.sqrt (2 * α) *
    (3 * γ / 2 + α + 3 * γ ^ 2 / 2 + α ^ 2 / 2 + α * γ ^ 2 / 2)

def holExpandedDriftLip (α γ LF LG : ℝ) : ℝ :=
  4 * (LF + LG + 1 + 2 * γ + α)

def holExpandedConstant0 (d α γ LF LG fzero gzero bzero : ℝ) : ℝ :=
  let K := 4 * (LF + LG + 1 + 2 * γ + α)
  let β := Real.sqrt α * Real.sqrt (2 * d)
  holExpandedGrowthConstant α γ LF LG fzero gzero +
    Real.sqrt d * holExpandedNoiseConstant α γ +
    (8 / 3 : ℝ) * K * (bzero + K * Real.exp (K + 1) * (bzero + β) + β)

def holExpandedConstant1 (α γ LF LG fzero gzero : ℝ) : ℝ :=
  let K := 4 * (LF + LG + 1 + 2 * γ + α)
  holExpandedGrowthConstant α γ LF LG fzero gzero +
    (8 / 3 : ℝ) * K ^ 2 * Real.exp (K + 1)

theorem holUniformLocalConstant0_expanded (I : Type*) [Fintype I]
    (α γ LF LG fzero gzero bzero : ℝ)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hLF : 0 ≤ LF) (hLG : 0 ≤ LG) :
    holUniformLocalConstant0 I α γ LF LG fzero gzero bzero =
      holExpandedConstant0 (Fintype.card I) α γ LF LG fzero gzero bzero := by
  apply PBGSO.Methods.holUniformLocalConstant0_expanded <;> assumption

theorem holUniformLocalConstant1_expanded (α γ LF LG fzero gzero : ℝ)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hLF : 0 ≤ LF) (hLG : 0 ≤ LG) :
    holUniformLocalConstant1 α γ LF LG fzero gzero =
      holExpandedConstant1 α γ LF LG fzero gzero := by
  apply PBGSO.Methods.holUniformLocalConstant1_expanded <;> assumption

end LocalErrorFormulas

/-! ## Positive maximum step and full-state discretisation bound -/
theorem step_and_discretization_bound [FiniteDimensional ℝ A]
    (hα : 0 < α) (hγ : 0 ≤ γ)
    (ρ : ℝ) (hρ : 0 < ρ) (hmono : TwistedJointMonotonicity (sourceModel (forces.data) α γ) Geo ρ) :
    0 < PBGSO.FullyUniformHigherOrder.maximumStep (forces.data) α γ Geo μ ρ ∧
      0 ≤ PBGSO.FullyUniformHigherOrder.discretizationConstant (forces.data) α γ Geo μ hμ a Variance hVariance ρ ∧
      ∀ (h : ℝ≥0) (n : ℕ), 0 < (h : ℝ) → (h : ℝ) ≤ PBGSO.FullyUniformHigherOrder.maximumStep (forces.data) α γ Geo μ ρ →
        ‖higherOrderPullbackParticleIterate (Fin N × J)
          (ParticleNoiseSpace.probability (J := J) μ N)
          (ParticleNoiseSpace.noise_preserving (J := J) μ N) (forces.data) α γ h
          (initial (forces.data) α γ Geo μ hμ a Variance hVariance) n -
          higherOrderUnpackLp (ParticleNoiseSpace.probability (J := J) μ N) (forces.data)
            ((particle (forces.data) α γ Geo μ hμ a Variance hVariance).state (n * (h : ℝ)))‖ ≤
          PBGSO.FullyUniformHigherOrder.discretizationConstant (forces.data) α γ Geo μ hμ a Variance hVariance ρ * Real.sqrt (h : ℝ) := by
  apply PBGSO.FullyUniformHigherOrder.explicit_discretization_guarantee (D := forces.data) (α := α) (γ := γ) (Geo := Geo) (μ := μ) (hμ := hμ) (a := a) (Variance := Variance) (hVariance := hVariance) (hcloud := rfl) <;> assumption

#print axioms PBGSO.Standalone.NewB.step_and_discretization_bound

/-! ## Final numerical parameter bound -/
theorem theorem_new_b [FiniteDimensional ℝ A]
    (hα : 0 < α) (hγ : 0 ≤ γ)
    (νStar : Measure (HigherOrderSampler (EuclideanSpace ℝ J))) [IsProbabilityMeasure νStar]
    (hνStar : MemLp (fun z : HigherOrderSampler (EuclideanSpace ℝ J) ↦ z) 2 νStar)
    (aStar : A)
    (Frozen : AdditiveStationary.FrozenTrajectory (ULA.CanonicalBrownian.vectorProbability J)
      (higherOrderForceDynamics (forces.data) α γ) νStar hνStar aStar (input α))
    (ρ : ℝ) (hρ : 0 < ρ) (hmono : TwistedJointMonotonicity (sourceModel (forces.data) α γ) Geo ρ)
    (hg : (sourceModel (forces.data) α γ).meanGradient νStar aStar = 0)
    (hV : 0 ≤ Variance)
    (h : ℝ≥0) (n : ℕ) (hh : 0 < (h : ℝ))
    (hhstep : (h : ℝ) ≤ PBGSO.FullyUniformHigherOrder.maximumStep (forces.data) α γ Geo μ ρ) :
        ‖(higherOrderPullbackParticleIterate (Fin N × J)
          (ParticleNoiseSpace.probability (J := J) μ N)
          (ParticleNoiseSpace.noise_preserving (J := J) μ N) (forces.data) α γ h
          (initial (forces.data) α γ Geo μ hμ a Variance hVariance) n).1 -
          Lp.const 2 (ParticleNoiseSpace.probability (J := J) μ N) aStar‖ ≤
        PBGSO.FullyUniformHigherOrder.discretizationConstant (forces.data) α γ Geo μ hμ a Variance hVariance ρ * Real.sqrt (h : ℝ) +
        (Real.sqrt Geo.conditionNumber * Real.exp (-ρ * (n * (h : ℝ))) *
          optimizerLawDistance a aStar μ νStar +
          (1 / ρ) * Real.sqrt (Geo.conditionNumber * Variance / (N : ℝ)) *
            (1 - Real.exp (-ρ * (n * (h : ℝ))))) := by
  apply PBGSO.FullyUniformHigherOrder.explicit_parameter_bound (D := forces.data) (α := α) (γ := γ) (Geo := Geo) (μ := μ) (hμ := hμ) (a := a) (Variance := Variance) (hVariance := hVariance) (hcloud := rfl) <;> assumption

#print axioms PBGSO.Standalone.NewB.theorem_new_b

end PBGSO.Standalone.NewB
