import PBGSO.FullyUniformMomentum
import PBGSO.UniformConstantExpansions

/-!
# Theorem New A: actual time-uniform M-MFPO bound

This is a reader-facing, checked theorem file. Primitive force assumptions,
all ambient variables, the source assumptions, explicit constants and final
inequalities are stated below; the proofs only apply the checked library.

`A` is the optimiser position space; `J` indexes each sampler's position
and Brownian coordinates. `N` is the positive particle count. The full
sampler state also includes its velocity.
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
  python3 scripts/check-pbgso-standalone.py --endpoint new-a --output /tmp/pbgso-new-a --check
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal InnerProductSpace RealInnerProductSpace
namespace PBGSO.Standalone.NewA
open PBGSO.Methods PBGSO.ImplementationDynamics PBGSO.FullyConstructedMomentum

variable {A J : Type*} {N : ℕ} [Fintype J] [DecidableEq J]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [FiniteDimensional ℝ A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  (γ : ℝ)

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

variable
  (Geometry : TwistedGeometry (HypocoercivePhase A) (HypocoercivePhase (EuclideanSpace ℝ J)))
  (μ : Measure (HypocoercivePhase (EuclideanSpace ℝ J))) [IsProbabilityMeasure μ]
  (hμ : MemLp (fun z : HypocoercivePhase (EuclideanSpace ℝ J) ↦ z) 2 μ)
  (a : HypocoercivePhase A) (Variance : ℝ)
  (hVariance : ∀ r, 0 ≤ r →
    (∫ z, ‖(model (forces.data) γ).observation
      ((model (forces.data) γ).parameter (AdditiveCanonical.optimizer (ULA.CanonicalBrownian.vectorProbability J)
        (momentumForceDynamics (forces.data) γ) μ hμ a (input γ) (input_continuous γ) (input_zero γ) r))
      ((model (forces.data) γ).position z) -
      (model (forces.data) γ).meanGradient (AdditiveCanonical.law (ULA.CanonicalBrownian.vectorProbability J)
        (momentumForceDynamics (forces.data) γ) μ hμ a (input γ) (input_continuous γ) (input_zero γ) r)
        (AdditiveCanonical.optimizer (ULA.CanonicalBrownian.vectorProbability J) (momentumForceDynamics (forces.data) γ)
          μ hμ a (input γ) (input_continuous γ) (input_zero γ) r)‖ ^ 2
      ∂AdditiveCanonical.law (ULA.CanonicalBrownian.vectorProbability J) (momentumForceDynamics (forces.data) γ)
        μ hμ a (input γ) (input_continuous γ) (input_zero γ) r) ≤ Variance)


/-! ## Explicit data-only constants
The following definitions repeat the exact library formulas. Cross-references
are qualified to make the correspondence directly inspectable. -/
/-- Coercivity of the constructed source metric in raw kinetic coordinates. -/
def metricCoercivity : ℝ := Real.sqrt (EmpiricalMetric.lower N Geometry) / 2

/-- Data-only upper norm bound for the constructed metric factor. -/
def metricUpper : ℝ := 2 * Real.sqrt (EmpiricalMetric.upper N Geometry)

/-- Actual Brownian increment radius, with the given nonnegative friction. -/
def noiseRadius (hγ : 0 ≤ γ) : ℝ :=
  momentumUniformBrownianRadius (I := Fin N × J) ⟨γ, hγ⟩

/-- State-independent part of the proved OBABO local Gaussian error. -/
def localConstant0 (hγ : 0 ≤ γ) : ℝ :=
  let Q := ParticleNoiseSpace.probability (J := J) μ N
  (momentumUniformDefect (momentumUniformForceLip (forces.data)) ⟨γ, hγ⟩
    ‖coupledForce ((forces.data).meanForceLp Q) ((forces.data).samplerForceLp Q) 0‖
    (Real.sqrt (Fintype.card (Fin N × J) : ℝ)) (PBGSO.FullyUniformMomentum.noiseRadius (N := N) (J := J) γ hγ)).1

/-- Linear initial-state part of the proved OBABO local Gaussian error. -/
def localConstant1 (hγ : 0 ≤ γ) : ℝ :=
  let Q := ParticleNoiseSpace.probability (J := J) μ N
  (momentumUniformDefect (momentumUniformForceLip (forces.data)) ⟨γ, hγ⟩
    ‖coupledForce ((forces.data).meanForceLp Q) ((forces.data).samplerForceLp Q) 0‖
    (Real.sqrt (Fintype.card (Fin N × J) : ℝ)) (PBGSO.FullyUniformMomentum.noiseRadius (N := N) (J := J) γ hγ)).2

/-- Explicit one-unit exact kinetic radius when started at zero. -/
def zeroStartRadius (hγ : 0 ≤ γ) : ℝ :=
  let Q := ParticleNoiseSpace.probability (J := J) μ N
  let γnn : ℝ≥0 := ⟨γ, hγ⟩
  UniformIntegral.radius (momentumUniformForceLip (forces.data) + γnn + 1)
    ‖coupledForce ((forces.data).meanForceLp Q) ((forces.data).samplerForceLp Q) 0‖
    (PBGSO.FullyUniformMomentum.noiseRadius (N := N) (J := J) γ hγ) 0

/-- Data-only transformed zero-start radius `S`. -/
def zeroStartMoment (hγ : 0 ≤ γ) : ℝ :=
  PBGSO.FullyUniformMomentum.metricUpper (N := N) Geometry * PBGSO.FullyUniformMomentum.zeroStartRadius (forces.data) γ μ hγ

/-- Uniform exact-reference radius, derived by contraction and unit restarts. -/
def referenceRadius (hγ : 0 ≤ γ) (ρ : ℝ) : ℝ :=
  let S := PBGSO.FullyUniformMomentum.zeroStartMoment (forces.data) γ Geometry μ hγ
  PBGSO.FullyUniformMomentum.metricUpper (N := N) Geometry * ‖initial (forces.data) γ Geometry μ hμ a Variance hVariance‖ +
    S / (1 - Real.exp (-ρ)) + S

/-- Linear-radius coefficient absorbed by exact-flow dissipation. -/
def radiusGrowth (hγ : 0 ≤ γ) : ℝ :=
  PBGSO.FullyUniformMomentum.metricUpper (N := N) Geometry * PBGSO.FullyUniformMomentum.localConstant1 (forces.data) γ μ hγ / PBGSO.FullyUniformMomentum.metricCoercivity (N := N) Geometry

/-- Explicit time-uniform numerical coefficient, independent of `h,n`. -/
def discretizationConstant (hγ : 0 ≤ γ) (ρ : ℝ) : ℝ :=
  4 * (PBGSO.FullyUniformMomentum.metricUpper (N := N) Geometry * PBGSO.FullyUniformMomentum.localConstant0 (forces.data) γ μ hγ +
    PBGSO.FullyUniformMomentum.radiusGrowth (forces.data) γ Geometry μ hγ * PBGSO.FullyUniformMomentum.referenceRadius (forces.data) γ Geometry μ hμ a Variance hVariance hγ ρ) /
      (ρ * PBGSO.FullyUniformMomentum.metricCoercivity (N := N) Geometry)

/-- Explicit positive upper step size; `hγ` only forms the physical friction. -/
def maximumStep (hγ : 0 ≤ γ) (ρ : ℝ) : ℝ :=
  UniformStep.maximumStep ρ (PBGSO.FullyUniformMomentum.radiusGrowth (forces.data) γ Geometry μ hγ)


/-- The displayed copied formulas are definitionally the exact constants in
the library theorem. This check detects drift between the readable contract
and the implementation without assuming any error bound. -/
theorem constants_match_source (hγ : 0 ≤ γ) (ρ : ℝ) :
    metricCoercivity (N := N) Geometry = PBGSO.FullyUniformMomentum.metricCoercivity (N := N) Geometry ∧
    metricUpper (N := N) Geometry = PBGSO.FullyUniformMomentum.metricUpper (N := N) Geometry ∧
    discretizationConstant (forces := forces) (γ := γ) (μ := μ) (Geometry := Geometry) (hμ := hμ) (a := a) (Variance := Variance) (hVariance := hVariance) (ρ := ρ) (hγ := hγ) = PBGSO.FullyUniformMomentum.discretizationConstant (forces.data) γ Geometry μ hμ a Variance hVariance hγ ρ ∧
    maximumStep (forces := forces) (γ := γ) (μ := μ) (Geometry := Geometry) (ρ := ρ) (hγ := hγ) = PBGSO.FullyUniformMomentum.maximumStep (forces.data) γ Geometry μ hγ ρ := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Closed arithmetic for the local coefficients
The identities here connect these arithmetic expressions to the exact
coefficients referenced above. No local-error premise is supplied. -/
namespace LocalErrorFormulas
def momentumExpandedConstant0 (L γ fzero Ξ β : ℝ) : ℝ :=
  ((γ + 1) / 2 + L / 4) * fzero +
    (L / 2 + Real.sqrt γ + (3 / 2 : ℝ) * γ * Real.sqrt γ) * Ξ +
    (2 / 3 : ℝ) * (L + γ + 1) *
      (fzero + (L + γ + 1) * Real.exp (L + γ + 2) * (fzero + β) + β)

def momentumExpandedConstant1 (L γ : ℝ) : ℝ :=
  (γ ^ 2 + γ + L) / 2 + ((γ + 1) / 2 + L / 4) * L +
    (2 / 3 : ℝ) * (L + γ + 1) ^ 2 * Real.exp (L + γ + 2)

theorem momentumUniformDefect_expanded (L γ : ℝ≥0) (fzero Ξ β : ℝ) :
    momentumUniformDefect L γ fzero Ξ β =
      (momentumExpandedConstant0 L γ fzero Ξ β,
       momentumExpandedConstant1 L γ) := by
  exact PBGSO.Methods.momentumUniformDefect_expanded L γ fzero Ξ β

end LocalErrorFormulas

/-! ## Positive maximum step and full-state discretisation bound -/
theorem step_and_discretization_bound (hγ : 0 ≤ γ)
    (star : A) (νStar : Measure (HypocoercivePhase (EuclideanSpace ℝ J))) [IsProbabilityMeasure νStar]
    (hνStar : MemLp (fun z : HypocoercivePhase (EuclideanSpace ℝ J) ↦ z) 2 νStar)
    (Frozen : AdditiveStationary.FrozenTrajectory (ULA.CanonicalBrownian.vectorProbability J)
      (momentumForceDynamics (forces.data) γ) νStar hνStar (targetState star) (input γ))
    (ρ : ℝ) (hρ : 0 < ρ) (hmono : TwistedJointMonotonicity (model (forces.data) γ) Geometry ρ)
    (hg : (model (forces.data) γ).meanGradient νStar (targetState star) = 0)
    (hV : 0 ≤ Variance) :
    0 < PBGSO.FullyUniformMomentum.maximumStep (forces.data) γ Geometry μ hγ ρ ∧
      0 ≤ PBGSO.FullyUniformMomentum.discretizationConstant (forces.data) γ Geometry μ hμ a Variance hVariance hγ ρ ∧
      ∀ h : ℝ, 0 < h → h ≤ PBGSO.FullyUniformMomentum.maximumStep (forces.data) γ Geometry μ hγ ρ → ∀ n : ℕ,
        (‖momentumParticleIterate (ParticleNoiseSpace.probability (J := J) μ N)
          (particleBrownian (J := J) μ N) (particleBrownian_isPreBrownian (J := J) μ N)
          (forces.data) γ h (initial (forces.data) γ Geometry μ hμ a Variance hVariance) n -
          momentumUnpackLp (ParticleNoiseSpace.probability (J := J) μ N) (forces.data)
            ((particles (forces.data) γ Geometry μ hμ a Variance hVariance).state (n*h))‖ ≤ PBGSO.FullyUniformMomentum.discretizationConstant (forces.data) γ Geometry μ hμ a Variance hVariance hγ ρ * Real.sqrt h) ∧
        ‖(momentumParticleIterate (ParticleNoiseSpace.probability (J := J) μ N)
          (particleBrownian (J := J) μ N) (particleBrownian_isPreBrownian (J := J) μ N)
          (forces.data) γ h (initial (forces.data) γ Geometry μ hμ a Variance hVariance) n).2.1 -
          Lp.const 2 (ParticleNoiseSpace.probability (J := J) μ N) star‖ ≤
        PBGSO.FullyUniformMomentum.discretizationConstant (forces.data) γ Geometry μ hμ a Variance hVariance hγ ρ * Real.sqrt h +
        (Real.sqrt Geometry.conditionNumber * Real.exp (-ρ * (n*h)) *
          optimizerLawDistance a (targetState star) μ νStar +
          ((2+γ)/ρ) * Real.sqrt (Geometry.conditionNumber * Variance/(N : ℝ)) *
            (1-Real.exp (-ρ * (n*h)))) := by
  apply PBGSO.FullyUniformMomentum.explicit_guarantee (D := forces.data) (γ := γ) (Geometry := Geometry) (μ := μ) (hμ := hμ) (a := a) (Variance := Variance) (hVariance := hVariance) (hcloud := rfl) <;> assumption

#print axioms PBGSO.Standalone.NewA.step_and_discretization_bound

/-! ## Final numerical parameter bound -/
theorem theorem_new_a (hγ : 0 ≤ γ)
    (star : A) (νStar : Measure (HypocoercivePhase (EuclideanSpace ℝ J))) [IsProbabilityMeasure νStar]
    (hνStar : MemLp (fun z : HypocoercivePhase (EuclideanSpace ℝ J) ↦ z) 2 νStar)
    (Frozen : AdditiveStationary.FrozenTrajectory (ULA.CanonicalBrownian.vectorProbability J)
      (momentumForceDynamics (forces.data) γ) νStar hνStar (targetState star) (input γ))
    (ρ : ℝ) (hρ : 0 < ρ) (hmono : TwistedJointMonotonicity (model (forces.data) γ) Geometry ρ)
    (hg : (model (forces.data) γ).meanGradient νStar (targetState star) = 0)
    (hV : 0 ≤ Variance)
    (h : ℝ) (hh : 0 < h) (hhmax : h ≤ PBGSO.FullyUniformMomentum.maximumStep (forces.data) γ Geometry μ hγ ρ) (n : ℕ) :
        ‖(momentumParticleIterate (ParticleNoiseSpace.probability (J := J) μ N)
          (particleBrownian (J := J) μ N) (particleBrownian_isPreBrownian (J := J) μ N)
          (forces.data) γ h (initial (forces.data) γ Geometry μ hμ a Variance hVariance) n).2.1 -
          Lp.const 2 (ParticleNoiseSpace.probability (J := J) μ N) star‖ ≤
        PBGSO.FullyUniformMomentum.discretizationConstant (forces.data) γ Geometry μ hμ a Variance hVariance hγ ρ * Real.sqrt h +
        (Real.sqrt Geometry.conditionNumber * Real.exp (-ρ * (n*h)) *
          optimizerLawDistance a (targetState star) μ νStar +
          ((2+γ)/ρ) * Real.sqrt (Geometry.conditionNumber * Variance/(N : ℝ)) *
            (1-Real.exp (-ρ * (n*h)))) := by
  apply PBGSO.FullyUniformMomentum.explicit_parameter_bound (D := forces.data) (γ := γ) (Geometry := Geometry) (μ := μ) (hμ := hμ) (a := a) (Variance := Variance) (hVariance := hVariance) (hcloud := rfl) <;> assumption

#print axioms PBGSO.Standalone.NewA.theorem_new_a

end PBGSO.Standalone.NewA
