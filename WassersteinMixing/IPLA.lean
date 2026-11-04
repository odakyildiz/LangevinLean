import WassersteinMixing.IPLABridge
import IPLA.Concentration
import IPLA.Dynamics
import IPLA.Foundations

set_option linter.style.header false

/-! # New linear-step parameter bounds for actual Gaussian IPLA

The setting below contains only the joint potential's structural assumptions
and the algorithm's numerical parameters. The invariant measure, transport
comparison and parameter concentration are all proved, not supplied inputs.
The extra C² regularity and the small-step range relative to Project 03 are
explicit. The actual Gaussian law is identified with every implementation
satisfying IPLA's original independent-innovation specification.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace WassersteinMixing

/-- Structural assumptions of the new IPLA application. Unlike Project 03,
this sharp-step application explicitly requires twice continuous differentiability. -/
structure IPLASetting where
  N : ℕ
  dθ : ℕ
  dx : ℕ
  U : IPLA.Joint dθ dx → ℝ
  m : ℝ
  L : ℝ≥0
  γ : ℝ
  particles_pos : 0 < N
  curvature_pos : 0 < m
  curvature_le_smoothness : m ≤ L
  step_pos : 0 < γ
  step_small : γ * L ≤ 1
  regularity : ContDiff ℝ 2 U
  strongConvexity : StrongConvexOn univ m U
  gradientLipschitz : LipschitzWith L (gradient U)

/-- The exact lifted parameters; no particle factor is hidden in the step. -/
def IPLASetting.parameters (A : IPLASetting) : Parameters :=
  iplaParameters A.N A.dθ A.dx A.m A.L A.γ A.particles_pos A.curvature_pos
    A.curvature_le_smoothness A.step_pos A.step_small

/-- All analytic assumptions for the lifted potential follow from the joint potential. -/
theorem IPLASetting.potentialAssumptions (A : IPLASetting) :
    PotentialAssumptions A.parameters (@IPLA.potential A.N A.dθ A.dx A.U) :=
  ipla_potentialAssumptions A.particles_pos A.curvature_pos A.curvature_le_smoothness
    A.step_pos A.step_small A.regularity A.strongConvexity A.gradientLipschitz

/-- The invariant law constructed by the sharp theorem, in the actual scaled state. -/
def IPLASetting.invariantLaw (A : IPLASetting) : Measure (IPLA.State A.N A.dθ A.dx) :=
  coordinateInvariantLaw A.parameters (iplaCoordinates A.N A.dθ A.dx)
    (IPLA.potential A.U) A.potentialAssumptions

/-- Iteration of the actual independent-Gaussian IPLA kernel in scaled coordinates. -/
def IPLASetting.law (A : IPLASetting) (μ : Measure (IPLA.State A.N A.dθ A.dx))
    (k : ℕ) : Measure (IPLA.State A.N A.dθ A.dx) :=
  (ULA.ulaLawStep (IPLA.potential A.U) (A.γ / A.N))^[k] μ

/-- Every Gaussian implementation of IPLA has exactly the displayed kernel laws. -/
theorem IPLASetting.law_eq_gaussian (A : IPLASetting)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (initial : Lp (IPLA.State A.N A.dθ A.dx) 2 P)
    (noise : ℕ → Lp (IPLA.State A.N A.dθ A.dx) 2 P)
    (hGaussian : IPLA.GaussianInnovations P initial noise) (k : ℕ) :
    A.law (P.map initial) k = IPLA.laws P A.U A.γ A.L
      (A.regularity.differentiable (by norm_num)) A.gradientLipschitz initial noise k := by
  exact (IPLA.laws_eq_ulaLawStep P A.U A.γ A.L
    (A.regularity.differentiable (by norm_num)) A.gradientLipschitz
    initial noise hGaussian k).symm

/-- The statistical radius of the exact parameter marginal. -/
def IPLASetting.radius (A : IPLASetting) : ℝ :=
  Real.sqrt (2 * (A.dθ : ℝ) / ((A.N : ℝ) * A.m))

/-- The linear-step discretization error, with the exact effective dimension. -/
def IPLASetting.bias (A : IPLASetting) : ℝ :=
  iplaLinearBias A.m A.L A.γ (iplaEffectiveDimension A.N A.dθ A.dx)

/-- Projection to the parameter costs no factor depending on particle number. -/
theorem ipla_parameter_projection (A : IPLASetting)
    (θStar : EuclideanSpace ℝ (Fin A.dθ)) (hmax : IPLA.IsMarginalMaximizer A.U θStar)
    (μ : Measure (IPLA.State A.N A.dθ A.dx)) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : IPLA.State A.N A.dθ A.dx → IPLA.State A.N A.dθ A.dx) 2 μ)
    (k : ℕ) :
    Real.sqrt (∫ z, ‖IPLA.parameterCLM z - θStar‖ ^ 2 ∂A.law μ k) ≤
      ULA.wasserstein2Real (A.law μ k) (@IPLA.gibbsTarget A.N A.dθ A.dx A.U) +
        A.radius := by
  have hfinite := coordinate_convergence_finite A.parameters
    (iplaCoordinates A.N A.dθ A.dx) (IPLA.potential A.U) A.potentialAssumptions μ hμ k
  have hc := IPLA.gibbsTarget_parameter_concentration A.particles_pos A.U A.m
    A.curvature_pos (A.regularity.differentiable (by norm_num)) A.strongConvexity θStar hmax
  have hp := IPLA.projectedRMSReal_le_wasserstein2Real_add
    (@IPLA.parameterCLM A.N A.dθ A.dx) IPLA.norm_parameterCLM_le_one θStar A.radius
    (Real.sqrt_nonneg _) hfinite hc
  have hmom := IPLA.projectedRMS_ne_top
    (@IPLA.parameterCLM A.N A.dθ A.dx) IPLA.norm_parameterCLM_le_one θStar A.radius
    hfinite hc
  rw [IPLA.projectedRMSReal_eq_sqrt_integral _ _ _ hmom] at hp
  exact hp

/-- Theorem A: the actual IPLA parameter RMS has a linear-step bias. -/
theorem ipla_parameter_error (A : IPLASetting)
    (θStar : EuclideanSpace ℝ (Fin A.dθ)) (hmax : IPLA.IsMarginalMaximizer A.U θStar)
    (μ : Measure (IPLA.State A.N A.dθ A.dx)) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : IPLA.State A.N A.dθ A.dx → IPLA.State A.N A.dθ A.dx) 2 μ)
    (k : ℕ) :
    Real.sqrt (∫ z, ‖IPLA.parameterCLM z - θStar‖ ^ 2 ∂A.law μ k) ≤
      A.radius + (1 - A.m * A.γ) ^ k * ULA.wasserstein2Real μ A.invariantLaw + A.bias := by
  have ht := ipla_wasserstein_bound A.particles_pos A.curvature_pos
    A.curvature_le_smoothness A.step_pos A.step_small A.regularity A.strongConvexity
    A.gradientLipschitz μ hμ k
  have hp := ipla_parameter_projection A θStar hmax μ hμ k
  change ULA.wasserstein2Real (A.law μ k) (@IPLA.gibbsTarget A.N A.dθ A.dx A.U) ≤
    (1 - A.m * A.γ) ^ k * ULA.wasserstein2Real μ A.invariantLaw + A.bias at ht
  linarith

/-- Theorem B: the initialization distance is to the exact target, as in Project 03. -/
theorem ipla_parameter_error_target (A : IPLASetting)
    (θStar : EuclideanSpace ℝ (Fin A.dθ)) (hmax : IPLA.IsMarginalMaximizer A.U θStar)
    (μ : Measure (IPLA.State A.N A.dθ A.dx)) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : IPLA.State A.N A.dθ A.dx → IPLA.State A.N A.dθ A.dx) 2 μ)
    (k : ℕ) :
    Real.sqrt (∫ z, ‖IPLA.parameterCLM z - θStar‖ ^ 2 ∂A.law μ k) ≤
      A.radius + (1 - A.m * A.γ) ^ k *
        ULA.wasserstein2Real μ (@IPLA.gibbsTarget A.N A.dθ A.dx A.U) +
        A.bias := by
  have ht := coordinate_convergence_target_bound_sharp A.parameters
    (iplaCoordinates A.N A.dθ A.dx) (IPLA.potential A.U) A.potentialAssumptions μ hμ k
  have hn : (A.N : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast A.particles_pos)
  have hq : (A.N : ℝ) * A.m * (A.γ / A.N) = A.m * A.γ := by field_simp
  have hb : A.parameters.bias = A.bias := by
    exact ipla_lifted_bias_eq A.N A.dθ A.dx A.particles_pos A.m A.L A.γ
  rw [hb] at ht
  have ht' : ULA.wasserstein2Real (A.law μ k)
      (@IPLA.gibbsTarget A.N A.dθ A.dx A.U) ≤
      (1 - A.m * A.γ) ^ k *
        ULA.wasserstein2Real μ (@IPLA.gibbsTarget A.N A.dθ A.dx A.U) +
        A.bias := by
    simpa only [IPLASetting.law, Parameters.contraction, IPLASetting.parameters,
      iplaParameters, hq, IPLA.gibbsTarget_eq_gibbsMeasure] using ht
  have hp := ipla_parameter_projection A θStar hmax μ hμ k
  linarith

/-- The weaker doubled-bias estimate is retained as a convenience corollary. -/
theorem ipla_parameter_error_target_uniform (A : IPLASetting)
    (θStar : EuclideanSpace ℝ (Fin A.dθ)) (hmax : IPLA.IsMarginalMaximizer A.U θStar)
    (μ : Measure (IPLA.State A.N A.dθ A.dx)) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : IPLA.State A.N A.dθ A.dx → IPLA.State A.N A.dθ A.dx) 2 μ)
    (k : ℕ) :
    Real.sqrt (∫ z, ‖IPLA.parameterCLM z - θStar‖ ^ 2 ∂A.law μ k) ≤
      A.radius + (1 - A.m * A.γ) ^ k *
        ULA.wasserstein2Real μ (@IPLA.gibbsTarget A.N A.dθ A.dx A.U) + 2 * A.bias := by
  have ht := ipla_parameter_error_target A θStar hmax μ hμ k
  have hb : 0 ≤ A.bias :=
    mul_nonneg (mul_nonneg (by norm_num) A.step_pos.le) (Real.sqrt_nonneg _)
  linarith

/-- Direct domination of Project 03's complete right-hand side in the common
regularity class and the stated small-step regime. -/
theorem ipla_parameter_error_improves_project03 (A : IPLASetting)
    (θStar : EuclideanSpace ℝ (Fin A.dθ)) (hmax : IPLA.IsMarginalMaximizer A.U θStar)
    (μ : Measure (IPLA.State A.N A.dθ A.dx)) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : IPLA.State A.N A.dθ A.dx → IPLA.State A.N A.dθ A.dx) 2 μ)
    (k : ℕ) (hsmall : A.m * A.γ ≤ (121 / 1600 : ℝ)) :
    Real.sqrt (∫ z, ‖IPLA.parameterCLM z - θStar‖ ^ 2 ∂A.law μ k) ≤
      A.radius + (1 - A.m * A.γ) ^ k *
        ULA.wasserstein2Real μ (@IPLA.gibbsTarget A.N A.dθ A.dx A.U) +
        iplaProject03Bias A.m A.L A.γ (iplaEffectiveDimension A.N A.dθ A.dx) := by
  have ht := ipla_parameter_error_target A θStar hmax μ hμ k
  have hb := ipla_linear_bias_le_project03 A.m A.L A.γ
    (iplaEffectiveDimension A.N A.dθ A.dx) A.curvature_pos A.L.coe_nonneg A.step_pos.le
    (iplaEffectiveDimension_nonneg A.N A.dθ A.dx) hsmall
  exact ht.trans (add_le_add_right hb _ |>.trans_eq (by ring))

/-- Theorem C: explicit particle, step and iteration choices for normalized accuracy. -/
theorem ipla_parameter_accuracy (A : IPLASetting)
    (θStar : EuclideanSpace ℝ (Fin A.dθ)) (hmax : IPLA.IsMarginalMaximizer A.U θStar)
    (μ : Measure (IPLA.State A.N A.dθ A.dx)) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : IPLA.State A.N A.dθ A.dx → IPLA.State A.N A.dθ A.dx) 2 μ)
    (ε : ℝ) (hε : 0 < ε)
    (hparticles : 18 * (A.dθ : ℝ) ≤ (A.N : ℝ) * ε ^ 2)
    (hstep : A.γ = iplaAccuracyStep A.L (iplaEffectiveDimension A.N A.dθ A.dx) ε)
    (k : ℕ)
    (hk : iplaAccuracyPrefactor A.m A.L (iplaEffectiveDimension A.N A.dθ A.dx) ε *
      Real.log (1 + 3 * Real.sqrt A.m * ULA.wasserstein2Real μ A.invariantLaw / ε) ≤ k) :
    Real.sqrt A.m *
      Real.sqrt (∫ z, ‖IPLA.parameterCLM z - θStar‖ ^ 2 ∂A.law μ k) ≤ ε := by
  have he := mul_le_mul_of_nonneg_left (ipla_parameter_error A θStar hmax μ hμ k)
    (Real.sqrt_nonneg A.m)
  have ha := ipla_accuracy_arithmetic A.N A.dθ A.particles_pos A.m A.L
    (iplaEffectiveDimension A.N A.dθ A.dx) (ULA.wasserstein2Real μ A.invariantLaw) ε
    A.curvature_pos A.curvature_le_smoothness (iplaEffectiveDimension_nonneg _ _ _)
    ENNReal.toReal_nonneg hε hparticles k hk
  have hc := ipla_concentration_scale A.N A.dθ A.particles_pos A.m A.curvature_pos
  unfold IPLASetting.radius IPLASetting.bias at he
  rw [hstep] at he
  nlinarith

/-- The same accuracy guarantee with the exact-target initialization distance. -/
theorem ipla_parameter_accuracy_target (A : IPLASetting)
    (θStar : EuclideanSpace ℝ (Fin A.dθ)) (hmax : IPLA.IsMarginalMaximizer A.U θStar)
    (μ : Measure (IPLA.State A.N A.dθ A.dx)) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : IPLA.State A.N A.dθ A.dx → IPLA.State A.N A.dθ A.dx) 2 μ)
    (ε : ℝ) (hε : 0 < ε)
    (hparticles : 18 * (A.dθ : ℝ) ≤ (A.N : ℝ) * ε ^ 2)
    (hstep : A.γ = iplaAccuracyStep A.L (iplaEffectiveDimension A.N A.dθ A.dx) ε)
    (k : ℕ)
    (hk : iplaAccuracyPrefactor A.m A.L (iplaEffectiveDimension A.N A.dθ A.dx) ε *
      Real.log (1 + 3 * Real.sqrt A.m *
        ULA.wasserstein2Real μ (@IPLA.gibbsTarget A.N A.dθ A.dx A.U) / ε) ≤ k) :
    Real.sqrt A.m *
      Real.sqrt (∫ z, ‖IPLA.parameterCLM z - θStar‖ ^ 2 ∂A.law μ k) ≤ ε := by
  have he := mul_le_mul_of_nonneg_left
    (ipla_parameter_error_target A θStar hmax μ hμ k) (Real.sqrt_nonneg A.m)
  have ha := ipla_accuracy_arithmetic A.N A.dθ A.particles_pos A.m A.L
    (iplaEffectiveDimension A.N A.dθ A.dx)
    (ULA.wasserstein2Real μ (@IPLA.gibbsTarget A.N A.dθ A.dx A.U)) ε A.curvature_pos
    A.curvature_le_smoothness (iplaEffectiveDimension_nonneg _ _ _) ENNReal.toReal_nonneg
    hε hparticles k hk
  have hc := ipla_concentration_scale A.N A.dθ A.particles_pos A.m A.curvature_pos
  unfold IPLASetting.radius IPLASetting.bias at he
  rw [hstep] at he
  nlinarith

/-- The sharp new rate in exactly the original Gaussian IPLA implementation API.
All setting fields and the finite initial law moment are constructed here from
the displayed structural assumptions and square-integrable initialization. -/
theorem ipla_gaussian_parameter_error
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N dθ dx : ℕ) (hN : 0 < N) (U : IPLA.Joint dθ dx → ℝ)
    (m γ : ℝ) (L : ℝ≥0) (hm : 0 < m) (hmL : m ≤ L)
    (hγ : 0 < γ) (hγL : γ * L ≤ 1)
    (hU : ContDiff ℝ 2 U) (hsc : StrongConvexOn univ m U)
    (hLip : LipschitzWith L (gradient U))
    (θStar : EuclideanSpace ℝ (Fin dθ)) (hmax : IPLA.IsMarginalMaximizer U θStar)
    (initial : Lp (IPLA.State N dθ dx) 2 P)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 P)
    (hGaussian : IPLA.GaussianInnovations P initial noise) (k : ℕ) :
    Real.sqrt (∫ z, ‖IPLA.parameterCLM z - θStar‖ ^ 2
      ∂IPLA.laws P U γ L (hU.differentiable (by norm_num)) hLip initial noise k) ≤
      Real.sqrt (2 * (dθ : ℝ) / ((N : ℝ) * m)) +
        (1 - m * γ) ^ k * ULA.wasserstein2Real (P.map initial)
          (@IPLA.gibbsTarget N dθ dx U) +
        iplaLinearBias m L γ (iplaEffectiveDimension N dθ dx) := by
  let A : IPLASetting :=
    { N := N, dθ := dθ, dx := dx, U := U, m := m, L := L, γ := γ
      particles_pos := hN, curvature_pos := hm, curvature_le_smoothness := hmL
      step_pos := hγ, step_small := hγL, regularity := hU
      strongConvexity := hsc, gradientLipschitz := hLip }
  have hμ : MemLp (id : IPLA.State N dθ dx → IPLA.State N dθ dx) 2
      (P.map initial) :=
    (memLp_map_measure_iff (by fun_prop)
      (Lp.aestronglyMeasurable initial).aemeasurable).mpr (Lp.memLp initial)
  have h := ipla_parameter_error_target A θStar hmax (P.map initial) hμ k
  rw [A.law_eq_gaussian P initial noise hGaussian k] at h
  exact h

end WassersteinMixing
