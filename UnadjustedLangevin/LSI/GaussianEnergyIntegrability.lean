import UnadjustedLangevin.LSI.GaussianMeasurability
import UnadjustedLangevin.LSI.EntropyEndpoint
import UnadjustedLangevin.GaussianProposalPairDensity

set_option linter.style.header false

/-! # Quantitative spacetime energy bounds for the actual Gaussian interpolation

The relative score splits into the potential gradient and the Lebesgue score.
The Gaussian Fisher bound and the propagated gradient moment give integrable
energy on every compact positive-time interval. The frozen gradient error is
controlled on the fixed initial-state/noise product space, avoiding a
parameter-dependent choice of conditional expectation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ULA.LSI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
private theorem norm_add_sq_le_two (x y : E) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := norm_add_le x y
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr h
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- Relative Fisher energy is bounded by the propagated gradient energy and
`d/t`, the Gaussian smoothing term. -/
theorem interpolationRelativeScoreField_energy_le
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (L : ℝ≥0) (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hG : Integrable (fun x ↦ ‖gradient U x‖ ^ 2) μ) (t : ℝ) (ht : 0 < t) :
    Integrable (fun y ↦ ‖interpolationRelativeScoreField U μ t y‖ ^ 2)
      (interpolationLaw U μ t) ∧
      (∫ y, ‖interpolationRelativeScoreField U μ t y‖ ^ 2 ∂interpolationLaw U μ t) ≤
        2 * (∫ y, ‖gradient U y‖ ^ 2 ∂interpolationLaw U μ t) +
          (Module.finrank ℝ E : ℝ) / t := by
  have hgrad : MemLp (gradient U) 2 μ :=
    (memLp_two_iff_integrable_sq_norm hLip.continuous.aestronglyMeasurable).mpr hG
  have hs := (interpolationRelativeScore_memLp U μ L hU hLip hgrad t ht).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)
  have heq (y : E) := interpolationRelativeScoreField_eq U μ L hU hLip t ht y
  have hi : Integrable (fun y ↦ ‖interpolationRelativeScoreField U μ t y‖ ^ 2)
      (interpolationLaw U μ t) := by
    simpa only [heq] using hs
  have hGi := (interpolationLaw_gradient_moment U L hLip μ hG t ht.le).1
  have hLeb := interpolationLebesgue_fisher_bound U μ L hLip t ht
  have hp (y : E) : ‖interpolationRelativeScoreField U μ t y‖ ^ 2 ≤
      2 * ‖gradient U y‖ ^ 2 +
        2 * ‖gradient (fun y ↦ Real.log (interpolationLebesgueDensity U μ t y)) y‖ ^ 2 := by
    rw [heq, gradient_log_interpolationRelativeDensity U μ L hU hLip t ht y]
    exact norm_add_sq_le_two _ _
  have hb := integral_mono hi
    (by simpa only [Pi.add_def] using (hGi.const_mul 2).add (hLeb.1.const_mul 2)) hp
  rw [integral_add (hGi.const_mul 2) (hLeb.1.const_mul 2), integral_const_mul,
    integral_const_mul] at hb
  refine ⟨hi, hb.trans ?_⟩
  have hdiv : 2 * ((Module.finrank ℝ E : ℝ) / (2 * t)) =
      (Module.finrank ℝ E : ℝ) / t := by ring
  nlinarith [hLeb.2]

/-- Explicit relative-Fisher bound entirely in terms of the initial gradient
moment, dimension, smoothness, and positive interpolation time. -/
theorem interpolationRelativeScoreField_energy_bound
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (L : ℝ≥0) (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hG : Integrable (fun x ↦ ‖gradient U x‖ ^ 2) μ) (t : ℝ) (ht : 0 < t) :
    (∫ y, ‖interpolationRelativeScoreField U μ t y‖ ^ 2 ∂interpolationLaw U μ t) ≤
      4 * (1 + (L : ℝ) ^ 2 * t ^ 2) * (∫ x, ‖gradient U x‖ ^ 2 ∂μ) +
        8 * t * (Module.finrank ℝ E : ℝ) * (L : ℝ) ^ 2 +
        (Module.finrank ℝ E : ℝ) / t := by
  have h := (interpolationRelativeScoreField_energy_le U μ L hU hLip hG t ht).2
  have h' := (interpolationLaw_gradient_moment U L hLip μ hG t ht.le).2
  nlinarith

/-- The same energy is a genuine weighted integral under the fixed Gibbs law,
with integrability derived by the actual relative-density identification. -/
theorem interpolationRelativeScoreField_weighted_energy
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (L : ℝ≥0) (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hG : Integrable (fun x ↦ ‖gradient U x‖ ^ 2) μ) (t : ℝ) (ht : 0 < t) :
    Integrable (fun y ↦ interpolationRelativeDensity U μ t y *
      ‖interpolationRelativeScoreField U μ t y‖ ^ 2) (ULA.gibbsMeasure U) ∧
      (∫ y, interpolationRelativeDensity U μ t y *
        ‖interpolationRelativeScoreField U μ t y‖ ^ 2 ∂ULA.gibbsMeasure U) =
        ∫ y, ‖interpolationRelativeScoreField U μ t y‖ ^ 2 ∂interpolationLaw U μ t := by
  have hrm := interpolationRelativeDensity_measurable U μ L hU hLip t
  have hr := interpolationRelativeDensity_pos U μ L hU hLip t ht
  have hi := (interpolationRelativeScoreField_energy_le U μ L hU hLip hG t ht).1
  rw [← tiltedMeasure_interpolationRelativeDensity U μ L hU hLip t ht] at hi
  constructor
  · unfold tiltedMeasure at hi
    have hh := (integrable_withDensity_iff_integrable_smul' hrm.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).mp hi
    simpa only [ENNReal.toReal_ofReal (hr _).le, smul_eq_mul] using hh
  · rw [← tiltedMeasure_interpolationRelativeDensity U μ L hU hLip t ht,
      integral_tiltedMeasure (ULA.gibbsMeasure U) (interpolationRelativeDensity U μ t)
        hrm (fun y ↦ (hr y).le)]

/-- Relative Fisher energy is L¹ jointly in time and space on every compact
positive-time interval, under a single fixed Gibbs reference measure. -/
theorem integrable_interpolationRelativeScoreField_energy_spacetime
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (L : ℝ≥0) (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hG : Integrable (fun x ↦ ‖gradient U x‖ ^ 2) μ) (a b : ℝ) (ha : 0 < a) :
    Integrable (fun p : ℝ × E ↦ interpolationRelativeDensity U μ p.1 p.2 *
      ‖interpolationRelativeScoreField U μ p.1 p.2‖ ^ 2)
      ((volume.restrict (Icc a b)).prod (ULA.gibbsMeasure U)) := by
  let G := ∫ x, ‖gradient U x‖ ^ 2 ∂μ
  let C := 4 * (1 + (L : ℝ) ^ 2 * b ^ 2) * G +
    8 * b * (Module.finrank ℝ E : ℝ) * (L : ℝ) ^ 2 + (Module.finrank ℝ E : ℝ) / a
  have hG0 : 0 ≤ G := integral_nonneg fun _ ↦ sq_nonneg _
  have hm : StronglyMeasurable (fun p : ℝ × E ↦ interpolationRelativeDensity U μ p.1 p.2 *
      ‖interpolationRelativeScoreField U μ p.1 p.2‖ ^ 2) := by
    exact (interpolationRelativeDensity_joint_measurable U μ L hU hLip).stronglyMeasurable.mul
      ((interpolationRelativeScoreField_stronglyMeasurable U μ L hLip).norm.pow 2)
  have hnonneg (t : ℝ) (y : E) : 0 ≤ interpolationRelativeDensity U μ t y *
      ‖interpolationRelativeScoreField U μ t y‖ ^ 2 := by
    have hr : 0 ≤ interpolationRelativeDensity U μ t y :=
      mul_nonneg (mul_nonneg ENNReal.toReal_nonneg (Real.exp_nonneg _)) ENNReal.toReal_nonneg
    exact mul_nonneg hr (sq_nonneg _)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (interpolationRelativeScoreField_weighted_energy U μ L hU hLip hG t
      (lt_of_lt_of_le ha ht.1)).1
  · apply (integrable_const C).mono' hm.norm.integral_prod_right.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have htpos : 0 < t := lt_of_lt_of_le ha ht.1
    have hbpos : 0 < b := lt_of_lt_of_le htpos ht.2
    have henergy := interpolationRelativeScoreField_energy_bound U μ L hU hLip hG t htpos
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg t _)]
    rw [(interpolationRelativeScoreField_weighted_energy U μ L hU hLip hG t htpos).2]
    rw [abs_of_nonneg (integral_nonneg fun y ↦ sq_nonneg
      (‖interpolationRelativeScoreField U μ t y‖))]
    apply henergy.trans
    dsimp [C, G]
    gcongr <;> first | exact ht.1 | exact ht.2

/-- The frozen gradient error, on the fixed independent initial/noise space. -/
def frozenGradientErrorField (U : E → ℝ) (t : ℝ) (p : E × E) : E :=
  gradient U (ULA.malaProposal U t p.1 p.2) - gradient U p.1

/-- The frozen gradient-error energy is jointly integrable in time and the
fixed initial/noise variables on every compact nonnegative interval. -/
theorem integrable_frozenGradientErrorField_energy_spacetime
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (hG : Integrable (fun x ↦ ‖gradient U x‖ ^ 2) μ) (a b : ℝ) (ha : 0 ≤ a) :
    Integrable (fun p : ℝ × (E × E) ↦ ‖frozenGradientErrorField U p.1 p.2‖ ^ 2)
      ((volume.restrict (Icc a b)).prod (μ.prod (stdGaussian E))) := by
  let C := b ^ 2 * (L : ℝ) ^ 2 * (∫ x, ‖gradient U x‖ ^ 2 ∂μ) +
    2 * b * (Module.finrank ℝ E : ℝ) * (L : ℝ) ^ 2
  have hg := hLip.continuous
  have hm : StronglyMeasurable (fun p : ℝ × (E × E) ↦
      ‖frozenGradientErrorField U p.1 p.2‖ ^ 2) := by
    unfold frozenGradientErrorField ULA.malaProposal
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (frozen_gradient_error_energy μ U L hLip hG t (ha.trans ht.1)).1
  · apply (integrable_const C).mono' hm.norm.integral_prod_right.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hinner : (∫ p : E × E, ‖‖frozenGradientErrorField U t p‖ ^ 2‖
        ∂μ.prod (stdGaussian E)) =
        ∫ p : E × E, ‖frozenGradientErrorField U t p‖ ^ 2 ∂μ.prod (stdGaussian E) := by
      apply integral_congr_ae
      exact ae_of_all _ fun p ↦ Real.norm_of_nonneg (sq_nonneg _)
    rw [hinner, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun p ↦
      sq_nonneg (‖frozenGradientErrorField U t p‖))]
    have h := (frozen_gradient_error_energy μ U L hLip hG t (ha.trans ht.1)).2
    apply h.trans
    dsimp [C]
    have ht0 : 0 ≤ t := ha.trans ht.1
    have hG0 : 0 ≤ ∫ x, ‖gradient U x‖ ^ 2 ∂μ := integral_nonneg fun _ ↦ sq_nonneg _
    calc
      _ ≤ (L : ℝ) ^ 2 * (b ^ 2 * (∫ x, ‖gradient U x‖ ^ 2 ∂μ) +
          2 * b * (Module.finrank ℝ E : ℝ)) := by
        gcongr <;> exact ht.2
      _ = _ := by ring


/-- Exact frozen gradient-error energy on the actual initial/output pair law.
The bound is transported from the independent Gaussian noise calculation. -/
theorem frozenGaussianPair_gradient_error_energy
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (hG : Integrable (fun x ↦ ‖gradient U x‖ ^ 2) μ) (t : ℝ) (ht : 0 ≤ t) :
    let P := (μ.prod (stdGaussian E)).map
      (fun z : E × E ↦ (z.1, ULA.malaProposal U t z.1 z.2))
    Integrable (fun z : E × E ↦ ‖gradient U z.2 - gradient U z.1‖ ^ 2) P ∧
      (∫ z : E × E, ‖gradient U z.2 - gradient U z.1‖ ^ 2 ∂P) ≤
        (L : ℝ) ^ 2 * (t ^ 2 * (∫ x, ‖gradient U x‖ ^ 2 ∂μ) +
          2 * t * (Module.finrank ℝ E : ℝ)) := by
  have hY := ULA.malaProposal_measurable U t L hLip
  have hT := measurable_fst.prodMk hY
  have hg := hLip.continuous
  have hF : StronglyMeasurable (fun z : E × E ↦
      ‖gradient U z.2 - gradient U z.1‖ ^ 2) := by fun_prop
  have herror := frozen_gradient_error_energy μ U L hLip hG t ht
  constructor
  · apply (integrable_map_measure hF.aestronglyMeasurable hT.aemeasurable).mpr
    exact herror.1
  · rw [integral_map_of_stronglyMeasurable hT hF]
    exact herror.2

/-- The sharp error energy in the Gaussian-weighted Lebesgue pair integral
used by the weak equation. Both its integrability and exact forcing bound
come from the actual pair law, rather than a pointwise loss of constants. -/
theorem frozenGaussianKernel_gradient_error_energy
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (hG : Integrable (fun x ↦ ‖gradient U x‖ ^ 2) μ) (t : ℝ) (ht : 0 < t) :
    Integrable (fun z : E × E ↦ realGaussianKernel (1 / (4 * t))
      (z.1 - t • gradient U z.1) z.2 * ‖gradient U z.2 - gradient U z.1‖ ^ 2)
      (μ.prod volume) ∧
      (∫ z : E × E, realGaussianKernel (1 / (4 * t))
        (z.1 - t • gradient U z.1) z.2 * ‖gradient U z.2 - gradient U z.1‖ ^ 2
          ∂μ.prod volume) ≤
        (L : ℝ) ^ 2 * (t ^ 2 * (∫ x, ‖gradient U x‖ ^ 2 ∂μ) +
          2 * t * (Module.finrank ℝ E : ℝ)) := by
  let K : E × E → ℝ := fun z ↦ realGaussianKernel (1 / (4 * t))
    (z.1 - t • gradient U z.1) z.2
  have hKpos (z : E × E) : 0 ≤ K z :=
    mul_nonneg (ULA.radialGaussianNormalizer_pos _ (by positivity)).le (Real.exp_nonneg _)
  have hKm : Measurable K := by
    have hg := hLip.continuous
    unfold K realGaussianKernel
    fun_prop
  have hpair : (μ.prod (stdGaussian E)).map (fun z : E × E ↦
      (z.1, ULA.malaProposal U t z.1 z.2)) =
      (μ.prod volume).withDensity (fun z ↦ ENNReal.ofReal (K z)) := by
    change (μ.prod (stdGaussian E)).map (fun z : E × E ↦
      (z.1, z.1 - t • gradient U z.1 + Real.sqrt (2 * t) • z.2)) = _
    rw [ULA.gaussian_proposal_pair_density μ (fun x ↦ x - t • gradient U x)
      (measurable_id.sub (hLip.continuous.measurable.const_smul t)) t ht]
    congr 1
    ext z
    unfold ULA.gaussianProposalDensity ULA.gaussianProposalNormalizer K realGaussianKernel
    congr 2
    ring
  have herror := frozenGaussianPair_gradient_error_energy U μ L hLip hG t ht.le
  dsimp only at herror
  rw [hpair] at herror
  constructor
  · have hi := (integrable_withDensity_iff_integrable_smul' hKm.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).mp herror.1
    simpa only [ENNReal.toReal_ofReal (hKpos _), smul_eq_mul] using hi
  · rw [integral_withDensity_eq_integral_toReal_smul hKm.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)] at herror
    simpa only [ENNReal.toReal_ofReal (hKpos _), smul_eq_mul] using herror.2

end ULA.LSI
