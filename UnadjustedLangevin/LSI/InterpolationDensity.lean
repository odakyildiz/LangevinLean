import UnadjustedLangevin.LSI.ULALaw
import UnadjustedLangevin.LSI.FunctionalInequality
import UnadjustedLangevin.GaussianProposalDensity
import Mathlib.MeasureTheory.Measure.Prod

set_option linter.style.header false

/-! # The actual frozen-drift Gaussian mixture density

At every positive interpolation time, the law has the explicit Lebesgue
density obtained by mixing its Gaussian transition densities over the initial
law. This constructs a density for arbitrary initial probability measures;
it does not assume that the initial measure has a density. Spatial and time
regularity and admissibility of the entropy weak test require further proofs.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ULA.LSI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The explicit extended density of the frozen-drift Gaussian mixture. -/
def interpolationDensity (U : E → ℝ) (μ : Measure E) (t : ℝ) (y : E) : ℝ≥0∞ :=
  ∫⁻ x, ULA.gaussianProposalDensity t (x - t • gradient U x) y ∂μ

/-- The mixture density is measurable when the gradient is Lipschitz. -/
theorem interpolationDensity_measurable (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0) (hLip : LipschitzWith L (gradient U)) (t : ℝ) :
    Measurable (interpolationDensity U μ t) := by
  apply Measurable.lintegral_prod_left
  unfold ULA.gaussianProposalDensity
  have hg := hLip.continuous.measurable
  fun_prop

/-- Identification of the actual Gaussian update with its explicit mixture
density. Tonelli exchanges the initial-state and proposed-state integrals;
the fixed-state Gaussian density is already identified with the actual noise. -/
theorem interpolationLaw_eq_withDensity (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (t : ℝ) (ht : 0 < t) :
    interpolationLaw U μ t = volume.withDensity (interpolationDensity U μ t) := by
  have hmap := ULA.malaProposal_measurable U t L hLip
  have hd : Measurable (fun p : E × E ↦
      ULA.gaussianProposalDensity t (p.1 - t • gradient U p.1) p.2) := by
    unfold ULA.gaussianProposalDensity
    have hg := hLip.continuous.measurable
    fun_prop
  apply Measure.ext
  intro A hA
  rw [interpolationLaw, ULA.ulaLawStep, Measure.map_apply hmap hA,
    Measure.prod_apply (hmap hA), withDensity_apply _ hA]
  have hinner (x : E) :
      (stdGaussian E) (Prod.mk x ⁻¹' ((fun p : E × E ↦
        ULA.malaProposal U t p.1 p.2) ⁻¹' A)) =
        ∫⁻ y in A, ULA.gaussianProposalDensity t (x - t • gradient U x) y := by
    rw [← withDensity_apply _ hA, ← ULA.gaussian_proposal_density t ht,
      Measure.map_apply (by fun_prop) hA]
    rfl
  simp_rw [hinner]
  exact lintegral_lintegral_swap (μ := μ) (ν := volume.restrict A) hd.aemeasurable


/-- The Gaussian-mixture density is positive at every point at positive time.
Strict positivity follows because every component Gaussian has positive density
and the mixing probability measure has total mass one. -/
theorem interpolationDensity_pos (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (t : ℝ) (ht : 0 < t) (y : E) : 0 < interpolationDensity U μ t y := by
  have hq : Measurable (fun x ↦ ULA.gaussianProposalDensity t (x - t • gradient U x) y) := by
    unfold ULA.gaussianProposalDensity
    have hg := hLip.continuous.measurable
    fun_prop
  have hqpos (x : E) :
      0 < ULA.gaussianProposalDensity t (x - t • gradient U x) y := by
    unfold ULA.gaussianProposalDensity
    exact ENNReal.ofReal_pos.mpr (mul_pos (ULA.gaussianProposalNormalizer_pos t ht)
      (Real.exp_pos _))
  have hsupp : Function.support
      (fun x ↦ ULA.gaussianProposalDensity t (x - t • gradient U x) y) = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hqpos x).ne'
  rw [interpolationDensity, lintegral_pos_iff_support hq, hsupp, measure_univ]
  exact zero_lt_one

/-- The probability mixture is bounded by the Gaussian normalizer. This gives
pointwise finiteness, not merely almost-everywhere finiteness of a density. -/
theorem interpolationDensity_le_normalizer (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (t : ℝ) (ht : 0 < t) (y : E) :
    interpolationDensity U μ t y ≤ ENNReal.ofReal (ULA.gaussianProposalNormalizer (H := E) t) := by
  unfold interpolationDensity
  calc
    _ ≤ ∫⁻ _x : E, ENNReal.ofReal (ULA.gaussianProposalNormalizer (H := E) t) ∂μ := by
      apply lintegral_mono
      intro x
      unfold ULA.gaussianProposalDensity
      apply ENNReal.ofReal_le_ofReal
      have hexp : Real.exp (-‖y - (x - t • gradient U x)‖ ^ 2 / (4 * t)) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp
        (ULA.gaussianProposalNormalizer_pos t ht).le
    _ = _ := by simp

/-- The explicit mixture density is finite at every point. -/
theorem interpolationDensity_ne_top (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (t : ℝ) (ht : 0 < t) (y : E) :
    interpolationDensity U μ t y ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (interpolationDensity_le_normalizer U μ t ht y)

/-- A real-valued representative of the actual Gaussian mixture density. -/
def interpolationLebesgueDensity (U : E → ℝ) (μ : Measure E) (t : ℝ) (y : E) : ℝ :=
  (interpolationDensity U μ t y).toReal

/-- The actual Gaussian interpolation has the displayed real Lebesgue density;
pointwise finiteness justifies conversion from its extended-valued version. -/
theorem interpolationLaw_eq_real_withDensity (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (t : ℝ) (ht : 0 < t) :
    interpolationLaw U μ t = volume.withDensity
      (fun y ↦ ENNReal.ofReal (interpolationLebesgueDensity U μ t y)) := by
  rw [interpolationLaw_eq_withDensity U μ L hLip t ht]
  congr 1
  funext y
  exact (ENNReal.ofReal_toReal (interpolationDensity_ne_top U μ t ht y)).symm

/-- Every positive-time interpolation law is absolutely continuous with
respect to Lebesgue measure, including from singular initial laws. -/
theorem interpolationLaw_absolutelyContinuous (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (t : ℝ) (ht : 0 < t) : interpolationLaw U μ t ≪ volume := by
  rw [interpolationLaw_eq_withDensity U μ L hLip t ht]
  exact withDensity_absolutelyContinuous _ _


/-- The real mixture density is the ordinary integral of the displayed
Gaussian density. Domination by its normalizer justifies the real integral. -/
theorem interpolationLebesgueDensity_eq_integral (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (t : ℝ) (ht : 0 < t) (y : E) :
    interpolationLebesgueDensity U μ t y =
      ∫ x, ULA.gaussianProposalNormalizer (H := E) t *
        Real.exp (-‖y - (x - t • gradient U x)‖ ^ 2 / (4 * t)) ∂μ := by
  have hnonneg (x : E) : 0 ≤ ULA.gaussianProposalNormalizer (H := E) t *
      Real.exp (-‖y - (x - t • gradient U x)‖ ^ 2 / (4 * t)) := by
    exact mul_nonneg (ULA.gaussianProposalNormalizer_pos t ht).le (Real.exp_nonneg _)
  have hbound (x : E) : ULA.gaussianProposalNormalizer (H := E) t *
      Real.exp (-‖y - (x - t • gradient U x)‖ ^ 2 / (4 * t)) ≤
        ULA.gaussianProposalNormalizer (H := E) t := by
    have he : Real.exp (-‖y - (x - t • gradient U x)‖ ^ 2 / (4 * t)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he
      (ULA.gaussianProposalNormalizer_pos t ht).le
  have hint : Integrable (fun x ↦ ULA.gaussianProposalNormalizer (H := E) t *
      Real.exp (-‖y - (x - t • gradient U x)‖ ^ 2 / (4 * t))) μ := by
    apply (integrable_const (ULA.gaussianProposalNormalizer (H := E) t)).mono'
    · have hg := hLip.continuous
      fun_prop
    · filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg x)]
      exact hbound x
  unfold interpolationLebesgueDensity interpolationDensity ULA.gaussianProposalDensity
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hnonneg),
    ENNReal.toReal_ofReal (integral_nonneg hnonneg)]

/-- The actual positive-time mixture density is continuous in space. The
Gaussian normalizer is a common integrable bound for all proposed states. -/
theorem interpolationLebesgueDensity_continuous (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (t : ℝ) (ht : 0 < t) : Continuous (interpolationLebesgueDensity U μ t) := by
  have heq := funext (interpolationLebesgueDensity_eq_integral U μ L hLip t ht)
  rw [heq]
  apply continuous_of_dominated (bound := fun _ : E ↦ ULA.gaussianProposalNormalizer (H := E) t)
  · intro y
    have hg := hLip.continuous
    fun_prop
  · intro y
    filter_upwards [] with x
    have hp : 0 ≤ ULA.gaussianProposalNormalizer (H := E) t *
        Real.exp (-‖y - (x - t • gradient U x)‖ ^ 2 / (4 * t)) :=
      mul_nonneg (ULA.gaussianProposalNormalizer_pos t ht).le (Real.exp_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hp]
    have he : Real.exp (-‖y - (x - t • gradient U x)‖ ^ 2 / (4 * t)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he
      (ULA.gaussianProposalNormalizer_pos t ht).le
  · exact integrable_const _
  · filter_upwards [] with x
    fun_prop

omit [CompleteSpace E] in
/-- A normalized Gibbs target cannot have an infinite partition function.
This uses probability normalization itself and needs no strong convexity. -/
theorem gibbsPartition_ne_top_of_probability (U : E → ℝ)
    [IsProbabilityMeasure (ULA.gibbsMeasure U)] : ULA.gibbsPartition U ≠ ⊤ := by
  intro hZ
  have hzero : ULA.gibbsMeasure U = 0 := by simp [ULA.gibbsMeasure, hZ]
  have hmass := measure_univ (μ := ULA.gibbsMeasure U)
  rw [hzero] at hmass
  norm_num at hmass

/-- The explicit positive-time density relative to the normalized Gibbs target.
The Lebesgue density is multiplied by `Z exp U`, exactly the reciprocal target
density. Its use below retains finite partition and density proofs. -/
def interpolationRelativeDensity (U : E → ℝ) (μ : Measure E) (t : ℝ) (y : E) : ℝ :=
  (ULA.gibbsPartition U).toReal * Real.exp (U y) * interpolationLebesgueDensity U μ t y

/-- The actual Gibbs-relative mixture density is measurable. -/
theorem interpolationRelativeDensity_measurable (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0) (hU : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (t : ℝ) :
    Measurable (interpolationRelativeDensity U μ t) := by
  exact (measurable_const.mul (Real.measurable_exp.comp hU.continuous.measurable)).mul
    (interpolationDensity_measurable U μ L hLip t).ennreal_toReal


/-- Multiplying the continuous mixture density by the reciprocal Gibbs density
gives continuity of the explicit positive-time relative density. -/
theorem interpolationRelativeDensity_continuous (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0) (hU : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (t : ℝ) (ht : 0 < t) :
    Continuous (interpolationRelativeDensity U μ t) := by
  exact (continuous_const.mul (Real.continuous_exp.comp hU.continuous)).mul
    (interpolationLebesgueDensity_continuous U μ L hLip t ht)

/-- The explicitly constructed relative density is strictly positive everywhere
at every positive interpolation time. No initial density is required. -/
theorem interpolationRelativeDensity_pos (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (L : ℝ≥0) (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (t : ℝ) (ht : 0 < t) (y : E) : 0 < interpolationRelativeDensity U μ t y := by
  have hZpos := ULA.gibbsPartition_pos U hU
  have hZfin := gibbsPartition_ne_top_of_probability U
  have hqpos := interpolationDensity_pos U μ L hLip t ht y
  have hqfin := interpolationDensity_ne_top U μ t ht y
  exact mul_pos (mul_pos (ENNReal.toReal_pos hZpos.ne' hZfin) (Real.exp_pos _))
    (ENNReal.toReal_pos hqpos.ne' hqfin)

/-- Positive-time identification of the explicit relative density with the
actual independent-Gaussian interpolation. This establishes the law and
positivity part of the density interface; its analytic regularity and the
noncompact entropy test remain distinct obligations. -/
theorem tiltedMeasure_interpolationRelativeDensity (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (L : ℝ≥0) (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (t : ℝ) (ht : 0 < t) :
    tiltedMeasure (ULA.gibbsMeasure U) (interpolationRelativeDensity U μ t) =
      interpolationLaw U μ t := by
  have hZzero := (ULA.gibbsPartition_pos U hU).ne'
  have hZfin := gibbsPartition_ne_top_of_probability U
  have hw : Measurable (ULA.gibbsWeight U) :=
    (Real.measurable_exp.comp hU.continuous.measurable.neg).ennreal_ofReal
  have hr := (interpolationRelativeDensity_measurable U μ L hU hLip t).ennreal_ofReal
  rw [interpolationLaw_eq_withDensity U μ L hLip t ht, tiltedMeasure, ULA.gibbsMeasure,
    withDensity_smul_measure, ← withDensity_mul volume hw hr,
    ← withDensity_smul' _ _ (ENNReal.inv_ne_top.mpr hZzero)]
  congr 1
  funext y
  have hrel : ENNReal.ofReal (interpolationRelativeDensity U μ t y) =
      ULA.gibbsPartition U * ENNReal.ofReal (Real.exp (U y)) * interpolationDensity U μ t y := by
    unfold interpolationRelativeDensity interpolationLebesgueDensity
    rw [ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg (Real.exp_nonneg _)),
      ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hZfin,
      ENNReal.ofReal_toReal (interpolationDensity_ne_top U μ t ht y)]
  have hexp : ENNReal.ofReal (Real.exp (-U y)) * ENNReal.ofReal (Real.exp (U y)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add,
      neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one]
  change (ULA.gibbsPartition U)⁻¹ * (ULA.gibbsWeight U y *
    ENNReal.ofReal (interpolationRelativeDensity U μ t y)) = _
  rw [hrel]
  unfold ULA.gibbsWeight
  calc
    _ = ((ULA.gibbsPartition U)⁻¹ * ULA.gibbsPartition U) *
        (ENNReal.ofReal (Real.exp (-U y)) * ENNReal.ofReal (Real.exp (U y))) *
        interpolationDensity U μ t y := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hZzero hZfin, hexp]; simp

/-- The constructed positive-time relative density has total mass one,
because its induced measure equals the actual Gaussian interpolation law. -/
theorem interpolationRelativeDensity_isProbability (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (L : ℝ≥0) (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (t : ℝ) (ht : 0 < t) :
    IsProbabilityMeasure (tiltedMeasure (ULA.gibbsMeasure U)
      (interpolationRelativeDensity U μ t)) := by
  rw [tiltedMeasure_interpolationRelativeDensity U μ L hU hLip t ht]
  exact interpolationLaw_isProbability U μ L hLip t

end ULA.LSI
