import UnadjustedLangevin.LSI.GaussianWeakEquation

set_option linter.style.header false

/-! # Gaussian score pairings on the actual joint law

The Lebesgue score is the posterior mean of the Gaussian component score.
Pairing this identity with a square-integrable state-dependent field gives
the Fisher-information term in the entropy calculation.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ULA.LSI
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Gaussian component score in the proposed state. -/
def frozenGaussianScore (U : E → ℝ) (t : ℝ) (x y : E) : E :=
  (-(1 / (2 * t))) • (y - (x - t • gradient U x))

/-- The concrete pair law has a square-integrable Gaussian component score.
No input moment assumption is required. -/
theorem frozenGaussianScore_memLp (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (t : ℝ) (ht : 0 < t) :
    MemLp (fun z : E × E ↦ frozenGaussianScore U t z.1 z.2) 2
      ((μ.prod (stdGaussian E)).map (fun z : E × E ↦
        (z.1, ULA.malaProposal U t z.1 z.2))) := by
  have hY := ULA.malaProposal_measurable U t L hLip
  have hT := measurable_fst.prodMk hY
  have hS : Continuous (fun z : E × E ↦ frozenGaussianScore U t z.1 z.2) := by
    have hg := hLip.continuous
    unfold frozenGaussianScore
    fun_prop
  apply (memLp_map_measure_iff hS.aestronglyMeasurable hT.aemeasurable).mpr
  have hz : MemLp (fun z : E ↦ z) 2 (stdGaussian E) :=
    IsGaussian.memLp_id (stdGaussian E) 2 (by norm_num)
  have h := (hz.comp_snd μ).const_smul (-(1 / (2 * t)) * Real.sqrt (2 * t))
  simpa only [Function.comp_def, frozenGaussianScore, ULA.malaProposal,
    add_sub_cancel_left, smul_smul, Pi.smul_apply] using! h

/-- A state-dependent field retains its square integrability on the actual
initial/output pair law. -/
theorem frozenGaussianJoint_memLp_state_field (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (t : ℝ) (V : E → E) (hV : Continuous V)
    (hVLp : MemLp V 2 (interpolationLaw U μ t)) :
    MemLp (fun z : E × E ↦ V z.2) 2
      ((μ.prod (stdGaussian E)).map (fun z : E × E ↦
        (z.1, ULA.malaProposal U t z.1 z.2))) := by
  have hY := ULA.malaProposal_measurable U t L hLip
  have hT := measurable_fst.prodMk hY
  apply (memLp_map_measure_iff
    (hV.comp continuous_snd).aestronglyMeasurable hT.aemeasurable).mpr
  exact (memLp_map_measure_iff hVLp.aestronglyMeasurable hY.aemeasurable).mp hVLp

/-- The Gaussian score paired with a square-integrable state field is
integrable on the explicit Lebesgue pair density. -/
theorem integrable_frozenGaussianScore_pairing (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (t : ℝ) (ht : 0 < t) (V : E → E) (hV : Continuous V)
    (hVLp : MemLp V 2 (interpolationLaw U μ t)) :
    Integrable (fun z : E × E ↦ frozenGaussianKernel U t z.1 z.2 *
      inner ℝ (frozenGaussianScore U t z.1 z.2) (V z.2)) (μ.prod volume) := by
  let Q := (μ.prod (stdGaussian E)).map (fun z : E × E ↦
    (z.1, ULA.malaProposal U t z.1 z.2))
  have hS := frozenGaussianScore_memLp U μ L hLip t ht
  have hVQ := frozenGaussianJoint_memLp_state_field U μ L hLip t V hV hVLp
  have hprod : MemLp (fun z : E × E ↦ ‖frozenGaussianScore U t z.1 z.2‖ *
      ‖V z.2‖) 1 Q := hS.norm.mul hVQ.norm
  have hint : Integrable (fun z : E × E ↦
      inner ℝ (frozenGaussianScore U t z.1 z.2) (V z.2)) Q := by
    apply (hprod.integrable (by norm_num)).mono'
    · exact hS.aestronglyMeasurable.inner hVQ.aestronglyMeasurable
    · exact ae_of_all _ fun z ↦ norm_inner_le_norm (𝕜 := ℝ) _ _
  rw [show Q = (μ.prod volume).withDensity (fun z : E × E ↦
      ENNReal.ofReal (frozenGaussianKernel U t z.1 z.2)) by
    dsimp only [Q]
    rw [frozenGaussianJointLaw_eq_density U μ L hLip t ht]
    congr 1
    funext z
    rw [frozenGaussianKernel_eq_realGaussianKernel]] at hint
  have hqmeas : Measurable (fun z : E × E ↦ ENNReal.ofReal
      (frozenGaussianKernel U t z.1 z.2)) := by
    have hg := hLip.continuous
    unfold frozenGaussianKernel
    fun_prop
  have hqnonneg (z : E × E) : 0 ≤ frozenGaussianKernel U t z.1 z.2 := by
    unfold frozenGaussianKernel
    positivity [ULA.gaussianProposalNormalizer_pos (H := E) t ht]
  have hw := (integrable_withDensity_iff_integrable_smul' hqmeas
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).mp hint
  simpa only [ENNReal.toReal_ofReal (hqnonneg _), smul_eq_mul] using hw

/-- The actual density times its Lebesgue score is the mixture of the
Gaussian component score fluxes. This pointwise identity is Bayes' formula
for the spatial derivative already constructed by dominated differentiation. -/
theorem interpolationLebesgueDensity_weighted_score (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (t : ℝ) (ht : 0 < t) (y : E) :
    interpolationLebesgueDensity U μ t y •
        gradient (fun y ↦ Real.log (interpolationLebesgueDensity U μ t y)) y =
      ∫ x, frozenGaussianKernel U t x y • frozenGaussianScore U t x y ∂μ := by
  let a : ℝ := 1 / (4 * t)
  let c : E → E := fun x ↦ x - t • gradient U x
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : Measurable c := measurable_id.sub (hLip.continuous.measurable.const_smul t)
  have heq : interpolationLebesgueDensity U μ t =
      fun y ↦ ∫ x, realGaussianKernel a (c x) y ∂μ := by
    funext y
    rw [interpolationLebesgueDensity_eq_integral U μ L hLip t ht y]
    apply integral_congr_ae
    filter_upwards [] with x
    unfold realGaussianKernel ULA.gaussianProposalNormalizer
    dsimp only [a, c]
    congr 2
    ring
  have hp := integral_realGaussianKernel_pos μ a ha c hc y
  have hmeas : Measurable (fun x ↦ realGaussianKernel a (c x) y /
      (∫ z, realGaussianKernel a (c z) y ∂μ)) := by
    unfold realGaussianKernel
    fun_prop
  have hnonneg (x : E) : 0 ≤ realGaussianKernel a (c x) y /
      (∫ z, realGaussianKernel a (c z) y ∂μ) := by
    exact div_nonneg (mul_nonneg (ULA.radialGaussianNormalizer_pos a ha).le
      (Real.exp_nonneg _)) hp.le
  rw [heq, gradient_log_integral_realGaussianKernel μ a ha c hc y,
    gaussianPosterior, integral_withDensity_eq_integral_toReal_smul
      hmeas.ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hnonneg _)]
  rw [← integral_smul, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [frozenGaussianKernel_eq_realGaussianKernel]
  dsimp only [frozenGaussianScore, a, c]
  simp only [smul_smul]
  congr 1
  dsimp only [a, c] at hp
  field_simp [hp.ne', ht.ne']
  ring

/-- The Gaussian component score flux itself is integrable on the explicit
Lebesgue pair density. -/
theorem integrable_frozenGaussianScore_weighted (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (t : ℝ) (ht : 0 < t) :
    Integrable (fun z : E × E ↦ frozenGaussianKernel U t z.1 z.2 •
      frozenGaussianScore U t z.1 z.2) (μ.prod volume) := by
  have hint := (frozenGaussianScore_memLp U μ L hLip t ht).integrable (by norm_num)
  rw [frozenGaussianJointLaw_eq_density U μ L hLip t ht] at hint
  have hqmeas : Measurable (fun z : E × E ↦ ENNReal.ofReal
      (realGaussianKernel (1 / (4 * t)) (z.1 - t • gradient U z.1) z.2)) := by
    have hg := hLip.continuous
    unfold realGaussianKernel
    fun_prop
  have hqnonneg (z : E × E) : 0 ≤
      realGaussianKernel (1 / (4 * t)) (z.1 - t • gradient U z.1) z.2 :=
    mul_nonneg (ULA.radialGaussianNormalizer_pos _ (by positivity)).le (Real.exp_nonneg _)
  have hw := (integrable_withDensity_iff_integrable_smul' hqmeas
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).mp hint
  simpa only [ENNReal.toReal_ofReal (hqnonneg _),
    frozenGaussianKernel_eq_realGaussianKernel] using hw


/-- Pairing the Gaussian component score with a square-integrable output
field equals pairing the actual mixture score with that field. The
conditional averaging is proved from the explicit Gaussian density. -/
theorem integral_frozenGaussianScore_pairing (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (t : ℝ) (ht : 0 < t) (V : E → E) (hV : Continuous V)
    (hVLp : MemLp V 2 (interpolationLaw U μ t)) :
    (∫ z : E × E, frozenGaussianKernel U t z.1 z.2 *
      inner ℝ (frozenGaussianScore U t z.1 z.2) (V z.2) ∂μ.prod volume) =
      ∫ y, inner ℝ (gradient (fun y ↦ Real.log (interpolationLebesgueDensity U μ t y)) y)
        (V y) ∂interpolationLaw U μ t := by
  have hpair := integrable_frozenGaussianScore_pairing U μ L hLip t ht V hV hVLp
  have hweighted := integrable_frozenGaussianScore_weighted U μ L hLip t ht
  have hpoint : ∀ᵐ y ∂(volume : Measure E),
      (∫ x, frozenGaussianKernel U t x y *
        inner ℝ (frozenGaussianScore U t x y) (V y) ∂μ) =
      interpolationLebesgueDensity U μ t y *
        inner ℝ (gradient (fun y ↦ Real.log (interpolationLebesgueDensity U μ t y)) y)
          (V y) := by
    filter_upwards [hweighted.prod_left_ae] with y hy
    calc
      _ = inner ℝ (∫ x, frozenGaussianKernel U t x y •
          frozenGaussianScore U t x y ∂μ) (V y) := by
        have h := integral_inner (𝕜 := ℝ) hy (V y)
        simpa only [real_inner_smul_right, real_inner_comm] using h
      _ = _ := by
        rw [← interpolationLebesgueDensity_weighted_score U μ L hLip t ht y,
          real_inner_smul_left]
  have hqmeas := (interpolationLebesgueDensity_continuous U μ L hLip t ht).measurable
  have hqpos (y : E) : 0 ≤ interpolationLebesgueDensity U μ t y := ENNReal.toReal_nonneg
  calc
    _ = ∫ y, ∫ x, frozenGaussianKernel U t x y *
        inner ℝ (frozenGaussianScore U t x y) (V y) ∂μ := by
      rw [integral_prod _ hpair, integral_integral_swap hpair]
    _ = ∫ y, interpolationLebesgueDensity U μ t y *
        inner ℝ (gradient (fun y ↦ Real.log (interpolationLebesgueDensity U μ t y)) y)
          (V y) := integral_congr_ae hpoint
    _ = _ := by
      rw [interpolationLaw_eq_real_withDensity U μ L hLip t ht,
        integral_withDensity_eq_integral_toReal_smul hqmeas.ennreal_ofReal
          (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
      simp only [ENNReal.toReal_ofReal (hqpos _), smul_eq_mul]

/-- The averaged-score pairing on the fixed independent initial/noise space.
This form is used directly in the raw entropy flux decomposition. -/
theorem integral_frozenGaussianScore_pairing_independent (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (t : ℝ) (ht : 0 < t) (V : E → E) (hV : Continuous V)
    (hVLp : MemLp V 2 (interpolationLaw U μ t)) :
    (∫ z : E × E, inner ℝ
      ((-(1 / (2 * t)) * Real.sqrt (2 * t)) • z.2)
      (V (ULA.malaProposal U t z.1 z.2)) ∂μ.prod (stdGaussian E)) =
      ∫ y, inner ℝ (gradient (fun y ↦ Real.log (interpolationLebesgueDensity U μ t y)) y)
        (V y) ∂interpolationLaw U μ t := by
  let T : E × E → E × E := fun z ↦ (z.1, ULA.malaProposal U t z.1 z.2)
  let F : E × E → ℝ := fun z ↦ inner ℝ (frozenGaussianScore U t z.1 z.2) (V z.2)
  have hT : Measurable T := measurable_fst.prodMk (ULA.malaProposal_measurable U t L hLip)
  have hF : StronglyMeasurable F := by
    have hg := hLip.continuous
    unfold F frozenGaussianScore
    exact (by fun_prop : Continuous _).stronglyMeasurable
  have hmap := integral_map_of_stronglyMeasurable
    (μ := μ.prod (stdGaussian E)) hT hF
  change (∫ z, F z ∂(μ.prod (stdGaussian E)).map T) = ∫ z, F (T z) ∂μ.prod (stdGaussian E) at hmap
  dsimp only [T] at hmap
  rw [frozenGaussianJointLaw_eq_density U μ L hLip t ht] at hmap
  have hqmeas : Measurable (fun z : E × E ↦ ENNReal.ofReal
      (realGaussianKernel (1 / (4 * t)) (z.1 - t • gradient U z.1) z.2)) := by
    have hg := hLip.continuous
    unfold realGaussianKernel
    fun_prop
  have hqnonneg (z : E × E) : 0 ≤
      realGaussianKernel (1 / (4 * t)) (z.1 - t • gradient U z.1) z.2 :=
    mul_nonneg (ULA.radialGaussianNormalizer_pos _ (by positivity)).le (Real.exp_nonneg _)
  rw [integral_withDensity_eq_integral_toReal_smul hqmeas
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)] at hmap
  simp only [ENNReal.toReal_ofReal (hqnonneg _), smul_eq_mul] at hmap
  have hpair := integral_frozenGaussianScore_pairing U μ L hLip t ht V hV hVLp
  simp_rw [frozenGaussianKernel_eq_realGaussianKernel] at hpair
  have hfinal := hmap.symm.trans hpair
  simpa only [F, frozenGaussianScore, ULA.malaProposal,
    add_sub_cancel_left, smul_smul] using hfinal

end ULA.LSI
