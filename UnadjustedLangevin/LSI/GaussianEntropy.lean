import UnadjustedLangevin.LSI.InterpolationDensity
import UnadjustedLangevin.LSI.ConditionalDrift
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

set_option linter.style.header false

/-! # Spatial regularity of the actual Gaussian interpolation

At every strictly positive time, convolution with the Gaussian transition
kernel gives a continuously differentiable density, even for a singular
initial law. The proof differentiates the actual displayed mixture integral;
a global Gaussian derivative bound supplies the required domination.

These results establish spatial admissibility in the logarithmic Sobolev
inequality. They do not assert an entropy time derivative or an admissible
noncompact weak equation.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace ULA.LSI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The quadratic Gaussian envelope is bounded uniformly in space. -/
theorem norm_sq_mul_exp_neg_norm_sq_le (a : ℝ) (ha : 0 < a) (z : E) :
    ‖z‖ ^ 2 * Real.exp (-a * ‖z‖ ^ 2) ≤ a⁻¹ := by
  apply (mul_le_mul_iff_right₀ ha).mp
  calc
    a * (‖z‖ ^ 2 * Real.exp (-a * ‖z‖ ^ 2)) =
        (a * ‖z‖ ^ 2) * Real.exp (-(a * ‖z‖ ^ 2)) := by ring_nf
    _ ≤ Real.exp (-1) := Real.mul_exp_neg_le_exp_neg_one _
    _ ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    _ = a * a⁻¹ := (mul_inv_cancel₀ ha.ne').symm

/-- A uniform radial bound, useful for differentiating a Gaussian mixture
without any moment assumption on its mixing measure. -/
theorem norm_mul_exp_neg_norm_sq_le (a : ℝ) (ha : 0 < a) (z : E) :
    ‖z‖ * Real.exp (-a * ‖z‖ ^ 2) ≤ 1 + a⁻¹ := by
  have hexp : Real.exp (-a * ‖z‖ ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) (sq_nonneg _))
  have haux := Real.mul_exp_neg_le_exp_neg_one (a * ‖z‖ ^ 2)
  have hone : Real.exp (-1 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hsq : ‖z‖ ^ 2 * Real.exp (-a * ‖z‖ ^ 2) ≤ a⁻¹ := by
    apply (mul_le_mul_iff_right₀ ha).mp
    calc
      a * (‖z‖ ^ 2 * Real.exp (-a * ‖z‖ ^ 2)) =
          (a * ‖z‖ ^ 2) * Real.exp (-(a * ‖z‖ ^ 2)) := by ring_nf
      _ ≤ 1 := haux.trans hone
      _ = a * a⁻¹ := (mul_inv_cancel₀ ha.ne').symm
  have hnorm : ‖z‖ ≤ 1 + ‖z‖ ^ 2 := by nlinarith [sq_nonneg (‖z‖ - 1)]
  calc
    _ ≤ (1 + ‖z‖ ^ 2) * Real.exp (-a * ‖z‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hnorm (Real.exp_nonneg _)
    _ = Real.exp (-a * ‖z‖ ^ 2) +
        ‖z‖ ^ 2 * Real.exp (-a * ‖z‖ ^ 2) := by ring
    _ ≤ 1 + a⁻¹ := add_le_add hexp hsq

/-- Real normalized Gaussian kernel at precision `a`. -/
def realGaussianKernel (a : ℝ) (c y : E) : ℝ :=
  ULA.radialGaussianNormalizer (H := E) a * Real.exp (-a * ‖y - c‖ ^ 2)

/-- The spatial derivative of the normalized Gaussian kernel. -/
def realGaussianKernelDeriv (a : ℝ) (c y : E) : E →L[ℝ] ℝ :=
  (realGaussianKernel a c y * (-2 * a)) • innerSL ℝ (y - c)

/-- The explicit Gaussian kernel derivative follows from the derivative of
squared norm and the exponential chain rule. -/
theorem hasFDerivAt_realGaussianKernel (a : ℝ) (c y : E) :
    HasFDerivAt (realGaussianKernel a c) (realGaussianKernelDeriv a c y) y := by
  have hd := ((((hasFDerivAt_id y).sub_const c).norm_sq.const_mul (-a)).exp).const_mul
    (ULA.radialGaussianNormalizer (H := E) a)
  change HasFDerivAt (fun y ↦ ULA.radialGaussianNormalizer (H := E) a *
    Real.exp (-a * ‖y - c‖ ^ 2)) _ y
  convert! hd using 1
  ext v
  simp [realGaussianKernelDeriv, realGaussianKernel]
  ring

/-- A spatially uniform operator-norm bound for the Gaussian derivative. -/
theorem norm_realGaussianKernelDeriv_le (a : ℝ) (ha : 0 < a) (c y : E) :
    ‖realGaussianKernelDeriv a c y‖ ≤
      ULA.radialGaussianNormalizer (H := E) a * (2 * a) * (1 + a⁻¹) := by
  have hK := ULA.radialGaussianNormalizer_pos (H := E) a ha
  have hq := norm_mul_exp_neg_norm_sq_le a ha (y - c)
  rw [realGaussianKernelDeriv, norm_smul, innerSL_apply_norm]
  simp only [realGaussianKernel, Real.norm_eq_abs, abs_mul,
    abs_of_pos hK, abs_of_pos (Real.exp_pos _), abs_of_nonpos (by linarith : -2 * a ≤ 0)]
  nlinarith [mul_le_mul_of_nonneg_left hq (show 0 ≤
    ULA.radialGaussianNormalizer (H := E) a * (2 * a) by positivity)]

/-- Mixing the spatial derivative of the actual Gaussian transition. -/
def interpolationLebesgueDensityDeriv (U : E → ℝ) (μ : Measure E) (t : ℝ)
    (y : E) : E →L[ℝ] ℝ :=
  ∫ x, realGaussianKernelDeriv (1 / (4 * t)) (x - t • gradient U x) y ∂μ

/-- The Gaussian kernel is integrable over any probability mixture. -/
theorem integrable_realGaussianKernel (μ : Measure E) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (c : E → E) (hc : Measurable c) (y : E) :
    Integrable (fun x ↦ realGaussianKernel a (c x) y) μ := by
  apply (integrable_const (ULA.radialGaussianNormalizer (H := E) a)).mono'
  · unfold realGaussianKernel
    fun_prop
  · filter_upwards [] with x
    have hK := ULA.radialGaussianNormalizer_pos (H := E) a ha
    rw [realGaussianKernel, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right hK.le (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) (sq_nonneg _)))

/-- The derivative kernel is integrable with no moment assumption on the
mixing probability measure. -/
theorem integrable_realGaussianKernelDeriv (μ : Measure E) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (c : E → E) (hc : Measurable c) (y : E) :
    Integrable (fun x ↦ realGaussianKernelDeriv a (c x) y) μ := by
  apply (integrable_const (ULA.radialGaussianNormalizer (H := E) a * (2 * a) *
    (1 + a⁻¹))).mono'
  · unfold realGaussianKernelDeriv realGaussianKernel
    fun_prop
  · exact ae_of_all _ fun x ↦ norm_realGaussianKernelDeriv_le a ha (c x) y

/-- Differentiation of an actual normalized Gaussian mixture. The derivative
is the mixture of the explicit transition derivatives. -/
theorem hasFDerivAt_integral_realGaussianKernel (μ : Measure E) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (c : E → E) (hc : Measurable c) (y : E) :
    HasFDerivAt (fun y ↦ ∫ x, realGaussianKernel a (c x) y ∂μ)
      (∫ x, realGaussianKernelDeriv a (c x) y ∂μ) y := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := μ) (F := fun y x ↦ realGaussianKernel a (c x) y)
    (F' := fun y x ↦ realGaussianKernelDeriv a (c x) y)
    (s := Set.univ) (bound := fun _ : E ↦
      ULA.radialGaussianNormalizer (H := E) a * (2 * a) * (1 + a⁻¹))
    (by simp)
  · exact .of_forall fun y ↦ (integrable_realGaussianKernel μ a ha c hc y).aestronglyMeasurable
  · exact integrable_realGaussianKernel μ a ha c hc y
  · exact (integrable_realGaussianKernelDeriv μ a ha c hc y).aestronglyMeasurable
  · exact ae_of_all _ fun x y _ ↦ norm_realGaussianKernelDeriv_le a ha (c x) y
  · exact integrable_const _
  · exact ae_of_all _ fun x y _ ↦ hasFDerivAt_realGaussianKernel a (c x) y

/-- The Gaussian mixture derivative is continuous by the same uniform
Gaussian domination used for differentiation. -/
theorem continuous_integral_realGaussianKernelDeriv (μ : Measure E) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (c : E → E) (hc : Measurable c) :
    Continuous (fun y ↦ ∫ x, realGaussianKernelDeriv a (c x) y ∂μ) := by
  apply continuous_of_dominated (bound := fun _ : E ↦
    ULA.radialGaussianNormalizer (H := E) a * (2 * a) * (1 + a⁻¹))
  · exact fun y ↦ (integrable_realGaussianKernelDeriv μ a ha c hc y).aestronglyMeasurable
  · exact fun y ↦ ae_of_all _ fun x ↦ norm_realGaussianKernelDeriv_le a ha (c x) y
  · exact integrable_const _
  · filter_upwards [] with x
    unfold realGaussianKernelDeriv realGaussianKernel
    fun_prop

/-- Gaussian smoothing is continuously differentiable for arbitrary
probability input. No initial density or moment is used. -/
theorem contDiff_integral_realGaussianKernel (μ : Measure E) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (c : E → E) (hc : Measurable c) :
    ContDiff ℝ 1 (fun y ↦ ∫ x, realGaussianKernel a (c x) y ∂μ) := by
  exact contDiff_one_iff_hasFDerivAt.mpr ⟨_,
    continuous_integral_realGaussianKernelDeriv μ a ha c hc,
    hasFDerivAt_integral_realGaussianKernel μ a ha c hc⟩

/-- The actual positive-time interpolation density is continuously
differentiable in space. This discharges spatial regularity from the concrete
Gaussian law, rather than taking a density regularity hypothesis. -/
theorem interpolationLebesgueDensity_contDiff (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (t : ℝ) (ht : 0 < t) : ContDiff ℝ 1 (interpolationLebesgueDensity U μ t) := by
  have heq : interpolationLebesgueDensity U μ t =
      fun y ↦ ∫ x, realGaussianKernel (1 / (4 * t)) (x - t • gradient U x) y ∂μ := by
    funext y
    rw [interpolationLebesgueDensity_eq_integral U μ L hLip t ht y]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [realGaussianKernel, ULA.gaussianProposalNormalizer]
    congr 2
    ring
  rw [heq]
  exact contDiff_integral_realGaussianKernel μ _ (by positivity) _
    (measurable_id.sub (hLip.continuous.measurable.const_smul t))

/-- The derivative of the actual interpolation density is the integral of
Gaussian component derivatives, with the exact frozen-drift center. -/
theorem hasFDerivAt_interpolationLebesgueDensity (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (t : ℝ) (ht : 0 < t) (y : E) :
    HasFDerivAt (interpolationLebesgueDensity U μ t)
      (interpolationLebesgueDensityDeriv U μ t y) y := by
  have hd := hasFDerivAt_integral_realGaussianKernel μ (1 / (4 * t))
    (by positivity) (fun x ↦ x - t • gradient U x)
    (measurable_id.sub (hLip.continuous.measurable.const_smul t)) y
  convert hd using 1
  · funext y
    rw [interpolationLebesgueDensity_eq_integral U μ L hLip t ht y]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [realGaussianKernel, ULA.gaussianProposalNormalizer]
    congr 2
    ring
  · rfl

/-- A differentiable potential with continuous gradient is continuously
differentiable. The Riesz isometry identifies its Fréchet derivative. -/
theorem contDiff_potential_of_lipschitz_gradient (U : E → ℝ) (L : ℝ≥0)
    (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U)) :
    ContDiff ℝ 1 U := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨hU, ?_⟩
  rw [← toDual_comp_gradient]
  exact (InnerProductSpace.toDual ℝ E).continuous.comp hLip.continuous

/-- The concrete positive-time density relative to Gibbs satisfies the
spatial smoothness premise of the repository's logarithmic Sobolev inequality.
Only the original smooth-potential assumptions are used. -/
theorem interpolationRelativeDensity_contDiff (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0) (hU : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (t : ℝ) (ht : 0 < t) :
    ContDiff ℝ 1 (interpolationRelativeDensity U μ t) := by
  exact (contDiff_const.mul (contDiff_potential_of_lipschitz_gradient U L hU hLip).exp).mul
    (interpolationLebesgueDensity_contDiff U μ L hLip t ht)

/-- The logarithmic Sobolev inequality applies directly to the actual
positive-time Gaussian interpolation. Its smooth positive test function and
probability normalization have all been constructed from the original law. -/
theorem interpolationLaw_logSobolev (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (α : ℝ) (L : ℝ≥0) (hU : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U))
    (hLSI : IsLogSobolev (ULA.gibbsMeasure U) α) (t : ℝ) (ht : 0 < t) :
    ENNReal.ofReal (2 * α) *
        InformationTheory.klDiv (interpolationLaw U μ t) (ULA.gibbsMeasure U) ≤
      relativeFisher (ULA.gibbsMeasure U) (interpolationRelativeDensity U μ t) := by
  letI : IsProbabilityMeasure (ULA.gibbsMeasure U) := hLSI.1
  have h := hLSI.2 (interpolationRelativeDensity U μ t)
    (interpolationRelativeDensity_pos U μ L hU hLip t ht)
    (interpolationRelativeDensity_contDiff U μ L hU hLip t ht)
    (interpolationRelativeDensity_isProbability U μ L hU hLip t ht)
  rwa [tiltedMeasure_interpolationRelativeDensity U μ L hU hLip t ht] at h

/-- Jensen's square-norm inequality with the normalization displayed as an
ordinary real integral. This version is useful for Gaussian posterior laws. -/
theorem norm_integral_sq_le_integral_norm_sq (μ : Measure E) [IsProbabilityMeasure μ]
    (f : E → E) (hf : MemLp f 2 μ) :
    ‖∫ x, f x ∂μ‖ ^ 2 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := by
  exact (convexOn_univ_norm.pow (fun _ _ ↦ norm_nonneg _) 2).map_integral_le
    (by fun_prop) isClosed_univ (ae_of_all _ fun _ ↦ Set.mem_univ _)
    (hf.integrable (by norm_num)) (hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))

/-- The posterior mixing law at a proposed state, obtained by Bayes'
normalization of the actual Gaussian transition density. -/
def gaussianPosterior (μ : Measure E) (a : ℝ) (c : E → E) (y : E) : Measure E :=
  μ.withDensity (fun x ↦ ENNReal.ofReal (realGaussianKernel a (c x) y /
    (∫ z, realGaussianKernel a (c z) y ∂μ)))

/-- Every nonzero Gaussian mixture has a strictly positive real density. -/
theorem integral_realGaussianKernel_pos (μ : Measure E) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (c : E → E) (hc : Measurable c) (y : E) :
    0 < ∫ x, realGaussianKernel a (c x) y ∂μ := by
  apply integral_pos_iff_support_of_nonneg
    (fun x ↦ ?_) (integrable_realGaussianKernel μ a ha c hc y) |>.mpr
  · have hs : Function.support (fun x ↦ realGaussianKernel a (c x) y) = Set.univ := by
      ext x
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (mul_pos (ULA.radialGaussianNormalizer_pos a ha) (Real.exp_pos _)).ne'
    rw [hs, measure_univ]
    exact zero_lt_one
  · exact mul_nonneg (ULA.radialGaussianNormalizer_pos a ha).le (Real.exp_nonneg _)

/-- Bayes' posterior kernel is a probability measure at every proposed state. -/
theorem gaussianPosterior_isProbability (μ : Measure E) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (c : E → E) (hc : Measurable c) (y : E) :
    IsProbabilityMeasure (gaussianPosterior μ a c y) := by
  have hp := integral_realGaussianKernel_pos μ a ha c hc y
  have hq := integrable_realGaussianKernel μ a ha c hc y
  constructor
  rw [gaussianPosterior, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hq.div_const _) (ae_of_all _ fun x ↦
      div_nonneg (mul_nonneg (ULA.radialGaussianNormalizer_pos a ha).le
        (Real.exp_nonneg _)) hp.le), integral_div, div_self hp.ne',
    ENNReal.ofReal_one]

/-- The Gaussian posterior has finite conditional displacement variance,
even if the initial mixing measure has no finite moments. -/
theorem gaussianPosterior_memLp_displacement (μ : Measure E) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (c : E → E) (hc : Measurable c) (y : E) :
    MemLp (fun x ↦ y - c x) 2 (gaussianPosterior μ a c y) := by
  have hp := integral_realGaussianKernel_pos μ a ha c hc y
  have hnonneg (x : E) : 0 ≤ realGaussianKernel a (c x) y /
      (∫ z, realGaussianKernel a (c z) y ∂μ) := by
    exact div_nonneg (mul_nonneg (ULA.radialGaussianNormalizer_pos a ha).le
      (Real.exp_nonneg _)) hp.le
  have hmeas : Measurable (fun x ↦ realGaussianKernel a (c x) y /
      (∫ z, realGaussianKernel a (c z) y ∂μ)) := by
    unfold realGaussianKernel
    fun_prop
  have hsquare : Integrable (fun x ↦ ‖y - c x‖ ^ 2) (gaussianPosterior μ a c y) := by
    rw [gaussianPosterior, integrable_withDensity_iff_integrable_smul'
      hmeas.ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hnonneg _), smul_eq_mul]
    apply (integrable_const ((ULA.radialGaussianNormalizer (H := E) a * a⁻¹) /
      (∫ z, realGaussianKernel a (c z) y ∂μ))).mono'
    · fun_prop
    · filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hnonneg x) (sq_nonneg _))]
      have hbound := mul_le_mul_of_nonneg_left
        (norm_sq_mul_exp_neg_norm_sq_le a ha (y - c x))
        (ULA.radialGaussianNormalizer_pos (H := E) a ha).le
      rw [div_mul_eq_mul_div]
      apply (div_le_div_iff_of_pos_right hp).mpr
      dsimp [realGaussianKernel]
      nlinarith
  apply (memLp_two_iff_integrable_sq_norm ?_).mpr hsquare
  exact ((measurable_const.sub hc).aestronglyMeasurable).mono_ac
    (withDensity_absolutelyContinuous μ _)

/-- The score of the displayed Gaussian mixture is the posterior mean of
the component score. This is an equality for the actual spatial derivative,
not a chosen representative of a Radon–Nikodym derivative. -/
theorem gradient_log_integral_realGaussianKernel (μ : Measure E) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (c : E → E) (hc : Measurable c) (y : E) :
    gradient (fun y ↦ Real.log (∫ x, realGaussianKernel a (c x) y ∂μ)) y =
      (-2 * a) • (∫ x, y - c x ∂gaussianPosterior μ a c y) := by
  have hp := integral_realGaussianKernel_pos μ a ha c hc y
  have hmeas : Measurable (fun x ↦ realGaussianKernel a (c x) y /
      (∫ z, realGaussianKernel a (c z) y ∂μ)) := by
    unfold realGaussianKernel
    fun_prop
  have hnonneg (x : E) : 0 ≤ realGaussianKernel a (c x) y /
      (∫ z, realGaussianKernel a (c z) y ∂μ) := by
    exact div_nonneg (mul_nonneg (ULA.radialGaussianNormalizer_pos a ha).le
      (Real.exp_nonneg _)) hp.le
  have hd := (hasFDerivAt_integral_realGaussianKernel μ a ha c hc y).log hp.ne'
  unfold gradient
  rw [hd.fderiv]
  rw [map_smul]
  have hcomm := (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.integral_comp_comm
    (μ := μ) (fun x ↦ realGaussianKernelDeriv a (c x) y)
  change (∫ x, (InnerProductSpace.toDual ℝ E).symm
    (realGaussianKernelDeriv a (c x) y) ∂μ) = (InnerProductSpace.toDual ℝ E).symm
      (∫ x, realGaussianKernelDeriv a (c x) y ∂μ) at hcomm
  rw [← hcomm]
  have hgrad (x : E) : (InnerProductSpace.toDual ℝ E).symm
      (realGaussianKernelDeriv a (c x) y) =
      (realGaussianKernel a (c x) y * (-2 * a)) • (y - c x) := by
    apply (InnerProductSpace.toDual ℝ E).injective
    rw [(InnerProductSpace.toDual ℝ E).apply_symm_apply, map_smul]
    rfl
  simp_rw [hgrad]
  rw [gaussianPosterior, integral_withDensity_eq_integral_toReal_smul
    hmeas.ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hnonneg _)]
  rw [← integral_smul, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_smul]
  congr 1
  field_simp

/-- Pointwise Gaussian score energy is controlled by the mixture of the
component score energies. This is posterior Jensen with Bayes' formula. -/
theorem gaussianMixture_score_energy_le (μ : Measure E) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (c : E → E) (hc : Measurable c) (y : E) :
    (∫ x, realGaussianKernel a (c x) y ∂μ) *
        ‖gradient (fun y ↦ Real.log (∫ x, realGaussianKernel a (c x) y ∂μ)) y‖ ^ 2 ≤
      (4 * a ^ 2) * ∫ x, realGaussianKernel a (c x) y * ‖y - c x‖ ^ 2 ∂μ := by
  letI := gaussianPosterior_isProbability μ a ha c hc y
  have hp := integral_realGaussianKernel_pos μ a ha c hc y
  have hj := norm_integral_sq_le_integral_norm_sq (gaussianPosterior μ a c y)
    (fun x ↦ y - c x) (gaussianPosterior_memLp_displacement μ a ha c hc y)
  rw [gradient_log_integral_realGaussianKernel μ a ha c hc y,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hmeas : Measurable (fun x ↦ realGaussianKernel a (c x) y /
      (∫ z, realGaussianKernel a (c z) y ∂μ)) := by
    unfold realGaussianKernel
    fun_prop
  have hnonneg (x : E) : 0 ≤ realGaussianKernel a (c x) y /
      (∫ z, realGaussianKernel a (c z) y ∂μ) := by
    exact div_nonneg (mul_nonneg (ULA.radialGaussianNormalizer_pos a ha).le
      (Real.exp_nonneg _)) hp.le
  calc
    _ ≤ (∫ x, realGaussianKernel a (c x) y ∂μ) *
        ((-2 * a) ^ 2 * ∫ x, ‖y - c x‖ ^ 2 ∂gaussianPosterior μ a c y) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hj (sq_nonneg _)) hp.le
    _ = _ := by
      rw [gaussianPosterior, integral_withDensity_eq_integral_toReal_smul
        hmeas.ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
      simp only [ENNReal.toReal_ofReal (hnonneg _), smul_eq_mul, div_mul_eq_mul_div]
      rw [integral_div]
      field_simp
      ring

/-- Exact component displacement energy, including the required Lebesgue
integrability of its displayed density-weighted integrand. -/
theorem realGaussianKernel_displacement_moment (t : ℝ) (ht : 0 < t) (c : E) :
    Integrable (fun y ↦ realGaussianKernel (1 / (4 * t)) c y * ‖y - c‖ ^ 2) volume ∧
      (∫ y, realGaussianKernel (1 / (4 * t)) c y * ‖y - c‖ ^ 2) =
        2 * t * (Module.finrank ℝ E : ℝ) := by
  let q : E → ℝ := realGaussianKernel (1 / (4 * t)) c
  have hq : Measurable q := by
    change Measurable (fun y ↦ ULA.radialGaussianNormalizer (H := E) (1 / (4 * t)) *
      Real.exp (-(1 / (4 * t)) * ‖y - c‖ ^ 2))
    fun_prop
  have hqpos (y : E) : 0 ≤ q y :=
    mul_nonneg (ULA.radialGaussianNormalizer_pos _ (by positivity)).le (Real.exp_nonneg _)
  have hd : (stdGaussian E).map (fun z ↦ c + Real.sqrt (2 * t) • z) =
      volume.withDensity (fun y ↦ ENNReal.ofReal (q y)) := by
    exact ULA.gaussian_proposal_radial_density t ht c
  have hnoise : Integrable (fun z : E ↦ ‖Real.sqrt (2 * t) • z‖ ^ 2) (stdGaussian E) := by
    simpa only [norm_smul, mul_pow, id_eq] using
      ((IsGaussian.memLp_id (stdGaussian E) 2 (by norm_num)).integrable_norm_pow
        (by norm_num : (2 : ℕ) ≠ 0)).const_mul (‖Real.sqrt (2 * t)‖ ^ 2)
  have hmapint : Integrable (fun y ↦ ‖y - c‖ ^ 2)
      ((stdGaussian E).map (fun z ↦ c + Real.sqrt (2 * t) • z)) := by
    apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
    simpa only [Function.comp_def, add_sub_cancel_left] using hnoise
  rw [hd] at hmapint
  have hweighted : Integrable (fun y ↦ q y * ‖y - c‖ ^ 2) volume := by
    have h := (integrable_withDensity_iff_integrable_smul' hq.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).mp hmapint
    simpa only [ENNReal.toReal_ofReal (hqpos _), smul_eq_mul] using h
  refine ⟨hweighted, ?_⟩
  calc
    _ = ∫ y, ‖y - c‖ ^ 2 ∂volume.withDensity (fun y ↦ ENNReal.ofReal (q y)) := by
      rw [integral_withDensity_eq_integral_toReal_smul hq.ennreal_ofReal
        (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
      simp only [ENNReal.toReal_ofReal (hqpos _), smul_eq_mul, q]
    _ = ∫ z : E, ‖Real.sqrt (2 * t) • z‖ ^ 2 ∂stdGaussian E := by
      rw [← hd, integral_map (by fun_prop) (by fun_prop)]
      simp only [add_sub_cancel_left]
    _ = _ := by
      simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      rw [integral_const_mul, Real.sq_sqrt (by positivity), integral_norm_sq_stdGaussian]

/-- Finite Lebesgue Fisher information of a Gaussian mixture. Gaussian
smoothing gives the universal `d / (2t)` bound, independently of the mixing law. -/
theorem gaussianMixture_fisher_bound (μ : Measure E) [IsProbabilityMeasure μ]
    (c : E → E) (hc : Measurable c) (t : ℝ) (ht : 0 < t) :
    let p := fun y ↦ ∫ x, realGaussianKernel (1 / (4 * t)) (c x) y ∂μ
    Integrable (fun y ↦ p y * ‖gradient (fun y ↦ Real.log (p y)) y‖ ^ 2) volume ∧
      (∫ y, p y * ‖gradient (fun y ↦ Real.log (p y)) y‖ ^ 2) ≤
        (Module.finrank ℝ E : ℝ) / (2 * t) := by
  let a : ℝ := 1 / (4 * t)
  have ha : 0 < a := by dsimp [a]; positivity
  let p := fun y ↦ ∫ x, realGaussianKernel a (c x) y ∂μ
  have hp (y : E) : 0 < p y := integral_realGaussianKernel_pos μ a ha c hc y
  have hprod : Integrable (fun z : E × E ↦
      realGaussianKernel a (c z.1) z.2 * ‖z.2 - c z.1‖ ^ 2) (μ.prod volume) := by
    apply (integrable_prod_iff (by unfold realGaussianKernel; fun_prop)).mpr
    refine ⟨ae_of_all _ fun x ↦ (realGaussianKernel_displacement_moment t ht (c x)).1, ?_⟩
    have habs (x y : E) : ‖realGaussianKernel a (c x) y * ‖y - c x‖ ^ 2‖ =
        realGaussianKernel a (c x) y * ‖y - c x‖ ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact mul_nonneg (mul_nonneg (ULA.radialGaussianNormalizer_pos a ha).le
        (Real.exp_nonneg _)) (sq_nonneg _)
    simp_rw [habs]
    dsimp only [a]
    simp_rw [(realGaussianKernel_displacement_moment t ht (c _)).2]
    exact integrable_const _
  have hR := hprod.integral_prod_right.const_mul (4 * a ^ 2)
  have hsmooth := (contDiff_integral_realGaussianKernel μ a ha c hc).log (fun y ↦ (hp y).ne')
  have hscore : Continuous (gradient (fun y ↦ Real.log (p y))) := by
    exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (hsmooth.continuous_fderiv (by norm_num))
  have hW : Integrable (fun y ↦ p y * ‖gradient (fun y ↦ Real.log (p y)) y‖ ^ 2) volume := by
    apply hR.mono'
    · exact ((contDiff_integral_realGaussianKernel μ a ha c hc).continuous.mul
        (hscore.norm.pow 2)).aestronglyMeasurable
    · filter_upwards [] with y
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hp y).le (sq_nonneg _))]
      exact gaussianMixture_score_energy_le μ a ha c hc y
  refine ⟨hW, ?_⟩
  calc
    _ ≤ ∫ y, (4 * a ^ 2) * ∫ x,
        realGaussianKernel a (c x) y * ‖y - c x‖ ^ 2 ∂μ := by
      exact integral_mono hW hR (fun y ↦ gaussianMixture_score_energy_le μ a ha c hc y)
    _ = (4 * a ^ 2) * (∫ x, (∫ y,
        realGaussianKernel a (c x) y * ‖y - c x‖ ^ 2) ∂μ) := by
      rw [integral_const_mul, ← integral_integral_swap hprod]
    _ = (4 * a ^ 2) * (2 * t * (Module.finrank ℝ E : ℝ)) := by
      dsimp only [a]
      simp_rw [(realGaussianKernel_displacement_moment t ht (c _)).2]
      simp
    _ = _ := by dsimp [a]; field_simp; ring

/-- The gradient stays square integrable under the actual interpolation.
Finite gradient energy is sufficient; no second state moment is required. -/
theorem memLp_gradient_interpolationLaw (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (hgrad : MemLp (gradient U) 2 μ) (t : ℝ) (ht : 0 ≤ t) :
    MemLp (gradient U) 2 (interpolationLaw U μ t) := by
  have hY := ULA.malaProposal_measurable U t L hLip
  have hD := (memLp_two_iff_integrable_sq_norm
    (((hLip.continuous.measurable.comp hY).sub
      (hLip.continuous.measurable.comp measurable_fst)).aestronglyMeasurable)).mpr
    (frozen_gradient_error_energy μ U L hLip
      (hgrad.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)) t ht).1
  have hsum := hD.add (hgrad.comp_fst (stdGaussian E))
  change MemLp (gradient U) 2
    ((μ.prod (stdGaussian E)).map (fun p : E × E ↦ ULA.malaProposal U t p.1 p.2))
  apply (memLp_map_measure_iff hLip.continuous.aestronglyMeasurable hY.aemeasurable).mpr
  simpa only [Pi.add_apply, Function.comp_def, sub_add_cancel] using hsum

/-- Finite Fisher information of the actual interpolation with respect to
Lebesgue measure. The explicit universal bound is `d / (2t)`. -/
theorem interpolationLebesgue_fisher_bound (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (t : ℝ) (ht : 0 < t) :
    Integrable (fun y ↦ ‖gradient (fun y ↦ Real.log
      (interpolationLebesgueDensity U μ t y)) y‖ ^ 2) (interpolationLaw U μ t) ∧
    (∫ y, ‖gradient (fun y ↦ Real.log (interpolationLebesgueDensity U μ t y)) y‖ ^ 2
      ∂interpolationLaw U μ t) ≤ (Module.finrank ℝ E : ℝ) / (2 * t) := by
  have heq : interpolationLebesgueDensity U μ t =
      fun y ↦ ∫ x, realGaussianKernel (1 / (4 * t)) (x - t • gradient U x) y ∂μ := by
    funext y
    rw [interpolationLebesgueDensity_eq_integral U μ L hLip t ht y]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [realGaussianKernel, ULA.gaussianProposalNormalizer]
    congr 2
    ring
  have hf := gaussianMixture_fisher_bound μ (fun x ↦ x - t • gradient U x)
    (measurable_id.sub (hLip.continuous.measurable.const_smul t)) t ht
  rw [← heq] at hf
  have hqpos (y : E) : 0 ≤ interpolationLebesgueDensity U μ t y := ENNReal.toReal_nonneg
  have hqmeas := (interpolationLebesgueDensity_continuous U μ L hLip t ht).measurable
  rw [interpolationLaw_eq_real_withDensity U μ L hLip t ht]
  constructor
  · apply (integrable_withDensity_iff_integrable_smul' hqmeas.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).mpr
    simpa only [ENNReal.toReal_ofReal (hqpos _), smul_eq_mul] using hf.1
  · rw [integral_withDensity_eq_integral_toReal_smul hqmeas.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    simpa only [ENNReal.toReal_ofReal (hqpos _), smul_eq_mul] using hf.2

/-- The real Gaussian-mixture density is positive at every state. -/
theorem interpolationLebesgueDensity_pos (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (t : ℝ) (ht : 0 < t) (y : E) : 0 < interpolationLebesgueDensity U μ t y :=
  ENNReal.toReal_pos (interpolationDensity_pos U μ L hLip t ht y).ne'
    (interpolationDensity_ne_top U μ t ht y)

/-- The Gibbs-relative score is the sum of the potential gradient and the
Lebesgue score of the actual Gaussian mixture. -/
theorem gradient_log_interpolationRelativeDensity (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (L : ℝ≥0) (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (t : ℝ) (ht : 0 < t) (y : E) :
    gradient (fun y ↦ Real.log (interpolationRelativeDensity U μ t y)) y =
      gradient U y + gradient (fun y ↦ Real.log
        (interpolationLebesgueDensity U μ t y)) y := by
  have hZpos : 0 < (ULA.gibbsPartition U).toReal :=
    ENNReal.toReal_pos (ULA.gibbsPartition_pos U hU).ne'
      (gibbsPartition_ne_top_of_probability U)
  have hp := interpolationLebesgueDensity_pos U μ L hLip t ht
  have heq : (fun y ↦ Real.log (interpolationRelativeDensity U μ t y)) =
      fun y ↦ Real.log (ULA.gibbsPartition U).toReal + U y +
        Real.log (interpolationLebesgueDensity U μ t y) := by
    funext y
    rw [interpolationRelativeDensity, Real.log_mul (mul_pos hZpos (Real.exp_pos _)).ne'
      (hp y).ne', Real.log_mul hZpos.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hpdiff := (interpolationLebesgueDensity_contDiff U μ L hLip t ht).differentiable
    (by norm_num)
  rw [heq]
  unfold gradient
  rw [fderiv_fun_add ((hU y).const_add _) ((hpdiff y).log (hp y).ne'),
    fderiv_const_add, map_add]

/-- The actual Gibbs-relative score is square integrable at every positive
time whenever the initial gradient has finite energy. -/
theorem interpolationRelativeScore_memLp (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (L : ℝ≥0) (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hgrad : MemLp (gradient U) 2 μ) (t : ℝ) (ht : 0 < t) :
    MemLp (gradient (fun y ↦ Real.log (interpolationRelativeDensity U μ t y))) 2
      (interpolationLaw U μ t) := by
  have hp := interpolationLebesgueDensity_pos U μ L hLip t ht
  have hlog := (interpolationLebesgueDensity_contDiff U μ L hLip t ht).log
    (fun y ↦ (hp y).ne')
  have hscore : Continuous (gradient (fun y ↦ Real.log
      (interpolationLebesgueDensity U μ t y))) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (hlog.continuous_fderiv (by norm_num))
  have hLeb := (memLp_two_iff_integrable_sq_norm hscore.aestronglyMeasurable).mpr
    (interpolationLebesgue_fisher_bound U μ L hLip t ht).1
  have hsum := (memLp_gradient_interpolationLaw U μ L hLip hgrad t ht.le).add hLeb
  convert hsum using 1
  funext y
  exact gradient_log_interpolationRelativeDensity U μ L hU hLip t ht y

/-- Relative Fisher information is finite along the actual interpolation
whenever the initial gradient has finite energy. -/
theorem interpolationRelativeFisher_ne_top (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (L : ℝ≥0) (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hgrad : MemLp (gradient U) 2 μ) (t : ℝ) (ht : 0 < t) :
    relativeFisher (ULA.gibbsMeasure U) (interpolationRelativeDensity U μ t) ≠ ⊤ := by
  have hint := (interpolationRelativeScore_memLp U μ L hU hLip hgrad t ht).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)
  rw [relativeFisher, tiltedMeasure_interpolationRelativeDensity U μ L hU hLip t ht,
    ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ ↦ sq_nonneg _)]
  exact ENNReal.ofReal_ne_top

/-- LSI and the constructed finite Fisher information prove finite actual KL
at positive interpolation times. No initial density regularity is needed. -/
theorem interpolationLaw_klDiv_ne_top (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (α : ℝ) (hα : 0 < α) (L : ℝ≥0)
    (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hLSI : IsLogSobolev (ULA.gibbsMeasure U) α)
    (hgrad : MemLp (gradient U) 2 μ) (t : ℝ) (ht : 0 < t) :
    InformationTheory.klDiv (interpolationLaw U μ t) (ULA.gibbsMeasure U) ≠ ⊤ := by
  letI : IsProbabilityMeasure (ULA.gibbsMeasure U) := hLSI.1
  have hFI := interpolationRelativeFisher_ne_top U μ L hU hLip hgrad t ht
  have h := interpolationLaw_logSobolev U μ α L hU hLip hLSI t ht
  intro hKL
  rw [hKL, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by positivity : 0 < 2 * α)).ne'] at h
  exact hFI (top_unique h)

end ULA.LSI
