import UnadjustedLangevin.LSI.InterpolationDensity
import UnadjustedLangevin.Generator

set_option linter.style.header false

/-! # A pointwise Gibbs-density bound near the initial interpolation time

The reference law is the actual frozen-drift Gaussian update of Gibbs itself.
First-order smoothness bounds its density ratio by a Gaussian square completion.
This estimate is intended for the initial entropy endpoint, through data
processing relative to the updated Gibbs law. No Jacobian of the Euler map,
second derivative of the potential, or initial spatial moment is needed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ULA.LSI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [CompleteSpace E] in
/-- The Gaussian normalizer ratio depends only on the ratio of the two times. -/
theorem gaussianProposalNormalizer_ratio (t s : ℝ) (ht : 0 < t) (hs : 0 < s) :
    ULA.gaussianProposalNormalizer (H := E) t /
      ULA.gaussianProposalNormalizer (H := E) s =
        (s / t) ^ ((Module.finrank ℝ E : ℝ) / 2) := by
  unfold ULA.gaussianProposalNormalizer ULA.radialGaussianNormalizer ULA.radialGaussianIntegral
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity : 0 < 1 / (4 * t)),
    GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity : 0 < 1 / (4 * s)),
    inv_div_inv, ← Real.div_rpow (by positivity) (by positivity)]
  congr 1
  field_simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Smoothness and the gradient Lipschitz estimate control the frozen-kernel
exponent by a centered Gaussian with the inflated time `s`.
The equation relating the times is exactly `s = t / (1 - 4tL)`. -/
theorem gibbs_frozen_exponent_le
    (U : E → ℝ) (L : ℝ≥0) (hU : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (t s : ℝ) (ht : 0 < t) (hs : 0 < s)
    (hscale : s * (1 - 4 * t * (L : ℝ)) = t) (x y : E) :
    U y - U x - ‖y - (x - t • gradient U x)‖ ^ 2 / (4 * t) ≤
      -‖x - (y - s • gradient U y)‖ ^ 2 / (4 * s) + s * ‖gradient U y‖ ^ 2 / 4 := by
  let z := y - x
  have hmodel := ULA.Analysis.smooth_upper_bound U L hU hLip x y
  have hdiff : ‖gradient U x - gradient U y‖ ≤ (L : ℝ) * ‖z‖ := by
    calc
      _ ≤ (L : ℝ) * ‖x - y‖ := by simpa only [dist_eq_norm] using hLip.dist_le_mul x y
      _ = _ := by dsimp [z]; rw [norm_sub_rev]
  have hinner : inner ℝ (gradient U x) z ≤ inner ℝ (gradient U y) z +
      (L : ℝ) * ‖z‖ ^ 2 := by
    have hcs := real_inner_le_norm (gradient U x - gradient U y) z
    have hm := mul_le_mul_of_nonneg_right hdiff (norm_nonneg z)
    simp only [inner_sub_left] at hcs
    nlinarith
  have hx : y - (x - t • gradient U x) = z + t • gradient U x := by
    dsimp [z]
    module
  have hy : ‖x - (y - s • gradient U y)‖ ^ 2 = ‖z - s • gradient U y‖ ^ 2 := by
    have heq : x - (y - s • gradient U y) = -(z - s • gradient U y) := by
      dsimp [z]
      module
    rw [heq, norm_neg]
  rw [hx, hy, norm_add_sq_real z (t • gradient U x),
    norm_sub_sq_real z (s • gradient U y)]
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  change U y ≤ U x + inner ℝ (gradient U x) z + (L : ℝ) / 2 * ‖z‖ ^ 2 at hmodel
  rw [real_inner_comm (gradient U x) z, real_inner_comm (gradient U y) z]
  have hscale' : s - 4 * s * t * (L : ℝ) = t := by nlinarith [hscale]
  apply (mul_le_mul_iff_of_pos_left (by positivity : 0 < 4 * t * s)).mp
  have hm := mul_le_mul_of_nonneg_left hmodel (by positivity : 0 ≤ 4 * t * s)
  have hi := mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ 2 * t * s)
  have hz := congrArg (fun c : ℝ ↦ c * ‖z‖ ^ 2) hscale'
  field_simp
  nlinarith [mul_nonneg (sq_nonneg t) (mul_nonneg hs.le (sq_nonneg ‖gradient U x‖))]

/-- Pointwise comparison of the weighted frozen kernel with a normalized
Gaussian in the *initial* variable. Integrating this comparison removes that
variable and gives a bound on the updated Gibbs density. -/
theorem gibbs_weighted_proposal_le
    (U : E → ℝ) (L : ℝ≥0) (hU : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (t s : ℝ) (ht : 0 < t) (hs : 0 < s)
    (hscale : s * (1 - 4 * t * (L : ℝ)) = t) (x y : E) :
    Real.exp (U y) * Real.exp (-U x) *
        (ULA.gaussianProposalNormalizer (H := E) t *
          Real.exp (-‖y - (x - t • gradient U x)‖ ^ 2 / (4 * t))) ≤
      (ULA.gaussianProposalNormalizer (H := E) t /
        ULA.gaussianProposalNormalizer (H := E) s * Real.exp (s * ‖gradient U y‖ ^ 2 / 4)) *
          (ULA.gaussianProposalNormalizer (H := E) s *
            Real.exp (-‖x - (y - s • gradient U y)‖ ^ 2 / (4 * s))) := by
  have he := Real.exp_le_exp.mpr (gibbs_frozen_exponent_le U L hU hLip t s ht hs hscale x y)
  have hm := mul_le_mul_of_nonneg_left he (ULA.gaussianProposalNormalizer_pos (H := E) t ht).le
  calc
    _ = ULA.gaussianProposalNormalizer (H := E) t *
        Real.exp (U y - U x - ‖y - (x - t • gradient U x)‖ ^ 2 / (4 * t)) := by
      have hsplit : Real.exp (U y - U x - ‖y - (x - t • gradient U x)‖ ^ 2 / (4 * t)) =
          Real.exp (U y) * Real.exp (-U x) *
            Real.exp (-‖y - (x - t • gradient U x)‖ ^ 2 / (4 * t)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [hsplit]
      ring
    _ ≤ _ := hm
    _ = _ := by
      rw [Real.exp_add]
      field_simp [(ULA.gaussianProposalNormalizer_pos (H := E) s hs).ne']

/-- The actual Gibbs-relative density of a frozen Gaussian step, with a
pointwise upper bound requiring only first-order smoothness. -/
theorem interpolationRelativeDensity_gibbs_le
    (U : E → ℝ) (L : ℝ≥0) (hU : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U))
    [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (t s : ℝ) (ht : 0 < t) (hs : 0 < s)
    (hscale : s * (1 - 4 * t * (L : ℝ)) = t) (y : E) :
    interpolationRelativeDensity U (ULA.gibbsMeasure U) t y ≤
      (s / t) ^ ((Module.finrank ℝ E : ℝ) / 2) *
        Real.exp (s * ‖gradient U y‖ ^ 2 / 4) := by
  let C := ULA.gaussianProposalNormalizer (H := E) t /
    ULA.gaussianProposalNormalizer (H := E) s * Real.exp (s * ‖gradient U y‖ ^ 2 / 4)
  let g : E → ℝ := fun x ↦ ULA.gaussianProposalNormalizer (H := E) s *
    Real.exp (-‖x - (y - s • gradient U y)‖ ^ 2 / (4 * s))
  have hg : Integrable g volume := by
    convert ULA.integrable_radialGaussianDensity_real (H := E)
      (1 / (4 * s)) (by positivity) (y - s • gradient U y) using 1
    funext x
    dsimp [g, ULA.gaussianProposalNormalizer]
    congr 2
    ring
  have hgint : (∫ x, g x ∂volume) = 1 := by
    convert ULA.integral_radialGaussianDensity_real (H := E)
      (1 / (4 * s)) (by positivity) (y - s • gradient U y) using 1
    congr 1
    funext x
    dsimp [g, ULA.gaussianProposalNormalizer]
    congr 2
    ring
  let f : E → ℝ := fun x ↦ Real.exp (U y) * Real.exp (-U x) *
    (ULA.gaussianProposalNormalizer (H := E) t *
      Real.exp (-‖y - (x - t • gradient U x)‖ ^ 2 / (4 * t)))
  have hpoint (x : E) : f x ≤ C * g x :=
    gibbs_weighted_proposal_le U L hU hLip t s ht hs hscale x y
  have hf : Integrable f volume := by
    apply (hg.const_mul C).mono'
    · have hUc := hU.continuous
      have hgc := hLip.continuous
      dsimp [f]
      fun_prop
    · filter_upwards [] with x
      have hnonneg : 0 ≤ f x := by
        dsimp [f]
        exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
          (mul_nonneg (ULA.gaussianProposalNormalizer_pos (H := E) t ht).le
            (Real.exp_nonneg _))
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact hpoint x
  have hZ : 0 < (ULA.gibbsPartition U).toReal :=
    ENNReal.toReal_pos (ULA.gibbsPartition_pos U hU).ne'
      (gibbsPartition_ne_top_of_probability U)
  have hformula : interpolationRelativeDensity U (ULA.gibbsMeasure U) t y =
      ∫ x, f x ∂volume := by
    rw [interpolationRelativeDensity,
      interpolationLebesgueDensity_eq_integral U (ULA.gibbsMeasure U) L hLip t ht y,
      ULA.integral_gibbs_eq_weighted U hU, ENNReal.toReal_inv]
    dsimp only [f]
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    field_simp [hZ.ne']
    apply integral_congr_ae
    exact ae_of_all _ fun x ↦ by ring
  calc
    _ = ∫ x, f x ∂volume := hformula
    _ ≤ ∫ x, C * g x ∂volume := integral_mono hf (hg.const_mul C) hpoint
    _ = C := by rw [integral_const_mul, hgint, mul_one]
    _ = _ := by dsimp [C]; rw [gaussianProposalNormalizer_ratio t s ht hs]

end ULA.LSI
