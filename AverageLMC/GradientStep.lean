import AverageLMC.Assumptions
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# The deterministic steps in the proof

`gradient_step` is equation (eq:basic-gd), with precisely the potential's
strong convexity and differentiability hypotheses. `gradient_descent`
is equation (eq:exp-upper), the second conclusion of the smoothing lemma.
Neither theorem assumes any stochastic coupling estimate.
-/

noncomputable section

open scoped NNReal

namespace AverageLMC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The gradient-step lemma (eq:basic-gd). The proof also covers `h = 0`. -/
theorem gradient_step (f : H → ℝ) (m h : ℝ) (hdiff : Differentiable ℝ f)
    (hsc : StrongConvexOn Set.univ m f) (hh : 0 ≤ h) (θ y : H) :
    ‖θ - h • gradient f θ - y‖ ^ 2 ≤
      (1 - m * h) * ‖θ - y‖ ^ 2 + 2 * h * (f y - f θ) +
        h ^ 2 * ‖gradient f θ‖ ^ 2 := by
  have hfirst := ULA.strong_first_order hdiff hsc θ y
  have hnorm : ‖y - θ‖ = ‖θ - y‖ := norm_sub_rev y θ
  have hinner : inner ℝ (gradient f θ) (y - θ) =
      -inner ℝ (θ - y) (gradient f θ) := by
    rw [show y - θ = -(θ - y) by module, inner_neg_right, real_inner_comm]
  rw [hnorm, hinner] at hfirst
  have hscaled := mul_le_mul_of_nonneg_left hfirst (show 0 ≤ 2 * h by positivity)
  rw [show θ - h • gradient f θ - y = (θ - y) - h • gradient f θ by module,
    norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hh]
  nlinarith

/-- The deterministic descent statement of the smoothing lemma (eq:exp-upper),
with the actual gradient of `f`. -/
theorem gradient_descent (f : H → ℝ) (M : ℝ≥0) (hdiff : Differentiable ℝ f)
    (hLip : LipschitzWith M (gradient f)) (θ : H) (h : ℝ) (hh : 0 ≤ h) :
    2 * (f (θ - h • gradient f θ) - f θ) ≤
      -h * (2 - h * (M : ℝ)) * ‖gradient f θ‖ ^ 2 := by
  have hs := ULA.Analysis.smooth_upper_bound f M hdiff hLip θ (θ - h • gradient f θ)
  have heq : θ - h • gradient f θ - θ = -h • gradient f θ := by module
  rw [heq, real_inner_smul_right, real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hh] at hs
  nlinarith

/-- The usual descent conclusion for the paper's admissible step range. -/
theorem gradient_descent_nonincreasing (f : H → ℝ) (M : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hLip : LipschitzWith M (gradient f))
    (θ : H) (h : ℝ) (hh : 0 ≤ h) (hstep : h * (M : ℝ) ≤ 2) :
    f (θ - h • gradient f θ) ≤ f θ := by
  have hs := gradient_descent f M hdiff hLip θ h hh
  have hneg : -h * (2 - h * (M : ℝ)) * ‖gradient f θ‖ ^ 2 ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hh) (sub_nonneg.mpr hstep))
      (sq_nonneg _)
  linarith

end AverageLMC
