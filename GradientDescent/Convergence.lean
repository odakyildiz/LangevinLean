import GradientDescent.Minimizer
import GradientDescent.Smooth
import GradientDescent.Rates

-- This project does not prescribe Mathlib copyright headers.
set_option linter.style.header false

/-! # Gradient descent for strongly convex functions with Lipschitz gradient

The main theorem proves existence and uniqueness of the minimizer, convergence
of the iterates and objective values, and explicit geometric rates, for every
constant step `0 < α < 2 / L`. No minimizer is assumed in the hypotheses.
-/

open scoped NNReal

noncomputable section

namespace GradientDescent

open Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The geometric objective-gap factor. The maximum covers the degenerate
one-point space without requiring the redundant usual assumption `m ≤ L`. -/
def rate (m α : ℝ) (L : ℝ≥0) : ℝ := max 0 (1 - m * α * (2 - (L : ℝ) * α))

theorem rate_nonneg (m α : ℝ) (L : ℝ≥0) : 0 ≤ rate m α L := le_max_left _ _

theorem rate_lt_one {m α : ℝ} {L : ℝ≥0}
    (hm : 0 < m) (hL : 0 < (L : ℝ)) (hα : 0 < α) (hαL : α < 2 / (L : ℝ)) :
    rate m α L < 1 := by
  have hαL' : α * (L : ℝ) < 2 := (lt_div_iff₀ hL).mp hαL
  have hp : 0 < m * α * (2 - (L : ℝ) * α) := by
    apply mul_pos (mul_pos hm hα)
    nlinarith
  exact max_lt (by norm_num) (by linarith)

/-- In the usual parameter range `m ≤ L`, the maximum in `rate` is unnecessary. -/
theorem rate_eq {m α : ℝ} {L : ℝ≥0}
    (hmL : m ≤ (L : ℝ)) (hL : 0 < (L : ℝ)) (hα : 0 < α)
    (hαL : α < 2 / (L : ℝ)) :
    rate m α L = 1 - m * α * (2 - (L : ℝ) * α) := by
  have hαL' : α * (L : ℝ) < 2 := (lt_div_iff₀ hL).mp hαL
  have hnonneg : 0 ≤ α * (2 - (L : ℝ) * α) := by
    apply mul_nonneg hα.le
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hmL hnonneg
  have hbound : (L : ℝ) * α * (2 - (L : ℝ) * α) ≤ 1 := by
    nlinarith [sq_nonneg ((L : ℝ) * α - 1)]
  apply max_eq_right
  nlinarith

/-- Smoothness gives the decrease in one gradient step. -/
theorem gradient_descent_decrease {f : H → ℝ} {L : ℝ≥0}
    (hdiff : Differentiable ℝ f) (hLip : LipschitzWith L (gradient f))
    (α : ℝ) (x : H) :
    f (x - α • gradient f x) ≤
      f x - α * (1 - (L : ℝ) * α / 2) * ‖gradient f x‖ ^ 2 := by
  have h := smooth_upper_bound f L hdiff hLip x (x - α • gradient f x)
  rw [sub_sub_cancel_left, inner_neg_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, norm_neg, norm_smul, Real.norm_eq_abs] at h
  rw [mul_pow, sq_abs] at h
  nlinarith

/-- One step contracts the objective gap for every `0 < α < 2/L`. -/
theorem gradient_descent_gap_step {f : H → ℝ} {m α : ℝ} {L : ℝ≥0}
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ m f)
    (hLip : LipschitzWith L (gradient f)) (hm : 0 < m)
    (hL : 0 < (L : ℝ)) (hα : 0 < α) (hαL : α < 2 / (L : ℝ))
    {z : H} (hz : gradient f z = 0) (x : H) :
    f (x - α • gradient f x) - f z ≤ rate m α L * (f x - f z) := by
  have hαL' : α * (L : ℝ) < 2 := (lt_div_iff₀ hL).mp hαL
  have hc : 0 ≤ α * (1 - (L : ℝ) * α / 2) := by
    apply mul_nonneg hα.le
    nlinarith
  have hpl : 2 * m * (f x - f z) ≤ ‖gradient f x‖ ^ 2 := by
    simpa only [mul_comm] using
      (le_div_iff₀ (by positivity : 0 < 2 * m)).mp (strong_upper_gap hdiff hsc hm x z)
  have hscaled := mul_le_mul_of_nonneg_left hpl hc
  have hdesc := gradient_descent_decrease hdiff hLip α x
  have hgap : 0 ≤ f x - f z := by
    have h := strong_lower_gap hdiff hsc hz x
    have hn : 0 ≤ m / 2 * ‖x - z‖ ^ 2 := by positivity
    linarith
  have hraw : f (x - α • gradient f x) - f z ≤
      (1 - m * α * (2 - (L : ℝ) * α)) * (f x - f z) := by
    nlinarith
  exact hraw.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hgap)

/-- Full convergence theorem: unique global minimizer, convergence in norm and
of objective values, and geometric objective and squared-distance bounds. -/
theorem gradient_descent_converges {f : H → ℝ} {m α : ℝ} {L : ℝ≥0}
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ m f)
    (hLip : LipschitzWith L (gradient f)) (hm : 0 < m)
    (hL : 0 < (L : ℝ)) (hα : 0 < α) (hαL : α < 2 / (L : ℝ)) (x₀ : H) :
    ∃ z : H, gradient f z = 0 ∧
      (∀ x : H, f z ≤ f x) ∧
      (∀ y : H, (∀ x : H, f y ≤ f x) → y = z) ∧
      Tendsto (iterate (gradient f) α x₀) atTop (𝓝 z) ∧
      Tendsto (fun n ↦ f (iterate (gradient f) α x₀ n)) atTop (𝓝 (f z)) ∧
      ∀ n : ℕ,
        0 ≤ f (iterate (gradient f) α x₀ n) - f z ∧
        f (iterate (gradient f) α x₀ n) - f z ≤ rate m α L ^ n * (f x₀ - f z) ∧
        ‖iterate (gradient f) α x₀ n - z‖ ^ 2 ≤
          (2 / m) * (rate m α L ^ n * (f x₀ - f z)) := by
  obtain ⟨z, hz⟩ := exists_stationary hdiff hsc hm hLip
  obtain ⟨hmin, huniq⟩ := stationary_unique_minimizer hdiff hsc hm hz
  have hρ₀ := rate_nonneg m α L
  have hρ₁ := rate_lt_one hm hL hα hαL
  have hlower (n : ℕ) := strong_lower_gap hdiff hsc hz (iterate (gradient f) α x₀ n)
  have hstep (n : ℕ) :
      f (iterate (gradient f) α x₀ (n + 1)) - f z ≤
        rate m α L * (f (iterate (gradient f) α x₀ n) - f z) := by
    rw [iterate_succ]
    exact gradient_descent_gap_step hdiff hsc hLip hm hL hα hαL hz _
  have hgap (n : ℕ) : 0 ≤ f (iterate (gradient f) α x₀ n) - f z := sub_nonneg.mpr (hmin _)
  have hx := tendsto_of_geometric_gap f (iterate (gradient f) α x₀) z hm hρ₀ hρ₁ hlower hstep
  have hf := gap_tendsto_zero f (iterate (gradient f) α x₀) z hρ₀ hρ₁ hgap hstep
  have hf' : Tendsto (fun n ↦ f (iterate (gradient f) α x₀ n)) atTop (𝓝 (f z)) := by
    simpa only [sub_add_cancel, zero_add] using hf.add_const (f z)
  refine ⟨z, hz, hmin, huniq, hx, hf', fun n ↦ ⟨hgap n, ?_, ?_⟩⟩
  · simpa only [iterate_zero] using
      geometric_gap_bound f (iterate (gradient f) α x₀) z hρ₀ hstep n
  · simpa only [iterate_zero] using
      squared_distance_bound f (iterate (gradient f) α x₀) z hm hρ₀ hlower hstep n

end GradientDescent
