import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Topology.MetricSpace.Contracting

/-! Squared and square-root bounds for a strongly monotone Lipschitz Euler step.
See `exposition/GradientDescent.tex` for the corresponding mathematical proof. -/

open scoped NNReal

namespace GradientDescent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Monotonicity and Lipschitz bounds control squared distance after one Euler step. -/
theorem gradient_step_sq_bound
    (x y gx gy : H) (m h : ℝ) (L : ℝ≥0) (hh : 0 ≤ h)
    (hmono : m * ‖x - y‖ ^ 2 ≤ inner ℝ (gx - gy) (x - y))
    (hLip : ‖gx - gy‖ ≤ (L : ℝ) * ‖x - y‖) :
    ‖(x - h • gx) - (y - h • gy)‖ ^ 2 ≤
      (1 - 2 * h * m + h ^ 2 * (L : ℝ) ^ 2) * ‖x - y‖ ^ 2 := by
  have hLipSq : ‖gx - gy‖ ^ 2 ≤ (L : ℝ) ^ 2 * ‖x - y‖ ^ 2 := by
    nlinarith [norm_nonneg (gx - gy), norm_nonneg (x - y), L.coe_nonneg]
  have hmonoScaled := mul_le_mul_of_nonneg_left hmono (show 0 ≤ 2 * h by positivity)
  have hLipScaled := mul_le_mul_of_nonneg_left hLipSq (sq_nonneg h)
  rw [show (x - h • gx) - (y - h • gy) = (x - y) - h • (gx - gy) by module,
    norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hh, ← real_inner_comm (x - y) (gx - gy)]
  nlinarith

/-- One Euler step satisfies the usual square-root norm bound; the coefficient
need not be assumed nonnegative. -/
theorem gradient_step_contract
    (x y gx gy : H) (m h : ℝ) (L : ℝ≥0) (hh : 0 ≤ h)
    (hmono : m * ‖x - y‖ ^ 2 ≤ inner ℝ (gx - gy) (x - y))
    (hLip : ‖gx - gy‖ ≤ (L : ℝ) * ‖x - y‖) :
    ‖(x - h • gx) - (y - h • gy)‖ ≤
      Real.sqrt (1 - 2 * h * m + h ^ 2 * (L : ℝ) ^ 2) * ‖x - y‖ := by
  have hsq := gradient_step_sq_bound x y gx gy m h L hh hmono hLip
  have hbound := Real.le_sqrt_of_sq_le hsq
  rwa [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hbound

/-- The Euler step is a contraction whenever `0 < α` and `α L² < 2m`.
This sufficient condition is used only to construct a minimizer. -/
theorem contracting_gradient_step (g : H → H) (m α : ℝ) (L : ℝ≥0)
    (hα : 0 < α) (hsmall : α * (L : ℝ) ^ 2 < 2 * m)
    (hmono : ∀ x y, m * ‖x - y‖ ^ 2 ≤ inner ℝ (g x - g y) (x - y))
    (hLip : LipschitzWith L g) :
    ContractingWith (⟨Real.sqrt (1 - 2 * α * m + α ^ 2 * (L : ℝ) ^ 2),
      Real.sqrt_nonneg _⟩ : ℝ≥0) (fun x ↦ x - α • g x) := by
  constructor
  · change Real.sqrt (1 - 2 * α * m + α ^ 2 * (L : ℝ) ^ 2) < 1
    have hq : 1 - 2 * α * m + α ^ 2 * (L : ℝ) ^ 2 < 1 := by
      nlinarith [mul_pos hα (sub_pos.mpr hsmall)]
    simpa only [Real.sqrt_one] using
      (Real.sqrt_lt_sqrt_iff_of_pos (show (0:ℝ) < 1 by norm_num)).2 hq
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have hb : ‖g x - g y‖ ≤ (L : ℝ) * ‖x - y‖ := by
      simpa only [dist_eq_norm] using hLip.dist_le_mul x y
    simp only [dist_eq_norm]
    change ‖(x - α • g x) - (y - α • g y)‖ ≤
      Real.sqrt (1 - 2 * α * m + α ^ 2 * (L : ℝ) ^ 2) * ‖x - y‖
    exact gradient_step_contract x y (g x) (g y) m α L hα.le (hmono x y) hb

end GradientDescent
