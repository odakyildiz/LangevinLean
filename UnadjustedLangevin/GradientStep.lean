import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity

/-! Squared and square-root bounds for a strongly monotone Lipschitz Euler step.
See `GradientStep.tex` for the corresponding mathematical proof. -/

open scoped NNReal

namespace ULA

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

end ULA
