import UnadjustedLangevin.StrongConvexity
import Mathlib.Topology.MetricSpace.Lipschitz

set_option linter.style.header false

/-!
# Compatibility of strong convexity and a Lipschitz gradient

On a nontrivial Hilbert space the inequality `m ≤ L` is a consequence of the
potential assumptions, and does not need to be an independent numerical input.
The gradient is that of the same differentiable function in both hypotheses.
-/

noncomputable section

open scoped NNReal

namespace ULA

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [Nontrivial H]

/-- The strong-convexity constant cannot exceed the gradient Lipschitz constant
on a nontrivial Hilbert space. Neither constant needs to be positive here. -/
theorem strongConvex_le_lipschitz {U : H → ℝ} {m : ℝ} {L : ℝ≥0}
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (hLip : LipschitzWith L (gradient U)) : m ≤ (L : ℝ) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hmono : m * ‖x‖ ^ 2 ≤ inner ℝ (gradient U x - gradient U 0) x := by
    simpa only [sub_zero] using strong_gradient_monotone hdiff hsc x 0
  have hbound : inner ℝ (gradient U x - gradient U 0) x ≤ (L : ℝ) * ‖x‖ ^ 2 := by
    calc
      _ ≤ ‖gradient U x - gradient U 0‖ * ‖x‖ := real_inner_le_norm _ _
      _ ≤ ((L : ℝ) * ‖x‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (by simpa only [sub_zero] using hLip.norm_sub_le x 0)
          (norm_nonneg x)
      _ = _ := by ring
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hxpos)).mp
    (by simpa only [mul_comm] using hmono.trans hbound)

end ULA
