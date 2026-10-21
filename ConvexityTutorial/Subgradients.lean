import ConvexityTutorial.Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Supporting lines and optimality

These real-variable results use only a supporting-line inequality. No derivative
is needed: a supporting slope is an explicit certificate that the affine line
stays below the function everywhere.
-/

namespace ConvexityTutorial

/-- A horizontal supporting line certifies a global minimum. -/
theorem global_minimizer_of_zero_support
    (f : ℝ → ℝ) (x : ℝ) (hsupport : SupportsAt f x 0) :
    IsGlobalMinimizer f x := by
  intro y
  have h := hsupport y
  simpa only [zero_mul, add_zero] using h

/-- Conversely, a global minimum supplies a horizontal supporting line. -/
theorem zero_support_of_global_minimizer
    (f : ℝ → ℝ) (x : ℝ) (hmin : IsGlobalMinimizer f x) :
    SupportsAt f x 0 := by
  intro y
  have h := hmin y
  simpa only [zero_mul, add_zero] using h

/-- Supporting slopes are monotone: their change has the same sign as the
change in position. Add the two supporting-line inequalities to prove this. -/
theorem supporting_slopes_monotone
    (f : ℝ → ℝ) (x y gx gy : ℝ)
    (hx : SupportsAt f x gx) (hy : SupportsAt f y gy) :
    0 ≤ (gy - gx) * (y - x) := by
  have hxy := hx y
  have hyx := hy x
  have hsum : gx * (y - x) + gy * (x - y) ≤ 0 := by
    linarith
  calc
    0 ≤ -(gx * (y - x) + gy * (x - y)) := neg_nonneg.mpr hsum
    _ = (gy - gx) * (y - x) := by ring

end ConvexityTutorial
