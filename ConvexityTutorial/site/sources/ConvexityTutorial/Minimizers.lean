import ConvexityTutorial.Basic

-- This project does not prescribe Mathlib copyright headers.
set_option linter.style.header false

/-! # Convex combinations and uniqueness of global minimizers -/

namespace ConvexityTutorial

/-- Every convex combination of two global minimizers is again a minimizer. -/
theorem convex_combination_minimizer (f : ℝ → ℝ) (hf : IsConvex f)
    (x y a b : ℝ) (hx : IsGlobalMinimizer f x) (hy : IsGlobalMinimizer f y)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    IsGlobalMinimizer f (a * x + b * y) := by
  have hsame : f y = f x := le_antisymm (hy x) (hx y)
  have hcomb : f (a * x + b * y) ≤ f x := by
    calc
      f (a * x + b * y) ≤ a * f x + b * f y := hf x y a b ha hb hab
      _ = (a + b) * f x := by rw [hsame]; ring
      _ = f x := by rw [hab, one_mul]
  unfold IsGlobalMinimizer
  intro z
  calc
    f (a * x + b * y) ≤ f x := hcomb
    _ ≤ f z := hx z

/-- Strict convexity makes two distinct global minimizers impossible. -/
theorem strictly_convex_unique_minimizer (f : ℝ → ℝ) (hf : IsStrictlyConvex f)
    (x y : ℝ) (hx : IsGlobalMinimizer f x) (hy : IsGlobalMinimizer f y) : x = y := by
  by_contra hxy
  have hhalf : 0 < (1 / 2 : ℝ) := by norm_num
  have hsum : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  have hstrict := hf x y (1 / 2) (1 / 2) hxy hhalf hhalf hsum
  have hsame : f y = f x := le_antisymm (hy x) (hx y)
  rw [hsame] at hstrict
  have hminimal := hx ((1 / 2 : ℝ) * x + (1 / 2 : ℝ) * y)
  linarith

end ConvexityTutorial
