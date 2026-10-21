import ConvexityTutorial.Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

-- This project does not prescribe Mathlib copyright headers.
set_option linter.style.header false

/-! # Five elementary convexity facts proved directly from Jensen's inequality -/

namespace ConvexityTutorial

/-- A constant function is convex: its weighted average is the same constant. -/
theorem convex_const (c : ℝ) : IsConvex (fun _ : ℝ ↦ c) := by
  unfold IsConvex
  intro x y a b ha hb hab
  change c ≤ a * c + b * c
  apply le_of_eq
  calc
    c = (a + b) * c := by rw [hab, one_mul]
    _ = a * c + b * c := by rw [add_mul]

/-- An affine function satisfies Jensen's inequality with equality. -/
theorem convex_affine (s c : ℝ) : IsConvex (fun x : ℝ ↦ s * x + c) := by
  unfold IsConvex
  intro x y a b ha hb hab
  change s * (a * x + b * y) + c ≤ a * (s * x + c) + b * (s * y + c)
  apply le_of_eq
  calc
    s * (a * x + b * y) + c = s * (a * x + b * y) + (a + b) * c := by
      rw [hab, one_mul]
    _ = a * (s * x + c) + b * (s * y + c) := by ring

/-- Equal Jensen weights give the familiar midpoint inequality. -/
theorem convex_midpoint (f : ℝ → ℝ) (hf : IsConvex f) (x y : ℝ) :
    f ((x + y) / 2) ≤ (f x + f y) / 2 := by
  have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have hsum : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  have h := hf x y (1 / 2) (1 / 2) hhalf hhalf hsum
  have hpoint : (1 / 2 : ℝ) * x + (1 / 2 : ℝ) * y = (x + y) / 2 := by ring
  have hvalue : (1 / 2 : ℝ) * f x + (1 / 2 : ℝ) * f y = (f x + f y) / 2 := by ring
  rw [hpoint, hvalue] at h
  exact h

/-- Adding two convex functions adds their Jensen inequalities. -/
theorem convex_add (f g : ℝ → ℝ) (hf : IsConvex f) (hg : IsConvex g) :
    IsConvex (fun x : ℝ ↦ f x + g x) := by
  unfold IsConvex
  intro x y a b ha hb hab
  have h_f := hf x y a b ha hb hab
  have h_g := hg x y a b ha hb hab
  change f (a * x + b * y) + g (a * x + b * y) ≤
    a * (f x + g x) + b * (f y + g y)
  calc
    f (a * x + b * y) + g (a * x + b * y) ≤
        (a * f x + b * f y) + (a * g x + b * g y) := add_le_add h_f h_g
    _ = a * (f x + g x) + b * (f y + g y) := by ring

/-- Multiplication by a nonnegative constant preserves convexity. -/
theorem convex_nonnegative_scale (f : ℝ → ℝ) (hf : IsConvex f)
    (c : ℝ) (hc : 0 ≤ c) : IsConvex (fun x : ℝ ↦ c * f x) := by
  unfold IsConvex
  intro x y a b ha hb hab
  have h := hf x y a b ha hb hab
  change c * f (a * x + b * y) ≤ a * (c * f x) + b * (c * f y)
  calc
    c * f (a * x + b * y) ≤ c * (a * f x + b * f y) :=
      mul_le_mul_of_nonneg_left h hc
    _ = a * (c * f x) + b * (c * f y) := by ring

end ConvexityTutorial
