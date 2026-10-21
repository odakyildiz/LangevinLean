import Mathlib.Analysis.Convex.Function
import Mathlib.Basic.Real.Basic

-- This project does not prescribe Mathlib copyright headers.
set_option linter.style.header false

/-!
# Convexity on the real line, with the quantifiers visible

The educational predicates below use ordinary real multiplication. The
equivalence theorems connect them to mathlib's general whole-space predicates.
-/

namespace ConvexityTutorial

/-- Jensen's inequality for two nonnegative weights that sum to one. -/
def IsConvex (f : ℝ → ℝ) : Prop :=
  ∀ x y a b : ℝ,
    0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a * x + b * y) ≤ a * f x + b * f y

/-- Strict Jensen inequality for distinct points and strictly positive weights. -/
def IsStrictlyConvex (f : ℝ → ℝ) : Prop :=
  ∀ x y a b : ℝ,
    x ≠ y → 0 < a → 0 < b → a + b = 1 →
      f (a * x + b * y) < a * f x + b * f y

/-- A point whose value is no greater than the value at any other real point. -/
def IsGlobalMinimizer (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ y : ℝ, f x ≤ f y

/-- The line with slope `slope` through `(x, f x)` lies below the entire graph. -/
def SupportsAt (f : ℝ → ℝ) (x slope : ℝ) : Prop :=
  ∀ y : ℝ, f x + slope * (y - x) ≤ f y

/-- The visible real-line definition is exactly mathlib convexity on all reals. -/
theorem isConvex_iff_mathlib (f : ℝ → ℝ) :
    IsConvex f ↔ ConvexOn ℝ Set.univ f := by
  constructor
  · intro hf
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    change f (a * x + b * y) ≤ a * f x + b * f y
    exact hf x y a b ha hb hab
  · intro hf
    unfold IsConvex
    intro x y a b ha hb hab
    have h := hf.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    simpa only [smul_eq_mul] using h

/-- The strict educational definition also agrees with mathlib's predicate. -/
theorem isStrictlyConvex_iff_mathlib (f : ℝ → ℝ) :
    IsStrictlyConvex f ↔ StrictConvexOn ℝ Set.univ f := by
  constructor
  · intro hf
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    change f (a * x + b * y) < a * f x + b * f y
    exact hf x y a b hxy ha hb hab
  · intro hf
    unfold IsStrictlyConvex
    intro x y a b hxy ha hb hab
    have h := hf.2 (Set.mem_univ x) (Set.mem_univ y) hxy ha hb hab
    simpa only [smul_eq_mul] using h

end ConvexityTutorial
