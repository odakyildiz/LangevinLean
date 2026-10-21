import GradientDescent.Rates
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Strong

-- This project does not prescribe Mathlib copyright headers.
set_option linter.style.header false

/-! # Sharpness of the strict step-size endpoints

The one-dimensional objective `quadratic x = x² / 2` is `1`-strongly convex
and its gradient is `1`-Lipschitz. From the initial point `1`, step size `0`
produces the constant sequence `1`, while step size `2` produces `(-1)^n`.
Neither sequence tends to the unique minimizer `0`.
-/

noncomputable section

namespace GradientDescent

open Filter
open scoped Topology

/-- A quadratic with strong-convexity and gradient-Lipschitz constants both `1`. -/
def quadratic (x : ℝ) : ℝ := x ^ 2 / 2

lemma quadratic_hasDerivAt (x : ℝ) : HasDerivAt quadratic x x := by
  have h := ((hasDerivAt_id x).pow 2).div_const 2
  convert h using 1
  · rfl
  · simp

lemma quadratic_differentiable : Differentiable ℝ quadratic :=
  fun x => (quadratic_hasDerivAt x).differentiableAt

@[simp]
lemma gradient_quadratic (x : ℝ) : gradient quadratic x = x := by
  rw [gradient_eq_deriv', (quadratic_hasDerivAt x).deriv]

lemma quadratic_strongConvex : StrongConvexOn Set.univ 1 quadratic := by
  apply strongConvexOn_iff_convex.mpr
  have hzero : (fun x : ℝ => quadratic x - (1 : ℝ) / 2 * ‖x‖ ^ 2) =
      (fun _ : ℝ => (0 : ℝ)) := by
    funext x
    simp [quadratic, Real.norm_eq_abs, sq_abs]
    ring
  rw [hzero]
  exact convexOn_const 0 (convex_univ : Convex ℝ (Set.univ : Set ℝ))

lemma quadratic_gradient_lipschitz : LipschitzWith 1 (gradient quadratic) := by
  simpa only [show gradient quadratic = id by funext x; exact gradient_quadratic x] using
    (LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ))

/-- Exact iterates of the quadratic from the initial point `1`. -/
lemma quadratic_iterate (α : ℝ) (n : ℕ) :
    iterate (gradient quadratic) α (1 : ℝ) n = (1 - α) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iterate_succ, ih, gradient_quadratic, smul_eq_mul, pow_succ]
      ring

lemma quadratic_iterate_zero (n : ℕ) :
    iterate (gradient quadratic) 0 (1 : ℝ) n = 1 := by
  simp [quadratic_iterate]

lemma quadratic_iterate_two (n : ℕ) :
    iterate (gradient quadratic) 2 (1 : ℝ) n = (-1 : ℝ) ^ n := by
  norm_num [quadratic_iterate]

/-- The lower step-size endpoint does not guarantee convergence to the minimizer. -/
theorem quadratic_zero_step_not_tendsto :
    ¬ Tendsto (iterate (gradient quadratic) 0 (1 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
  intro h
  have hn : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    change Tendsto (fun n => iterate (gradient quadratic) 0 (1 : ℝ) n) atTop
      (𝓝 (0 : ℝ)) at h
    simpa only [quadratic_iterate_zero] using h
  have heq : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hn
  norm_num at heq

/-- The upper step-size endpoint does not guarantee convergence to the minimizer. -/
theorem quadratic_two_step_not_tendsto :
    ¬ Tendsto (iterate (gradient quadratic) 2 (1 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
  intro h
  have hn : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [quadratic_iterate_two, norm_pow, norm_neg, norm_one, one_pow,
      norm_zero] using h.norm
  have heq : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hn
  norm_num at heq

end GradientDescent
