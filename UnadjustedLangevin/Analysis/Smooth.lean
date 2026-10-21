import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The quadratic upper bound for a function with a Lipschitz gradient

This shared analytic lemma underlies ULA contraction and the Gibbs/MALA
estimates. Restrict the function to the line segment from `x` to `y`, subtract
the affine approximation and a quadratic correction, and show that the
resulting scalar function is decreasing on `[0, 1]`.
-/

open scoped NNReal

namespace ULA.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A Lipschitz gradient gives the usual quadratic upper bound. -/
theorem smooth_upper_bound (f : H → ℝ) (L : ℝ≥0)
    (hf : Differentiable ℝ f) (hLip : LipschitzWith L (gradient f)) (x y : H) :
    f y ≤ f x + inner ℝ (gradient f x) (y - x) + (L : ℝ) / 2 * ‖y - x‖ ^ 2 := by
  let d := y - x
  let a := inner ℝ (gradient f x) d
  let b := ‖d‖ ^ 2
  let q : ℝ → ℝ := fun t => f (x + t • d) - f x - t * a - (L : ℝ) / 2 * t ^ 2 * b
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ => x + s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have hcomp (t : ℝ) :
      HasDerivAt (fun s : ℝ => f (x + s • d)) (inner ℝ (gradient f (x + t • d)) d) t := by
    simpa [Function.comp_def, inner_gradient_left] using
      (hf (x + t • d)).hasFDerivAt.comp_hasDerivAt t (hline t)
  have hq (t : ℝ) :
      HasDerivAt q (inner ℝ (gradient f (x + t • d)) d - a - (L : ℝ) * t * b) t := by
    convert (((hcomp t).sub_const (f x)).sub ((hasDerivAt_id t).mul_const a)).sub
      (((hasDerivAt_id t).pow 2).const_mul ((L : ℝ) / 2) |>.mul_const b) using 1
    · ext s
      simp only [q, Pi.sub_apply, Pi.pow_apply, id_eq]
    · simp only [id_eq]
      ring
  have hq_nonpos (t : ℝ) (ht : t ∈ interior (Set.Icc (0 : ℝ) 1)) :
      inner ℝ (gradient f (x + t • d)) d - a - (L : ℝ) * t * b ≤ 0 := by
    have ht0 : 0 ≤ t := (interior_subset ht).1
    have hnorm : ‖gradient f (x + t • d) - gradient f x‖ ≤ (L : ℝ) * t * ‖d‖ := by
      simpa [dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, mul_assoc] using
        hLip.dist_le_mul (x + t • d) x
    have hinner := real_inner_le_norm (gradient f (x + t • d) - gradient f x) d
    have hprod := mul_le_mul_of_nonneg_right hnorm (norm_nonneg d)
    rw [inner_sub_left] at hinner
    dsimp [a, b]
    nlinarith
  have hanti : AntitoneOn q (Set.Icc (0 : ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact (continuous_iff_continuousAt.mpr (fun t => (hq t).continuousAt)).continuousOn
    · exact (show Differentiable ℝ q from fun t => (hq t).differentiableAt).differentiableOn
    · intro t ht
      rw [(hq t).deriv]
      exact hq_nonpos t ht
  have hfinal := hanti (by simp : (0 : ℝ) ∈ Set.Icc 0 1)
    (by simp : (1 : ℝ) ∈ Set.Icc 0 1) (by norm_num : (0 : ℝ) ≤ 1)
  dsimp [q, a, b, d] at hfinal
  simp only [one_smul, zero_smul, add_zero, zero_mul, one_mul, one_pow, zero_pow
      (by norm_num : 2 ≠ 0), mul_zero, sub_self] at hfinal
  have hxy : x + (y - x) = y := by abel
  rw [hxy] at hfinal
  linarith

end ULA.Analysis
