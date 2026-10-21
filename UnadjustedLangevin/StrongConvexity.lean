import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Linarith

/-! Supporting-plane inequalities and strong gradient monotonicity.
See `StrongConvexity.tex` for the corresponding mathematical proof. -/

noncomputable section

namespace ULA

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Convexity bounds each secant below by the directional derivative at its starting point. -/
lemma convex_first_order {f : H → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f) (x y : H) :
    f x + fderiv ℝ f x (y - x) ≤ f y := by
  let line : ℝ →ᵃ[ℝ] H := AffineMap.lineMap x y
  have hc : ConvexOn ℝ Set.univ (f ∘ line) := by
    simpa [line] using hf.comp_affineMap line
  have hl : HasDerivAt line (y - x) 0 := by
    change HasDerivAt (fun t : ℝ ↦ t • (y - x) + x) (y - x) 0
    simpa using
      ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).add_const x
  have hd : HasDerivAt (f ∘ line) (fderiv ℝ f x (y - x)) 0 := by
    exact (hdiff x).hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp [line])
  have hs := hc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1)
    (zero_lt_one : (0 : ℝ) < 1) hd
  simp only [slope_def_field, Function.comp_apply, line, AffineMap.lineMap_apply_one,
    AffineMap.lineMap_apply_zero, sub_zero, div_one] at hs
  linarith

/-- Strong convexity makes the gradient strongly monotone. -/
lemma strong_gradient_monotone [CompleteSpace H] {f : H → ℝ} {m : ℝ}
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ m f) (x y : H) :
    m * ‖x - y‖ ^ 2 ≤ inner ℝ (gradient f x - gradient f y) (x - y) := by
  let g : H → ℝ := fun v ↦ f v - m / 2 * ‖v‖ ^ 2
  have hc : ConvexOn ℝ Set.univ g := strongConvexOn_iff_convex.mp hsc
  have hg (v : H) : HasFDerivAt g
      (fderiv ℝ f v - (m / 2) • (2 • innerSL ℝ v)) v := by
    exact (hdiff v).hasFDerivAt.sub
      ((hasStrictFDerivAt_norm_sq v).hasFDerivAt.const_mul (m / 2))
  have hgd : Differentiable ℝ g := fun v ↦ (hg v).differentiableAt
  have hxy := convex_first_order hc hgd x y
  have hyx := convex_first_order hc hgd y x
  rw [(hg x).fderiv] at hxy
  rw [(hg y).fderiv] at hyx
  simp only [g, sub_apply, smul_apply,
    smul_eq_mul, innerSL_apply_apply, ← inner_gradient_left] at hxy hyx
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  rw [norm_sub_sq_real]
  simp only [inner_sub_right, real_inner_self_eq_norm_sq, two_smul,
    real_inner_comm] at hxy hyx ⊢
  nlinarith

/-- The supporting-plane inequality associated with `m`-strong convexity.
This shared form supplies both sharp ULA contraction and Gibbs tail bounds. -/
lemma strong_first_order [CompleteSpace H] {f : H → ℝ} {m : ℝ}
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ m f) (x y : H) :
    f x + inner ℝ (gradient f x) (y - x) + m / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  let g : H → ℝ := fun v ↦ f v - m / 2 * ‖v‖ ^ 2
  have hc : ConvexOn ℝ Set.univ g := strongConvexOn_iff_convex.mp hsc
  have hg (v : H) : HasFDerivAt g
      (fderiv ℝ f v - (m / 2) • (2 • innerSL ℝ v)) v := by
    exact (hdiff v).hasFDerivAt.sub
      ((hasStrictFDerivAt_norm_sq v).hasFDerivAt.const_mul (m / 2))
  have hgd : Differentiable ℝ g := fun v ↦ (hg v).differentiableAt
  have hxy := convex_first_order hc hgd x y
  rw [(hg x).fderiv] at hxy
  simp only [g, sub_apply, smul_apply, smul_eq_mul, innerSL_apply_apply,
    ← inner_gradient_left, inner_sub_right, real_inner_self_eq_norm_sq,
    two_smul, add_apply] at hxy
  rw [norm_sub_sq_real]
  simp only [inner_sub_right, real_inner_comm] at hxy ⊢
  nlinarith

end ULA
