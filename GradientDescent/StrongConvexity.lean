import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! # First-order consequences of strong convexity

All statements use Mathlib's `StrongConvexOn Set.univ m f`, with quadratic
normalization `m / 2`. In a real Hilbert space this is equivalent to convexity
of `fun x ↦ f x - m / 2 * ‖x‖ ^ 2`.
-/

noncomputable section

namespace GradientDescent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A differentiable convex function lies above each of its tangent planes. -/
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

/-- The first-order inequality associated with `m`-strong convexity. -/
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

/-- Strong convexity makes the gradient strongly monotone. -/
lemma strong_gradient_monotone [CompleteSpace H] {f : H → ℝ} {m : ℝ}
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ m f) (x y : H) :
    m * ‖x - y‖ ^ 2 ≤ inner ℝ (gradient f x - gradient f y) (x - y) := by
  have hxy := strong_first_order hdiff hsc x y
  have hyx := strong_first_order hdiff hsc y x
  rw [norm_sub_rev y x] at hxy
  have hi : inner ℝ (gradient f x) (y - x) =
      -inner ℝ (gradient f x) (x - y) := by
    rw [← neg_sub, inner_neg_right]
  rw [hi] at hxy
  rw [inner_sub_left]
  linarith

/-- A stationary point has a quadratic lower bound on the objective gap. -/
lemma strong_lower_gap [CompleteSpace H] {f : H → ℝ} {m : ℝ}
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ m f)
    {z : H} (hz : gradient f z = 0) (x : H) :
    m / 2 * ‖x - z‖ ^ 2 ≤ f x - f z := by
  have h := strong_first_order hdiff hsc z x
  rw [hz, inner_zero_left, add_zero] at h
  linarith

/-- Strong convexity gives the Polyak--Łojasiewicz upper bound on an objective gap.
The reference point can be arbitrary; no stationarity hypothesis is required. -/
lemma strong_upper_gap [CompleteSpace H] {f : H → ℝ} {m : ℝ}
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ m f)
    (hm : 0 < m) (x z : H) :
    f x - f z ≤ ‖gradient f x‖ ^ 2 / (2 * m) := by
  have hfirst := strong_first_order hdiff hsc x z
  have hinner := neg_le_of_abs_le (abs_real_inner_le_norm (gradient f x) (z - x))
  have hgap : f x - f z ≤
      ‖gradient f x‖ * ‖z - x‖ - m / 2 * ‖z - x‖ ^ 2 := by
    linarith
  apply hgap.trans
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * m)).2
  nlinarith [sq_nonneg (m * ‖z - x‖ - ‖gradient f x‖)]

end GradientDescent
