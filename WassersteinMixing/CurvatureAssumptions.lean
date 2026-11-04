import WassersteinMixing.Curvature
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # The original `C²` Hessian assumptions imply the potential contract

The source matrix inequalities are written as inequalities of quadratic
forms of the actual Hessian.  No first-order convexity or Lipschitz-gradient
hypothesis is added: both are derived below.
-/

noncomputable section
open MeasureTheory Set

namespace WassersteinMixing

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The literal source Hessian bounds on a twice continuously differentiable potential. -/
structure HessianAssumptions (P : Parameters) (V : H → ℝ) : Prop where
  regularity : ContDiff ℝ 2 V
  lower : ∀ x v, P.alpha * ‖v‖ ^ 2 ≤ inner ℝ v (hessianOperator V x v)
  upper : ∀ x v, inner ℝ v (hessianOperator V x v) ≤ P.beta * ‖v‖ ^ 2

/-- Uniform positive Hessian form bounds imply the sharp operator norm bound. -/
theorem hessian_norm_le_of_forms (P : Parameters) (V : H → ℝ)
    (hV : HessianAssumptions P V) (x : H) : ‖hessianOperator V x‖ ≤ P.beta := by
  let T := P.beta⁻¹ • hessianOperator V x
  have hb := P.beta_pos
  have hsym (u v : H) : inner ℝ (T u) v = inner ℝ u (T v) := by
    simp only [T, smul_apply, real_inner_smul_left,
      real_inner_smul_right, hessianOperator_symmetric V hV.regularity]
  have hpos (v : H) : 0 ≤ inner ℝ v (T v) := by
    have hl := hV.lower x v
    simp only [T, smul_apply, real_inner_smul_right]
    exact mul_nonneg (inv_nonneg.mpr hb.le) ((mul_nonneg P.alpha_pos.le (sq_nonneg _)).trans hl)
  have hupper (v : H) : inner ℝ v (T v) ≤ ‖v‖ ^ 2 := by
    have hu := mul_le_mul_of_nonneg_left (hV.upper x v) (inv_nonneg.mpr hb.le)
    simpa only [T, smul_apply, real_inner_smul_right,
      ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hb), one_mul] using hu
  apply (hessianOperator V x).opNorm_le_bound hb.le
  intro v
  have hc := positive_contraction_cocoercive T hsym hpos hupper v
  have hnorm : ‖T v‖ ≤ ‖v‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hc.trans (hupper v))
  have heq : ‖T v‖ = ‖hessianOperator V x v‖ / P.beta := by
    simp only [T, smul_apply, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hb), div_eq_inv_mul]
  rw [heq] at hnorm
  simpa only [mul_comm] using (div_le_iff₀ hb).mp hnorm

/-- The source smoothness bound implies global Lipschitzness of the true gradient. -/
theorem gradient_lipschitz_of_hessian (P : Parameters) (V : H → ℝ)
    (hV : HessianAssumptions P V) :
    LipschitzWith ⟨P.beta, P.beta_pos.le⟩ (gradient V) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((contDiff_gradient_of_two V hV.regularity).differentiable (by norm_num))
  intro x
  exact_mod_cast hessian_norm_le_of_forms P V hV x

/-- The lower source Hessian bound implies the full first-order strong supporting plane. -/
theorem strong_support_of_hessian (P : Parameters) (V : H → ℝ)
    (hV : HessianAssumptions P V) (x y : H) :
    V x + inner ℝ (gradient V x) (y - x) + P.alpha / 2 * ‖y - x‖ ^ 2 ≤ V y := by
  let v := y - x
  let φ : ℝ → ℝ := fun t ↦ inner ℝ (gradient V (x + t • v)) v
  have hg := (contDiff_gradient_of_two V hV.regularity).differentiable (by norm_num)
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ ↦ gradient V (x + s • v))
      (hessianOperator V (x + t • v) v) t := by
    exact (hg _).hasFDerivAt.comp_hasDerivAt t
      (by simpa using ((hasDerivAt_id t).smul_const v).const_add x)
  have hdφ (t : ℝ) : HasDerivAt φ (inner ℝ (hessianOperator V (x + t • v) v) v) t := by
    simpa only [φ, inner_zero_right, zero_add] using (hd t).inner ℝ (hasDerivAt_const t v)
  have hφ : Continuous φ := by
    exact (((contDiff_gradient_of_two V hV.regularity).continuous.comp
      (by fun_prop : Continuous (fun t : ℝ ↦ x + t • v))).inner continuous_const)
  have hφbound (t : ℝ) (ht : 0 ≤ t) : φ 0 + P.alpha * ‖v‖ ^ 2 * t ≤ φ t := by
    have hm := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).mul_sub_le_image_sub_of_le_deriv
      hφ.continuousOn (fun s _ ↦ (hdφ s).differentiableAt.differentiableWithinAt)
      (C := P.alpha * ‖v‖ ^ 2)
      (fun s _ ↦ by rw [(hdφ s).deriv, real_inner_comm]; exact hV.lower _ v)
      0 (mem_univ _) t (mem_univ _) ht
    simp only [sub_zero] at hm
    linarith
  have hVd (t : ℝ) : HasDerivAt (fun s : ℝ ↦ V (x + s • v)) (φ t) t := by
    have hl : HasDerivAt (fun s : ℝ ↦ x + s • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have hh := (hV.regularity.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t hl
    simpa only [φ, Function.comp_def, inner_gradient_left] using hh
  have hVint := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hVd t)
    (hφ.intervalIntegrable 0 1)
  have hpint : IntervalIntegrable (fun t : ℝ ↦ φ 0 + P.alpha * ‖v‖ ^ 2 * t) volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ ↦ φ 0 + P.alpha * ‖v‖ ^ 2 * t)).intervalIntegrable _ _
  have hm := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    hpint (hφ.intervalIntegrable 0 1) (fun t ht ↦ hφbound t ht.1)
  have hp : IntervalIntegrable (fun t : ℝ ↦ P.alpha * ‖v‖ ^ 2 * t) volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ ↦ P.alpha * ‖v‖ ^ 2 * t)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add intervalIntegrable_const hp,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id] at hm
  rw [hVint] at hm
  simp only [φ, v, zero_smul, add_zero, one_smul, add_sub_cancel, sub_zero,
    one_pow, zero_pow (by norm_num : 2 ≠ 0), one_div, zero_div, smul_eq_mul, one_mul] at hm
  nlinarith

omit [CompleteSpace H] in
/-- Supporting planes suffice for convexity; this elementary lemma avoids any
additional differentiability premise on the abstract supporting vector field. -/
theorem convexOn_of_supporting_planes (F : H → ℝ) (G : H → H)
    (hplane : ∀ x y, F x + inner ℝ (G x) (y - x) ≤ F y) : ConvexOn ℝ Set.univ F := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z := a • x + b • y
  have hx := mul_le_mul_of_nonneg_left (hplane z x) ha
  have hy := mul_le_mul_of_nonneg_left (hplane z y) hb
  have hvec : a • (x - z) + b • (y - z) = 0 := by
    calc
      _ = a • x + b • y - (a + b) • z := by module
      _ = 0 := by rw [hab, one_smul]; simp only [z, sub_self]
  have hi := congrArg (fun w ↦ inner ℝ (G z) w) hvec
  simp only [inner_add_right, real_inner_smul_right, inner_zero_right] at hi
  change F z ≤ a * F x + b * F y
  nlinarith [congrArg (fun t : ℝ ↦ t * F z) hab]

/-- The source lower Hessian bound implies strong convexity. -/
theorem strongConvexity_of_hessian (P : Parameters) (V : H → ℝ)
    (hV : HessianAssumptions P V) : StrongConvexOn Set.univ P.alpha V := by
  apply strongConvexOn_iff_convex.mpr
  apply convexOn_of_supporting_planes _ (fun x ↦ gradient V x - P.alpha • x)
  intro x y
  have hs := strong_support_of_hessian P V hV x y
  rw [inner_sub_left, real_inner_smul_left]
  rw [norm_sub_sq_real] at hs
  simp only [inner_sub_right, real_inner_self_eq_norm_sq] at hs ⊢
  rw [real_inner_comm x y] at hs
  nlinarith

/-- The original Hessian assumptions discharge every field of the potential contract. -/
theorem HessianAssumptions.toPotentialAssumptions (P : Parameters) (V : H → ℝ)
    (hV : HessianAssumptions P V) : PotentialAssumptions P V where
  regularity := hV.regularity
  strongConvexity := strongConvexity_of_hessian P V hV
  gradientLipschitz := gradient_lipschitz_of_hessian P V hV

end WassersteinMixing
