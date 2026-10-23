import KineticLangevin.Hessian
import UnadjustedLangevin.StrongConvexity
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open Set
open scoped RealInnerProductSpace NNReal
namespace KineticLangevin
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The scalar second variation along an actual affine line follows from the actual Hessian derivative. -/
theorem hessian_line_derivatives (f : E→ℝ) (H : E→E→L[ℝ] E)
    (hf : Differentiable ℝ f) (hH : ∀ x,HasFDerivAt (gradient f) (H x) x)
    (x u : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ f (x+s • u)) ⟪gradient f (x+t • u),u⟫ t ∧
    HasDerivAt (fun s : ℝ ↦ ⟪gradient f (x+s • u),u⟫) ⟪H (x+t • u) u,u⟫ t := by
  have hl := (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const u)
  constructor
  · convert ((hf (x+t • u)).hasGradientAt.hasFDerivAt.comp t hl.hasFDerivAt).hasDerivAt using 1
    · rfl
    · simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,
        smul_eq_mul,mul_one,one_smul,InnerProductSpace.toDual_apply_apply,zero_add]
  · have hh := ((hH (x+t • u)).comp t hl.hasFDerivAt).hasDerivAt
    convert hh.inner ℝ (hasDerivAt_const t u) using 1 <;> first
      | rfl
      | simp only [zero_add,inner_zero_right,add_zero,ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.toSpanSingleton_apply,one_smul]

/-- The lower Hessian quadratic bound implies the exact source strong-convexity assumption. -/
theorem strongConvex_of_hessian_lower (f : E→ℝ) (H : E→E→L[ℝ] E) (m : ℝ)
    (hf : Differentiable ℝ f) (hH : ∀ x,HasFDerivAt (gradient f) (H x) x)
    (hlower : ∀ x u,m*‖u‖^2≤⟪H x u,u⟫) : StrongConvexOn univ m f := by
  rw [strongConvexOn_iff_convex]
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  let u := y-x
  let F := fun t : ℝ ↦ f (x+t • u)-m/2*‖x+t • u‖^2
  let D := fun t : ℝ ↦ ⟪gradient f (x+t • u),u⟫-m*⟪x+t • u,u⟫
  let Q := fun t : ℝ ↦ ⟪H (x+t • u) u,u⟫-m*‖u‖^2
  have hD (t : ℝ) : HasDerivAt F (D t) t := by
    have hl := (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const u)
    convert (hessian_line_derivatives f H hf hH x u t).1.sub ((hl.norm_sq).const_mul (m/2)) using 1
    · rfl
    · dsimp [D]
      simp only [zero_add,one_smul]
      ring
  have hQ (t : ℝ) : HasDerivAt D (Q t) t := by
    have hl := (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const u)
    convert (hessian_line_derivatives f H hf hH x u t).2.sub
      (((hl.inner ℝ (hasDerivAt_const t u))).const_mul m) using 1
    · rfl
    · dsimp [Q]
      simp only [zero_add,one_smul,inner_zero_right,add_zero,real_inner_self_eq_norm_sq]
  have hconv : ConvexOn ℝ univ F := by
    apply convexOn_of_hasDerivWithinAt2_nonneg convex_univ
      ((continuous_iff_continuousAt.mpr (fun t ↦ (hD t).continuousAt)).continuousOn)
      (fun t _ ↦ (hD t).hasDerivWithinAt) (fun t _ ↦ (hQ t).hasDerivWithinAt)
    intro t _
    exact sub_nonneg.mpr (hlower _ _)
  have hc := hconv.2 (mem_univ 0) (mem_univ 1) ha hb hab
  have hline : x+b • u=a • x+b • y := by
    dsimp [u]
    rw [smul_sub]
    have haeq : a=1-b := by linarith
    rw [haeq]
    module
  simpa only [F,smul_eq_mul,mul_zero,mul_one,zero_add,zero_smul,add_zero,one_smul,
    show x+u=y by dsimp [u];abel,hline] using hc

/-- Symmetric positive semidefinite operators are bounded by their upper quadratic-form bound. -/
theorem hessian_norm_le_of_quadratic (T : E→L[ℝ] E) (M : ℝ≥0) (hSym : T.IsSymmetric)
    (hpos : ∀ u,0≤⟪T u,u⟫) (hupp : ∀ u,⟪T u,u⟫≤(M : ℝ)*‖u‖^2) : ‖T‖≤M := by
  rw [T.norm_eq_iSup_rayleighQuotient hSym]
  apply ciSup_le
  intro u
  by_cases hu : u=0
  · simp [hu,ContinuousLinearMap.rayleighQuotient]
  · have hp : 0<‖u‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
    simp only [ContinuousLinearMap.rayleighQuotient,ContinuousLinearMap.reApplyInnerSelf_apply,
      RCLike.re_to_real,abs_div,abs_of_nonneg (hpos u),abs_of_nonneg (sq_nonneg ‖u‖)]
    exact (div_le_iff₀ hp).mpr (hupp u)

/-- The upper Hessian bound implies the global gradient Lipschitz premise used by the checked sampler theorems. -/
theorem gradient_lipschitz_of_hessian_bounds (f : E→ℝ) (H : E→E→L[ℝ] E) (m : ℝ) (M : ℝ≥0)
    (hm : 0≤m) (hH : ∀ x,HasFDerivAt (gradient f) (H x) x)
    (hSym : ∀ x,(H x).IsSymmetric)
    (hlower : ∀ x u,m*‖u‖^2≤⟪H x u,u⟫)
    (hupper : ∀ x u,⟪H x u,u⟫≤(M : ℝ)*‖u‖^2) : LipschitzWith M (gradient f) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (fun x ↦ (hH x).differentiableAt)
  intro x
  rw [(hH x).fderiv]
  exact_mod_cast hessian_norm_le_of_quadratic (H x) M (hSym x)
    (fun u ↦ (mul_nonneg hm (sq_nonneg ‖u‖)).trans (hlower x u)) (hupper x)

/-- Both source first-order assumptions follow from actual symmetric Hessians between mI and MI. -/
theorem hessian_bounds_firstOrder (f : E→ℝ) (H : E→E→L[ℝ] E) (m : ℝ) (M : ℝ≥0)
    (hm : 0≤m) (hf : Differentiable ℝ f) (hH : ∀ x,HasFDerivAt (gradient f) (H x) x)
    (hSym : ∀ x,(H x).IsSymmetric)
    (hlower : ∀ x u,m*‖u‖^2≤⟪H x u,u⟫)
    (hupper : ∀ x u,⟪H x u,u⟫≤(M : ℝ)*‖u‖^2) :
    StrongConvexOn univ m f ∧ LipschitzWith M (gradient f) :=
  ⟨strongConvex_of_hessian_lower f H m hf hH hlower,
    gradient_lipschitz_of_hessian_bounds f H m M hm hH hSym hlower hupper⟩
end KineticLangevin
