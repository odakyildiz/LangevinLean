import KineticLangevin.LpHessian
import KineticLangevin.GaussianTruncation
import UnadjustedLangevin.SharpContraction

/-! # The sharp Hessian-difference operator bound and its actual L² cutoff -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal RealInnerProductSpace
namespace KineticLangevin
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Centering a strongly convex smooth gradient halves the width of its curvature interval. -/
theorem centered_gradient_lipschitz (f : E→ℝ) (m : ℝ) (M : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m≤(M:ℝ)) :
    LipschitzWith ⟨((M:ℝ)-m)/2,by linarith⟩ (fun x ↦ gradient f x-((m+(M:ℝ))/2) • x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,dist_eq_norm]
  have hb := ULA.gradient_difference_centered_bound x y (gradient f x) (gradient f y) m M hmM
    (ULA.strong_smooth_gradient_interpolation f m M hf hsc hLip hmM x y)
  have he : gradient f x-((m+(M:ℝ))/2) • x-(gradient f y-((m+(M:ℝ))/2) • y)=
      gradient f x-gradient f y-((m+(M:ℝ))/2) • (x-y) := by module
  rw [he]
  exact hb

/-- The genuine derivative of the centered gradient has the half-width operator bound. -/
theorem hessian_centered_norm_le (f : E→ℝ) (m : ℝ) (M : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m≤(M:ℝ))
    (x : E) (H : E→L[ℝ] E) (hH : HasFDerivAt (gradient f) H x) :
    ‖H-((m+(M:ℝ))/2) • ContinuousLinearMap.id ℝ E‖≤((M:ℝ)-m)/2 := by
  have hd : HasFDerivAt (fun y ↦ gradient f y-((m+(M:ℝ))/2) • y)
      (H-((m+(M:ℝ))/2) • ContinuousLinearMap.id ℝ E) x :=
    hH.sub ((hasFDerivAt_id x).const_smul ((m+(M:ℝ))/2))
  exact hd.le_of_lipschitz (centered_gradient_lipschitz f m M hf hsc hLip hmM)

/-- Actual Hessians of the same strongly convex smooth potential differ by at most the curvature width. -/
theorem hessian_difference_norm_le (f : E→ℝ) (m : ℝ) (M : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m≤(M:ℝ))
    (x y : E) (Hx Hy : E→L[ℝ] E)
    (hHx : HasFDerivAt (gradient f) Hx x) (hHy : HasFDerivAt (gradient f) Hy y) :
    ‖Hx-Hy‖≤(M:ℝ)-m := by
  have hx := hessian_centered_norm_le f m M hf hsc hLip hmM x Hx hHx
  have hy := hessian_centered_norm_le f m M hf hsc hLip hmM y Hy hHy
  have he : Hx-Hy=(Hx-((m+(M:ℝ))/2) • ContinuousLinearMap.id ℝ E)-
      (Hy-((m+(M:ℝ))/2) • ContinuousLinearMap.id ℝ E) := by abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]

/-- The difference of the two actual random Hessian operators is the pointwise Hessian difference. -/
theorem lpHessian_difference_coe (g : E→E) (H : E→E→L[ℝ] E) (M M₂ : ℝ≥0)
    (hG : LipschitzWith M g) (hH : LipschitzWith M₂ H)
    (hg : ∀ x,HasFDerivAt g (H x) x) (X Y Z : Lp E 2 P) :
    (lpHessian P g H M M₂ hG hH hg X-lpHessian P g H M M₂ hG hH hg Y) Z =ᵐ[P]
      fun ω ↦ (H (X ω)-H (Y ω)) (Z ω) := by
  simp only [sub_apply]
  filter_upwards [Lp.coeFn_sub (lpHessian P g H M M₂ hG hH hg X Z) (lpHessian P g H M M₂ hG hH hg Y Z),
    lpHessian_coe P g H M M₂ hG hH hg X Z,lpHessian_coe P g H M M₂ hG hH hg Y Z] with ω hsub hx hy
  rw [hsub,Pi.sub_apply,hx,hy]

/-- The actual random Hessian difference retains the sharp deterministic curvature-width bound on L². -/
theorem lpHessian_difference_norm_le (f : E→ℝ) (H : E→E→L[ℝ] E) (m : ℝ) (M M₂ : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hG : LipschitzWith M (gradient f)) (hmM : m≤(M:ℝ))
    (hH : LipschitzWith M₂ H) (hg : ∀ x,HasFDerivAt (gradient f) (H x) x) (X Y : Lp E 2 P) :
    ‖lpHessian P (gradient f) H M M₂ hG hH hg X-lpHessian P (gradient f) H M M₂ hG hH hg Y‖≤(M:ℝ)-m := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sub_nonneg.mpr hmM)
  intro Z
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [lpHessian_difference_coe P (gradient f) H M M₂ hG hH hg X Y Z] with ω hω
  rw [hω]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
    (hessian_difference_norm_le f m M hf hsc hG hmM (X ω) (Y ω) _ _ (hg _) (hg _)) (norm_nonneg _))

variable {ι : Type*} [Fintype ι]

/-- The sharp cutoff applies directly to the actual Hessian difference and an actual Gaussian velocity. -/
theorem lpHessian_difference_gaussian_truncation [IsProbabilityMeasure P]
    (f : EuclideanSpace ℝ ι→ℝ)
    (H : EuclideanSpace ℝ ι→EuclideanSpace ℝ ι→L[ℝ] EuclideanSpace ℝ ι)
    (m : ℝ) (M M₂ : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hG : LipschitzWith M (gradient f)) (hmM : m≤(M:ℝ))
    (hH : LipschitzWith M₂ H) (hg : ∀ x,HasFDerivAt (gradient f) (H x) x)
    (X Y V : Lp (EuclideanSpace ℝ ι) 2 P)
    (hV : HasLaw V (stdGaussian (EuclideanSpace ℝ ι)) P)
    (α : ℝ) (hα : 5*(Fintype.card ι : ℝ)≤α) :
    ‖(lpHessian P (gradient f) H M M₂ hG hH hg X-lpHessian P (gradient f) H M M₂ hG hH hg Y) V‖≤
      (M₂:ℝ)*Real.sqrt α*‖X-Y‖+2*((M:ℝ)-m)*Real.exp (-(α-(Fintype.card ι : ℝ))/8) := by
  apply gaussian_truncation_Lp P _ (X-Y) V hV ((M:ℝ)-m) M₂ α
    (sub_nonneg.mpr hmM) M₂.coe_nonneg hα
  filter_upwards [lpHessian_difference_coe P (gradient f) H M M₂ hG hH hg X Y V,Lp.coeFn_sub X Y]
    with ω hω hXY
  rw [hω]
  have hB := hessian_difference_norm_le f m M hf hsc hG hmM (X ω) (Y ω) _ _ (hg _) (hg _)
  have hL := hH.norm_sub_le (X ω) (Y ω)
  have he : ‖(X-Y) ω‖=‖X ω-Y ω‖ := by rw [hXY,Pi.sub_apply]
  rw [he]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (le_min hB hL) (norm_nonneg _))

end KineticLangevin
