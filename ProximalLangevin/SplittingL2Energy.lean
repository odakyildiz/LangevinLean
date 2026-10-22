import ProximalLangevin.SplittingCoupling
import ProximalLangevin.SplittingContraction

/-!
# Convex energy and exact Hilbert identities for splitting couplings

The supporting-plane inequalities are integrated against the actual random
variables. All scalar potential expectations and quadratic moments are proved
integrable before manipulating them.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped NNReal ENNReal RealInnerProductSpace
namespace ProximalLangevin

section HilbertAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A weighted quadratic triangle bound with an explicit positive weight. -/
theorem norm_add_sq_le_weighted (v r : H) {t : ℝ} (ht : 0 < t) :
    ‖v + r‖ ^ 2 ≤ (1 + t) * ‖v‖ ^ 2 + (1 + t⁻¹) * ‖r‖ ^ 2 := by
  rw [norm_add_sq_real]
  have hc := real_inner_le_norm v r
  have hy : 2 * ⟪v, r⟫ ≤ t * ‖v‖ ^ 2 + t⁻¹ * ‖r‖ ^ 2 := by
    apply (mul_le_mul_iff_of_pos_right ht).mp
    field_simp
    nlinarith [sq_nonneg (t * ‖v‖ - ‖r‖)]
  nlinarith

/-- The weighted estimate retains a linear contraction in the squared error. -/
theorem norm_add_sq_le_of_contraction (e v r : H) {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hv : ‖v‖ ≤ (1 - t) * ‖e‖) :
    ‖v + r‖ ^ 2 ≤ (1 - t) * ‖e‖ ^ 2 + (1 + t⁻¹) * ‖r‖ ^ 2 := by
  have hbase := norm_add_sq_le_weighted v r ht
  have hv2 : ‖v‖ ^ 2 ≤ (1 - t) ^ 2 * ‖e‖ ^ 2 := by
    nlinarith [norm_nonneg v, norm_nonneg e]
  have hw := mul_le_mul_of_nonneg_left hv2 (show 0 ≤ 1 + t by linarith)
  have hf : (1 + t) * (1 - t) ^ 2 ≤ 1 - t := by
    nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht1)]
  have hfactor := mul_le_mul_of_nonneg_right hf (sq_nonneg ‖e‖)
  nlinarith

/-- Moving an integrated nonsmooth drift into a cross term avoids a
Lipschitz constant for that drift in the consistency estimate. -/
theorem norm_sum_rearranged (v r b : H) :
    ‖v + r + b‖ ^ 2 = ‖v + r‖ ^ 2 + 2 * ⟪v + r + b, b⟫ - ‖b‖ ^ 2 := by
  simp only [norm_add_sq_real, inner_add_left, real_inner_self_eq_norm_sq]
  ring

end HilbertAlgebra

section RandomVariables
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (P : Measure Ω) [IsProbabilityMeasure P]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Every globally Lipschitz scalar observable of an `L²` random variable is integrable. -/
theorem integrable_lipschitz_compLp {f : E → ℝ} {K : ℝ≥0}
    (hK : LipschitzWith K f) (X : Lp E 2 P) : Integrable (fun ω => f (X ω)) P := by
  have hcenter : LipschitzWith K (fun x => f x - f 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq, sub_sub_sub_cancel_right] using hK.dist_le_mul x y
  have hc : MemLp (fun ω => f (X ω) - f 0) 2 P := by
    simpa only [Function.comp_def] using
      hcenter.comp_memLp (by simp) (Lp.memLp X)
  have hf : MemLp (fun ω => f (X ω)) 2 P := by
    convert hc.add (memLp_const (f 0)) using 1
    funext ω
    simp only [Pi.add_apply, sub_add_cancel]
  exact hf.integrable (by norm_num)

omit [CompleteSpace E] [IsProbabilityMeasure P] in
/-- Exact second-moment identity for actual `L²` random variables. -/
theorem lp_norm_sq_eq_integral (X : Lp E 2 P) :
    ‖X‖ ^ 2 = ∫ ω, ‖X ω‖ ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => real_inner_self_eq_norm_sq _

omit [CompleteSpace E] in
/-- Lift a proved deterministic energy inequality to actual `L²` random variables.
This is an integration lemma; the particle instantiation below proves its
pointwise premise from the genuine proximal minimization problem. -/
theorem lp_energy_of_pointwise {T : E → E} {LT : ℝ≥0} (hT : LipschitzWith LT T)
    {f : E → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (h C : ℝ)
    (hpoint : ∀ x y, ‖T x - y‖ ^ 2 ≤ ‖x - y‖ ^ 2 - 2 * h * (f x - f y) + C)
    (S Y : Lp E 2 P) :
    ‖ULA.lpDrift P T hT S - Y‖ ^ 2 ≤ ‖S - Y‖ ^ 2 -
      2 * h * ((∫ ω, f (S ω) ∂P) - ∫ ω, f (Y ω) ∂P) + C := by
  have hn (V : Lp E 2 P) : Integrable (fun ω => ‖V ω‖ ^ 2) P :=
    (Lp.memLp V).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hfS := integrable_lipschitz_compLp P hf S
  have hfY := integrable_lipschitz_compLp P hf Y
  have hright : Integrable (fun ω => ‖(S - Y) ω‖ ^ 2 -
      2 * h * (f (S ω) - f (Y ω)) + C) P :=
    ((hn _).sub ((hfS.sub hfY).const_mul _)).add (integrable_const _)
  have hi := integral_mono_ae (hn (ULA.lpDrift P T hT S - Y)) hright (show
      ∀ᵐ ω ∂P, ‖(ULA.lpDrift P T hT S - Y) ω‖ ^ 2 ≤
        ‖(S - Y) ω‖ ^ 2 - 2 * h * (f (S ω) - f (Y ω)) + C from by
    filter_upwards [Lp.coeFn_sub (ULA.lpDrift P T hT S) Y,
      ULA.lpDrift_coe P T hT S, Lp.coeFn_sub S Y] with ω hsub hmap hdiff
    simpa only [hsub, hmap, hdiff, Pi.sub_apply] using hpoint (S ω) (Y ω))
  rw [integral_add (f := fun ω => ‖(S - Y) ω‖ ^ 2 -
      2 * h * (f (S ω) - f (Y ω))) (g := fun _ => C)
      ((hn _).sub ((hfS.sub hfY).const_mul (2 * h))) (integrable_const C),
    integral_sub (f := fun ω => ‖(S - Y) ω‖ ^ 2)
      (g := fun ω => 2 * h * (f (S ω) - f (Y ω)))
      (hn _) ((hfS.sub hfY).const_mul (2 * h)), integral_const_mul,
    integral_sub hfS hfY, integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
  simpa only [← lp_norm_sq_eq_integral P] using hi

/-- The actual convex gradient supports every square-integrable comparison
variable after integrating the pointwise supporting-plane inequality. -/
theorem lp_convex_gradient_support {e : E → ℝ}
    (he : Differentiable ℝ e) (hconv : ConvexOn ℝ univ e)
    {L K : ℝ≥0} (hgrad : LipschitzWith L (gradient e)) (hLip : LipschitzWith K e)
    (S Y : Lp E 2 P) :
    ⟪S - Y, ULA.lpDrift P (gradient e) hgrad Y⟫ ≤
      (∫ ω, e (S ω) ∂P) - ∫ ω, e (Y ω) ∂P := by
  rw [L2.inner_def, ← integral_sub (integrable_lipschitz_compLp P hLip S)
    (integrable_lipschitz_compLp P hLip Y)]
  apply integral_mono_ae (L2.integrable_inner _ _)
    ((integrable_lipschitz_compLp P hLip S).sub (integrable_lipschitz_compLp P hLip Y))
  filter_upwards [Lp.coeFn_sub S Y, ULA.lpDrift_coe P (gradient e) hgrad Y] with ω hsub hb
  rw [hsub, hb]
  simp only [Pi.sub_apply]
  have h := ULA.convex_first_order hconv he (Y ω) (S ω)
  rw [← inner_gradient_left] at h
  rw [real_inner_comm]
  linarith

/-- Endpoint comparison split into the convex energy difference and a
reference-increment cross term, all in the genuine `L²` inner product. -/
theorem lp_convex_gradient_cross {e : E → ℝ}
    (he : Differentiable ℝ e) (hconv : ConvexOn ℝ univ e)
    {L K : ℝ≥0} (hgrad : LipschitzWith L (gradient e)) (hLip : LipschitzWith K e)
    (S Y Z : Lp E 2 P) :
    ⟪S - Z, ULA.lpDrift P (gradient e) hgrad Y⟫ ≤
      (∫ ω, e (S ω) ∂P) - (∫ ω, e (Y ω) ∂P) +
      ⟪Y - Z, ULA.lpDrift P (gradient e) hgrad Y⟫ := by
  have heq : S - Z = (S - Y) + (Y - Z) := by abel
  rw [heq, inner_add_left]
  exact add_le_add (lp_convex_gradient_support P he hconv hgrad hLip S Y) le_rfl

end RandomVariables

end ProximalLangevin
