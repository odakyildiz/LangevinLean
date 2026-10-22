import ProximalLangevin.Moreau
import ProximalLangevin.SharpConcentration
import ProximalLangevin.Algorithms
import UnadjustedLangevin.StationaryMoments
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Smoothing-uniform moments for the synchronous splitting reference

The smooth part of the drift has a Gibbs second-moment bound depending on
its own smoothness and the bounded nonsmooth gradient, rather than the
inverse smoothing scale.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped NNReal ENNReal RealInnerProductSpace
namespace ProximalLangevin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A Lipschitz potential has a Moreau envelope with the same Lipschitz constant. -/
theorem moreau_lipschitz_of_lipschitz {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    (hb : ∃ b, ∀ z, b ≤ f z) {lam : ℝ} (hlam : 0 < lam)
    {K : ℝ≥0} (hK : LipschitzWith K f) : LipschitzWith K (moreau f lam) := by
  apply LipschitzWith.of_le_add_mul
  intro x y
  let p := prox f lam y
  have hmin := prox_isProxPoint hf hb hlam x (p + (x - y))
  have hdist0 := hK.dist_le_mul (p + (x - y)) p
  rw [Real.dist_eq] at hdist0
  have hd : f (p + (x - y)) ≤ f p + (K : ℝ) * dist (p + (x - y)) p := by
    have hh := (le_abs_self _).trans hdist0
    linarith
  have hnorm : ‖p + (x - y) - x‖ = ‖p - y‖ := by congr 1; abel
  have hdist : dist (p + (x - y)) p = dist x y := by
    simp only [dist_eq_norm_sub, add_sub_cancel_left]
  rw [hdist] at hd
  unfold proxObjective at hmin
  rw [hnorm] at hmin
  change moreau f lam x ≤ moreau f lam y + (K : ℝ) * dist x y
  change moreau f lam x ≤ _ at hmin
  dsimp [moreau, proxObjective, p] at *
  linarith

/-- A differentiable function has zero gradient at an actual global minimizer. -/
theorem gradient_eq_zero_at_minimum {f : E → ℝ} {z : E}
    (hz : ∀ x, f z ≤ f x) : gradient f z = 0 := by
  have hmin : IsMinOn f univ z := fun x _ => hz x
  have hlocal := hmin.isLocalMin (Filter.univ_mem : univ ∈ nhds z)
  simp only [gradient, hlocal.fderiv_eq_zero, map_zero]

/-- A smooth strongly convex real-valued function attains its minimum. -/
theorem exists_strongConvex_minimum (f : E → ℝ) (m : ℝ) (hm : 0 < m)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) :
    ∃ z, ∀ x, f z ≤ f x := by
  let R := 2 * ‖gradient f 0‖ / m + 1
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨z, hz, hmin⟩ := (isCompact_closedBall (0 : E) R).exists_isMinOn
    ⟨0, mem_closedBall_self hR.le⟩ hf.continuous.continuousOn
  refine ⟨z, fun x => ?_⟩
  by_cases hx : x ∈ closedBall (0 : E) R
  · exact hmin hx
  have hz0 : f z ≤ f 0 := hmin (mem_closedBall_self hR.le)
  apply hz0.trans
  have hxR : R < ‖x‖ := by simpa [mem_closedBall, not_le] using hx
  have hlarge : 2 * ‖gradient f 0‖ < ‖x‖ * m := by
    have h := (div_lt_iff₀ hm).mp (show 2 * ‖gradient f 0‖ / m < ‖x‖ by
      dsimp [R] at hxR
      linarith)
    exact h
  have hg := ULA.strongConvex_quadratic_lower_bound f m hm hf hsc x
  have hdiv : ‖gradient f 0‖ ^ 2 / m * m = ‖gradient f 0‖ ^ 2 :=
    div_mul_cancel₀ _ hm.ne'
  have hnonneg : 0 ≤ m / 4 * ‖x‖ ^ 2 - ‖gradient f 0‖ ^ 2 / m := by
    apply (mul_nonneg_iff_of_pos_right hm).mp
    nlinarith [sq_nonneg (‖x‖ * m - 2 * ‖gradient f 0‖), norm_nonneg (gradient f 0)]
  linarith

/-- At a minimum of the sum, a bounded second gradient bounds the first gradient. -/
theorem gradient_smoothPart_at_minimum {f e : E → ℝ}
    (hf : Differentiable ℝ f) (he : Differentiable ℝ e)
    {K : ℝ≥0} (hb : ∀ x, ‖gradient e x‖ ≤ (K : ℝ)) {z : E}
    (hz : ∀ x, f z + e z ≤ f x + e x) : ‖gradient f z‖ ≤ (K : ℝ) := by
  have hg := gradient_eq_zero_at_minimum (f := fun x => f x + e x) (z := z) hz
  rw [gradient_add_of_differentiable hf he] at hg
  have hneg : gradient f z = -gradient e z := eq_neg_of_add_eq_zero_left hg
  rw [hneg, norm_neg]
  exact hb z

/-- Global Lipschitzness bounds the actual gradient norm. -/
theorem gradient_norm_le_of_lipschitz {f : E → ℝ} {K : ℝ≥0}
    (hK : LipschitzWith K f) (x : E) : ‖gradient f x‖ ≤ (K : ℝ) := by
  simpa only [gradient, LinearIsometryEquiv.norm_map] using
    (norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hK)

section BoundedLp
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A pointwise bounded Lipschitz drift is bounded by the same constant in `L²`. -/
theorem lpDrift_norm_le_of_bounded {b : E → E} {L K : ℝ≥0}
    (hLip : LipschitzWith L b) (hb : ∀ x, ‖b x‖ ≤ (K : ℝ)) (Y : Lp E 2 P) :
    ‖ULA.lpDrift P b hLip Y‖ ≤ (K : ℝ) := by
  have hpoint : ∀ᵐ ω ∂P, ‖ULA.lpDrift P b hLip Y ω‖ ≤ (K : ℝ) := by
    filter_upwards [ULA.lpDrift_coe P b hLip Y] with ω hω
    rw [hω]
    exact hb _
  simpa [measureUnivNNReal] using
    Lp.norm_le_of_ae_bound K.coe_nonneg hpoint

end BoundedLp

section GibbsMoments
variable [MeasurableSpace E] [BorelSpace E]

/-- A smoothing-uniform second moment for the smooth part of a Gibbs drift.
Only the smooth part's own Lipschitz constant enters the bound. -/
theorem integral_sq_smooth_gradient_le {f e : E → ℝ} (m : ℝ) (hm : 0 < m)
    (hf : Differentiable ℝ f) (he : Differentiable ℝ e)
    (hsc : StrongConvexOn univ m (fun x => f x + e x))
    {L K : ℝ≥0} (hLip : LipschitzWith L (gradient f))
    (hb : ∀ x, ‖gradient e x‖ ≤ (K : ℝ)) :
    (∫ x, ‖gradient f x‖ ^ 2 ∂ULA.gibbsMeasure (fun x => f x + e x)) ≤
      2 * (L : ℝ) ^ 2 * ((Module.finrank ℝ E : ℝ) / m) + 2 * (K : ℝ) ^ 2 := by
  let F := fun x => f x + e x
  let μ := ULA.gibbsMeasure F
  have hF : Differentiable ℝ F := hf.add he
  have : IsProbabilityMeasure μ := ULA.isProbabilityMeasure_gibbsMeasure F m hm hF hsc
  obtain ⟨z, hz⟩ := exists_strongConvex_minimum F m hm hF hsc
  have hgz : ‖gradient f z‖ ≤ (K : ℝ) := gradient_smoothPart_at_minimum hf he hb hz
  have hpoint (x : E) : ‖gradient f x‖ ^ 2 ≤
      2 * (L : ℝ) ^ 2 * ‖x - z‖ ^ 2 + 2 * (K : ℝ) ^ 2 := by
    have hl := hLip.dist_le_mul x z
    rw [dist_eq_norm_sub, dist_eq_norm_sub] at hl
    have hn : ‖gradient f x‖ ≤ (L : ℝ) * ‖x - z‖ + (K : ℝ) := by
      calc
        _ ≤ ‖gradient f x - gradient f z‖ + ‖gradient f z‖ := norm_le_norm_sub_add _ _
        _ ≤ _ := add_le_add hl hgz
    nlinarith [sq_nonneg ((L : ℝ) * ‖x - z‖ - (K : ℝ)), norm_nonneg (gradient f x),
      norm_nonneg (x - z), L.coe_nonneg, K.coe_nonneg]
  have hdist : Integrable (fun x => ‖x - z‖ ^ 2) μ :=
    ULA.integrable_sq_dist_gibbs_of_continuous_strongConvex_mode F m hm hF.continuous hsc z hz
  have hbound : Integrable (fun x =>
      2 * (L : ℝ) ^ 2 * ‖x - z‖ ^ 2 + 2 * (K : ℝ) ^ 2) μ :=
    (hdist.const_mul _).add (integrable_const _)
  have hgrad : Integrable (fun x => ‖gradient f x‖ ^ 2) μ := by
    apply hbound.mono' ((hLip.continuous.norm.pow 2).aestronglyMeasurable)
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint x
  have hi := integral_mono hgrad hbound hpoint
  rw [integral_add (hdist.const_mul _) (integrable_const _), integral_const_mul,
    integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
  have hc := sharp_integral_sq_dist_gibbs_le F m hm hF.continuous hsc z hz
  change (∫ x, ‖x - z‖ ^ 2 ∂μ) ≤ _ at hc
  exact hi.trans (add_le_add (mul_le_mul_of_nonneg_left hc
    (show 0 ≤ 2 * (L : ℝ) ^ 2 by positivity)) le_rfl)

/-- The corresponding actual `L²` smooth-drift bound for a random variable
with the proved reference Gibbs law. -/
theorem lpDrift_smooth_gradient_norm_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {f e : E → ℝ} (m : ℝ) (hm : 0 < m)
    (hf : Differentiable ℝ f) (he : Differentiable ℝ e)
    (hsc : StrongConvexOn univ m (fun x => f x + e x))
    {L K : ℝ≥0} (hLip : LipschitzWith L (gradient f))
    (hb : ∀ x, ‖gradient e x‖ ≤ (K : ℝ))
    (Y : Lp E 2 P) (hlaw : P.map Y = ULA.gibbsMeasure (fun x => f x + e x)) :
    ‖ULA.lpDrift P (gradient f) hLip Y‖ ≤
      Real.sqrt (2 * (L : ℝ) ^ 2 * ((Module.finrank ℝ E : ℝ) / m) + 2 * (K : ℝ) ^ 2) := by
  apply ULA.lpDrift_norm_le_sqrt
  have heq := integral_map (Lp.aestronglyMeasurable Y).aemeasurable
    ((hLip.continuous.norm.pow 2).aestronglyMeasurable)
  rw [hlaw] at heq
  simp only [Pi.pow_apply] at heq
  rw [← heq]
  exact integral_sq_smooth_gradient_le m hm hf he hsc hLip hb

end GibbsMoments

end ProximalLangevin
