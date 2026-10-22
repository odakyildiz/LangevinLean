import ProximalLangevin.Proximal
import Mathlib.Analysis.Calculus.Gradient.Basic

set_option linter.style.header false

/-!
# Moreau envelopes of finite-valued convex functions

The envelope is the value at the actual proximal minimizer.  Its derivative,
convexity, sharp smoothness, and Lipschitz approximation bounds are proved here.
-/

open Set Metric Filter
open scoped RealInnerProductSpace Topology

namespace ProximalLangevin

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Moreau envelope, evaluated at the selected true proximal point. -/
def moreau (f : E → ℝ) (lam : ℝ) (x : E) : ℝ :=
  proxObjective f lam x (prox f lam x)

/-- The proximal residual, which is the actual Moreau gradient on its domain. -/
def residual (f : E → ℝ) (lam : ℝ) (x : E) : E :=
  lam⁻¹ • (x - prox f lam x)

variable {f : E → ℝ} (hf : ConvexOn ℝ univ f) (hb : ∃ b, ∀ z, b ≤ f z)
  {lam : ℝ} (hlam : 0 < lam)

include hf hb hlam

/-- The Moreau envelope lies below the original potential. -/
theorem moreau_le (x : E) : moreau f lam x ≤ f x := by
  simpa [moreau, proxObjective] using prox_isProxPoint hf hb hlam x x

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] hf hb in
/-- The Moreau envelope is above every common lower bound of the potential. -/
theorem le_moreau {b : ℝ} (hbf : ∀ z, b ≤ f z) (x : E) : b ≤ moreau f lam x := by
  unfold moreau proxObjective
  exact (hbf _).trans (le_add_of_nonneg_right (by positivity))

/-- The proximal residual supports the Moreau envelope globally. -/
theorem moreau_support (x y : E) :
    moreau f lam x + ⟪residual f lam x, y - x⟫ ≤ moreau f lam y := by
  let p := prox f lam x
  let q := prox f lam y
  have h := subgradient_of_isProxPoint hf hlam (prox_isProxPoint hf hb hlam x) q
  change f p + ⟪lam⁻¹ • (x - p), q - p⟫ ≤ f q at h
  simp only [real_inner_smul_left] at h
  have hd : q - p = (q - y) - (p - x) + (y - x) := by abel
  rw [hd, inner_add_right, inner_sub_right,
    show x - p = -(p - x) by abel, inner_neg_left, inner_neg_left,
    inner_neg_left, real_inner_self_eq_norm_sq] at h
  have hs := sq_nonneg ‖(q - y) - (p - x)‖
  rw [norm_sub_sq_real, real_inner_comm] at hs
  change f p + ‖p - x‖ ^ 2 / (2 * lam) +
      ⟪lam⁻¹ • (x - p), y - x⟫ ≤ f q + ‖q - y‖ ^ 2 / (2 * lam)
  rw [real_inner_smul_left, show x - p = -(p - x) by abel, inner_neg_left]
  apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < 2 * lam)).mp
  have h' := mul_le_mul_of_nonneg_left h hlam.le
  field_simp at h' ⊢
  nlinarith

/-- Quadratic upper Taylor bound for the Moreau envelope. -/
theorem moreau_upper (x y : E) :
    moreau f lam y ≤ moreau f lam x + ⟪residual f lam x, y - x⟫ +
      ‖y - x‖ ^ 2 / (2 * lam) := by
  have h := prox_isProxPoint hf hb hlam y (prox f lam x)
  apply h.trans_eq
  unfold moreau proxObjective residual
  rw [show prox f lam x - y = (prox f lam x - x) - (y - x) by abel,
    norm_sub_sq_real, real_inner_smul_left,
    show x - prox f lam x = -(prox f lam x - x) by abel, inner_neg_left]
  field_simp
  ring

/-- Convexity of the envelope is a consequence of its global supports. -/
theorem moreau_convex : ConvexOn ℝ univ (moreau f lam) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb' hab => ?_⟩
  let z := a • x + b • y
  have hx := moreau_support hf hb hlam z x
  have hy := moreau_support hf hb hlam z y
  have hi : a * ⟪residual f lam z, x - z⟫ +
      b * ⟪residual f lam z, y - z⟫ = 0 := by
    rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right]
    have hz : a • (x - z) + b • (y - z) = 0 := by
      calc
        a • (x - z) + b • (y - z) = (a • x + b • y) - (a + b) • z := by
          rw [add_smul, smul_sub, smul_sub]
          abel
        _ = 0 := by rw [hab, one_smul]; exact sub_self _
    rw [hz, inner_zero_right]
  simp only [smul_eq_mul]
  have h1 := mul_le_mul_of_nonneg_left hx ha
  have h2 := mul_le_mul_of_nonneg_left hy hb'
  change moreau f lam z ≤ _
  have hm : a * moreau f lam z + b * moreau f lam z = moreau f lam z := by
    rw [← add_mul, hab, one_mul]
  nlinarith

/-- The selected proximal mapping is nonexpansive. -/
theorem prox_lipschitz : LipschitzWith 1 (prox f lam) := by
  apply LipschitzWith.mk_one
  intro x y
  simpa only [dist_eq_norm_sub] using
    (prox_isProxPoint hf hb hlam x).nonexpansive hf hlam (prox_isProxPoint hf hb hlam y)

/-- The actual envelope residual has the sharp `1 / lam` Lipschitz constant. -/
theorem residual_lipschitz : LipschitzWith lam⁻¹.toNNReal (residual f lam) := by
  apply LipschitzWith.of_dist_le'
  intro x y
  rw [dist_eq_norm_sub, residual, residual, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam), dist_eq_norm_sub]
  exact mul_le_mul_of_nonneg_left
    ((prox_isProxPoint hf hb hlam x).residual_nonexpansive hf hlam
      (prox_isProxPoint hf hb hlam y)) (inv_nonneg.mpr hlam.le)

/-- The Moreau envelope is differentiable, with gradient equal to its proximal residual. -/
theorem moreau_hasGradientAt (x : E) : HasGradientAt (moreau f lam) (residual f lam x) x := by
  rw [hasGradientAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [Metric.ball_mem_nhds x (mul_pos hc (show 0 < 2 * lam by positivity))]
    with y hy
  have hdist : ‖y - x‖ < c * (2 * lam) := by
    simpa only [Metric.mem_ball, dist_eq_norm_sub] using hy
  have hlo := moreau_support hf hb hlam x y
  have hhi := moreau_upper hf hb hlam x y
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  apply (show moreau f lam y - moreau f lam x - ⟪residual f lam x, y - x⟫ ≤
      ‖y - x‖ ^ 2 / (2 * lam) by linarith).trans
  apply (div_le_iff₀ (by positivity : 0 < 2 * lam)).mpr
  nlinarith [norm_nonneg (y - x)]

/-- Differentiability of the actual Moreau envelope. -/
theorem moreau_differentiable : Differentiable ℝ (moreau f lam) :=
  fun x => (moreau_hasGradientAt hf hb hlam x).differentiableAt

/-- Exact formula for the actual Moreau gradient. -/
theorem gradient_moreau (x : E) : gradient (moreau f lam) x = residual f lam x :=
  (moreau_hasGradientAt hf hb hlam x).gradient

/-- The envelope is continuously differentiable, even when `f` is nonsmooth. -/
theorem moreau_contDiff : ContDiff ℝ 1 (moreau f lam) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun x => InnerProductSpace.toDual ℝ E (residual f lam x), ?_, ?_⟩
  · exact (InnerProductSpace.toDual ℝ E).continuous.comp
      (residual_lipschitz hf hb hlam).continuous
  · intro x
    exact (moreau_hasGradientAt hf hb hlam x).hasFDerivAt

/-- The Moreau gradient has norm at most the Lipschitz constant of `f`. -/
theorem residual_norm_le {K : NNReal} (hK : LipschitzWith K f) (x : E) :
    ‖residual f lam x‖ ≤ (K : ℝ) := by
  let p := prox f lam x
  let g := residual f lam x
  have hs := subgradient_of_isProxPoint hf hlam (prox_isProxPoint hf hb hlam x) (p + g)
  change f p + ⟪g, p + g - p⟫ ≤ f (p + g) at hs
  rw [add_sub_cancel_left, real_inner_self_eq_norm_sq] at hs
  have hd := hK.dist_le_mul (p + g) p
  rw [Real.dist_eq, dist_eq_norm_sub, add_sub_cancel_left] at hd
  have hdiff : f (p + g) - f p ≤ (K : ℝ) * ‖g‖ := (le_abs_self _).trans hd
  change ‖g‖ ≤ (K : ℝ)
  nlinarith [norm_nonneg g, NNReal.coe_nonneg K]

/-- A Lipschitz potential moves each proximal point by at most `lam K`. -/
theorem prox_displacement_le {K : NNReal} (hK : LipschitzWith K f) (x : E) :
    ‖x - prox f lam x‖ ≤ lam * (K : ℝ) := by
  have h := residual_norm_le hf hb hlam hK x
  rw [residual, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam)] at h
  have hh := mul_le_mul_of_nonneg_left h hlam.le
  field_simp at hh
  exact hh

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] hf hb in
/-- Sharp uniform approximation bound for a `K`-Lipschitz potential. -/
theorem moreau_lower_of_lipschitz {K : NNReal} (hK : LipschitzWith K f) (x : E) :
    f x - lam * (K : ℝ) ^ 2 / 2 ≤ moreau f lam x := by
  have hdist := hK.dist_le_mul x (prox f lam x)
  rw [Real.dist_eq, dist_eq_norm_sub, norm_sub_rev x (prox f lam x)] at hdist
  have hdiff : f x - f (prox f lam x) ≤ (K : ℝ) * ‖prox f lam x - x‖ :=
    (le_abs_self _).trans hdist
  unfold moreau proxObjective
  apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < 2 * lam)).mp
  field_simp
  have hdiff' := mul_le_mul_of_nonneg_left hdiff hlam.le
  nlinarith [sq_nonneg (‖prox f lam x - x‖ - lam * (K : ℝ))]

/-- The pointwise Moreau correction is nonnegative and at most `lam K² / 2`. -/
theorem moreau_gap_of_lipschitz {K : NNReal} (hK : LipschitzWith K f) (x : E) :
    0 ≤ f x - moreau f lam x ∧ f x - moreau f lam x ≤ lam * (K : ℝ) ^ 2 / 2 := by
  constructor
  · exact sub_nonneg.mpr (moreau_le hf hb hlam x)
  · have h := moreau_lower_of_lipschitz hlam hK x
    linarith

end

end ProximalLangevin
