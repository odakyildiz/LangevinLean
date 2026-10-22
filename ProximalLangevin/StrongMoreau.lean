import ProximalLangevin.Moreau

set_option linter.style.header false

/-!
# Strong convexity of the full Moreau envelope

Smoothing an `m`-strongly convex potential changes its convexity constant to
`m / (1 + m * lam)`. The proof compares actual proximal minimizers and completes
a weighted square; no smoothness of the original potential is required.
-/

open Set
open scoped RealInnerProductSpace
namespace ProximalLangevin
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact square identity for a convex combination in a real inner product space. -/
theorem norm_convexCombo_sq (u v : E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    ‖a • u + b • v‖ ^ 2 = a * ‖u‖ ^ 2 + b * ‖v‖ ^ 2 -
      a * b * ‖u - v‖ ^ 2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ha, abs_of_nonneg hb, mul_pow, mul_pow,
    real_inner_smul_left, real_inner_smul_right, norm_sub_sq_real]
  obtain rfl := eq_sub_of_add_eq hab
  ring

/-- The quadratic infimal convolution has the sharp effective modulus. -/
theorem weighted_quadratic_lower {m lam : ℝ} (hm : 0 ≤ m) (hlam : 0 < lam)
    (u v : E) :
    m / (1 + m * lam) * ‖v‖ ^ 2 ≤ m * ‖u‖ ^ 2 + ‖u - v‖ ^ 2 / lam := by
  have hden : 0 < 1 + m * lam := by positivity
  have heq : m * ‖u‖ ^ 2 + ‖u - v‖ ^ 2 / lam -
      m / (1 + m * lam) * ‖v‖ ^ 2 =
      ‖(1 + m * lam) • u - v‖ ^ 2 / (lam * (1 + m * lam)) := by
    rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
      abs_of_pos hden, mul_pow, real_inner_smul_left]
    field_simp
    ring
  have hpos : 0 ≤ ‖(1 + m * lam) • u - v‖ ^ 2 / (lam * (1 + m * lam)) :=
    div_nonneg (sq_nonneg _) (mul_pos hlam hden).le
  rw [← heq] at hpos
  linarith

/-- The actual Moreau envelope preserves strong convexity with the exact reduced modulus. -/
theorem moreau_strongConvex [FiniteDimensional ℝ E] {f : E → ℝ}
    {m lam : ℝ} (hm : 0 ≤ m) (hsc : StrongConvexOn univ m f)
    (hb : ∃ b, ∀ z, b ≤ f z) (hlam : 0 < lam) :
    StrongConvexOn univ (m / (1 + m * lam)) (moreau f lam) := by
  have hden : 0 < 1 + m * lam := by positivity
  have hf : ConvexOn ℝ univ f := strongConvexOn_zero.mp (hsc.mono hm)
  refine ⟨convex_univ, fun x _ y _ a b ha hb' hab => ?_⟩
  let p := prox f lam x
  let q := prox f lam y
  have hmin := prox_isProxPoint hf hb hlam (a • x + b • y) (a • p + b • q)
  have hs := hsc.2 (mem_univ p) (mem_univ q) ha hb' hab
  dsimp only at hs ⊢
  simp only [smul_eq_mul] at hs ⊢
  have heq : a • p + b • q - (a • x + b • y) =
      a • (p - x) + b • (q - y) := by
    simp only [smul_sub]
    abel
  change moreau f lam (a • x + b • y) ≤ _ at hmin
  unfold proxObjective at hmin
  rw [heq, norm_convexCombo_sq (p - x) (q - y) ha hb' hab] at hmin
  have hd : (p - x) - (q - y) = (p - q) - (x - y) := by abel
  rw [hd] at hmin
  have hw := weighted_quadratic_lower hm hlam (p - q) (x - y)
  have hww := mul_le_mul_of_nonneg_left hw (mul_nonneg ha hb')
  change moreau f lam (a • x + b • y) ≤
    a * (f p + ‖p - x‖ ^ 2 / (2 * lam)) +
    b * (f q + ‖q - y‖ ^ 2 / (2 * lam)) -
    a * b * (m / (1 + m * lam) / 2 * ‖x - y‖ ^ 2)
  have hscale := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * lam by positivity)
  have hmin' := mul_le_mul_of_nonneg_right hmin (show 0 ≤ 2 * lam by positivity)
  field_simp at hmin' ⊢
  have hweight := mul_le_mul_of_nonneg_left hww hlam.le
  field_simp at hweight
  nlinarith

end
end ProximalLangevin
