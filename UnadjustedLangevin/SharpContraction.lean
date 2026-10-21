import UnadjustedLangevin.Analysis.Smooth
import UnadjustedLangevin.StrongConvexity
import UnadjustedLangevin.ULAupdate
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity

/-!
# Dalalyan's sharp deterministic contraction

The Lipschitz-gradient and strong-convexity hypotheses imply a stronger
interpolation inequality than strong monotonicity alone. That inequality gives
the factors `1 - m*h` and `L*h - 1` in the two step-size regimes.
-/

noncomputable section

open scoped NNReal

namespace ULA

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A quadratic upper model and supporting planes imply cocoercivity.
The vector field need not be separately assumed to be a gradient: the two
model inequalities contain all the information needed by this proof. -/
theorem cocoercive_of_quadratic_models (f : H → ℝ) (g : H → H) (K : ℝ)
    (hK : 0 ≤ K)
    (hlower : ∀ x y, f x + inner ℝ (g x) (y - x) ≤ f y)
    (hupper : ∀ x y,
      f y ≤ f x + inner ℝ (g x) (y - x) + K / 2 * ‖y - x‖ ^ 2)
    (x y : H) :
    ‖g x - g y‖ ^ 2 ≤ K * inner ℝ (g x - g y) (x - y) := by
  have hbregman (a b : H) (t : ℝ) (ht : 0 ≤ t) :
      t * ‖g a - g b‖ ^ 2 - K / 2 * t ^ 2 * ‖g a - g b‖ ^ 2 ≤
        f a - f b - inner ℝ (g b) (a - b) := by
    let z := a - t • (g a - g b)
    have hl := hlower b z
    have hu := hupper a z
    have hz₁ : z - a = -t • (g a - g b) := by dsimp [z]; module
    have hz₂ : z - b = (a - b) - t • (g a - g b) := by dsimp [z]; module
    rw [hz₂, inner_sub_right, real_inner_smul_right] at hl
    rw [hz₁, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_neg, abs_of_nonneg ht] at hu
    have hi : inner ℝ (g a) (g a - g b) - inner ℝ (g b) (g a - g b) =
        ‖g a - g b‖ ^ 2 := by
      rw [← inner_sub_left, real_inner_self_eq_norm_sq]
    nlinarith
  have hsum (t : ℝ) (ht : 0 ≤ t) :
      2 * t * ‖g x - g y‖ ^ 2 - K * t ^ 2 * ‖g x - g y‖ ^ 2 ≤
        inner ℝ (g x - g y) (x - y) := by
    have hxy := hbregman x y t ht
    have hyx := hbregman y x t ht
    rw [norm_sub_rev] at hyx
    rw [← neg_sub x y, inner_neg_right] at hyx
    rw [inner_sub_left]
    linarith
  rcases hK.eq_or_lt with hzero | hpos
  · subst K
    have h := hsum 1 (by norm_num)
    have hmono : 0 ≤ inner ℝ (g x - g y) (x - y) := by
      nlinarith [sq_nonneg ‖g x - g y‖]
    by_contra hn
    have hnpos : 0 < ‖g x - g y‖ ^ 2 := by
      simp only [zero_mul] at hn
      exact lt_of_not_ge hn
    have hh := hsum
      ((inner ℝ (g x - g y) (x - y) + 1) / (2 * ‖g x - g y‖ ^ 2))
      (by positivity)
    have heq : 2 * ((inner ℝ (g x - g y) (x - y) + 1) /
        (2 * ‖g x - g y‖ ^ 2)) * ‖g x - g y‖ ^ 2 =
        inner ℝ (g x - g y) (x - y) + 1 := by
      have hnorm : ‖g x - g y‖ ≠ 0 := by
        intro hz
        simp only [hz, zero_pow (by norm_num : 2 ≠ 0)] at hnpos
        linarith
      field_simp [hnorm]
    simp only [zero_mul, sub_zero] at hh
    rw [heq] at hh
    linarith
  · have h := hsum K⁻¹ (inv_nonneg.mpr hpos.le)
    have hmul := mul_le_mul_of_nonneg_left h hpos.le
    have hne : K ≠ 0 := ne_of_gt hpos
    field_simp at hmul
    nlinarith

/-- Strong convexity and a Lipschitz gradient give the strong-smooth
interpolation inequality, including the boundary case `m = L`. -/
theorem strong_smooth_gradient_interpolation [CompleteSpace H]
    (f : H → ℝ) (m : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ m f)
    (hLip : LipschitzWith L (gradient f)) (hmL : m ≤ (L : ℝ)) (x y : H) :
    m * (L : ℝ) * ‖x - y‖ ^ 2 + ‖gradient f x - gradient f y‖ ^ 2 ≤
      (m + (L : ℝ)) * inner ℝ (gradient f x - gradient f y) (x - y) := by
  let F : H → ℝ := fun v ↦ f v - m / 2 * ‖v‖ ^ 2
  let G : H → H := fun v ↦ gradient f v - m • v
  have hlower (a b : H) : F a + inner ℝ (G a) (b - a) ≤ F b := by
    have h := strong_first_order hdiff hsc a b
    dsimp [F, G]
    simp only [inner_sub_left, real_inner_smul_left, inner_sub_right,
      real_inner_self_eq_norm_sq] at h ⊢
    rw [norm_sub_sq_real, real_inner_comm a b] at h
    nlinarith
  have hupper (a b : H) :
      F b ≤ F a + inner ℝ (G a) (b - a) + ((L : ℝ) - m) / 2 * ‖b - a‖ ^ 2 := by
    have h := Analysis.smooth_upper_bound f L hdiff hLip a b
    dsimp [F, G]
    simp only [inner_sub_left, real_inner_smul_left, inner_sub_right,
      real_inner_self_eq_norm_sq] at h ⊢
    rw [norm_sub_sq_real]
    rw [norm_sub_sq_real, real_inner_comm a b] at h
    rw [real_inner_comm a b]
    nlinarith
  have hc := cocoercive_of_quadratic_models F G ((L : ℝ) - m)
    (sub_nonneg.mpr hmL) hlower hupper x y
  have hG : G x - G y = (gradient f x - gradient f y) - m • (x - y) := by
    dsimp [G]
    module
  rw [hG, norm_sub_sq_real] at hc
  simp only [inner_sub_left, real_inner_smul_left, real_inner_smul_right,
    norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs] at hc ⊢
  have hinner : inner ℝ x (x - y) - inner ℝ y (x - y) = ‖x - y‖ ^ 2 := by
    rw [← inner_sub_left, real_inner_self_eq_norm_sq]
  rw [hinner] at hc
  nlinarith

/-- The interpolation inequality places the gradient difference in a ball
centered at `(m+L)/2` times the point difference. -/
theorem gradient_difference_centered_bound
    (x y gx gy : H) (m L : ℝ) (hmL : m ≤ L)
    (hinterp : m * L * ‖x - y‖ ^ 2 + ‖gx - gy‖ ^ 2 ≤
      (m + L) * inner ℝ (gx - gy) (x - y)) :
    ‖(gx - gy) - ((m + L) / 2) • (x - y)‖ ≤
      ((L - m) / 2) * ‖x - y‖ := by
  have hrad : 0 ≤ (L - m) / 2 := by linarith
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg hrad (norm_nonneg _))).mp
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, mul_pow]
  nlinarith

/-- A sharp Euler bound, written using the midpoint of the curvature interval.
Splitting the absolute value gives Dalalyan's two step-size regimes. -/
theorem gradient_step_centered_contract
    (x y gx gy : H) (m L h : ℝ) (hmL : m ≤ L) (hh : 0 ≤ h)
    (hinterp : m * L * ‖x - y‖ ^ 2 + ‖gx - gy‖ ^ 2 ≤
      (m + L) * inner ℝ (gx - gy) (x - y)) :
    ‖(x - h • gx) - (y - h • gy)‖ ≤
      (|1 - h * ((m + L) / 2)| + h * ((L - m) / 2)) * ‖x - y‖ := by
  have hc := gradient_difference_centered_bound x y gx gy m L hmL hinterp
  have heq : (x - h • gx) - (y - h • gy) =
      (1 - h * ((m + L) / 2)) • (x - y) +
        (-h) • ((gx - gy) - ((m + L) / 2) • (x - y)) := by module
  rw [heq]
  have htri := norm_add_le
    ((1 - h * ((m + L) / 2)) • (x - y))
    ((-h) • ((gx - gy) - ((m + L) / 2) • (x - y)))
  simp only [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hh] at htri
  have hscaled := mul_le_mul_of_nonneg_left hc hh
  nlinarith

/-- Dalalyan's sharp factor `1-mh` for `h ≤ 2/(m+L)`. -/
theorem gradient_step_sharp_contract_small
    (x y gx gy : H) (m L h : ℝ) (hmL : m ≤ L) (hpos : 0 < m + L)
    (hh : 0 ≤ h) (hsmall : h ≤ 2 / (m + L))
    (hinterp : m * L * ‖x - y‖ ^ 2 + ‖gx - gy‖ ^ 2 ≤
      (m + L) * inner ℝ (gx - gy) (x - y)) :
    ‖(x - h • gx) - (y - h • gy)‖ ≤ (1 - m * h) * ‖x - y‖ := by
  have hc := gradient_step_centered_contract x y gx gy m L h hmL hh hinterp
  have hs : h * (m + L) ≤ 2 := (le_div_iff₀ hpos).mp hsmall
  rw [abs_of_nonneg (show 0 ≤ 1 - h * ((m + L) / 2) by nlinarith)] at hc
  convert hc using 1
  ring

/-- Dalalyan's sharp factor `Lh-1` for `h ≥ 2/(m+L)`. -/
theorem gradient_step_sharp_contract_large
    (x y gx gy : H) (m L h : ℝ) (hmL : m ≤ L) (hpos : 0 < m + L)
    (hh : 0 ≤ h) (hlarge : 2 / (m + L) ≤ h)
    (hinterp : m * L * ‖x - y‖ ^ 2 + ‖gx - gy‖ ^ 2 ≤
      (m + L) * inner ℝ (gx - gy) (x - y)) :
    ‖(x - h • gx) - (y - h • gy)‖ ≤ (L * h - 1) * ‖x - y‖ := by
  have hc := gradient_step_centered_contract x y gx gy m L h hmL hh hinterp
  have hs : 2 ≤ h * (m + L) := (div_le_iff₀ hpos).mp hlarge
  rw [abs_of_nonpos (show 1 - h * ((m + L) / 2) ≤ 0 by nlinarith)] at hc
  convert hc using 1
  ring

/-- Sharp gradient-step contraction derived entirely from the potential's
strong convexity and Lipschitz gradient, in the small-step regime. -/
theorem strong_smooth_gradient_step_contract [CompleteSpace H]
    (f : H → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ m f)
    (hLip : LipschitzWith L (gradient f)) (hmL : m ≤ (L : ℝ))
    (hpos : 0 < m + (L : ℝ)) (hh : 0 ≤ h) (hsmall : h ≤ 2 / (m + (L : ℝ)))
    (x y : H) :
    ‖(x - h • gradient f x) - (y - h • gradient f y)‖ ≤
      (1 - m * h) * ‖x - y‖ := by
  exact gradient_step_sharp_contract_small x y (gradient f x) (gradient f y)
    m L h hmL hpos hh hsmall
    (strong_smooth_gradient_interpolation f m L hdiff hsc hLip hmL x y)

/-- The large-step branch of the sharp potential-based contraction. -/
theorem strong_smooth_gradient_step_contract_large [CompleteSpace H]
    (f : H → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ m f)
    (hLip : LipschitzWith L (gradient f)) (hmL : m ≤ (L : ℝ))
    (hpos : 0 < m + (L : ℝ)) (hh : 0 ≤ h) (hlarge : 2 / (m + (L : ℝ)) ≤ h)
    (x y : H) :
    ‖(x - h • gradient f x) - (y - h • gradient f y)‖ ≤
      ((L : ℝ) * h - 1) * ‖x - y‖ := by
  exact gradient_step_sharp_contract_large x y (gradient f x) (gradient f y)
    m L h hmL hpos hh hlarge
    (strong_smooth_gradient_interpolation f m L hdiff hsc hLip hmL x y)

/-- The two sharp branches can be expressed by the familiar maximum of the
absolute endpoint factors. -/
theorem strong_smooth_gradient_step_contract_max [CompleteSpace H]
    (f : H → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ m f)
    (hLip : LipschitzWith L (gradient f)) (hmL : m ≤ (L : ℝ))
    (hpos : 0 < m + (L : ℝ)) (hh : 0 ≤ h) (x y : H) :
    ‖(x - h • gradient f x) - (y - h • gradient f y)‖ ≤
      max |1 - m * h| |1 - (L : ℝ) * h| * ‖x - y‖ := by
  by_cases hs : h ≤ 2 / (m + (L : ℝ))
  · have hc := strong_smooth_gradient_step_contract f m h L hdiff hsc hLip
      hmL hpos hh hs x y
    exact hc.trans (mul_le_mul_of_nonneg_right
      ((le_abs_self _).trans (le_max_left _ _)) (norm_nonneg _))
  · have hc := strong_smooth_gradient_step_contract_large f m h L hdiff hsc hLip
      hmL hpos hh (le_of_lt (lt_of_not_ge hs)) x y
    have hfactor : (L : ℝ) * h - 1 ≤ |1 - (L : ℝ) * h| := by
      have ht := neg_le_abs (1 - (L : ℝ) * h)
      linarith
    exact hc.trans (mul_le_mul_of_nonneg_right
      (hfactor.trans (le_max_right _ _)) (norm_nonneg _))

/-- Shared Gaussian noise cancels, so one ULA step has the sharp small-step
factor `1-mh`. The statement holds for every vector of noise. -/
theorem ula_shared_noise_contract_sharp {d : ℕ}
    (f : E d → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ m f)
    (hLip : LipschitzWith L (gradient f)) (hmL : m ≤ (L : ℝ))
    (hpos : 0 < m + (L : ℝ)) (hh : 0 ≤ h) (hsmall : h ≤ 2 / (m + (L : ℝ)))
    (x y z : E d) :
    ‖ulaUpdate f h x z - ulaUpdate f h y z‖ ≤ (1 - m * h) * ‖x - y‖ := by
  rw [ulaUpdate_sub]
  exact strong_smooth_gradient_step_contract f m h L hdiff hsc hLip
    hmL hpos hh hsmall x y

/-- The sharp large-step shared-noise factor is `Lh-1`. -/
theorem ula_shared_noise_contract_sharp_large {d : ℕ}
    (f : E d → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ m f)
    (hLip : LipschitzWith L (gradient f)) (hmL : m ≤ (L : ℝ))
    (hpos : 0 < m + (L : ℝ)) (hh : 0 ≤ h) (hlarge : 2 / (m + (L : ℝ)) ≤ h)
    (x y z : E d) :
    ‖ulaUpdate f h x z - ulaUpdate f h y z‖ ≤ ((L : ℝ) * h - 1) * ‖x - y‖ := by
  rw [ulaUpdate_sub]
  exact strong_smooth_gradient_step_contract_large f m h L hdiff hsc hLip
    hmL hpos hh hlarge x y

end ULA
