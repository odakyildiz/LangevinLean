import KineticLangevin.OBABORemainder
import KineticLangevin.OBABO
import KineticLangevin.Recurrence

/-! # Nonlinear OBABO synchronous contraction

This is a contraction theorem for the actual noisy two-kick map, with the
source step-size constant.  The force estimates are derived from strong
convexity and smoothness; no intermediate Hessian point is selected.
-/

noncomputable section
set_option linter.style.header false
open scoped RealInnerProductSpace NNReal
namespace KineticLangevin
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem obabo_step_size_consequences (γ L m h : ℝ) (hγ : 0 < γ) (hh : 0 ≤ h)
    (hmL : m ≤ L) (hfriction : 4 * L ≤ γ ^ 2) (hstep : 33 * γ ^ 3 * h ≤ m) :
    γ * h ≤ 1 ∧ 12 * γ ^ 2 * h ^ 2 ≤ 1 := by
  have hsmall : γ * h ≤ 1 / 132 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hγ)).mp
    nlinarith only [hstep, hmL, hfriction]
  have hsq := (sq_le_sq₀ (mul_nonneg hγ.le hh) (by norm_num : (0:ℝ)≤1/132)).mpr hsmall
  constructor
  · linarith
  · nlinarith only [hsq]

theorem obabo_damping_bounds (γ h : ℝ) (hγ : 0 ≤ γ) (hh : 0 ≤ h) :
    let δ := obaboDamping γ h
    0 ≤ δ ∧ δ ≤ 1 ∧ 1 - δ ≤ γ * h / 2 ∧
      0 ≤ δ ^ 2 - 1 + γ * h ∧ δ ^ 2 - 1 + γ * h ≤ γ ^ 2 * h ^ 2 / 2 := by
  intro δ
  have hd : δ = Real.exp (-γ * h / 2) := rfl
  have hp := (obaboDamping_pos γ h).le
  have hle : δ ≤ 1 := by
    rw [hd]
    exact Real.exp_le_one_iff.mpr (by nlinarith only [mul_nonneg hγ hh])
  have hgap := Real.add_one_le_exp (-γ * h / 2)
  have hsq0 := Real.add_one_le_exp (-γ * h)
  have hsq := exp_neg_le_quadratic (γ * h) (mul_nonneg hγ hh)
  rw [← obaboDamping_sq] at hsq0
  rw [← neg_mul, ← obaboDamping_sq] at hsq
  rw [← hd] at hgap
  exact ⟨hp, hle, by linarith, by dsimp [δ];linarith,
    by dsimp [δ];nlinarith only [hsq]⟩

theorem obaboStep_synchronous_contraction (f : E → ℝ) (m γ h σ : ℝ) (M : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ m f)
    (hLip : LipschitzWith M (gradient f)) (hm : 0 ≤ m) (hmM : m ≤ (M : ℝ))
    (hγ : 0 < γ) (hM : 0 < (M : ℝ)) (hh : 0 ≤ h)
    (hfriction : 4 * (M : ℝ) ≤ γ ^ 2) (hstep : 33 * γ ^ 3 * h ≤ m)
    (z w : E × E) (ξ ξ' : E) :
    weightedPhaseEnergy (1 / (M : ℝ)) (1 / γ)
      (obaboStep (gradient f) h (obaboDamping γ h) σ z ξ ξ' -
        obaboStep (gradient f) h (obaboDamping γ h) σ w ξ ξ') ≤
      (1 - m * h / (3 * γ)) * weightedPhaseEnergy (1 / (M : ℝ)) (1 / γ) (z - w) := by
  let δ := obaboDamping γ h
  let xn := z.2 + h • (δ • z.1 + σ • ξ - (h / 2) • gradient f z.2)
  let yn := w.2 + h • (δ • w.1 + σ • ξ - (h / 2) • gradient f w.2)
  let x := z.2 - w.2
  let v := z.1 - w.1
  let F0 := gradient f z.2 - gradient f w.2
  let S := (1 / 2 : ℝ) • (F0 + (gradient f xn - gradient f yn))
  let err := (M : ℝ) / 2 * ‖(xn - yn) - x‖
  have hsizes := obabo_step_size_consequences γ M m h hγ hh hmM hfriction hstep
  have hd := obabo_damping_bounds γ h hγ.le hh
  have hδ0 : 0 ≤ δ := hd.1
  have hδ1 : δ ≤ 1 := hd.2.1
  have hF0 : ‖F0‖ ≤ (M : ℝ) * ‖x‖ := hLip.norm_sub_le z.2 w.2
  have herr : 0 ≤ err := by dsimp [err];positivity
  have hΔ : (xn - yn) - x = (h * δ) • v - (h ^ 2 / 2) • F0 := by
    dsimp [xn, yn, x, v, F0]
    module
  have hΔbound : ‖(xn - yn) - x‖ ≤ h * ‖v‖ + h ^ 2 * (M : ℝ) / 2 * ‖x‖ := by
    rw [hΔ]
    have ht := norm_sub_le ((h * δ) • v) ((h ^ 2 / 2) • F0)
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hh hδ0),
      abs_of_nonneg (by positivity : 0 ≤ h ^ 2 / 2)] at ht
    have hδ := mul_le_mul_of_nonneg_right hδ1 (by positivity : 0 ≤ h * ‖v‖)
    have hf := mul_le_mul_of_nonneg_left hF0 (by positivity : 0 ≤ h ^ 2 / 2)
    nlinarith only [ht, hδ, hf]
  have herrBound := mul_le_mul_of_nonneg_left hΔbound (by positivity : 0 ≤ (M : ℝ) / 2)
  have h0 := ULA.gradient_difference_centered_bound z.2 w.2 (gradient f z.2) (gradient f w.2) m M hmM
    (ULA.strong_smooth_gradient_interpolation f m M hdiff hsc hLip hmM z.2 w.2)
  have h1 := ULA.gradient_difference_centered_bound xn yn (gradient f xn) (gradient f yn) m M hmM
    (ULA.strong_smooth_gradient_interpolation f m M hdiff hsc hLip hmM xn yn)
  have hcenter := average_force_centered m M hm hmM x (xn - yn) F0
    (gradient f xn - gradient f yn) h0 h1
  have hforce : ‖S‖ ≤ (M : ℝ) * ‖x‖ + err := by
    have ht := norm_add_le (S - ((m + (M : ℝ)) / 2) • x) (((m + (M : ℝ)) / 2) • x)
    have hμ : ‖((m + (M : ℝ)) / 2) • x‖ = ((m + (M : ℝ)) / 2) * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (m + (M : ℝ)) / 2)]
    rw [sub_add_cancel, hμ] at ht
    change ‖S - ((m + (M : ℝ)) / 2) • x‖ ≤ ((M : ℝ) - m) / 2 * ‖x‖ + err at hcenter
    nlinarith only [ht, hcenter]
  have hdrift := obabo_average_force_dissipativity f m γ M hdiff hsc hLip hm hmM hγ hM hfriction
    z.2 w.2 xn yn v
  have he := obabo_algebra_contraction γ M m h δ err hγ hM hh hfriction hsizes.1 hsizes.2 hstep herr
    hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2 v x F0 S hF0 herrBound hforce hdrift
  have hid : obaboStep (gradient f) h δ σ z ξ ξ' - obaboStep (gradient f) h δ σ w ξ ξ' =
      (δ ^ 2 • v - (h * δ) • S, x + (h * δ) • v - (h ^ 2 / 2) • F0) := by
    dsimp [obaboStep, ornsteinStep, kickStep, driftStep, S, F0, v, x, xn, yn]
    ext <;> module
  have hinitial : (v, x) = z - w := rfl
  rw [hinitial, ← hid] at he
  exact he

theorem obabo_contraction_factor_nonneg (γ L m h : ℝ)
    (hγ : 0 < γ) (hh : 0 ≤ h) (hmL : m ≤ L)
    (hfriction : 4 * L ≤ γ ^ 2) (hsmall : γ * h ≤ 1) :
    0 ≤ 1 - m * h / (3 * γ) := by
  have hf := mul_le_mul_of_nonneg_right hfriction hh
  have hs := mul_le_mul_of_nonneg_left hsmall hγ.le
  have hm := mul_le_mul_of_nonneg_right hmL hh
  have hdiv : m * h / (3 * γ) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 3 * γ)).mpr
    nlinarith only [hf, hs, hm, hγ]
  linarith only [hdiv]

theorem obabo_synchronous_iteration (f : E → ℝ) (m γ h σ : ℝ) (M : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ m f)
    (hLip : LipschitzWith M (gradient f)) (hm : 0 ≤ m) (hmM : m ≤ (M : ℝ))
    (hγ : 0 < γ) (hM : 0 < (M : ℝ)) (hh : 0 ≤ h)
    (hfriction : 4 * (M : ℝ) ≤ γ ^ 2) (hstep : 33 * γ ^ 3 * h ≤ m)
    (Z W : ℕ → E × E) (ξ ξ' : ℕ → E)
    (hZ : ∀ n, Z (n + 1) = obaboStep (gradient f) h (obaboDamping γ h) σ (Z n) (ξ n) (ξ' n))
    (hW : ∀ n, W (n + 1) = obaboStep (gradient f) h (obaboDamping γ h) σ (W n) (ξ n) (ξ' n))
    (n : ℕ) :
    weightedPhaseEnergy (1 / (M : ℝ)) (1 / γ) (Z n - W n) ≤
      (1 - m * h / (3 * γ)) ^ n * weightedPhaseEnergy (1 / (M : ℝ)) (1 / γ) (Z 0 - W 0) := by
  have hs := obabo_step_size_consequences γ M m h hγ hh hmM hfriction hstep
  have hq := obabo_contraction_factor_nonneg γ M m h hγ hh hmM hfriction hs.1
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hZ, hW]
    calc
      _ ≤ (1 - m * h / (3 * γ)) * weightedPhaseEnergy (1 / (M : ℝ)) (1 / γ) (Z n - W n) :=
        obaboStep_synchronous_contraction f m γ h σ M hdiff hsc hLip hm hmM hγ hM hh hfriction hstep (Z n) (W n) (ξ n) (ξ' n)
      _ ≤ (1 - m * h / (3 * γ)) * ((1 - m * h / (3 * γ)) ^ n *
          weightedPhaseEnergy (1 / (M : ℝ)) (1 / γ) (Z 0 - W 0)) := mul_le_mul_of_nonneg_left ih hq
      _ = _ := by rw [pow_succ];ring

theorem obabo_synchronous_position_decay (f : E → ℝ) (m γ h σ : ℝ) (M : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ m f)
    (hLip : LipschitzWith M (gradient f)) (hm : 0 ≤ m) (hmM : m ≤ (M : ℝ))
    (hγ : 0 < γ) (hM : 0 < (M : ℝ)) (hh : 0 ≤ h)
    (hfriction : 4 * (M : ℝ) ≤ γ ^ 2) (hstep : 33 * γ ^ 3 * h ≤ m)
    (Z W : ℕ → E × E) (ξ ξ' : ℕ → E)
    (hZ : ∀ n, Z (n + 1) = obaboStep (gradient f) h (obaboDamping γ h) σ (Z n) (ξ n) (ξ' n))
    (hW : ∀ n, W (n + 1) = obaboStep (gradient f) h (obaboDamping γ h) σ (W n) (ξ n) (ξ' n))
    (hvelocity : (Z 0).1 = (W 0).1) (n : ℕ) :
    ‖(Z n).2 - (W n).2‖ ≤ Real.sqrt (2 * (1 - m * h / (3 * γ)) ^ n) * ‖(Z 0).2 - (W 0).2‖ := by
  have he := obabo_synchronous_iteration f m γ h σ M hdiff hsc hLip hm hmM hγ hM hh
    hfriction hstep Z W ξ ξ' hZ hW n
  have hini : weightedPhaseEnergy (1 / (M : ℝ)) (1 / γ) (Z 0 - W 0) = ‖(Z 0).2 - (W 0).2‖ ^ 2 := by
    simp [weightedPhaseEnergy, hvelocity]
  rw [hini] at he
  have hlo := (weightedPhaseEnergy_equiv (1 / (M : ℝ)) (1 / γ) (by positivity)
    (obabo_metric_condition γ M hγ hM hfriction) (Z n - W n)).1
  have hdiag : 0 ≤ (1 / (M : ℝ)) * ‖(Z n).1 - (W n).1‖ ^ 2 := by positivity
  change (1 / 2 : ℝ) * (‖(Z n).2 - (W n).2‖ ^ 2 + (1 / (M : ℝ)) * ‖(Z n).1 - (W n).1‖ ^ 2) ≤ _ at hlo
  have hsquared : ‖(Z n).2 - (W n).2‖ ^ 2 ≤
      (2 * (1 - m * h / (3 * γ)) ^ n) * ‖(Z 0).2 - (W 0).2‖ ^ 2 := by
    nlinarith only [he, hlo, hdiag]
  have hsmall := obabo_step_size_consequences γ M m h hγ hh hmM hfriction hstep
  have hq := obabo_contraction_factor_nonneg γ M m h hγ hh hmM hfriction hsmall.1
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact hsquared

end KineticLangevin
