import KineticLangevin.Geometry
import UnadjustedLangevin.SharpContraction

/-! # The modified metric for the OBABO contraction proof

The phase convention remains velocity first.  Monmarché's metric is
`|x|² + 2 b <x,v> + a |v|²`, with `a=1/L` and `b=1/γ`.
The lemmas below derive its positivity and its continuous drift estimate,
including the explicit error caused by an approximate gradient sector.
-/

noncomputable section
open scoped RealInnerProductSpace NNReal

namespace KineticLangevin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The weighted kinetic phase energy, velocity first. -/
def weightedPhaseEnergy (a b : ℝ) (s : E × E) : ℝ :=
  ‖s.2‖ ^ 2 + 2 * b * ⟪s.2, s.1⟫ + a * ‖s.1‖ ^ 2

/-- The corresponding energy without its mixed inner-product term. -/
def weightedBaseEnergy (a : ℝ) (s : E × E) : ℝ := ‖s.2‖ ^ 2 + a * ‖s.1‖ ^ 2

/-- The source metric is between one half and three halves of its diagonal
part whenever the cross coefficient satisfies `4 b² ≤ a`. -/
theorem weightedPhaseEnergy_equiv (a b : ℝ) (hb : 0 ≤ b) (hab : 4 * b ^ 2 ≤ a)
    (s : E × E) :
    (1 / 2 : ℝ) * weightedBaseEnergy a s ≤ weightedPhaseEnergy a b s ∧
      weightedPhaseEnergy a b s ≤ (3 / 2 : ℝ) * weightedBaseEnergy a s := by
  have hp := real_inner_le_norm s.2 s.1
  have hn := real_inner_le_norm s.2 (-s.1)
  simp only [inner_neg_right, norm_neg] at hn
  have hscaledp := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2 * b)
  have hscaledn := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 2 * b)
  have hs := sq_nonneg (‖s.2‖ - 2 * b * ‖s.1‖)
  have ha := mul_le_mul_of_nonneg_right hab (sq_nonneg ‖s.1‖)
  unfold weightedPhaseEnergy weightedBaseEnergy
  constructor <;> nlinarith

theorem weightedPhaseEnergy_nonneg (a b : ℝ) (hb : 0 ≤ b) (hab : 4 * b ^ 2 ≤ a)
    (s : E × E) : 0 ≤ weightedPhaseEnergy a b s := by
  have ha : 0 ≤ a := (by positivity : 0 ≤ 4 * b ^ 2).trans hab
  exact (by unfold weightedBaseEnergy; positivity : 0 ≤ (1 / 2 : ℝ) * weightedBaseEnergy a s).trans
    (weightedPhaseEnergy_equiv a b hb hab s).1

/-- The exact source parameters obey the metric condition under
`γ²≥4L`. -/
theorem obabo_metric_condition (γ L : ℝ) (hγ : 0 < γ) (hL : 0 < L)
    (hfriction : 4 * L ≤ γ ^ 2) : 4 * (1 / γ) ^ 2 ≤ 1 / L := by
  rw [div_pow, one_pow]
  apply (le_div_iff₀ hL).mpr
  have he : 4 * (1 / γ ^ 2) * L = (4 * L) / γ ^ 2 := by ring
  rw [he]
  exact (div_le_one (sq_pos_of_pos hγ)).mpr hfriction

/-- The numerator of the continuous source-metric energy derivative along
`v'=-γv-F`, `x'=v`, divided by its positive common denominator. -/
def obaboEnergyDerivative (γ L : ℝ) (v x force : E) : ℝ :=
  (-2 * L * ⟪x, force⟫ + (2 * L - 2 * γ ^ 2) * ‖v‖ ^ 2 -
    2 * γ * ⟪v, force⟫) / (γ * L)

/-- Strong monotonicity and cocoercivity with a visible sector error give
the continuous dissipativity needed for the actual average of the two
OBABO force evaluations. -/
theorem obabo_perturbed_dissipativity (γ L m err : ℝ)
    (hγ : 0 < γ) (hL : 0 < L) (hm : 0 ≤ m) (hmL : m ≤ L)
    (hfriction : 4 * L ≤ γ ^ 2) (v x force : E)
    (hmono : m * ‖x‖ ^ 2 - err * ‖x‖ ≤ ⟪x, force⟫)
    (hcoco : ‖force‖ ^ 2 ≤ L * ⟪x, force⟫ + L * err * ‖x‖ + err ^ 2) :
    obaboEnergyDerivative γ L v x force ≤
      (-2 * m / (3 * γ)) * weightedPhaseEnergy (1 / L) (1 / γ) (v, x) +
        2 * err * ‖x‖ / γ + err ^ 2 / (γ * L) := by
  have hmetric := weightedPhaseEnergy_equiv (1 / L) (1 / γ) (by positivity)
    (obabo_metric_condition γ L hγ hL hfriction) (v, x)
  have hupper : L * weightedPhaseEnergy (1 / L) (1 / γ) (v, x) ≤
      (3 / 2 : ℝ) * (L * ‖x‖ ^ 2 + ‖v‖ ^ 2) := by
    have hscaled := mul_le_mul_of_nonneg_left hmetric.2 hL.le
    unfold weightedBaseEnergy at hscaled
    convert hscaled using 1 <;> field_simp <;> ring
  have hmupper := mul_le_mul_of_nonneg_left hupper (by positivity : 0 ≤ 2 * m / 3)
  have hyoung := sq_nonneg ‖γ • v + force‖
  simp only [norm_add_sq_real, norm_smul, Real.norm_eq_abs,
    abs_of_pos hγ, mul_pow, real_inner_smul_left] at hyoung
  have hmonoscaled := mul_le_mul_of_nonneg_left hmono hL.le
  have hvnegative : 0 ≤ (γ ^ 2 - 2 * L - m) * ‖v‖ ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have hraw : -2 * L * ⟪x, force⟫ + (2 * L - 2 * γ ^ 2) * ‖v‖ ^ 2 -
      2 * γ * ⟪v, force⟫ ≤
      -(2 * m / 3) * (L * weightedPhaseEnergy (1 / L) (1 / γ) (v, x)) +
        2 * L * err * ‖x‖ + err ^ 2 := by nlinarith
  have hd := div_le_div_of_nonneg_right hraw (mul_nonneg hγ.le hL.le)
  unfold obaboEnergyDerivative
  convert hd using 1 <;> field_simp <;> ring

/-- Averaging the two force differences preserves the centered sector,
with only `L/2` times the change in the coupled position difference. -/
theorem average_force_centered (m L : ℝ) (hm : 0 ≤ m) (hmL : m ≤ L)
    (x x' F F' : E)
    (h0 : ‖F - ((m + L) / 2) • x‖ ≤ ((L - m) / 2) * ‖x‖)
    (h1 : ‖F' - ((m + L) / 2) • x'‖ ≤ ((L - m) / 2) * ‖x'‖) :
    ‖(1 / 2 : ℝ) • (F + F') - ((m + L) / 2) • x‖ ≤
      ((L - m) / 2) * ‖x‖ + (L / 2) * ‖x' - x‖ := by
  have hL : 0 ≤ L := hm.trans hmL
  have hid : (1 / 2 : ℝ) • (F + F') - ((m + L) / 2) • x =
      (1 / 2 : ℝ) • (F - ((m + L) / 2) • x) +
        (1 / 2 : ℝ) • (F' - ((m + L) / 2) • x') + ((m + L) / 4) • (x' - x) := by module
  rw [hid]
  have ht := norm_add_le
    ((1 / 2 : ℝ) • (F - ((m + L) / 2) • x) +
      (1 / 2 : ℝ) • (F' - ((m + L) / 2) • x')) (((m + L) / 4) • (x' - x))
  have ht' := norm_add_le ((1 / 2 : ℝ) • (F - ((m + L) / 2) • x))
    ((1 / 2 : ℝ) • (F' - ((m + L) / 2) • x'))
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
    abs_of_nonneg (by positivity : 0 ≤ (m + L) / 4)] at ht ht'
  have hx := norm_add_le x (x' - x)
  rw [add_sub_cancel] at hx
  have hxscaled := mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ (L - m) / 2)
  nlinarith

/-- An approximate strong-smooth centered sector implies the two scalar
inequalities used in the source metric drift estimate. -/
theorem perturbed_sector_bounds (m L err : ℝ) (hm : 0 ≤ m) (hmL : m ≤ L)
    (herr : 0 ≤ err) (x force : E)
    (hcenter : ‖force - ((m + L) / 2) • x‖ ≤ ((L - m) / 2) * ‖x‖ + err) :
    m * ‖x‖ ^ 2 - err * ‖x‖ ≤ ⟪x, force⟫ ∧
      ‖force‖ ^ 2 ≤ L * ⟪x, force⟫ + L * err * ‖x‖ + err ^ 2 := by
  have hL : 0 ≤ L := hm.trans hmL
  have hinner := real_inner_le_norm x (-(force - ((m + L) / 2) • x))
  simp only [inner_neg_right, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, norm_neg] at hinner
  have hscaled := mul_le_mul_of_nonneg_left hcenter (norm_nonneg x)
  constructor
  · nlinarith
  · have hid : force - (L / 2) • x =
        (force - ((m + L) / 2) • x) + (m / 2) • x := by module
    have ht := norm_add_le (force - ((m + L) / 2) • x) ((m / 2) • x)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ m / 2)] at ht
    have hzero : ‖force - (L / 2) • x‖ ≤ (L / 2) * ‖x‖ + err := by
      rw [hid]
      nlinarith
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ L / 2 * ‖x‖ + err)).mpr hzero
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, real_inner_comm x force] at hsq
    nlinarith

/-- The actual two nonlinear force evaluations of an OBABO synchronous
step obey the source-metric drift inequality, with an explicit position
increment remainder. No mean-value Hessian is selected. -/
theorem obabo_average_force_dissipativity [CompleteSpace E]
    (f : E → ℝ) (m γ : ℝ) (M : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ m f)
    (hLip : LipschitzWith M (gradient f)) (hm : 0 ≤ m) (hmM : m ≤ (M : ℝ))
    (hγ : 0 < γ) (hM : 0 < (M : ℝ)) (hfriction : 4 * (M : ℝ) ≤ γ ^ 2)
    (x y x' y' : E) :
    let S := (1 / 2 : ℝ) • ((gradient f x - gradient f y) + (gradient f x' - gradient f y'))
    let err := (M : ℝ) / 2 * ‖(x' - y') - (x - y)‖
    ∀ v : E, obaboEnergyDerivative γ M v (x - y) S ≤
      (-2 * m / (3 * γ)) * weightedPhaseEnergy (1 / (M : ℝ)) (1 / γ) (v, x - y) +
        2 * err * ‖x - y‖ / γ + err ^ 2 / (γ * (M : ℝ)) := by
  intro S err v
  have h0 := ULA.gradient_difference_centered_bound x y (gradient f x) (gradient f y) m M hmM
    (ULA.strong_smooth_gradient_interpolation f m M hdiff hsc hLip hmM x y)
  have h1 := ULA.gradient_difference_centered_bound x' y' (gradient f x') (gradient f y') m M hmM
    (ULA.strong_smooth_gradient_interpolation f m M hdiff hsc hLip hmM x' y')
  have hc := average_force_centered m M hm hmM (x - y) (x' - y')
    (gradient f x - gradient f y) (gradient f x' - gradient f y') h0 h1
  have hs := perturbed_sector_bounds m M err hm hmM (by dsimp [err]; positivity) (x - y) S hc
  exact obabo_perturbed_dissipativity γ M m err hγ hM hm hmM hfriction v (x - y) S hs.1 hs.2

end KineticLangevin
