import KineticLangevin.GaussianTail

/-! # Gaussian truncation without an independence assumption

A random Lipschitz factor is small where the velocity norm is moderate.
On the complement, its deterministic uniform bound is combined with the
actual Gaussian positive-part tail. The coupled position and velocity may
be dependent throughout.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace KineticLangevin

/-- The scalar cutoff inequality separates a small-factor term from the exact excess of the velocity square. -/
theorem gaussian_truncation_pointwise (d x v B L a : ℝ)
    (hd : 0≤d) (hx : 0≤x) (hv : 0≤v) (hB : 0≤B) (hL : 0≤L) (ha : 0≤a)
    (hbound : d≤min B (L*x)*v) :
    d^2≤L^2*a*x^2+B^2*max (v^2-a) 0 := by
  let k := min B (L*x)
  have hk : 0≤k := le_min hB (mul_nonneg hL hx)
  have hkd : d^2≤k^2*v^2 := by
    have he := (sq_le_sq₀ hd (mul_nonneg hk hv)).2 hbound
    simpa only [mul_pow] using he
  have hkB : k^2≤B^2 := (sq_le_sq₀ hk hB).2 (min_le_left _ _)
  have hkL : k^2≤(L*x)^2 := (sq_le_sq₀ hk (mul_nonneg hL hx)).2 (min_le_right _ _)
  by_cases hvcut : v^2≤a
  · rw [max_eq_right (sub_nonpos.mpr hvcut),mul_zero,add_zero]
    calc
      _ ≤ k^2*v^2 := hkd
      _ ≤ k^2*a := mul_le_mul_of_nonneg_left hvcut (sq_nonneg _)
      _ ≤ (L*x)^2*a := mul_le_mul_of_nonneg_right hkL ha
      _ = _ := by ring
  · have htail : 0≤v^2-a := sub_nonneg.mpr (le_of_lt (lt_of_not_ge hvcut))
    rw [max_eq_left htail]
    calc
      _ ≤ k^2*v^2 := hkd
      _ = k^2*a+k^2*(v^2-a) := by ring
      _ ≤ (L*x)^2*a+B^2*(v^2-a) :=
        add_le_add (mul_le_mul_of_nonneg_right hkL ha) (mul_le_mul_of_nonneg_right hkB htail)
      _ = _ := by ring

section LpNorm
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : Measure Ω)

/-- The actual Hilbert L² norm squared is its actual second-moment integral. -/
theorem lp_norm_sq_eq_integral (X : Lp E 2 P) : ‖X‖^2=∫ ω,‖X ω‖^2 ∂P := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]
end LpNorm

/-- A bounded random Lipschitz coefficient multiplied by an actual standard Gaussian velocity
admits the source-paper L² cutoff estimate, with no independence between velocity and error. -/
theorem gaussian_truncation_Lp {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D X V : Lp (EuclideanSpace ℝ ι) 2 P)
    (hV : HasLaw V (stdGaussian (EuclideanSpace ℝ ι)) P)
    (B L a : ℝ) (hB : 0≤B) (hL : 0≤L) (ha : 5*(Fintype.card ι : ℝ)≤a)
    (hbound : ∀ᵐ ω ∂P,‖D ω‖≤min B (L*‖X ω‖)*‖V ω‖) :
    ‖D‖≤L*Real.sqrt a*‖X‖+2*B*Real.exp (-(a-(Fintype.card ι : ℝ))/8) := by
  have ha0 : 0≤a := by linarith [Nat.cast_nonneg (Fintype.card ι) (α:=ℝ)]
  have hiD : Integrable (fun ω ↦ ‖D ω‖^2) P := (Lp.memLp D).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hiX : Integrable (fun ω ↦ ‖X ω‖^2) P := (Lp.memLp X).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hiV : Integrable (fun ω ↦ ‖V ω‖^2) P := (Lp.memLp V).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hiTail : Integrable (fun ω ↦ max (‖V ω‖^2-a) 0) P := by
    apply (hiV.add (integrable_const |a|)).mono' (by fun_prop)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
    change max (‖V ω‖^2-a) 0≤‖V ω‖^2+|a|
    apply max_le
    · linarith [neg_le_abs a]
    · positivity
  have hiR := (hiX.const_mul (L^2*a)).add (hiTail.const_mul (B^2))
  have hpoint : ∀ᵐ ω ∂P,‖D ω‖^2≤L^2*a*‖X ω‖^2+B^2*max (‖V ω‖^2-a) 0 := by
    filter_upwards [hbound] with ω hω
    exact gaussian_truncation_pointwise _ _ _ B L a (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hB hL ha0 hω
  have hint := integral_mono_ae hiD hiR hpoint
  dsimp only [Pi.add_apply] at hint
  rw [integral_add (hiX.const_mul (L^2*a)) (hiTail.const_mul (B^2)),integral_const_mul,
    integral_const_mul,← lp_norm_sq_eq_integral P D,← lp_norm_sq_eq_integral P X] at hint
  have htail := gaussian_norm_square_positivePart_le P V hV a ha
  have hsq : ‖D‖^2≤L^2*a*‖X‖^2+B^2*(4*Real.exp (-(a-(Fintype.card ι : ℝ))/4)) :=
    hint.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left htail (sq_nonneg B)))
  have he : Real.exp (-(a-(Fintype.card ι : ℝ))/8)^2=Real.exp (-(a-(Fintype.card ι : ℝ))/4) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤L*Real.sqrt a*‖X‖+2*B*Real.exp (-(a-(Fintype.card ι : ℝ))/8))).mp
  calc
    _ ≤ L^2*a*‖X‖^2+B^2*(4*Real.exp (-(a-(Fintype.card ι : ℝ))/4)) := hsq
    _ ≤ _ := by
      rw [add_sq,mul_pow,mul_pow,Real.sq_sqrt ha0,mul_pow,mul_pow,he]
      have hc : 0≤2*(L*Real.sqrt a*‖X‖)*(2*B*Real.exp (-(a-(Fintype.card ι : ℝ))/8)) := by positivity
      nlinarith only [hc]

end KineticLangevin
