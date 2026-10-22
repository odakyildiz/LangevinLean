import UnadjustedLangevin.GibbsScore
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

set_option linter.style.header false

/-! # Exponential moments and finite relative entropy

The entropy inequality transfers an exponential moment of the reference law
to an ordinary moment of any law of finite Kullback–Leibler divergence. The
integrability conclusion is part of the result, rather than an extra premise.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ULA.LSI

/-- The elementary exponential/entropy Young inequality, including zero density. -/
lemma mul_le_klFun_add_exp_sub_one (a b : ℝ) (ha : 0 ≤ a) :
    a * b ≤ InformationTheory.klFun a + Real.exp b - 1 := by
  rcases eq_or_lt_of_le ha with h | h
  · subst a
    simp only [InformationTheory.klFun_zero, zero_mul, add_sub_cancel_left]
    exact Real.exp_nonneg b
  · have he := Real.add_one_le_exp (b - Real.log a)
    have hm := mul_le_mul_of_nonneg_left he h.le
    rw [Real.exp_sub, Real.exp_log h] at hm
    rw [mul_div_cancel₀ _ h.ne'] at hm
    dsimp [InformationTheory.klFun]
    nlinarith

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A finite exponential moment and finite relative entropy imply integrability
of a nonnegative measurable observable, without assuming that moment in advance. -/
theorem integrable_of_finite_kl_of_integrable_exp
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω → ℝ) (hf : Measurable f) (hpos : ∀ x, 0 ≤ f x)
    (hKL : InformationTheory.klDiv μ ν ≠ ⊤)
    (hexp : Integrable (fun x ↦ Real.exp (f x)) ν) : Integrable f μ := by
  obtain ⟨hac, hllr⟩ := InformationTheory.klDiv_ne_top_iff.mp hKL
  have hkl := (InformationTheory.integrable_klFun_rnDeriv_iff hac).mpr hllr
  have hmajor := hkl.add hexp
  have hprod : Integrable (fun x ↦ (μ.rnDeriv ν x).toReal * f x) ν := by
    apply hmajor.mono' (by fun_prop)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (hpos x))]
    have hy := mul_le_klFun_add_exp_sub_one (μ.rnDeriv ν x).toReal (f x)
      ENNReal.toReal_nonneg
    change _ ≤ InformationTheory.klFun _ + Real.exp _
    linarith
  exact (integrable_toReal_rnDeriv_mul_iff hac).mp hprod

/-- The entropy inequality in a form that uses any certified logarithmic MGF
upper bound. In particular, all integrability of the law `μ` is derived. -/
theorem integral_le_kl_add_of_integral_exp_le
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω → ℝ) (hf : Measurable f) (hpos : ∀ x, 0 ≤ f x)
    (hKL : InformationTheory.klDiv μ ν ≠ ⊤)
    (hexp : Integrable (fun x ↦ Real.exp (f x)) ν)
    (c : ℝ) (hmgf : (∫ x, Real.exp (f x) ∂ν) ≤ Real.exp c) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ (InformationTheory.klDiv μ ν).toReal + c := by
  have hi := integrable_of_finite_kl_of_integrable_exp μ ν f hf hpos hKL hexp
  obtain ⟨hac, hllr⟩ := InformationTheory.klDiv_ne_top_iff.mp hKL
  have hkl := (InformationTheory.integrable_klFun_rnDeriv_iff hac).mpr hllr
  have hshift : Integrable (fun x ↦ Real.exp (f x - c)) ν := by
    simp_rw [Real.exp_sub, div_eq_mul_inv]
    exact hexp.mul_const _
  have hprod : Integrable (fun x ↦ (μ.rnDeriv ν x).toReal * (f x - c)) ν :=
    (integrable_toReal_rnDeriv_mul_iff hac).mpr (hi.sub (integrable_const c))
  have hsum : Integrable (fun x ↦ InformationTheory.klFun (μ.rnDeriv ν x).toReal +
      Real.exp (f x - c)) ν := hkl.add hshift
  have he := integral_mono hprod ((hkl.add hshift).sub (integrable_const 1))
    (fun x ↦ mul_le_klFun_add_exp_sub_one (μ.rnDeriv ν x).toReal
      (f x - c) ENNReal.toReal_nonneg)
  simp only [Pi.sub_apply, Pi.add_apply] at he
  rw [integral_toReal_rnDeriv_mul hac,
    integral_sub hi (integrable_const c), integral_const,
    integral_sub hsum (integrable_const 1),
    integral_add hkl hshift, integral_const] at he
  simp only [probReal_univ, one_smul] at he
  have hshift_bound : (∫ x, Real.exp (f x - c) ∂ν) ≤ 1 := by
    simp_rw [Real.exp_sub]
    rw [integral_div]
    exact (div_le_one (Real.exp_pos c)).mpr hmgf
  rw [← InformationTheory.toReal_klDiv_eq_integral_klFun hac] at he
  exact ⟨hi, by linarith⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Integrability of the radial Gaussian kernel in the ambient state space. -/
lemma integrable_radial_gaussian (b : ℝ) (hb : 0 < b) :
    Integrable (fun v : E ↦ Real.exp (-b * ‖v‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := E) (b := (b : ℂ)) (by simpa using hb) 0 (0 : E)).norm
  simpa [Complex.norm_exp, ← Complex.ofReal_pow] using h

/-- The normalization integral of the radial Gaussian kernel. -/
lemma lintegral_radial_gaussian (b : ℝ) (hb : 0 < b) :
    (∫⁻ v : E, ENNReal.ofReal (Real.exp (-b * ‖v‖ ^ 2))) =
      ENNReal.ofReal ((Real.pi / b) ^ (Module.finrank ℝ E / 2 : ℝ)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_radial_gaussian b hb)
    (ae_of_all _ fun _ ↦ Real.exp_nonneg _)]
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb]

/-- Completing the square gives a Gaussian linearization of the squared norm.
This identity holds as a nonnegative integral, before any integrability of the
score itself is known. -/
lemma lintegral_radial_gaussian_mul_exp_inner (b : ℝ) (hb : 0 < b) (g : E) :
    (∫⁻ v : E, ENNReal.ofReal (Real.exp (-b * ‖v‖ ^ 2)) *
        ENNReal.ofReal (Real.exp (inner ℝ g v))) =
      ENNReal.ofReal (Real.exp (‖g‖ ^ 2 / (4 * b))) *
        ENNReal.ofReal ((Real.pi / b) ^ (Module.finrank ℝ E / 2 : ℝ)) := by
  have hs (v : E) : -b * ‖v‖ ^ 2 + inner ℝ g v =
      ‖g‖ ^ 2 / (4 * b) + -b * ‖v + (-(1 / (2 * b))) • g‖ ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, real_inner_comm v g]
    field_simp
    ring
  simp_rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, hs,
    Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _)]
  rw [lintegral_const_mul _ (by fun_prop),
    lintegral_add_right_eq_self (fun v : E ↦ ENNReal.ofReal (Real.exp (-b * ‖v‖ ^ 2)))
      ((-(1 / (2 * b))) • g), lintegral_radial_gaussian b hb]

/-- Gaussian averaging converts all directional MGF bounds into one exponential
bound on the squared norm, with the exact finite-dimensional Gaussian constant. -/
theorem lintegral_exp_norm_sq_le_of_directional_mgf
    (μ : Measure Ω) [SFinite μ] (g : Ω → E) (hg : Measurable g)
    (L : ℝ) (hL : 0 < L)
    (hmgf : ∀ v : E, (∫⁻ x, ENNReal.ofReal (Real.exp (inner ℝ (g x) v)) ∂μ) ≤
      ENNReal.ofReal (Real.exp (L / 2 * ‖v‖ ^ 2))) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (‖g x‖ ^ 2 / (4 * L))) ∂μ) ≤
      ENNReal.ofReal (2 ^ (Module.finrank ℝ E / 2 : ℝ)) := by
  let C := ENNReal.ofReal ((Real.pi / L) ^ (Module.finrank ℝ E / 2 : ℝ))
  have hC0 : C ≠ 0 := by
    apply ne_of_gt
    exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (div_pos Real.pi_pos hL) _)
  have hCtop : C ≠ ⊤ := ENNReal.ofReal_ne_top
  have hTonelli :
      (∫⁻ x, ENNReal.ofReal (Real.exp (‖g x‖ ^ 2 / (4 * L))) ∂μ) * C =
        ∫⁻ v : E, ENNReal.ofReal (Real.exp (-L * ‖v‖ ^ 2)) *
          (∫⁻ x, ENNReal.ofReal (Real.exp (inner ℝ (g x) v)) ∂μ) := by
    dsimp [C]
    rw [← lintegral_mul_const _ (by fun_prop)]
    simp_rw [← lintegral_radial_gaussian_mul_exp_inner L hL]
    rw [lintegral_lintegral_swap (by fun_prop)]
    apply lintegral_congr
    intro v
    exact lintegral_const_mul _ (by fun_prop)
  have hbound :
      (∫⁻ x, ENNReal.ofReal (Real.exp (‖g x‖ ^ 2 / (4 * L))) ∂μ) * C ≤
        ENNReal.ofReal ((Real.pi / (L / 2)) ^ (Module.finrank ℝ E / 2 : ℝ)) := by
    rw [hTonelli]
    calc
      _ ≤ ∫⁻ v : E, ENNReal.ofReal (Real.exp (-L * ‖v‖ ^ 2)) *
          ENNReal.ofReal (Real.exp (L / 2 * ‖v‖ ^ 2)) :=
        lintegral_mono (fun v ↦ mul_le_mul_right (hmgf v) _)
      _ = _ := by
        simp_rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add,
          show ∀ v : E, -L * ‖v‖ ^ 2 + L / 2 * ‖v‖ ^ 2 =
            -(L / 2) * ‖v‖ ^ 2 by intro v; ring]
        exact lintegral_radial_gaussian (L / 2) (by positivity)
  have hconstant :
      ENNReal.ofReal ((Real.pi / (L / 2)) ^ (Module.finrank ℝ E / 2 : ℝ)) =
        ENNReal.ofReal (2 ^ (Module.finrank ℝ E / 2 : ℝ)) * C := by
    dsimp [C]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity)]
    congr 1
    ring
  rw [hconstant] at hbound
  exact (ENNReal.mul_le_mul_iff_left hC0 hCtop).mp hbound

/-- The squared Gibbs score has a dimension-exponential moment. The proof uses
only a differentiable potential, a Lipschitz gradient, and finite normalization;
there is no convexity or functional-inequality premise. -/
theorem gibbs_score_exponential_moment
    (U : E → ℝ) (L : ℝ≥0) (hL : 0 < L) (hU : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (hZ : ULA.gibbsPartition U ≠ ⊤) :
    Integrable (fun x ↦ Real.exp (‖gradient U x‖ ^ 2 / (4 * (L : ℝ))))
      (ULA.gibbsMeasure U) ∧
      (∫ x, Real.exp (‖gradient U x‖ ^ 2 / (4 * (L : ℝ)))
        ∂ULA.gibbsMeasure U) ≤ Real.exp (Module.finrank ℝ E / 2 : ℝ) := by
  have hL' : 0 < (L : ℝ) := hL
  have hgrad : Continuous (gradient U) := hLip.continuous
  let : IsProbabilityMeasure (ULA.gibbsMeasure U) := by
    constructor
    rw [ULA.gibbsMeasure, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
      setLIntegral_univ]
    exact ENNReal.inv_mul_cancel (ne_of_gt (ULA.gibbsPartition_pos U hU)) hZ
  have hdir (v : E) :
      (∫⁻ x, ENNReal.ofReal (Real.exp (inner ℝ (gradient U x) v)) ∂ULA.gibbsMeasure U) ≤
        ENNReal.ofReal (Real.exp ((L : ℝ) / 2 * ‖v‖ ^ 2)) := by
    have h := ULA.gibbs_score_lmgf_le U L hU hLip hZ (-v)
    simpa only [inner_neg_right, neg_neg, norm_neg] using h
  have hm := lintegral_exp_norm_sq_le_of_directional_mgf (ULA.gibbsMeasure U)
    (gradient U) hLip.continuous.measurable (L : ℝ) hL' hdir
  have hi : Integrable
      (fun x ↦ Real.exp (‖gradient U x‖ ^ 2 / (4 * (L : ℝ))))
      (ULA.gibbsMeasure U) := by
    refine ⟨(by fun_prop), ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ Real.exp_nonneg _)).mpr
    exact lt_of_le_of_lt hm ENNReal.ofReal_lt_top
  refine ⟨hi, ?_⟩
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ fun _ ↦ Real.exp_nonneg _)] at hreal
  simp only [ENNReal.toReal_ofReal (integral_nonneg (fun _ ↦ Real.exp_nonneg _)),
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 ^ (Module.finrank ℝ E / 2 : ℝ))]
    at hreal
  apply hreal.trans
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  exact (mul_le_mul_of_nonneg_right hlog (by positivity)).trans_eq (one_mul _)

/-- A law of finite relative entropy has a square-integrable Gibbs score, with
`Gμ ≤ 4 L KL(μ|π) + 2 dim(E) L`. This closes the gradient-moment bridge directly
from entropy and smoothness; the LSI-to-transport implication is unnecessary. -/
theorem gibbs_gradient_moment_bound_of_finite_kl
    (U : E → ℝ) (L : ℝ≥0) (hL : 0 < L) (hU : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U))
    [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (hKL : InformationTheory.klDiv μ (ULA.gibbsMeasure U) ≠ ⊤) :
    Integrable (fun x ↦ ‖gradient U x‖ ^ 2) μ ∧
      (∫ x, ‖gradient U x‖ ^ 2 ∂μ) ≤
        4 * (L : ℝ) * (InformationTheory.klDiv μ (ULA.gibbsMeasure U)).toReal +
          2 * (Module.finrank ℝ E : ℝ) * (L : ℝ) := by
  have hZ : ULA.gibbsPartition U ≠ ⊤ := by
    intro h
    have : ULA.gibbsMeasure U = 0 := by simp [ULA.gibbsMeasure, h]
    have hu := measure_univ (μ := ULA.gibbsMeasure U)
    simp [this] at hu
  have hgrad : Continuous (gradient U) := hLip.continuous
  obtain ⟨hexp, hmgf⟩ := gibbs_score_exponential_moment U L hL hU hLip hZ
  obtain ⟨hi, hb⟩ := integral_le_kl_add_of_integral_exp_le μ (ULA.gibbsMeasure U)
    (fun x ↦ ‖gradient U x‖ ^ 2 / (4 * (L : ℝ))) (by fun_prop)
    (fun x ↦ by positivity) hKL hexp (Module.finrank ℝ E / 2 : ℝ) hmgf
  have hL' : 0 < (L : ℝ) := hL
  have hint : Integrable (fun x ↦ ‖gradient U x‖ ^ 2) μ := by
    convert hi.const_mul (4 * (L : ℝ)) using 1
    ext x
    field_simp
  refine ⟨hint, ?_⟩
  rw [integral_div] at hb
  have hh := (div_le_iff₀ (by positivity : 0 < 4 * (L : ℝ))).mp hb
  nlinarith

/-- The coefficient used by the ULA interpolation theorem follows from the
stronger direct entropy/score estimate and the scalar compatibility `α ≤ L`.
In particular, no entropy-cost coupling has to be supplied. -/
theorem gibbs_gradient_moment_bound_of_finite_kl_of_alpha_le
    (U : E → ℝ) (L : ℝ≥0) (hU : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U))
    [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (hKL : InformationTheory.klDiv μ (ULA.gibbsMeasure U) ≠ ⊤)
    (α : ℝ) (hα : 0 < α) (hαL : α ≤ (L : ℝ)) :
    Integrable (fun x ↦ ‖gradient U x‖ ^ 2) μ ∧
      (∫ x, ‖gradient U x‖ ^ 2 ∂μ) ≤
        (4 * (L : ℝ) ^ 2 / α) *
          (InformationTheory.klDiv μ (ULA.gibbsMeasure U)).toReal +
          2 * (Module.finrank ℝ E : ℝ) * (L : ℝ) := by
  have hL : 0 < L := hα.trans_le hαL
  obtain ⟨hi, hb⟩ := gibbs_gradient_moment_bound_of_finite_kl U L hL hU hLip μ hKL
  refine ⟨hi, hb.trans ?_⟩
  have hcoeff : 4 * (L : ℝ) ≤ 4 * (L : ℝ) ^ 2 / α := by
    apply (le_div_iff₀ hα).mpr
    nlinarith [mul_nonneg (show 0 ≤ (L : ℝ) by positivity) (sub_nonneg.mpr hαL)]
  have hmul := mul_le_mul_of_nonneg_right hcoeff
    (ENNReal.toReal_nonneg (a := InformationTheory.klDiv μ (ULA.gibbsMeasure U)))
  linarith

end ULA.LSI
