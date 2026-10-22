import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Gradient.Basic

set_option linter.style.header false

/-! # Smooth bounded entropy tests

The logarithm is truncated smoothly by `m arctan(z/m)`. Its derivative lies
between zero and one. The primitive in density coordinates approximates the
nonnegative KL integrand and permits the entropy equation to be tested first
with bounded functions. All limits below concern these explicit functions.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace ULA.LSI

/-- Smooth bounded approximation of the identity in logarithmic coordinates. -/
def boundedLogSlope (m : ℕ) (z : ℝ) : ℝ :=
  (m + 1 : ℝ) * Real.arctan (z / (m + 1 : ℝ))

/-- Its derivative, the multiplier of the Fisher/error energy in the weak test. -/
def boundedLogWeight (m : ℕ) (z : ℝ) : ℝ :=
  (1 + (z / (m + 1 : ℝ)) ^ 2)⁻¹

/-- The nonnegative entropy primitive, normalized to vanish at density one. -/
def boundedEntropy (m : ℕ) (r : ℝ) : ℝ :=
  ∫ u in (1 : ℝ)..r, boundedLogSlope m (Real.log u)

@[simp]
theorem boundedLogSlope_zero (m : ℕ) : boundedLogSlope m 0 = 0 := by
  simp [boundedLogSlope]

theorem boundedLogSlope_contDiff (m : ℕ) : ContDiff ℝ ⊤ (boundedLogSlope m) := by
  unfold boundedLogSlope
  have ha : ContDiff ℝ ⊤ (fun z : ℝ ↦ Real.arctan (z / (m + 1 : ℝ))) :=
    Real.contDiff_arctan.comp (contDiff_id.div_const (m + 1 : ℝ))
  exact contDiff_const.mul ha

theorem boundedLogSlope_hasDerivAt (m : ℕ) (z : ℝ) :
    HasDerivAt (boundedLogSlope m) (boundedLogWeight m z) z := by
  have hd := (((hasDerivAt_id z).div_const (m + 1 : ℝ)).arctan).const_mul (m + 1 : ℝ)
  convert hd using 1
  · rfl
  · dsimp [boundedLogWeight]
    field_simp

theorem boundedLogWeight_nonneg (m : ℕ) (z : ℝ) : 0 ≤ boundedLogWeight m z := by
  dsimp [boundedLogWeight]
  positivity

theorem boundedLogWeight_le_one (m : ℕ) (z : ℝ) : boundedLogWeight m z ≤ 1 := by
  dsimp [boundedLogWeight]
  apply inv_le_one_of_one_le₀
  nlinarith [sq_nonneg (z / (m + 1 : ℝ))]

theorem boundedLogSlope_lipschitz (m : ℕ) : LipschitzWith 1 (boundedLogSlope m) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun z ↦ (boundedLogSlope_hasDerivAt m z).differentiableAt)
  intro z
  apply NNReal.coe_le_coe.mp
  change ‖deriv (boundedLogSlope m) z‖ ≤ (1 : ℝ)
  rw [(boundedLogSlope_hasDerivAt m z).deriv, Real.norm_eq_abs,
    abs_of_nonneg (boundedLogWeight_nonneg m z)]
  exact boundedLogWeight_le_one m z

theorem norm_boundedLogSlope_le (m : ℕ) (z : ℝ) : ‖boundedLogSlope m z‖ ≤ ‖z‖ := by
  simpa only [boundedLogSlope_zero, sub_zero, NNReal.coe_one, one_mul] using
    (boundedLogSlope_lipschitz m).norm_sub_le z 0

theorem norm_boundedLogSlope_le_const (m : ℕ) (z : ℝ) :
    ‖boundedLogSlope m z‖ ≤ (m + 1 : ℝ) * (Real.pi / 2) := by
  have hbound : |Real.arctan (z / (m + 1 : ℝ))| ≤ Real.pi / 2 :=
    (abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩).le
  rw [boundedLogSlope, norm_mul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (m + 1 : ℝ))]
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

theorem boundedLogSlope_nonneg (m : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ boundedLogSlope m z := by
  unfold boundedLogSlope
  exact mul_nonneg (by positivity) (Real.arctan_nonneg.mpr (div_nonneg hz (by positivity)))

theorem boundedLogSlope_nonpos (m : ℕ) {z : ℝ} (hz : z ≤ 0) :
    boundedLogSlope m z ≤ 0 := by
  unfold boundedLogSlope
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
    (Real.arctan_le_zero.mpr (div_nonpos_of_nonpos_of_nonneg hz (by positivity)))

theorem boundedLogSlope_tendsto (z : ℝ) :
    Tendsto (fun m : ℕ ↦ boundedLogSlope m z) atTop (𝓝 z) := by
  by_cases hz : z = 0
  · subst z
    simp
  have hden : Tendsto (fun m : ℕ ↦ (m + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun m : ℕ ↦ z / (m + 1 : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hden).const_mul z
  have hne : Tendsto (fun m : ℕ ↦ z / (m + 1 : ℝ)) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, Eventually.of_forall (fun m ↦ div_ne_zero hz (by positivity))⟩
  have hd := (Real.hasDerivAt_arctan (0 : ℝ)).tendsto_slope_zero.comp hne
  have hlim := hd.const_mul z
  convert hlim using 1
  · funext m
    simp only [zero_add, Real.arctan_zero, sub_zero, smul_eq_mul, boundedLogSlope, Function.comp_def]
    field_simp [hz]
  · norm_num

theorem boundedLogWeight_tendsto (z : ℝ) :
    Tendsto (fun m : ℕ ↦ boundedLogWeight m z) atTop (𝓝 1) := by
  have hden : Tendsto (fun m : ℕ ↦ (m + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun m : ℕ ↦ z / (m + 1 : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hden).const_mul z
  simpa only [boundedLogWeight, zero_pow (by norm_num : 2 ≠ 0), add_zero, inv_one] using
    ((hzero.pow 2).const_add 1).inv₀ (by norm_num : (1 + 0 ^ 2 : ℝ) ≠ 0)

theorem boundedLog_integrable (m : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun u ↦ boundedLogSlope m (Real.log u)) volume a b := by
  apply (intervalIntegrable_const (c := (m + 1 : ℝ) * (Real.pi / 2))).mono_fun'
  · exact ((boundedLogSlope_contDiff m).continuous.measurable.comp Real.measurable_log).aestronglyMeasurable
  · exact ae_of_all _ fun u ↦ norm_boundedLogSlope_le_const m (Real.log u)

theorem boundedEntropy_hasDerivAt (m : ℕ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (boundedEntropy m) (boundedLogSlope m (Real.log r)) r := by
  apply intervalIntegral.integral_hasDerivAt_right (boundedLog_integrable m 1 r)
  · have hm := ((boundedLogSlope_contDiff m).continuous.measurable.comp Real.measurable_log)
    exact hm.stronglyMeasurable.stronglyMeasurableAtFilter
  · exact (boundedLogSlope_contDiff m).continuous.continuousAt.comp
      (Real.continuousAt_log hr.ne')

@[simp]
theorem boundedEntropy_one (m : ℕ) : boundedEntropy m 1 = 0 := by
  simp [boundedEntropy]

theorem boundedEntropy_nonneg (m : ℕ) {r : ℝ} (hr : 0 < r) :
    0 ≤ boundedEntropy m r := by
  by_cases h : 1 ≤ r
  · apply intervalIntegral.integral_nonneg h
    intro u hu
    exact boundedLogSlope_nonneg m (Real.log_nonneg hu.1)
  · have hr1 : r ≤ 1 := le_of_not_ge h
    have hi : 0 ≤ ∫ u in r..(1 : ℝ), -(boundedLogSlope m (Real.log u)) := by
      apply intervalIntegral.integral_nonneg hr1
      intro u hu
      exact neg_nonneg.mpr (boundedLogSlope_nonpos m
        (Real.log_nonpos (hr.le.trans hu.1) hu.2))
    rw [intervalIntegral.integral_neg] at hi
    change 0 ≤ ∫ u in (1 : ℝ)..r, boundedLogSlope m (Real.log u)
    rw [intervalIntegral.integral_symm]
    exact hi

theorem boundedEntropy_le_klFun (m : ℕ) {r : ℝ} (hr : 0 < r) :
    boundedEntropy m r ≤ InformationTheory.klFun r := by
  by_cases h : 1 ≤ r
  · have hi : (∫ u in (1 : ℝ)..r, boundedLogSlope m (Real.log u)) ≤
        ∫ u in (1 : ℝ)..r, Real.log u := by
      apply intervalIntegral.integral_mono_on h (boundedLog_integrable m 1 r)
        intervalIntegral.intervalIntegrable_log'
      intro u hu
      have hb := norm_boundedLogSlope_le m (Real.log u)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hu.1)] at hb
      exact (le_abs_self _).trans hb
    calc
      _ ≤ ∫ u in (1 : ℝ)..r, Real.log u := hi
      _ = _ := by rw [integral_log]; simp [InformationTheory.klFun]; ring
  · have hr1 : r ≤ 1 := le_of_not_ge h
    have hi : (∫ u in r..(1 : ℝ), Real.log u) ≤
        ∫ u in r..(1 : ℝ), boundedLogSlope m (Real.log u) := by
      apply intervalIntegral.integral_mono_on hr1 intervalIntegral.intervalIntegrable_log'
        (boundedLog_integrable m r 1)
      intro u hu
      have hlog := Real.log_nonpos (hr.le.trans hu.1) hu.2
      have hb := norm_boundedLogSlope_le m (Real.log u)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonpos hlog] at hb
      linarith [neg_abs_le (boundedLogSlope m (Real.log u))]
    calc
      _ = -(∫ u in r..(1 : ℝ), boundedLogSlope m (Real.log u)) :=
        intervalIntegral.integral_symm r 1
      _ ≤ -(∫ u in r..(1 : ℝ), Real.log u) := neg_le_neg hi
      _ = _ := by rw [integral_log]; simp [InformationTheory.klFun]; ring

theorem boundedEntropy_tendsto {r : ℝ} (_hr : 0 < r) :
    Tendsto (fun m : ℕ ↦ boundedEntropy m r) atTop (𝓝 (InformationTheory.klFun r)) := by
  have hdct : Tendsto (fun m : ℕ ↦
      ∫ u in Set.uIoc (1 : ℝ) r, boundedLogSlope m (Real.log u)) atTop
      (𝓝 (∫ u in Set.uIoc (1 : ℝ) r, Real.log u)) := by
    apply tendsto_integral_of_dominated_convergence (fun u ↦ ‖Real.log u‖)
    · intro m
      have hm := ((boundedLogSlope_contDiff m).continuous.measurable.comp Real.measurable_log)
      exact hm.aestronglyMeasurable
    · exact intervalIntegral.intervalIntegrable_log'.def'.norm
    · intro m
      exact ae_of_all _ fun u ↦ norm_boundedLogSlope_le m (Real.log u)
    · exact ae_of_all _ fun u ↦ boundedLogSlope_tendsto (Real.log u)
  have hlim := hdct.const_mul (if (1 : ℝ) ≤ r then 1 else -1)
  have hformula : (∫ u in (1 : ℝ)..r, Real.log u) = InformationTheory.klFun r := by
    rw [integral_log]
    simp only [Real.log_one, mul_zero, sub_zero]
    unfold InformationTheory.klFun
    ring
  convert hlim using 1
  · funext m
    simpa only [boundedEntropy, smul_eq_mul] using
      (intervalIntegral.intervalIntegral_eq_integral_uIoc
        (fun u ↦ boundedLogSlope m (Real.log u)) 1 r volume)
  · rw [← smul_eq_mul, ← intervalIntegral.intervalIntegral_eq_integral_uIoc, hformula]

section Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gradient_boundedLogSlope_comp (m : ℕ) (f : E → ℝ) (x : E)
    (hf : DifferentiableAt ℝ f x) :
    gradient (fun y ↦ boundedLogSlope m (f y)) x =
      boundedLogWeight m (f x) • gradient f x := by
  have hd : HasFDerivAt (fun y ↦ boundedLogSlope m (f y))
      (boundedLogWeight m (f x) • fderiv ℝ f x) x := by
    convert (boundedLogSlope_hasDerivAt m (f x)).hasFDerivAt.comp x hf.hasFDerivAt using 1
    · rfl
    · ext v
      simp [mul_comm]
  simp only [gradient, hd.fderiv, map_smul]

theorem norm_gradient_boundedLogSlope_comp_le (m : ℕ) (f : E → ℝ) (x : E)
    (hf : DifferentiableAt ℝ f x) :
    ‖gradient (fun y ↦ boundedLogSlope m (f y)) x‖ ≤ ‖gradient f x‖ := by
  rw [gradient_boundedLogSlope_comp m f x hf, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (boundedLogWeight_nonneg m (f x))]
  exact mul_le_of_le_one_left (norm_nonneg _) (boundedLogWeight_le_one m (f x))

end Gradient

end ULA.LSI
