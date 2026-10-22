import UnadjustedLangevin.LSI.OneStep
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option linter.style.header false

/-! # Entropy comparison with almost-everywhere time derivatives

The finite-energy entropy chain rule yields an absolutely continuous entropy
curve and a differential inequality almost everywhere. The comparison here
uses precisely that conclusion, rather than requiring pointwise derivatives
at every time or a two-sided density extension through the initial time.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ULA.LSI

/-- Affine differential comparison on an interval for an absolutely continuous
real function. The derivative inequality is required only almost everywhere.
This is a scalar theorem and makes no assertion about an entropy path. -/
theorem affine_decay_of_ae_deriv_le
    (H : ℝ → ℝ) (a b s t : ℝ) (ha : 0 < a) (hst : s ≤ t)
    (hAC : AbsolutelyContinuousOnInterval H s t)
    (hbound : ∀ᵐ u ∂volume, u ∈ Icc s t → deriv H u ≤ -a * H u + b) :
    H t ≤ Real.exp (-a * (t - s)) * H s +
      b / a * (1 - Real.exp (-a * (t - s))) := by
  let F : ℝ → ℝ := fun u ↦ Real.exp (a * u) * (H u - b / a)
  have heAC : AbsolutelyContinuousOnInterval (fun u : ℝ ↦ Real.exp (a * u)) s t :=
    (by fun_prop : ContDiff ℝ 1 (fun u : ℝ ↦ Real.exp (a * u))).contDiffOn
      |>.absolutelyContinuousOnInterval
  have hcAC : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ b / a) s t :=
    (by fun_prop : ContDiff ℝ 1 (fun _ : ℝ ↦ b / a)).contDiffOn
      |>.absolutelyContinuousOnInterval
  have hFAC : AbsolutelyContinuousOnInterval F s t := heAC.fun_mul (hAC.sub hcAC)
  have hderiv : ∀ᵐ u ∂volume, u ∈ Icc s t → deriv F u ≤ 0 := by
    filter_upwards [hAC.ae_differentiableAt, hbound] with u hu hb huinterval
    have hdH := (hu (by simpa only [uIcc_of_le hst] using huinterval)).hasDerivAt
    have he := ((hasDerivAt_id u).const_mul a).exp
    have hF : HasDerivAt F
        (Real.exp (a * u) * (a * (H u - b / a) + deriv H u)) u := by
      convert he.mul (hdH.sub_const (b / a)) using 1
      · funext x
        simp [F]
      · simp only [id_eq, mul_one]
        ring
    rw [hF.deriv]
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _)
    have hcancel : a * (b / a) = b := by field_simp
    have hb' := hb huinterval
    nlinarith
  have hintegral : (∫ u in s..t, deriv F u) ≤ 0 := by
    rw [intervalIntegral.integral_of_le hst]
    apply integral_nonpos_of_ae
    change ∀ᵐ u ∂volume.restrict (Ioc s t), deriv F u ≤ 0
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hderiv] with u hu hus
    exact hu ⟨hus.1.le, hus.2⟩
  rw [hFAC.integral_deriv_eq_sub] at hintegral
  have hmult := mul_le_mul_of_nonneg_left (sub_nonpos.mp hintegral)
    (Real.exp_nonneg (-a * t))
  have htt : Real.exp (-a * t) * Real.exp (a * t) = 1 := by
    rw [← Real.exp_add, show -a * t + a * t = 0 by ring, Real.exp_zero]
  have hts : Real.exp (-a * t) * Real.exp (a * s) = Real.exp (-a * (t - s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp only [F] at hmult
  rw [← mul_assoc, htt, one_mul, ← mul_assoc, hts] at hmult
  nlinarith

/-- Initial entropy need only have a continuous upper envelope near zero.
The curve can be absolutely continuous solely on positive-time subintervals.
In particular, this comparison does not assume initial Fisher information,
initial density differentiability, or an entropy derivative at time zero. -/
theorem affine_decay_of_local_ae_deriv_le
    (H M : ℝ → ℝ) (a b T : ℝ) (ha : 0 < a) (hT : 0 < T)
    (hAC : ∀ s ∈ Ioo 0 T, AbsolutelyContinuousOnInterval H s T)
    (hbound : ∀ᵐ u ∂volume, u ∈ Ioo 0 T → deriv H u ≤ -a * H u + b)
    (hM : ContinuousAt M 0)
    (hupper : ∀ᶠ s in 𝓝[>] (0 : ℝ), H s ≤ M s) :
    H T ≤ Real.exp (-a * T) * M 0 + b / a * (1 - Real.exp (-a * T)) := by
  let F : ℝ → ℝ := fun s ↦ Real.exp (-a * (T - s)) * M s +
    b / a * (1 - Real.exp (-a * (T - s)))
  have hF : ContinuousAt F 0 := by
    dsimp only [F]
    fun_prop
  have hlim : Tendsto F (𝓝[>] (0 : ℝ))
      (𝓝 (Real.exp (-a * T) * M 0 + b / a * (1 - Real.exp (-a * T)))) := by
    simpa only [F, sub_zero] using hF.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [Ioo_mem_nhdsGT hT, hupper] with s hs hsM
  have hinterval : ∀ᵐ u ∂volume, u ∈ Icc s T → deriv H u ≤ -a * H u + b := by
    have hneq : ∀ᵐ u : ℝ ∂volume, u ≠ T := by
      rw [ae_iff]
      simpa only [not_not, ofPred_eq_eq_singleton] using (measure_singleton T : volume {T} = 0)
    filter_upwards [hbound, hneq] with u hu hune huIcc
    exact hu ⟨hs.1.trans_le huIcc.1, lt_of_le_of_ne huIcc.2 hune⟩
  have hcompare := affine_decay_of_ae_deriv_le H a b s T ha hs.2.le
    (hAC s hs) hinterval
  apply hcompare.trans
  dsimp only [F]
  exact add_le_add (mul_le_mul_of_nonneg_left hsM (Real.exp_nonneg _)) le_rfl

/-- The scalar ULA one-step estimate with an actual finite-energy entropy
chain rule: derivatives are needed almost everywhere at positive times, and
only a continuous upper envelope is required at the initial endpoint. -/
theorem one_step_entropy_of_ae_interpolation
    (H M I : ℝ → ℝ) (G₀ α L h n : ℝ)
    (hα : 0 < α) (hL : 0 < L) (hh : 0 < h) (hαL : α ≤ L) (hn : 0 ≤ n)
    (hsmall : h ≤ α / (4 * L ^ 2)) (hM₀ : 0 ≤ M 0)
    (hAC : ∀ s ∈ Ioo 0 h, AbsolutelyContinuousOnInterval H s h)
    (hM : ContinuousAt M 0)
    (hupper : ∀ᶠ s in 𝓝[>] (0 : ℝ), H s ≤ M s)
    (hlsi : ∀ᵐ t ∂volume, t ∈ Ioo 0 h → 2 * α * H t ≤ I t)
    (hproduction : ∀ᵐ t ∂volume, t ∈ Ioo 0 h →
      deriv H t ≤ -(3 / 4 : ℝ) * I t + t ^ 2 * L ^ 2 * G₀ + 2 * t * n * L ^ 2)
    (hgradient : G₀ ≤ (4 * L ^ 2 / α) * M 0 + 2 * n * L) :
    H h ≤ Real.exp (-α * h) * M 0 + 6 * h ^ 2 * n * L ^ 2 := by
  have hstep : 4 * h * L ^ 2 ≤ α := by
    have := (le_div_iff₀ (by positivity : 0 < 4 * L ^ 2)).mp hsmall
    nlinarith
  have hhL : h * L ≤ 1 / 4 := by
    have hp : (4 * h * L) * L ≤ 1 * L := by nlinarith
    have := (mul_le_mul_iff_of_pos_right hL).mp hp
    linarith
  have hhα : α * h ≤ 1 / 4 := by nlinarith
  let A := (4 * L ^ 2 / α) * M 0 + 2 * n * L
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hcoeff : h ^ 2 * L ^ 2 * (4 * L ^ 2 / α) ≤ α / 4 := by
    have hbase : h * L ^ 2 ≤ α / 4 := by linarith
    have hsquare : (h * L ^ 2) ^ 2 ≤ (α / 4) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).mpr hbase
    calc
      h ^ 2 * L ^ 2 * (4 * L ^ 2 / α) = 4 * (h * L ^ 2) ^ 2 / α := by ring
      _ ≤ 4 * (α / 4) ^ 2 / α :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsquare (by norm_num)) hα.le
      _ = α / 4 := by field_simp
  have hcoeffH := mul_le_mul_of_nonneg_right hcoeff hM₀
  have hnoise : h ^ 2 * L ^ 2 * (2 * n * L) ≤ (1 / 2 : ℝ) * h * n * L ^ 2 := by
    have hp := mul_le_mul_of_nonneg_left hhL
      (by positivity : 0 ≤ 2 * h * n * L ^ 2)
    nlinarith
  have huniform : h ^ 2 * L ^ 2 * A ≤
      (α / 4) * M 0 + (1 / 2 : ℝ) * h * n * L ^ 2 := by
    dsimp [A]
    nlinarith
  let b := (α / 4) * M 0 + (5 / 2 : ℝ) * h * n * L ^ 2
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hbound : ∀ᵐ t ∂volume, t ∈ Ioo 0 h →
      deriv H t ≤ -((3 / 2 : ℝ) * α) * H t + b := by
    filter_upwards [hproduction, hlsi] with t hproduction_t hlsi_t ht
    have htsq : t ^ 2 ≤ h ^ 2 := (sq_le_sq₀ ht.1.le hh.le).mpr ht.2.le
    have hp₁ := mul_le_mul_of_nonneg_left hgradient (by positivity : 0 ≤ t ^ 2 * L ^ 2)
    have hp₂ := mul_le_mul_of_nonneg_right htsq (by positivity : 0 ≤ L ^ 2 * A)
    have hp₃ := mul_le_mul_of_nonneg_right ht.2.le (by positivity : 0 ≤ 2 * n * L ^ 2)
    have hp₄ := mul_le_mul_of_nonneg_left (hlsi_t ht) (by norm_num : (0 : ℝ) ≤ 3 / 4)
    have hp₅ := hproduction_t ht
    change G₀ ≤ A at hgradient
    change t ^ 2 * L ^ 2 * G₀ ≤ t ^ 2 * L ^ 2 * A at hp₁
    dsimp [b]
    nlinarith
  have hcompare := affine_decay_of_local_ae_deriv_le H M ((3 / 2 : ℝ) * α) b h
    (by positivity) hh hAC hbound hM hupper
  have hintegral : b / ((3 / 2 : ℝ) * α) *
      (1 - Real.exp (-((3 / 2 : ℝ) * α) * h)) ≤ b * h := by
    have he : 1 - Real.exp (-((3 / 2 : ℝ) * α) * h) ≤ ((3 / 2 : ℝ) * α) * h := by
      linarith [Real.add_one_le_exp (-((3 / 2 : ℝ) * α) * h)]
    have hm := mul_le_mul_of_nonneg_left he
      (div_nonneg hb (by positivity : 0 ≤ (3 / 2 : ℝ) * α))
    have heq : b / ((3 / 2 : ℝ) * α) * (((3 / 2 : ℝ) * α) * h) = b * h := by
      field_simp
    simpa only [heq] using hm
  have hexp := mul_le_mul_of_nonneg_right
    (exp_three_halves_gap (α * h) (by positivity) hhα) hM₀
  have hnoise_final : (5 / 2 : ℝ) * h ^ 2 * n * L ^ 2 ≤ 6 * h ^ 2 * n * L ^ 2 := by
    have : 0 ≤ h ^ 2 * n * L ^ 2 := by positivity
    nlinarith
  have hexp_arg : -((3 / 2 : ℝ) * α) * h = -(3 / 2 : ℝ) * (α * h) := by ring
  rw [hexp_arg] at hcompare hintegral
  rw [show -(α * h) = -α * h by ring] at hexp
  dsimp [b] at hcompare hintegral
  nlinarith

end ULA.LSI
