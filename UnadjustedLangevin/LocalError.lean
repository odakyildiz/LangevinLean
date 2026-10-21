import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-!
# The local Euler defect in Dalalyan's synchronous-coupling proof

All integrals below are Bochner integrals. The ambient Banach space can be
the space of square-integrable random variables: its norm then is the L² norm.
The estimates are derived from the integral equation, rather than assumed as
an error recurrence. Existence and stationarity of a solution are separate
probabilistic obligations, not assertions of this file.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace ULA

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- The drift integral omitted by a single Euler step. -/
def localDefect (g : H → H) (Y : ℝ → H) (h : ℝ) : H :=
  ∫ t in 0..h, g (Y t) - g (Y 0)

/-- The local defect is the exact drift integral minus its Euler approximation. -/
theorem localDefect_eq_integral_sub (g : H → H) (Y : ℝ → H) (h : ℝ)
    (hInt : IntervalIntegrable (fun t ↦ g (Y t)) volume 0 h) :
    localDefect g Y h = (∫ t in 0..h, g (Y t)) - h • g (Y 0) := by
  unfold localDefect
  rw [intervalIntegral.integral_sub hInt intervalIntegrable_const]
  simp only [intervalIntegral.integral_const, sub_zero]

/-- The additive integral equation decomposes an exact step into an Euler step
with common noise and the explicitly defined local defect. -/
theorem localDefect_euler_identity (g : H → H) (Y B : ℝ → H) (h : ℝ)
    (hInt : IntervalIntegrable (fun t ↦ g (Y t)) volume 0 h)
    (heq : Y h - Y 0 = -(∫ t in 0..h, g (Y t)) + B h) :
    Y h = Y 0 - h • g (Y 0) + B h - localDefect g Y h := by
  rw [sub_eq_iff_eq_add] at heq
  rw [heq, localDefect_eq_integral_sub g Y h hInt]
  module

omit [NormedSpace ℝ H] [CompleteSpace H] in
/-- A continuous reference path supplies the integral's measurability and
integrability because its Lipschitz drift is continuous. -/
theorem localDefect_integrable {L : ℝ≥0} {g : H → H} (hLip : LipschitzWith L g)
    (Y : ℝ → H) (hY : Continuous Y) (h : ℝ) :
    IntervalIntegrable (fun t ↦ g (Y t)) volume 0 h :=
  (hLip.continuous.comp hY).intervalIntegrable 0 h

/-- The elementary square-root integral responsible for Dalalyan's `2/3`. -/
theorem integral_sqrt_zero (h : ℝ) (hh : 0 ≤ h) :
    (∫ t in 0..h, Real.sqrt t) = (2 / 3 : ℝ) * h * Real.sqrt h := by
  simp_rw [Real.sqrt_eq_rpow]
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 1 / 2))]
  rw [Real.zero_rpow (by norm_num : (1 / 2 : ℝ) + 1 ≠ 0), sub_zero,
    Real.rpow_add_one' hh (by norm_num : (1 / 2 : ℝ) + 1 ≠ 0)]
  ring

omit [CompleteSpace H] in
/-- A bounded drift and a square-root noise bound control the increment. -/
theorem integral_equation_increment_bound
    (g : H → H) (Y B : ℝ → H) (h G N : ℝ) (_hh : 0 ≤ h)
    (hG : ∀ t ∈ Set.Icc 0 h, ‖g (Y t)‖ ≤ G)
    (hB : ∀ t ∈ Set.Icc 0 h, ‖B t‖ ≤ N * Real.sqrt t)
    (heq : ∀ t ∈ Set.Icc 0 h,
      Y t - Y 0 = -(∫ s in 0..t, g (Y s)) + B t)
    {t : ℝ} (ht : t ∈ Set.Icc 0 h) :
    ‖Y t - Y 0‖ ≤ t * G + N * Real.sqrt t := by
  have hdrift : ‖∫ s in 0..t, g (Y s)‖ ≤ G * t := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := t) (C := G) (f := fun s ↦ g (Y s)) (fun s hs ↦ ?_)
    · simpa [abs_of_nonneg ht.1] using hb
    · rw [Set.uIoc_of_le ht.1] at hs
      exact hG s ⟨hs.1.le, hs.2.trans ht.2⟩
  rw [heq t ht]
  calc
    ‖-(∫ s in 0..t, g (Y s)) + B t‖ ≤
        ‖∫ s in 0..t, g (Y s)‖ + ‖B t‖ := by
      simpa only [norm_neg] using norm_add_le (-(∫ s in 0..t, g (Y s))) (B t)
    _ ≤ G * t + N * Real.sqrt t := add_le_add hdrift (hB t ht)
    _ = t * G + N * Real.sqrt t := by ring

omit [CompleteSpace H] in
/-- Integrating the Lipschitz increment estimate gives Dalalyan's local defect
bound, before replacing its two terms by a single numerical constant. -/
theorem localDefect_bound
    (g : H → H) (Y B : ℝ → H) (L : ℝ≥0) (h G N : ℝ)
    (hh : 0 ≤ h) (hLip : LipschitzWith L g)
    (hG : ∀ t ∈ Set.Icc 0 h, ‖g (Y t)‖ ≤ G)
    (hB : ∀ t ∈ Set.Icc 0 h, ‖B t‖ ≤ N * Real.sqrt t)
    (heq : ∀ t ∈ Set.Icc 0 h,
      Y t - Y 0 = -(∫ s in 0..t, g (Y s)) + B t) :
    ‖localDefect g Y h‖ ≤
      (L : ℝ) * (h ^ 2 * G / 2 + (2 / 3 : ℝ) * h * Real.sqrt h * N) := by
  have hbound (t : ℝ) (ht : t ∈ Set.Ioc 0 h) :
      ‖g (Y t) - g (Y 0)‖ ≤ (L : ℝ) * (t * G + N * Real.sqrt t) := by
    calc
      ‖g (Y t) - g (Y 0)‖ ≤ (L : ℝ) * ‖Y t - Y 0‖ := by
        simpa only [dist_eq_norm] using hLip.dist_le_mul (Y t) (Y 0)
      _ ≤ (L : ℝ) * (t * G + N * Real.sqrt t) :=
        mul_le_mul_of_nonneg_left
          (integral_equation_increment_bound g Y B h G N hh hG hB heq ⟨ht.1.le, ht.2⟩)
          L.coe_nonneg
  have hbint : IntervalIntegrable
      (fun t : ℝ ↦ (L : ℝ) * (t * G + N * Real.sqrt t)) volume 0 h :=
    (by fun_prop : Continuous
      (fun t : ℝ ↦ (L : ℝ) * (t * G + N * Real.sqrt t))).intervalIntegrable _ _
  unfold localDefect
  calc
    ‖∫ t in 0..h, g (Y t) - g (Y 0)‖ ≤
        ∫ t in 0..h, (L : ℝ) * (t * G + N * Real.sqrt t) :=
      intervalIntegral.norm_integral_le_of_norm_le hh
        (Filter.Eventually.of_forall hbound) hbint
    _ = (L : ℝ) * (h ^ 2 * G / 2 + (2 / 3 : ℝ) * h * Real.sqrt h * N) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add
          ((by fun_prop : Continuous (fun t : ℝ ↦ t * G)).intervalIntegrable 0 h)
          ((by fun_prop : Continuous (fun t : ℝ ↦ N * Real.sqrt t)).intervalIntegrable 0 h),
        intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
        integral_id, integral_sqrt_zero h hh]
      ring

/-- The corrected Dalalyan--Karagulyan numerical constant, as an exact rational. -/
theorem dalalyan_constant_bound : (7 / 6 : ℝ) * Real.sqrt 2 ≤ 33 / 20 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

/-- Specializing the drift and noise norms to the stationary L² moment values
gives the `1.65 L √(d h³)` local error used in the corrected proof. -/
theorem localDefect_dalalyan_bound
    (g : H → H) (Y B : ℝ → H) (L : ℝ≥0) (h d : ℝ)
    (hh : 0 ≤ h) (hd : 0 ≤ d) (hstep : (L : ℝ) * h ≤ 2)
    (hLip : LipschitzWith L g)
    (hG : ∀ t ∈ Set.Icc 0 h, ‖g (Y t)‖ ≤ Real.sqrt ((L : ℝ) * d))
    (hB : ∀ t ∈ Set.Icc 0 h, ‖B t‖ ≤ Real.sqrt (2 * d) * Real.sqrt t)
    (heq : ∀ t ∈ Set.Icc 0 h,
      Y t - Y 0 = -(∫ s in 0..t, g (Y s)) + B t) :
    ‖localDefect g Y h‖ ≤ (33 / 20 : ℝ) * (L : ℝ) * h * Real.sqrt (h * d) := by
  have hsmall : h * Real.sqrt ((L : ℝ) * d) ≤
      Real.sqrt 2 * Real.sqrt (h * d) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg L.coe_nonneg hd),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt (mul_nonneg hh hd)]
    have hb := mul_le_mul_of_nonneg_right hstep (mul_nonneg hh hd)
    nlinarith
  have hnoise : h * Real.sqrt h * Real.sqrt (2 * d) =
      h * Real.sqrt 2 * Real.sqrt (h * d) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul hh]
    ring
  calc
    ‖localDefect g Y h‖ ≤ (L : ℝ) *
        (h ^ 2 * Real.sqrt ((L : ℝ) * d) / 2 +
          (2 / 3 : ℝ) * h * Real.sqrt h * Real.sqrt (2 * d)) :=
      localDefect_bound g Y B L h (Real.sqrt ((L : ℝ) * d))
        (Real.sqrt (2 * d)) hh hLip hG hB heq
    _ ≤ (L : ℝ) * ((7 / 6 : ℝ) * Real.sqrt 2 * h * Real.sqrt (h * d)) := by
      have hb := mul_le_mul_of_nonneg_left hsmall (mul_nonneg hh L.coe_nonneg)
      rw [show (2 / 3 : ℝ) * h * Real.sqrt h * Real.sqrt (2 * d) =
        (2 / 3 : ℝ) * (h * Real.sqrt h * Real.sqrt (2 * d)) by ring, hnoise]
      nlinarith
    _ ≤ (33 / 20 : ℝ) * (L : ℝ) * h * Real.sqrt (h * d) := by
      have hb := mul_le_mul_of_nonneg_right dalalyan_constant_bound
        (show 0 ≤ (L : ℝ) * h * Real.sqrt (h * d) by positivity)
      nlinarith

end ULA
