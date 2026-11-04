import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-! # Local error energy from the actual time integral

The ambient space may itself be the Hilbert space of square-integrable random
vectors.  Time Cauchy--Schwarz then gives the paper's exact constant `3`.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WassersteinMixing

private theorem toLp_norm_sq {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (f : Ω → ℝ) (hf : MemLp f 2 Q) :
    ‖hf.toLp f‖ ^ 2 = ∫ ω, f ω ^ 2 ∂Q := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with ω hω
  simp [hω]

private theorem real_cauchy_schwarz {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (f g : Ω → ℝ) (hf : MemLp f 2 Q) (hg : MemLp g 2 Q) :
    (∫ ω, f ω * g ω ∂Q) ≤
      Real.sqrt (∫ ω, f ω ^ 2 ∂Q) * Real.sqrt (∫ ω, g ω ^ 2 ∂Q) := by
  have he : (∫ ω, f ω * g ω ∂Q) = inner ℝ (hf.toLp f) (hg.toLp g) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω hfω hgω
    simp [hfω, hgω, RCLike.inner_apply, mul_comm]
  have hn (f : Ω → ℝ) (hf : MemLp f 2 Q) :
      ‖hf.toLp f‖ = Real.sqrt (∫ ω, f ω ^ 2 ∂Q) := by
    rw [← toLp_norm_sq Q f hf, Real.sqrt_sq (norm_nonneg _)]
  rw [he, ← hn f hf, ← hn g hg]
  exact real_inner_le_norm _ _

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Time Cauchy--Schwarz for the genuine Bochner primitive. -/
theorem time_integral_norm_sq (increment : ℝ → H) (h : ℝ) (hh : 0 ≤ h)
    (hi : MemLp increment 2 (volume.restrict (Ioc 0 h))) :
    ‖∫ s in (0 : ℝ)..h, increment s‖ ^ 2 ≤
      h * ∫ s in (0 : ℝ)..h, ‖increment s‖ ^ 2 := by
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (f := increment) (μ := volume) hh
  have hcs := real_cauchy_schwarz (volume.restrict (Ioc 0 h))
    (fun s ↦ ‖increment s‖) (fun _ ↦ (1 : ℝ)) hi.norm (memLp_const 1)
  simp only [mul_one, one_pow, integral_const, Measure.real, Measure.restrict_apply_univ,
    Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hh, smul_eq_mul] at hcs
  simp only [intervalIntegral.integral_of_le hh] at hnorm ⊢
  have hnonneg : 0 ≤ ∫ s in Ioc 0 h, ‖increment s‖ ^ 2 :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hleft := hnorm.trans hcs
  have hs := Real.sq_sqrt hnonneg
  have ht := Real.sq_sqrt hh
  have hprod : (Real.sqrt (∫ s in Ioc 0 h, ‖increment s‖ ^ 2) * Real.sqrt h) ^ 2 =
      (∫ s in Ioc 0 h, ‖increment s‖ ^ 2) * h := by rw [mul_pow, hs, ht]
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hleft 2
  nlinarith

/-- The local defect is the actual integrated score increment. -/
def stationaryLocalDefect (increment : ℝ → H) (h : ℝ) : H :=
  ∫ s in (0 : ℝ)..h, increment s

/-- The score-increment estimate integrates to the paper's `3 h³ β² d`. -/
theorem stationaryLocalDefect_energy_le (increment : ℝ → H) (h β d : ℝ)
    (hh : 0 ≤ h) (hi : MemLp increment 2 (volume.restrict (Ioc 0 h)))
    (hbound : ∀ s ∈ Ioc 0 h, ‖increment s‖ ^ 2 ≤ 6 * s * β ^ 2 * d) :
    ‖stationaryLocalDefect increment h‖ ^ 2 ≤ 3 * h ^ 3 * β ^ 2 * d := by
  have hsq : IntervalIntegrable (fun s ↦ ‖increment s‖ ^ 2) volume 0 h := by
    rw [intervalIntegrable_iff, uIoc_of_le hh]
    exact hi.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hpoly : IntervalIntegrable (fun s : ℝ ↦ 6 * s * β ^ 2 * d) volume 0 h :=
    (by fun_prop : Continuous (fun s : ℝ ↦ 6 * s * β ^ 2 * d)).intervalIntegrable 0 h
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hh hsq hpoly
    (fun s hs ↦ hbound s ⟨hs.1, hs.2.le⟩)
  calc
    _ ≤ h * ∫ s in (0 : ℝ)..h, ‖increment s‖ ^ 2 := time_integral_norm_sq increment h hh hi
    _ ≤ h * ∫ s in (0 : ℝ)..h, 6 * s * β ^ 2 * d :=
      mul_le_mul_of_nonneg_left hmono hh
    _ = _ := by
      have heq : (fun s : ℝ ↦ 6 * s * β ^ 2 * d) = fun s ↦ (6 * β ^ 2 * d) * s := by
        funext s; ring
      rw [heq, intervalIntegral.integral_const_mul, integral_id]
      ring

/-- The paper's displacement polynomial simplifies under the stable step. -/
theorem displacement_polynomial_le (s h β : ℝ) (hs : 0 ≤ s) (hsh : s ≤ h)
    (hβ : 0 ≤ β) (hstep : h * β ≤ 1) :
    2 * s ^ 2 * β + 4 * s ≤ 6 * s := by
  have hsb : s * β ≤ 1 := (mul_le_mul_of_nonneg_right hsh hβ).trans hstep
  nlinarith [mul_le_mul_of_nonneg_left hsb hs]

end WassersteinMixing
