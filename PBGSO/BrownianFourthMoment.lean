import PBGSO.CanonicalBrownianDriver
import Mathlib.Probability.BorelCantelli

/-! # Actual Gaussian fourth moments and Brownian increment tails
The finite fourth moment constant is its actual standard Gaussian integral;
no exact evaluation or stochastic moment premise is assumed.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace PBGSO.BrownianFourthMoment

def fourthConstant : ℝ := ∫ x : ℝ, ‖x‖ ^ 4 ∂gaussianReal 0 1

theorem fourthConstant_nonneg : 0 ≤ fourthConstant :=
  integral_nonneg (fun _ => by positivity)

theorem standard_fourth_integrable : Integrable (fun x : ℝ => ‖x‖ ^ 4) (gaussianReal 0 1) :=
  (memLp_id_gaussianReal (μ := 0) (v := 1) 4).integrable_norm_pow' (p := 4)

theorem gaussian_fourth_moment (v : ℝ≥0) :
    (∫ x : ℝ, ‖x‖ ^ 4 ∂gaussianReal 0 v) = fourthConstant * (v : ℝ) ^ 2 := by
  have hv : (NNReal.mk ((Real.sqrt (v : ℝ)) ^ 2) (sq_nonneg _) : ℝ≥0) * 1 = v := by
    ext
    simp only [NNReal.coe_mk, mul_one]
    exact Real.sq_sqrt v.coe_nonneg
  have hLaw : HasLaw (fun x : ℝ => Real.sqrt (v : ℝ) * x)
      (gaussianReal 0 v) (gaussianReal 0 1) := by
    have h := gaussianReal_const_mul (HasLaw.id (μ := gaussianReal 0 1)) (Real.sqrt (v : ℝ))
    rw [hv] at h
    simpa only [Function.id_def, mul_zero] using h
  have he := hLaw.integral_comp (f := fun x : ℝ => ‖x‖ ^ 4) (by fun_prop)
  simp only [Function.comp_apply, Real.norm_eq_abs,
    abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow] at he
  rw [integral_const_mul] at he
  have hs : Real.sqrt (v : ℝ) ^ 4 = (v : ℝ) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, Real.sq_sqrt v.coe_nonneg]
  rw [hs] at he
  simpa only [fourthConstant, Real.norm_eq_abs, mul_comm] using he.symm

variable {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
  (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B Q)
include hB

theorem increment_fourth_integrable (s t : ℝ≥0) :
    Integrable (fun ω => ‖B t ω - B s ω‖ ^ 4) Q := by
  have h := (hB.hasLaw_sub t s).integrable_comp
    ((memLp_id_gaussianReal (μ := 0) (v := nndist (t : ℝ) (s : ℝ)) 4).integrable_norm_pow' (p := 4))
  exact h

theorem increment_fourth_moment (s t : ℝ≥0) :
    (∫ ω, ‖B t ω - B s ω‖ ^ 4 ∂Q) =
      fourthConstant * dist (t : ℝ) (s : ℝ) ^ 2 := by
  have he := (hB.hasLaw_sub t s).integral_comp (f := fun x : ℝ => ‖x‖ ^ 4) (by fun_prop)
  rw [gaussian_fourth_moment] at he
  exact he

/-- Actual fourth-moment Markov bound, stated for the genuine tail event. -/
theorem increment_tail_real (s t : ℝ≥0) (a : ℝ) (ha : 0 < a) :
    Q.real {ω | a ≤ ‖B t ω - B s ω‖} ≤
      fourthConstant * dist (t : ℝ) (s : ℝ) ^ 2 / a ^ 4 := by
  have hevent : {ω | a ≤ ‖B t ω - B s ω‖} =
      {ω | a ^ 4 ≤ ‖B t ω - B s ω‖ ^ 4} := by
    ext ω
    exact (pow_le_pow_iff_left₀ ha.le (norm_nonneg _) (by decide : (4 : ℕ) ≠ 0)).symm
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => pow_nonneg (norm_nonneg (B t ω - B s ω)) 4))
    (increment_fourth_integrable Q B hB s t) (a ^ 4)
  rw [increment_fourth_moment Q B hB s t, ← hevent] at hm
  exact (le_div_iff₀ (pow_pos ha 4)).mpr (by simpa only [mul_comm] using hm)

theorem increment_tail (s t : ℝ≥0) (a : ℝ) (ha : 0 < a) :
    Q {ω | a ≤ ‖B t ω - B s ω‖} ≤
      ENNReal.ofReal (fourthConstant * dist (t : ℝ) (s : ℝ) ^ 2 / a ^ 4) := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top Q _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (div_nonneg (mul_nonneg fourthConstant_nonneg (sq_nonneg _)) (pow_nonneg ha.le 4))]
  exact increment_tail_real Q B hB s t a ha
end PBGSO.BrownianFourthMoment
