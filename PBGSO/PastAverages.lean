import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Past translation averages in actual time-L²
The approximation is constructed by Bochner averaging the actual
measure-preserving translation action. Its convergence follows from FTC,
without time continuity of the original L² integrand.
-/
noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.PastAverages
variable {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R] [CompleteSpace R]
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
abbrev TimeLp := Lp R 2 (volume : Measure ℝ)

def shift (U : TimeLp (R := R)) (r : ℝ) : TimeLp (R := R) :=
  (DomAddAct.mk (-r) : DomAddAct ℝ) +ᵥ U

theorem shift_continuous (U : TimeLp (R := R)) : Continuous (shift U) :=
  (DomAddAct.continuous_mk.comp continuous_neg).vadd continuous_const

@[simp] theorem shift_zero (U : TimeLp (R := R)) : shift U 0 = U := by
  have hm : DomAddAct.mk (0 : ℝ) = (0 : DomAddAct ℝ) := rfl
  rw [shift, neg_zero, hm, zero_vadd]

theorem shift_coe (U : TimeLp (R := R)) (r : ℝ) :
    shift U r =ᵐ[volume] (fun t => U (t - r)) := by
  simpa only [shift, Equiv.symm_apply_apply, vadd_eq_add, sub_eq_add_neg, add_comm] using
    DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-r)) U

def average (U : TimeLp (R := R)) (ε : ℝ) : TimeLp (R := R) :=
  ε⁻¹ • ∫ r in 0..ε, shift U r

theorem average_tendsto (U : TimeLp (R := R)) :
    Tendsto (average U) (𝓝[>] (0 : ℝ)) (𝓝 U) := by
  have hder : HasDerivAt (fun ε : ℝ => ∫ r in 0..ε, shift U r) U 0 := by
    simpa only [shift_zero] using intervalIntegral.integral_hasDerivAt_right
      ((shift_continuous U).intervalIntegrable 0 0)
      (shift_continuous U).aestronglyMeasurable.stronglyMeasurableAtFilter
      (shift_continuous U).continuousAt
  change Tendsto (fun ε : ℝ => ε⁻¹ • ∫ r in 0..ε, shift U r) _ _
  simpa only [zero_add, intervalIntegral.integral_same, sub_zero] using
    hder.tendsto_slope_zero_right



theorem average_sub (U V : TimeLp (R := R)) (ε : ℝ) :
    average (U - V) ε = average U ε - average V ε := by
  have he : shift (U - V) = fun r => shift U r - shift V r := by
    funext r
    exact DomAddAct.vadd_Lp_sub (DomAddAct.mk (-r)) U V
  rw [average, he, intervalIntegral.integral_sub
    ((shift_continuous U).intervalIntegrable 0 ε) ((shift_continuous V).intervalIntegrable 0 ε), smul_sub]
  rfl

/-- Past averaging is a contraction in the actual time-L² norm. -/
theorem average_norm_le (U : TimeLp (R := R)) (ε : ℝ) (hε : 0 < ε) :
    ‖average U ε‖ ≤ ‖U‖ := by
  rw [average, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε]
  have hn : (fun r => ‖shift U r‖) = (fun _ : ℝ => ‖U‖) := by
    funext r
    exact DomAddAct.norm_vadd_Lp (DomAddAct.mk (-r)) U
  calc
    ε⁻¹ * ‖∫ r in 0..ε, shift U r‖ ≤ ε⁻¹ * ∫ r in 0..ε, ‖shift U r‖ :=
      mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm hε.le) (by positivity)
    _ = ‖U‖ := by rw [hn, intervalIntegral.integral_const, sub_zero, smul_eq_mul]; field_simp

theorem average_lipschitz (ε : ℝ) (hε : 0 < ε) :
    LipschitzWith 1 (fun U : TimeLp (R := R) => average U ε) := by
  apply LipschitzWith.of_dist_le_mul
  intro U V
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  rw [← average_sub]
  exact average_norm_le (U - V) ε hε

/-- The pointwise moving past average, independently of L² representatives. -/
def pastMean (u : ℝ → R) (ε t : ℝ) : R := ε⁻¹ • ∫ r in t - ε..t, u r

/-- Locally integrable coefficients have continuous moving past averages;
no pointwise continuity of the original curve is required. -/
theorem pastMean_continuous (u : ℝ → R) (hu : LocallyIntegrable u (volume : Measure ℝ)) (ε : ℝ) :
    Continuous (pastMean u ε) := by
  have hi (a b : ℝ) : IntervalIntegrable u volume a b :=
    intervalIntegrable_iff.mpr ((hu.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)
  have hp : Continuous (fun t => ∫ r in 0..t, u r) := intervalIntegral.continuous_primitive hi 0
  have he : pastMean u ε = fun t => ε⁻¹ • ((∫ r in 0..t, u r) - ∫ r in 0..t - ε, u r) := by
    funext t
    rw [intervalIntegral.integral_interval_sub_left (hi 0 t) (hi 0 (t - ε))]
    rfl
  rw [he]
  exact (hp.sub (hp.comp (continuous_id.sub continuous_const))).const_smul _

end PBGSO.PastAverages
