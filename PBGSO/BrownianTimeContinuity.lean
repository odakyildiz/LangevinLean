import PBGSO.BrownianFourthMoment
import PBGSO.DyadicPastSamples
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace PBGSO.BrownianTimeContinuity
open BrownianFourthMoment
variable {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
  (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B Q)
include hB

/-- The original Gaussian increment law implies stochastic time continuity,
with no sample-path continuity premise. -/
theorem tendstoInMeasure_of_time_tendsto (τ : ℕ → ℝ≥0) (t : ℝ≥0)
    (hτ : Tendsto τ atTop (𝓝 t)) :
    TendstoInMeasure Q (fun n => B (τ n)) atTop (B t) := by
  apply tendstoInMeasure_iff_measureReal_dist.mpr
  intro a ha
  have hd : Tendsto (fun n => dist (τ n : ℝ) (t : ℝ)) atTop (𝓝 0) := by
    simpa only [dist_self, Function.comp_def] using
      (((NNReal.continuous_coe.tendsto t).comp hτ).dist (tendsto_const_nhds (x := (t : ℝ))))
  have hz : Tendsto (fun n => fourthConstant * dist (τ n : ℝ) (t : ℝ) ^ 2 / a ^ 4)
      atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_div] using
      (tendsto_const_nhds.mul (hd.pow 2)).div_const (a ^ 4)
  apply squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_) hz
  simpa only [dist_eq_norm] using increment_tail_real Q B hB t (τ n) a ha

/-- Strict past dyadic samples retain the original value in probability. -/
theorem left_samples_tendstoInMeasure (t : ℝ) (ht : 0 ≤ t) :
    TendstoInMeasure Q
      (fun n => B (DyadicInterpolation.leftTime (2 ^ n) t).toNNReal)
      atTop (B t.toNNReal) := by
  apply tendstoInMeasure_of_time_tendsto Q B hB
  exact (continuous_real_toNNReal.tendsto t).comp
    (DyadicInterpolation.leftTime_dyadic_tendsto t ht)

/-- The same fixed-time law identification works on every scaled unit horizon. -/
theorem scaled_left_samples_tendstoInMeasure (T : ℝ≥0) (t : ℝ) (ht : 0 ≤ t) :
    TendstoInMeasure Q
      (fun n => B (T * (DyadicInterpolation.leftTime (2 ^ n) t).toNNReal))
      atTop (B (T * t.toNNReal)) := by
  apply tendstoInMeasure_of_time_tendsto Q B hB
  exact ((continuous_real_toNNReal.tendsto t).comp
    (DyadicInterpolation.leftTime_dyadic_tendsto t ht)).const_mul T

/-- Every actual almost-sure limit of the strict past samples is the same
original Brownian random variable at the specified time. -/
theorem scaled_left_limit_eq_ae (T : ℝ≥0) (t : ℝ) (ht : 0 ≤ t)
    (Z : Ω → ℝ)
    (hZ : ∀ᵐ ω ∂Q, Tendsto
      (fun n => B (T * (DyadicInterpolation.leftTime (2 ^ n) t).toNNReal) ω)
      atTop (𝓝 (Z ω))) : Z =ᵐ[Q] B (T * t.toNNReal) := by
  have hl := tendstoInMeasure_of_tendsto_ae
    (fun n => (hB.aemeasurable _).aestronglyMeasurable) hZ
  exact tendstoInMeasure_ae_unique hl (scaled_left_samples_tendstoInMeasure Q B hB T t ht)
end PBGSO.BrownianTimeContinuity
