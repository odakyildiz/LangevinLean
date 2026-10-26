import PBGSO.DyadicPastLimit
import PBGSO.BrownianDyadicProbability
import PBGSO.BrownianTimeContinuity
import PBGSO.FilteredBrownian
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-! # Actual adapted continuous Brownian versions on each finite horizon
The candidate uses only strict-past dyadic samples, even on exceptional
paths. Gaussian laws prove its continuous paths and its original timewise law.
No continuous-modification or adapted-limit conclusion is a premise.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.AdaptedBrownianWindow
open DyadicInterpolation BrownianDyadicProbability
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

def sampleTime (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  T * (leftTime (2 ^ n) ((t : ℝ) / T)).toNNReal

def candidate (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ :=
  pastCandidate (scaled B T ω) ((t : ℝ) / T)

theorem sampleTime_le (T : ℝ≥0) (hT : 0 < T) (n : ℕ) (t : ℝ≥0) :
    sampleTime T n t ≤ t := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  apply NNReal.coe_le_coe.mp
  rw [sampleTime, NNReal.coe_mul, Real.coe_toNNReal _ (leftTime_nonneg _ _)]
  calc
    (T : ℝ) * leftTime (2 ^ n) ((t : ℝ) / T) ≤ T * ((t : ℝ) / T) :=
      mul_le_mul_of_nonneg_left (leftTime_le _ (by positivity) _ (by positivity)) T.coe_nonneg
    _ = t := by field_simp

/-- The raw candidate is genuinely adapted to the original past; no
completion of the filtration or supplied limiting adaptedness is used. -/
theorem candidate_stronglyAdapted (F : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0 → Ω → ℝ) (hB : StronglyAdapted F B) (T : ℝ≥0) (hT : 0 < T) :
    StronglyAdapted F (candidate B T) := by
  intro t
  letI : MeasurableSpace Ω := F t
  have hs (n : ℕ) : StronglyMeasurable (fun ω => pastSample n (scaled B T ω) ((t : ℝ) / T)) := by
    change StronglyMeasurable (B (sampleTime T n t))
    exact (hB (sampleTime T n t)).mono (F.mono (sampleTime_le T hT n t))
  exact (hs 0).add (StronglyMeasurable.tsum (fun n => (hs (n + 1)).sub (hs n)))

section Laws
variable (Q : Measure Ω) [IsProbabilityMeasure Q]
  (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B Q)
include hB

/-- Gaussian fourth moments supply the literal full-level grid bounds for
exactly the scaled curve appearing in the past-only candidate. -/
theorem ae_scaled_steps (T : ℝ≥0) :
    ∀ᵐ ω ∂Q, ∀ᶠ n in atTop, ∀ j < 2 ^ n,
      ‖scaled B T ω (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) -
        scaled B T ω ((j : ℝ) / (2 : ℝ) ^ n)‖ ≤ radius n := by
  filter_upwards [ae_eventual_grid_bound Q B hB T] with ω hω
  filter_upwards [hω] with n hn
  intro j hj
  have he1 := scaled_sample B T ω (2 ^ n) (j + 1)
  have he0 := scaled_sample B T ω (2 ^ n) j
  simp only [Nat.cast_pow, Nat.cast_ofNat] at he1 he0
  rw [he1, he0]
  exact hn j hj

/-- At every horizon time, the actual adapted candidate is the original
Brownian variable almost surely, proved from convergence in measure. -/
theorem candidate_ae (T : ℝ≥0) (hT : 0 < T) (t : ℝ≥0) (ht : t ≤ T) :
    candidate B T t =ᵐ[Q] B t := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hu : ((t : ℝ) / T) ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hTr).mpr (by exact_mod_cast ht)⟩
  have he := BrownianTimeContinuity.scaled_left_limit_eq_ae Q B hB T ((t : ℝ) / T)
    hu.1 (candidate B T t) (by
      filter_upwards [ae_scaled_steps Q B hB T] with ω hω
      exact pastSample_tendsto_candidate (scaled B T ω) radius
        (fun n => (radius_pos n).le) radius_summable hω _ hu)
  have hs : T * ((t : ℝ) / T).toNNReal = t := by
    apply NNReal.eq
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hu.1]
    field_simp
  simpa only [hs] using he

/-- Actual simultaneous path continuity follows from the derived grid bounds
and deterministic polygon limits on the whole horizon. -/
theorem candidate_continuous_paths (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂Q, ContinuousOn (fun t => candidate B T t ω) (Iic T) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  filter_upwards [ae_scaled_steps Q B hB T] with ω hω
  have hc := pastCandidate_continuousOn (scaled B T ω) radius
    (fun n => (radius_pos n).le) radius_summable hω
  have hm : MapsTo (fun t : ℝ≥0 => (t : ℝ) / T) (Iic T) (Icc (0 : ℝ) 1) := by
    intro t ht
    exact ⟨by positivity, (div_le_one hTr).mpr (by exact_mod_cast ht)⟩
  exact hc.comp ((NNReal.continuous_coe.div_const (T : ℝ)).continuousOn) hm
end Laws
end PBGSO.AdaptedBrownianWindow
