import PBGSO.RawDampedState
import PBGSO.RawLocalLinearMap

/-! # Deterministic optimizer ODEs in actual local raw dynamics
The optimizer has literal zero physical Brownian columns. Zero stochastic
noise is proved by bounded-linear-map naturality of the actual local integral.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.RawDeterministicODE
open FilteredBrownian
variable {Ω I Z S : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  {Q : Measure Ω} [IsProbabilityMeasure Q] {D : Driver (I := I) Q} {T : ℝ≥0}

def coefficient (L : RawLocalDiffusion (Z := Z) Q D T) (j : ℝ → S)
    (hj : StronglyMeasurable j) (hi : IntervalIntegrable j volume 0 (T : ℝ)) :
    RawLocalDiffusion (Z := S) Q D T where
  sigma _ _ _ := 0
  sigma_strong _ := stronglyMeasurable_const
  sigma_adapted _ _ := stronglyMeasurable_const.aestronglyMeasurable
  q r ω := L.q r ω+‖j r‖
  q_strong := L.q_strong.add (hj.norm.comp_measurable measurable_fst)
  q_nonneg r ω := add_nonneg (L.q_nonneg r ω) (norm_nonneg _)
  q_local ω := (L.q_local ω).add
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mp hi).norm)
  q_progressive t := by
    have hqj : StronglyMeasurable[(inferInstance : MeasurableSpace ℝ).prod (D.filtration t)]
        (fun p : ℝ × Ω => (Ioc 0 (t : ℝ)).indicator (fun r => ‖j r‖) p.1) :=
      (hj.norm.indicator measurableSet_Ioc).comp_measurable measurable_fst
    convert (L.q_progressive t).add hqj using 1
    funext p
    by_cases h : p.1 ∈ Ioc 0 (t : ℝ) <;> simp [h]
  sigma_control r ω := by simp; exact add_nonneg (L.q_nonneg r ω) (norm_nonneg _)

/-- The literal deterministic optimizer equation has an actual full raw
realization with zero noise, regardless of the primitive sampler noise. -/
def data (L : RawLocalDiffusion (Z := Z) Q D T) (a j : ℝ → S)
    (ha : Continuous a) (hj : StronglyMeasurable j)
    (hi : IntervalIntegrable j volume 0 (T : ℝ))
    (he : ∀ t ∈ Icc 0 (T : ℝ), a t = a 0+∫ r in 0..t,j r) :
    RawDampedState.Data (coefficient L j hj hi) where
  state r _ := a r
  drift r _ := j r
  state_strong := ha.stronglyMeasurable.comp_measurable measurable_fst
  drift_strong := hj.comp_measurable measurable_fst
  drift_control r ω := le_add_of_nonneg_left (L.q_nonneg r ω)
  initial_square := memLp_const _
  state_adapted _ := stronglyMeasurable_const.aestronglyMeasurable
  state_continuous := Eventually.of_forall (fun _ => ha.continuousOn)
  equation := by
    have hn := L.localNoise_linearMap_congr (0 : Z →L[ℝ] S) (coefficient L j hj hi)
      (Eventually.of_forall (fun _ _ _ _ => rfl))
    filter_upwards [hn] with ω hn t ht
    rw [hn t.toNNReal ((Real.toNNReal_le_iff_le_coe).mpr ht.2)]
    simpa only [ContinuousLinearMap.zero_apply,add_zero] using he t ht

end PBGSO.RawDeterministicODE
