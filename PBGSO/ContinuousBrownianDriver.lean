import PBGSO.AdaptedBrownianModification
import PBGSO.FilteredBrownian

/-! # Continuous modifications of actual filtered Brownian drivers
The coordinates are explicit adapted past-series modifications. Every finite
increment law, spatial independence and future-past independence is preserved
by proved fixed-time almost-everywhere identities. The original filtration is
retained; original raw path continuity is never asserted.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace PBGSO.FilteredBrownian
variable {Ω I : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

/-- The explicit continuous coordinate modification is the same random
variable at every deterministic time. -/
theorem continuous_process_ae (i : I) (t : ℝ≥0) :
    AdaptedBrownianModification.process (D.process i) t =ᵐ[Q] D.process i t :=
  AdaptedBrownianModification.process_ae Q (D.process i) (D.brownian i) t

private theorem modified_increment_ae (s t : ℝ≥0) (i : I) :
    (fun ω => AdaptedBrownianModification.process (D.process i) t ω -
      AdaptedBrownianModification.process (D.process i) s ω) =ᵐ[Q]
      (fun ω => D.process i t ω - D.process i s ω) :=
  (continuous_process_ae Q D i t).sub (continuous_process_ae Q D i s)

private theorem modified_future_independent (s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap
      (fun ω i => AdaptedBrownianModification.process (D.process i) t ω -
        AdaptedBrownianModification.process (D.process i) s ω) inferInstance)
      (D.filtration s) Q := by
  let old : Ω → I → ℝ := fun ω i => D.process i t ω - D.process i s ω
  let new : Ω → I → ℝ := fun ω i =>
    AdaptedBrownianModification.process (D.process i) t ω -
      AdaptedBrownianModification.process (D.process i) s ω
  have heq : old =ᵐ[Q] new := by
    filter_upwards [ae_all_iff.mpr (fun i => modified_increment_ae Q D s t i)] with ω hω
    funext i
    exact (hω i).symm
  have hi : @IndepFun Ω (I → ℝ) Ω mΩ inferInstance (D.filtration s) old id Q := by
    simpa only [IndepFun, Kernel.IndepFun, Indep, MeasurableSpace.comap_id] using D.future_independent s t hst
  have hj := hi.congr heq (Filter.EventuallyEq.rfl : (id : Ω → Ω) =ᵐ[Q] id)
  simpa only [IndepFun, Kernel.IndepFun, Indep, MeasurableSpace.comap_id] using hj

/-- An actual valid Brownian driver with continuous coordinate paths, adapted
to exactly the original filtration. Its independence properties are derived. -/
def continuousDriver : Driver (I := I) Q where
  process i := AdaptedBrownianModification.process (D.process i)
  brownian i := (AdaptedBrownianModification.isBrownianReal Q (D.process i)
    (D.brownian i)).toIsPreBrownianReal
  filtration := D.filtration
  adapted i := AdaptedBrownianModification.process_stronglyAdapted
    D.filtration (D.process i) (D.adapted i)
  increment_coordinates s t hst :=
    (D.increment_coordinates s t hst).congr
      (fun i => (modified_increment_ae Q D s t i).symm)
  future_independent := modified_future_independent Q D

@[simp] theorem continuousDriver_filtration (t : ℝ≥0) :
    (continuousDriver Q D).filtration t = D.filtration t := rfl

theorem continuousDriver_process_ae (i : I) (t : ℝ≥0) :
    (continuousDriver Q D).process i t =ᵐ[Q] D.process i t :=
  continuous_process_ae Q D i t

theorem continuousDriver_brownian (i : I) :
    IsBrownianReal ((continuousDriver Q D).process i) Q :=
  AdaptedBrownianModification.isBrownianReal Q (D.process i) (D.brownian i)

theorem continuousDriver_continuous (i : I) :
    ∀ᵐ ω ∂Q, Continuous (fun t => (continuousDriver Q D).process i t ω) :=
  (continuousDriver_brownian Q D i).cont

/-- All finite coordinates have continuous paths on one probability-one event. -/
theorem continuousDriver_joint_continuous :
    ∀ᵐ ω ∂Q, ∀ i, Continuous (fun t => (continuousDriver Q D).process i t ω) :=
  ae_all_iff.mpr (continuousDriver_continuous Q D)

end PBGSO.FilteredBrownian
