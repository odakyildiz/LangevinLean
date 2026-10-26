import PBGSO.RawSamplerGrowth
import PBGSO.ContinuousProcessRepresentative
import PBGSO.RawDampedState

/-! # Measurable original optimizer fields from primitive Borel coefficients
A continuous joint representative of the original sampler proves actual
population observation measurability. No diffusion constancy, coefficient
growth, global sampler-drift moment, or supplied field measurability is used.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.RawOptimizerField
open FilteredBrownian RawDampedState
variable {Ω S Θ Z X I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace Θ] [BorelSpace Θ] [SecondCountableTopology Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {D : Driver (I := I) Q} {M : Model S Θ Z X I} {T : ℝ≥0}

/-- The actual original optimizer field has a globally strongly measurable
extension retaining every horizon value and its original ordinary integral. -/
theorem exists_field (U : RawLocalStationarity.Data Q D M T)
    (hObs : Measurable (fun p : S × Z => M.observation (M.parameter p.1) (M.position p.2)))
    (hOptimizer : Measurable (fun p : ℝ × (S × Θ) => M.optimizer p.1 p.2.1 p.2.2)) :
    ∃ j : ℝ → S, StronglyMeasurable j ∧ IntervalIntegrable j volume 0 (T : ℝ) ∧
      ∀ r ∈ Icc 0 (T : ℝ), j r = M.optimizerField r (U.optimizer r) (Q.map (U.sampler.state r)) := by
  let a : ℝ → S := fun r => U.optimizer (timeClamp T r)
  have haC : Continuous a := (RawSamplerGrowth.optimizer_continuous U).comp_continuous
    (by unfold timeClamp; fun_prop : Continuous (timeClamp T)) (timeClamp_mem T)
  have ha (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) : a r = U.optimizer r := by
    dsimp only [a]
    rw [timeClamp_eq T hr]
  have hxMeas (r : ℝ) : Measurable (U.sampler.state (timeClamp T r)) :=
    U.sampler.measurable _ (timeClamp_mem T r)
  have hxCont : ∀ᵐ ω ∂Q, Continuous (fun r => U.sampler.state (timeClamp T r) ω) := by
    filter_upwards [U.sampler.continuous_paths] with ω h
    exact h.comp_continuous (by unfold timeClamp; fun_prop : Continuous (timeClamp T)) (timeClamp_mem T)
  obtain ⟨x,hxJoint,hxC,hxAE⟩ := ContinuousProcessRepresentative.exists_joint_of_measurable Q
    (fun r ω => U.sampler.state (timeClamp T r) ω) hxMeas hxCont
  have hx : ∀ᵐ ω ∂Q, ∀ r ∈ Icc 0 (T : ℝ), x r ω = U.sampler.state r ω := by
    filter_upwards [hxAE] with ω h r hr
    simpa only [timeClamp_eq T hr] using h r
  have hxLaw (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) : Q.map (x r) = Q.map (U.sampler.state r) :=
    Measure.map_congr (hx.mono (fun _ h => h r hr))
  let j : ℝ → S := fun r => M.optimizerField r (a r) (Q.map (x r))
  have hjEq (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) :
      j r = M.optimizerField r (U.optimizer r) (Q.map (U.sampler.state r)) := by
    dsimp only [j]
    rw [ha r hr,hxLaw r hr]
  have hObsJoint : StronglyMeasurable (fun p : ℝ × Ω =>
      M.observation (M.parameter (a p.1)) (M.position (x p.1 p.2))) :=
    (hObs.comp ((haC.measurable.comp measurable_fst).prodMk hxJoint.measurable)).stronglyMeasurable
  have hjStrong : StronglyMeasurable j := by
    have hm := hObsJoint.integral_prod_right' (ν := Q)
    have hψ : StronglyMeasurable (fun r => M.optimizer r (a r)
        (∫ ω, M.observation (M.parameter (a r)) (M.position (x r ω)) ∂Q)) :=
      (hOptimizer.comp (measurable_id.prodMk (haC.measurable.prodMk hm.measurable))).stronglyMeasurable
    convert hψ using 1
    funext r
    dsimp only [j,Model.optimizerField,Model.meanGradient]
    have hxr : Measurable (x r) := hxJoint.of_uncurry_left.measurable
    have hor : Measurable (fun z : Z => M.observation (M.parameter (a r)) (M.position z)) :=
      hObs.comp (measurable_const.prodMk measurable_id)
    congr 1
    exact integral_map hxr.aemeasurable hor.stronglyMeasurable.aestronglyMeasurable
  refine ⟨j,hjStrong,?_,hjEq⟩
  apply (intervalIntegrable_congr (g := fun r =>
    M.optimizerField r (U.optimizer r) (Q.map (U.sampler.state r))) ?_).mpr U.optimizer_field_integrable
  intro r hr
  rw [uIoc_of_le T.coe_nonneg] at hr
  exact hjEq r (Ioc_subset_Icc_self hr)

end PBGSO.RawOptimizerField
