import PBGSO.RawReferenceCloudData
import PBGSO.RawEmpiricalDynamics
import PBGSO.RawOptimizerField
import PBGSO.RawDeterministicODE
import PBGSO.RawPairDynamics

/-! # Actual original empirical solution paired with independent reference copies
The full independent Brownian driver and reference trajectories are built
from independent whole seeds. Literal original strong equations construct the
actual pair. Its physical coefficients and iid reference law are proved.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.RawConstructedParticleCopy
open FilteredBrownian ConstructedItoParticle RawDampedState
variable {Ω S Θ Z X I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace Θ] [BorelSpace Θ] [SecondCountableTopology Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)
  (M : Model S Θ Z X I) (N : ℕ) {T : ℝ≥0}
  (U : RawLocalStationarity.Data Q D M T)

/-- Only the observation window is relevant. This literal extension derives
probability normalization without measurability assumptions outside it. -/
def referenceLaw (r : ℝ) : Measure Z := Q.map (U.sampler.state (timeClamp T r))

instance referenceLaw_probability (r : ℝ) : IsProbabilityMeasure (referenceLaw Q D M U r) :=
  (Measure.isProbabilityMeasure_map_iff (U.sampler.measurable _ (timeClamp_mem T r)).aemeasurable).mpr inferInstance

theorem referenceLaw_eq (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) :
    referenceLaw Q D M U r = Q.map (U.sampler.state r) := by
  unfold referenceLaw
  rw [timeClamp_eq T hr]

/-- Every output compatibility is proved for the original native solution
and the explicitly independently seeded reference cloud. -/
structure Construction (Y : RawEmpiricalDynamics.Solution M N
    (IndependentCopies.seeds (J := Fin N) Q) (RawIndependentCopies.driver Q D N) T) where
  localDiffusion : RawLocalDiffusion (Z := PairHilbert N S Z)
    (IndependentCopies.seeds (J := Fin N) Q)
    (nullAugmentedDriver (IndependentCopies.seeds (J := Fin N) Q) (RawIndependentCopies.driver Q D N)) T
  data : RawParticleInteraction.Data M (referenceLaw Q D M U) localDiffusion
  interacting_state : ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q, ∀ r ∈ Icc 0 (T : ℝ),
    (pairEquiv N (data.state r ω)).1 = oneEquiv N (Y.state r ω)
  reference_state : ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q, ∀ r ∈ Icc 0 (T : ℝ),
    (pairEquiv N (data.state r ω)).2 = (U.optimizer r,RawIndependentCopies.cloud Q D N U r ω)

/-- Actual paired original dynamics. This consumes an original interacting
strong solution; it does not infer interacting existence from mean-field A1.
All paired coefficients and reference laws follow from the construction. -/
def build (Y : RawEmpiricalDynamics.Solution M N
    (IndependentCopies.seeds (J := Fin N) Q) (RawIndependentCopies.driver Q D N) T)
    (hF : Measurable (fun p : S × Z => M.observation (M.parameter p.1) (M.position p.2)))
    (hb : Measurable (fun p : S × Z => M.drift (M.parameter p.1) p.2))
    (hΨ : Measurable (fun p : ℝ × (S × Θ) => M.optimizer p.1 p.2.1 p.2.2)) :
    Construction Q D M N U Y := Classical.choice <| by
  let H := RawEmpiricalDynamics.build M N Y hF hb hΨ
  let C := RawReferenceCloudData.build Q D M N U hb
  obtain ⟨j,hj,hji,hjE⟩ := RawOptimizerField.exists_field U hF hΨ
  let a : ℝ → S := fun r => U.optimizer (timeClamp T r)
  have haC : Continuous a := (RawSamplerGrowth.optimizer_continuous U).comp_continuous
    (by unfold timeClamp; fun_prop : Continuous (timeClamp T)) (timeClamp_mem T)
  have haE (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) : a r = U.optimizer r := by
    dsimp only [a]
    rw [timeClamp_eq T hr]
  have haODE : ∀ r ∈ Icc 0 (T : ℝ), a r = a 0+∫ t in 0..r,j t := by
    intro r hr
    rw [haE r hr,haE 0 ⟨le_rfl,T.coe_nonneg⟩,U.optimizer_equation r hr]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hr.1] at ht
    exact (hjE t ⟨ht.1,ht.2.trans hr.2⟩).symm
  let KL := RawDeterministicODE.coefficient C.localDiffusion j hj hji
  let A := RawDeterministicODE.data C.localDiffusion a j haC hj hji haODE
  let RL := RawPairDynamics.coefficient KL C.localDiffusion
  let R := RawPairDynamics.pair KL C.localDiffusion A C.data
  let PL := RawPairDynamics.coefficient H.localDiffusion RL
  let P := RawPairDynamics.pair H.localDiffusion RL H.data R
  have hDrift : ∀ r ∈ Icc 0 (T : ℝ), ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q,
      pairEquiv N (P.drift r ω) =
        particleCopyDrift M N (referenceLaw Q D M U r) r (pairEquiv N (P.state r ω)) := by
    intro r hr
    filter_upwards [H.drift_realizes,C.drift_realizes] with ω hh hc
    apply Prod.ext
    · change oneEquiv N (H.data.drift r ω) = _
      rw [hh r hr]
      exact RawEmpiricalDynamics.drift_coordinates M N r (H.data.state r ω)
    · apply Prod.ext
      · change j r = M.optimizerField r (a r) (referenceLaw Q D M U r)
        rw [haE r hr,referenceLaw_eq Q D M U r hr]
        exact hjE r hr
      · change (fun i => C.data.drift r ω i) =
          (fun i => M.drift (M.parameter (a r)) (C.data.state r ω i))
        rw [hc r hr,haE r hr]
        rfl
  have hSigma : ∀ r ∈ Icc 0 (T : ℝ), ∀ ij : Fin N × I,
      ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q,
      pairEquiv N (PL.sigma ij r ω) =
        particleCopyDiffusion M N (pairEquiv N (P.state r ω)) ij := by
    intro r hr ij
    filter_upwards [H.sigma_realizes,C.sigma_realizes] with ω hh hc
    apply Prod.ext
    · change oneEquiv N (H.localDiffusion.sigma ij r ω) = _
      rw [hh r hr ij]
      exact RawEmpiricalDynamics.sigma_coordinates M N ij (H.data.state r ω)
    · apply Prod.ext
      · rfl
      · change (fun i => C.localDiffusion.sigma ij r ω i) =
          (fun k => if k = ij.1 then M.diffusion (M.parameter (a r)) (C.data.state r ω k) ij.2 else 0)
        rw [hc r hr ij,haE r hr]
        funext k
        by_cases h : k = ij.1
        · subst k
          simp [RawReferenceCloudData.cloudModel,RawReferenceCloud.single_apply]
        · simp [RawReferenceCloudData.cloudModel,RawReferenceCloud.single_apply,h,Ne.symm h]
  let V : RawParticleInteraction.Data M (referenceLaw Q D M U)
      PL := {
    toData := P
    drift_realizes := hDrift
    sigma_realizes := hSigma }
  have hNative : ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q, ∀ r ∈ Icc 0 (T : ℝ),
      (pairEquiv N (V.state r ω)).1 = oneEquiv N (Y.state r ω) := by
    filter_upwards [H.state_eq] with ω h r hr
    change oneEquiv N (H.data.state r ω) = _
    rw [h r hr]
  have hReference : ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q, ∀ r ∈ Icc 0 (T : ℝ),
      (pairEquiv N (V.state r ω)).2 = (U.optimizer r,RawIndependentCopies.cloud Q D N U r ω) := by
    filter_upwards [C.state_eq] with ω h r hr
    change (a r,fun i => C.data.state r ω i) = _
    rw [haE r hr,h r hr]
    rfl
  exact ⟨⟨_,V,hNative,hReference⟩⟩

end PBGSO.RawConstructedParticleCopy
