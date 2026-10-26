import PBGSO.RawDriftGauge
import PBGSO.RawSamplerGrowthLaw
import PBGSO.RawProgressiveWindow
import PBGSO.NaturalPastTransport
import PBGSO.ContinuousProcessRepresentative

/-! # Natural original sampler equations yield actual controlled raw dynamics
A continuous joint representative, the proved null augmentation, and primitive
Borel drift supply progressivity and a genuine variation gauge. No growth,
global expected drift moment, or energy inequality is assumed.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.RawNaturalSampler
open FilteredBrownian RawDampedState
variable {Ω S Θ Z X I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {D : Driver (I := I) Q} {M : Model S Θ Z X I} {T : ℝ≥0} {a : ℝ → S}

/-- Actual original sampler realization. All whole-horizon identities are
conclusions on one event, rather than stochastic or coefficient premises. -/
structure Realization (U : RawLocalStationarity.SamplerData Q D M T a) where
  localDiffusion : RawLocalDiffusion (Z := Z) Q (nullAugmentedDriver Q D) T
  data : RawDampedState.Data localDiffusion
  continuous_all : ∀ ω, Continuous (fun r => data.state r ω)
  state_eq : ∀ᵐ ω ∂Q, ∀ r ∈ Icc 0 (T : ℝ), data.state r ω = U.state r ω
  drift_realizes : ∀ᵐ ω ∂Q, ∀ r ∈ Icc 0 (T : ℝ),
    data.drift r ω = M.drift (M.parameter (a r)) (data.state r ω)
  sigma_realizes : ∀ᵐ ω ∂Q, ∀ r ∈ Icc 0 (T : ℝ), ∀ i,
    localDiffusion.sigma i r ω = M.diffusion (M.parameter (a r)) (data.state r ω) i
  noise_eq : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T →
    localDiffusion.localNoise t ω = U.localDiffusion.localNoise t ω

/-- The original locally integrated sampler equation has a controlled raw
realization with its exact physical drift and diffusion. Primitive pathwise
integrability is retained; no coefficient growth or expected variation is
needed. The initial spatial L² requirement is the original initial moment. -/
def build (U : RawLocalStationarity.SamplerData Q D M T a)
    (ha : ContinuousOn a (Icc 0 (T : ℝ)))
    (h0 : MemLp (U.state 0) 2 Q)
    (hDrift : Measurable (fun p : S × Z => M.drift (M.parameter p.1) p.2)) : Realization U :=
  Classical.choice <| by
  let a' : ℝ → S := fun r => a (timeClamp T r)
  have haC : Continuous a' := ha.comp_continuous
    (by unfold timeClamp; fun_prop : Continuous (timeClamp T)) (timeClamp_mem T)
  have haE (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) : a' r = a r := by
    dsimp only [a']
    rw [timeClamp_eq T hr]
  have hxMeas (r : ℝ) : Measurable (U.state (timeClamp T r)) := U.measurable _ (timeClamp_mem T r)
  have hxCont : ∀ᵐ ω ∂Q, Continuous (fun r => U.state (timeClamp T r) ω) := by
    filter_upwards [U.continuous_paths] with ω h
    exact h.comp_continuous (by unfold timeClamp; fun_prop : Continuous (timeClamp T)) (timeClamp_mem T)
  obtain ⟨g,hgJoint,hgC,hgAE⟩ := ContinuousProcessRepresentative.exists_joint_of_measurable Q
    (fun r ω => U.state (timeClamp T r) ω) hxMeas hxCont
  have hgE : ∀ᵐ ω ∂Q, ∀ r ∈ Icc 0 (T : ℝ), g r ω = U.state r ω := by
    filter_upwards [hgAE] with ω h r hr
    simpa only [timeClamp_eq T hr] using h r
  let b : ℝ → Ω → Z := fun r ω => M.drift (M.parameter (a' r)) (g r ω)
  have hb : StronglyMeasurable (Function.uncurry b) :=
    (hDrift.comp ((haC.measurable.comp measurable_fst).prodMk hgJoint.measurable)).stronglyMeasurable
  have hA (t : ℝ≥0) : AEStronglyMeasurable[D.filtration t] (g t) Q := by
    let c : ℝ≥0 := (timeClamp T t).toNNReal
    have hcR : (c : ℝ) = timeClamp T t := Real.coe_toNNReal _ (timeClamp_mem T t).1
    have hct : c ≤ t := by
      rw [← NNReal.coe_le_coe,hcR]
      exact max_le t.coe_nonneg (min_le_left _ _)
    have hX : AEStronglyMeasurable[D.filtration t] (U.state (timeClamp T t)) Q := by
      simpa only [hcR] using (U.adapted c).mono (D.filtration.mono hct)
    exact hX.congr (hgAE.mono (fun _ h => (h t).symm))
  have hbi : ∀ᵐ ω ∂Q, IntervalIntegrable (fun r => b r ω) volume 0 (T : ℝ) := by
    filter_upwards [U.drift_integrable,hgE] with ω hi hg
    apply (intervalIntegrable_congr (g := fun r => M.drift (M.parameter (a r)) (U.state r ω)) ?_).mpr hi
    intro r hr
    rw [uIoc_of_le T.coe_nonneg] at hr
    dsimp only [b]
    rw [haE r (Ioc_subset_Icc_self hr),hg r (Ioc_subset_Icc_self hr)]
  have hbp : ∀ t : ℝ≥0,
      StronglyMeasurable[(inferInstance : MeasurableSpace ℝ).prod
        ((nullAugmentedDriver Q D).filtration t)]
        (fun p : ℝ × Ω => (Ioc 0 (t : ℝ)).indicator (fun r => ‖b r p.2‖) p.1) := by
    let E := nullAugmentedDriver Q D
    let u : ℝ≥0 → Ω → S × Z := fun t ω => (a' t,g t ω)
    have hu : StronglyAdapted E.filtration u := by
      intro t
      have hg : StronglyMeasurable[E.filtration t] (g t) :=
        (measurable_nullAugmentation_of_aestrong Q (D.filtration t)
          hgJoint.of_uncurry_left.measurable (hA t)).stronglyMeasurable
      exact stronglyMeasurable_const.prodMk hg
    have hc : ∀ ω, Continuous (fun t : ℝ≥0 => u t ω) := fun ω =>
      (haC.comp NNReal.continuous_coe).prodMk ((hgC ω).comp NNReal.continuous_coe)
    intro t
    have hw := RawProgressiveWindow.continuous_adapted_coefficient_window E.filtration u hu hc
      (fun p : S × Z => ‖M.drift (M.parameter p.1) p.2‖) hDrift.norm t
    convert hw using 1
    funext p
    by_cases hp : p.1 ∈ Ioc 0 (t : ℝ)
    · simp only [Set.indicator_of_mem hp,RawProgressiveWindow.realExtension,u,b,
        Real.coe_toNNReal _ hp.1.le]
    · simp only [Set.indicator_of_notMem hp]
  have heq : ∀ᵐ ω ∂Q, ∀ t ∈ Icc 0 (T : ℝ),
      g t ω = g 0 ω+(∫ r in 0..t,b r ω)+U.localDiffusion.localNoise t.toNNReal ω := by
    filter_upwards [U.equation,hgE] with ω he hg t ht
    rw [hg t ht,hg 0 ⟨le_rfl,T.coe_nonneg⟩,he t ht]
    congr 2
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le ht.1] at hr
    dsimp only [b]
    rw [haE r ⟨hr.1,hr.2.trans ht.2⟩,hg r ⟨hr.1,hr.2.trans ht.2⟩]
  have hG0 : MemLp (g 0) 2 Q :=
    (memLp_congr_ae (hgE.mono (fun _ h => h 0 ⟨le_rfl,T.coe_nonneg⟩))).mpr h0
  obtain ⟨K,R,hrState,hrDrift,hrSigma,hrNoise⟩ := RawDriftGauge.exists_data U.localDiffusion g b hgJoint hb
    hG0 hA (Eventually.of_forall (fun ω => (hgC ω).continuousOn)) hbi hbp heq
  have hstate : ∀ᵐ ω ∂Q, ∀ r ∈ Icc 0 (T : ℝ), R.state r ω = U.state r ω := by
    simpa only [hrState] using hgE
  refine ⟨⟨K,R,?_,hstate,?_,?_,hrNoise⟩⟩
  · simpa only [hrState] using hgC
  · filter_upwards [hrDrift] with ω h r hr
    rw [h r,hrState]
    dsimp only [b]
    rw [haE r hr]
  · filter_upwards [hrSigma,U.diffusion_realizes,hstate] with ω hK hU hR r hr i
    rw [hK i r,hU r hr i,hR r hr]

end PBGSO.RawNaturalSampler

namespace PBGSO.RawNaturalSampler
open FilteredBrownian
variable {Ω S Θ Z X I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {D : Driver (I := I) Q} {M : Model S Θ Z X I} {T : ℝ≥0}

/-- A natural complete model solution discharges optimizer continuity and
initial L² internally from its original ODE and probability-domain data. -/
def build_model (U : RawLocalStationarity.Data Q D M T)
    (hDrift : Measurable (fun p : S × Z => M.drift (M.parameter p.1) p.2)) :
    Realization U.sampler :=
  build U.sampler (RawSamplerGrowth.optimizer_continuous U)
    (RawSamplerGrowth.sampler_memLp D U 0 ⟨le_rfl,T.coe_nonneg⟩) hDrift

end PBGSO.RawNaturalSampler
