import PBGSO.PositiveWorkFubini
import PBGSO.ConstantNoiseWork
import PBGSO.IntegralModelContraction
import PBGSO.RawLocalNoiseCongruence

/-! # Raw constant-diffusion contraction from positive work
The original sampler drift need only be pathwise L¹. Constant diffusion
cancels on the actual common Brownian realization. Positive-work
integrability supplies the Fubini step needed to apply the source's original
full-law joint monotonicity. That extra one-sided integrability condition
is explicit; minimal source A1(i) is not asserted to imply it.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators RealInnerProductSpace InnerProductSpace
namespace PBGSO.RawConstantNoiseContraction
variable {Ω S Θ Z X I : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype I]

/-- Literal diagonal twisted bilinear form on a raw optimizer/sampler pair. -/
def rawMetricBilinear (D : TwistedGeometry S Z) :
    (S × Z) →L[ℝ] (S × Z) →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (ContinuousLinearMap.fst ℝ S Z)
    (D.optimizerWeight.comp (ContinuousLinearMap.fst ℝ S Z)) +
  (innerSL ℝ).bilinearComp (ContinuousLinearMap.snd ℝ S Z)
    (D.samplerWeight.comp (ContinuousLinearMap.snd ℝ S Z))

@[simp] theorem rawMetricBilinear_apply (D : TwistedGeometry S Z) (x y : S × Z) :
    rawMetricBilinear D x y = ⟪x.1,D.optimizerWeight y.1⟫_ℝ +
      ⟪x.2,D.samplerWeight y.2⟫_ℝ := rfl

theorem rawMetricBilinear_symmetric (D : TwistedGeometry S Z) (x y : S × Z) :
    rawMetricBilinear D x y = rawMetricBilinear D y x := by
  simp only [rawMetricBilinear_apply]
  congr 1
  · exact (D.optimizer_symmetric _ _).trans (real_inner_comm _ _)
  · exact (D.sampler_symmetric _ _).trans (real_inner_comm _ _)

theorem rawMetricBilinear_nonneg (D : TwistedGeometry S Z) (x : S × Z) :
    0 ≤ rawMetricBilinear D x x :=
  add_nonneg (D.optimizerSq_nonneg x.1) (D.samplerSq_nonneg x.2)

variable (Q : Measure Ω) [IsProbabilityMeasure Q]
  (M : Model S Θ Z X I) (D : TwistedGeometry S Z)

/-- Constancy is required only at parameters reachable from optimizer
states, exactly as in the source constant-diffusion branch. -/
theorem sampler_work_eq_drift
    (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i)
    (s s' : S) (z w : Z) :
    samplerCouplingWork M D s s' (z,w) =
      ⟪z-w,D.samplerWeight (M.drift (M.parameter s) z-M.drift (M.parameter s') w)⟫_ℝ := by
  have hz : ∑ i, D.samplerSq (M.diffusion (M.parameter s) z i-
      M.diffusion (M.parameter s') w i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [hσ s s' z w i,sub_self]
    simp [TwistedGeometry.samplerSq]
  simp only [samplerCouplingWork,hz,mul_zero,add_zero]

/-- Actual full joint law transfers source A3 to raw original drift work.
The sampler drift itself need not belong to L². -/
theorem original_work_le (ρ : ℝ) (hmono : TwistedJointMonotonicity M D ρ)
    (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i)
    (hb : ∀ θ, Measurable (M.drift θ))
    (t : ℝ) (ht : 0 ≤ t) (s s' : S) (x y : Ω → Z)
    (hx : StronglyMeasurable x) (hy : StronglyMeasurable y)
    (hx2 : MemLp x 2 Q) (hy2 : MemLp y 2 Q)
    (hobs : Integrable (fun z => M.observation (M.parameter s) (M.position z)) (Q.map x))
    (hobs' : Integrable (fun z => M.observation (M.parameter s') (M.position z)) (Q.map y))
    (hw : Integrable (fun ω => ⟪x ω-y ω,
      D.samplerWeight (M.drift (M.parameter s) (x ω)-M.drift (M.parameter s') (y ω))⟫_ℝ) Q) :
    (∫ ω, ⟪s-s',D.optimizerWeight
      (M.optimizerField t s (Q.map x)-M.optimizerField t s' (Q.map y))⟫_ℝ +
      ⟪x ω-y ω,D.samplerWeight
        (M.drift (M.parameter s) (x ω)-M.drift (M.parameter s') (y ω))⟫_ℝ ∂Q) ≤
      -ρ * ∫ ω, D.optimizerSq (s-s') + D.samplerSq (x ω-y ω) ∂Q := by
  let Λ := Q.map (fun ω => (x ω,y ω))
  have hxy : Measurable (fun ω => (x ω,y ω)) := hx.measurable.prodMk hy.measurable
  have hc : IsCoupling Λ (Q.map x) (Q.map y) := by
    constructor
    · rw [show Λ = Q.map (fun ω => (x ω,y ω)) from rfl,
        Measure.map_map measurable_fst hxy]
      rfl
    · rw [show Λ = Q.map (fun ω => (x ω,y ω)) from rfl,
        Measure.map_map measurable_snd hxy]
      rfl
  have hp : IsProbabilityMeasure (Q.map x) :=
    (Measure.isProbabilityMeasure_map_iff hx.measurable.aemeasurable).mpr inferInstance
  have hp' : IsProbabilityMeasure (Q.map y) :=
    (Measure.isProbabilityMeasure_map_iff hy.measurable.aemeasurable).mpr inferInstance
  have hm : HasFiniteSecondMoment (Q.map x) := by
    apply (integrable_map_measure (by fun_prop) hx.measurable.aemeasurable).mpr
    exact (memLp_two_iff_integrable_sq_norm hx.aestronglyMeasurable).mp hx2
  have hm' : HasFiniteSecondMoment (Q.map y) := by
    apply (integrable_map_measure (by fun_prop) hy.measurable.aemeasurable).mpr
    exact (memLp_two_iff_integrable_sq_norm hy.aestronglyMeasurable).mp hy2
  have hcost : Integrable (fun ω => D.samplerSq (x ω-y ω)) Q := by
    have h := PBGSO.lp_weighted_pairing_integrable Q D.samplerWeight
      ((hx2.sub hy2).toLp (fun ω => x ω-y ω)) ((hx2.sub hy2).toLp (fun ω => x ω-y ω))
    exact h.congr (((hx2.sub hy2).coeFn_toLp.fun_comp
      (fun z => ⟪z,D.samplerWeight z⟫_ℝ)))
  have hcmeas : Continuous (fun zz : Z × Z => D.samplerSq (zz.1-zz.2)) := by
    dsimp [TwistedGeometry.samplerSq]
    fun_prop
  have hworkmeas : Measurable (samplerCouplingWork M D s s') := by
    have he : samplerCouplingWork M D s s' = fun zz =>
        ⟪zz.1-zz.2,D.samplerWeight
          (M.drift (M.parameter s) zz.1-M.drift (M.parameter s') zz.2)⟫_ℝ := by
      funext zz
      exact sampler_work_eq_drift M D hσ s s' zz.1 zz.2
    rw [he]
    exact (continuous_fst.inner continuous_snd).measurable.comp
      ((measurable_fst.sub measurable_snd).prodMk
      (D.samplerWeight.continuous.measurable.comp
        (((hb _).comp measurable_fst).sub ((hb _).comp measurable_snd))))
  have hwi : Integrable (samplerCouplingWork M D s s') Λ := by
    apply (integrable_map_measure hworkmeas.aestronglyMeasurable hxy.aemeasurable).mpr
    simpa only [Function.comp_def, sampler_work_eq_drift M D hσ] using hw
  have hci : Integrable (fun zz => D.samplerSq (zz.1-zz.2)) Λ :=
    (integrable_map_measure hcmeas.aestronglyMeasurable hxy.aemeasurable).mpr hcost
  have h := hmono t ht s s' (Q.map x) (Q.map y) Λ hc hp hp' hm hm' hobs hobs' hwi hci
  rw [show Λ = Q.map (fun ω => (x ω,y ω)) from rfl,
    integral_map hxy.aemeasurable hworkmeas.aestronglyMeasurable,
    integral_map hxy.aemeasurable hcmeas.aestronglyMeasurable] at h
  simp only [sampler_work_eq_drift M D hσ] at h
  rw [integral_add (integrable_const _) hw, integral_add (integrable_const _) hcost]
  simpa only [integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul] using h


section RawModel
variable [DecidableEq I]
  (W : FilteredBrownian.Driver (I := I) Q) (T : ℝ≥0)

/-- Original finite-horizon raw equations. The stochastic input is the
computed local Brownian integral of the original diffusion, rather than an
arbitrary common forcing. The drift has only samplewise time L¹ regularity.
Fixed-time P₂ and observation integrability are separate explicit inputs. -/
structure Data (L : FilteredBrownian.RawLocalDiffusion (Z := Z) Q W T) where
  optimizer : ℝ → S
  optimizerDrift : ℝ → S
  sampler : ℝ → Ω → Z
  optimizer_strong : StronglyMeasurable optimizer
  optimizerDrift_strong : StronglyMeasurable optimizerDrift
  sampler_strong : StronglyMeasurable (Function.uncurry sampler)
  drift_strong : StronglyMeasurable (fun p : ℝ × Ω =>
    M.drift (M.parameter (optimizer p.1)) (sampler p.1 p.2))
  optimizerDrift_integrable : IntervalIntegrable optimizerDrift volume 0 (T : ℝ)
  optimizerDrift_realizes : ∀ t ∈ Icc 0 (T : ℝ), optimizerDrift t =
    M.optimizerField t (optimizer t) (Q.map (sampler t))
  optimizer_equation : ∀ t ∈ Icc 0 (T : ℝ),
    optimizer t = optimizer 0 + ∫ r in 0..t, optimizerDrift r
  drift_integrable : ∀ᵐ ω ∂Q, IntervalIntegrable
    (fun r => M.drift (M.parameter (optimizer r)) (sampler r ω)) volume 0 (T : ℝ)
  sampler_equation : ∀ᵐ ω ∂Q, ∀ t ∈ Icc 0 (T : ℝ),
    sampler t ω = sampler 0 ω +
      (∫ r in 0..t, M.drift (M.parameter (optimizer r)) (sampler r ω)) +
        L.localNoise t.toNNReal ω
  diffusion_realizes : ∀ i r ω, L.sigma i r ω =
    M.diffusion (M.parameter (optimizer r)) (sampler r ω) i
  sampler_square : ∀ t ∈ Icc 0 (T : ℝ), MemLp (sampler t) 2 Q
  observation_integrable : ∀ t ∈ Icc 0 (T : ℝ), Integrable
    (fun z => M.observation (M.parameter (optimizer t)) (M.position z)) (Q.map (sampler t))

variable {W T} {L K : FilteredBrownian.RawLocalDiffusion (Z := Z) Q W T}

def pairState (U : Data Q M W T L) (V : Data Q M W T K) (r : ℝ) (ω : Ω) : S × Z :=
  (U.optimizer r-V.optimizer r,U.sampler r ω-V.sampler r ω)

def pairDrift (U : Data Q M W T L) (V : Data Q M W T K) (r : ℝ) (ω : Ω) : S × Z :=
  (U.optimizerDrift r-V.optimizerDrift r,
    M.drift (M.parameter (U.optimizer r)) (U.sampler r ω)-
      M.drift (M.parameter (V.optimizer r)) (V.sampler r ω))

theorem pairState_strong (U : Data Q M W T L) (V : Data Q M W T K) :
    StronglyMeasurable (Function.uncurry (pairState Q M U V)) :=
  ((U.optimizer_strong.sub V.optimizer_strong).comp_measurable measurable_fst).prodMk
    (U.sampler_strong.sub V.sampler_strong)

theorem pairDrift_strong (U : Data Q M W T L) (V : Data Q M W T K) :
    StronglyMeasurable (Function.uncurry (pairDrift Q M U V)) :=
  ((U.optimizerDrift_strong.sub V.optimizerDrift_strong).comp_measurable measurable_fst).prodMk
    (U.drift_strong.sub V.drift_strong)

/-- Literal cancellation and original integral equations derive the entire
raw pair primitive; no drift-work or quadratic equation is supplied. -/
theorem pair_path (U : Data Q M W T L) (V : Data Q M W T K)
    (hnoise : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → L.localNoise t ω = K.localNoise t ω) :
    ∀ᵐ ω ∂Q, ContinuousOn (fun r => pairState Q M U V r ω) (Icc 0 (T : ℝ)) ∧
      IntervalIntegrable (fun r => pairDrift Q M U V r ω) volume 0 (T : ℝ) ∧
      ∀ r ∈ Icc 0 (T : ℝ), pairState Q M U V r ω =
        pairState Q M U V 0 ω + ∫ s in 0..r, pairDrift Q M U V s ω := by
  filter_upwards [U.drift_integrable,V.drift_integrable,U.sampler_equation,V.sampler_equation,
    hnoise] with ω hu hv heu hev hn
  have hg := U.optimizerDrift_integrable.sub V.optimizerDrift_integrable
  have hb := hu.sub hv
  have hi : IntervalIntegrable (fun r => pairDrift Q M U V r ω) volume 0 (T : ℝ) :=
    ⟨hg.1.prodMk hb.1,hg.2.prodMk hb.2⟩
  have he (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) : pairState Q M U V r ω =
      pairState Q M U V 0 ω + ∫ s in 0..r, pairDrift Q M U V s ω := by
    have hsub : uIcc 0 r ⊆ uIcc 0 (T : ℝ) := by
      simpa only [uIcc_of_le hr.1,uIcc_of_le T.coe_nonneg] using
        (Icc_subset_Icc le_rfl hr.2 : Icc 0 r ⊆ Icc 0 (T : ℝ))
    have hit := hi.mono_set hsub
    apply Prod.ext
    · change U.optimizer r-V.optimizer r = U.optimizer 0-V.optimizer 0 +
        (∫ s in 0..r, pairDrift Q M U V s ω).1
      have hf := (ContinuousLinearMap.fst ℝ S Z).intervalIntegral_comp_comm hit
      change (∫ s in 0..r, (pairDrift Q M U V s ω).1) =
        (∫ s in 0..r, pairDrift Q M U V s ω).1 at hf
      rw [← hf]
      change U.optimizer r-V.optimizer r = U.optimizer 0-V.optimizer 0 +
        ∫ s in 0..r, U.optimizerDrift s-V.optimizerDrift s
      rw [intervalIntegral.integral_sub (U.optimizerDrift_integrable.mono_set hsub)
        (V.optimizerDrift_integrable.mono_set hsub),U.optimizer_equation r hr,V.optimizer_equation r hr]
      abel
    · change U.sampler r ω-V.sampler r ω = U.sampler 0 ω-V.sampler 0 ω +
        (∫ s in 0..r, pairDrift Q M U V s ω).2
      have hf := (ContinuousLinearMap.snd ℝ S Z).intervalIntegral_comp_comm hit
      change (∫ s in 0..r, (pairDrift Q M U V s ω).2) =
        (∫ s in 0..r, pairDrift Q M U V s ω).2 at hf
      rw [← hf]
      change U.sampler r ω-V.sampler r ω = U.sampler 0 ω-V.sampler 0 ω +
        ∫ s in 0..r, M.drift (M.parameter (U.optimizer s)) (U.sampler s ω)-
          M.drift (M.parameter (V.optimizer s)) (V.sampler s ω)
      rw [intervalIntegral.integral_sub (hu.mono_set hsub) (hv.mono_set hsub),heu r hr,hev r hr,
        hn r.toNNReal (by exact_mod_cast (Real.toNNReal_le_iff_le_coe).mpr hr.2)]
      abel
  refine ⟨?_,hi,he⟩
  have hc : ContinuousOn (fun r => pairState Q M U V 0 ω +
      ∫ s in 0..r, pairDrift Q M U V s ω) (uIcc 0 (T : ℝ)) :=
    continuousOn_const.add (intervalIntegral.continuousOn_primitive_interval' hi
      (show (0 : ℝ) ∈ uIcc 0 (T : ℝ) from left_mem_uIcc))
  rw [uIcc_of_le T.coe_nonneg] at hc
  exact hc.congr he

/-- Primitive constant diffusion implies actual global coefficient square
integrability even when the original sampler drift is superlinear. -/
theorem diffusion_square (U : Data Q M W T L)
    (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i) (i : I) :
    Integrable (fun p : ℝ × Ω => ‖L.sigma i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := by
  have he : (fun p : ℝ × Ω => ‖L.sigma i p.1 p.2‖ ^ 2) =
      fun _ => ‖M.diffusion (M.parameter (0 : S)) (0 : Z) i‖ ^ 2 := by
    funext p
    rw [U.diffusion_realizes]
    rw [hσ (U.optimizer p.1) 0 (U.sampler p.1 p.2) 0 i]
  rw [he]
  exact integrable_const _


/-- Two original constant-diffusion equations driven by the same actual
Brownian driver have identical computed local stochastic inputs, regardless
of the two local stopping gauges. -/
theorem noise_cancels (U : Data Q M W T L) (V : Data Q M W T K)
    (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i) :
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → L.localNoise t ω = K.localNoise t ω := by
  apply L.localNoise_congr_on_horizon K (diffusion_square Q M U hσ) (diffusion_square Q M V hσ)
  intro i
  exact Eventually.of_forall (fun p => by
    change L.sigma i p.1 p.2 = K.sigma i p.1 p.2
    rw [U.diffusion_realizes,V.diffusion_realizes]
    exact hσ _ _ _ _ i)

theorem pair_energy_integrable (U : Data Q M W T L) (V : Data Q M W T K)
    (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) :
    Integrable (fun ω => rawMetricBilinear D (pairState Q M U V r ω)
      (pairState Q M U V r ω)) Q := by
  have h2 := (U.sampler_square r hr).sub (V.sampler_square r hr)
  have hi := lp_weighted_pairing_integrable Q D.samplerWeight
    (h2.toLp (fun ω => U.sampler r ω-V.sampler r ω))
    (h2.toLp (fun ω => U.sampler r ω-V.sampler r ω))
  have hs : Integrable (fun ω => D.samplerSq (U.sampler r ω-V.sampler r ω)) Q :=
    hi.congr (h2.coeFn_toLp.fun_comp (fun z => ⟪z,D.samplerWeight z⟫_ℝ))
  change Integrable (fun ω => D.optimizerSq (U.optimizer r-V.optimizer r) +
    D.samplerSq (U.sampler r ω-V.sampler r ω)) Q
  exact (integrable_const _).add hs

/-- Actual original equations and source A3 give exponential mean quadratic
contraction under an explicit positive-work condition. The sampler drift
need not be globally L² or have square-integrable total variation. -/
theorem energy_decay (U : Data Q M W T L) (V : Data Q M W T K)
    (ρ : ℝ) (hmono : TwistedJointMonotonicity M D ρ)
    (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i)
    (hb : ∀ θ, Measurable (M.drift θ))
    (hp : Integrable (fun p : ℝ × Ω =>
      max (rawMetricBilinear D (pairState Q M U V p.1 p.2)
        (pairDrift Q M U V p.1 p.2)) 0)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) :
    (∫ ω, rawMetricBilinear D (pairState Q M U V T ω) (pairState Q M U V T ω) ∂Q) ≤
      Real.exp (-2 * ρ * (T : ℝ)) *
        ∫ ω, rawMetricBilinear D (pairState Q M U V 0 ω) (pairState Q M U V 0 ω) ∂Q := by
  have hpath := pair_path Q M U V (noise_cancels Q M U V hσ)
  have hz := pair_energy_integrable Q M D U V 0 (by simp)
  have hw := PositiveWorkFubini.work_integrable Q (rawMetricBilinear D)
    (rawMetricBilinear_symmetric D) (rawMetricBilinear_nonneg D) T
    (pairState Q M U V) (pairDrift Q M U V) (pairState_strong Q M U V)
    (pairDrift_strong Q M U V) hpath hz hp
  apply PositiveWorkFubini.expected_energy_decay Q (rawMetricBilinear D)
    (rawMetricBilinear_symmetric D) (rawMetricBilinear_nonneg D) T
    (pairState Q M U V) (pairDrift Q M U V) (pairState_strong Q M U V)
    (pairDrift_strong Q M U V) hpath hz hp ρ
  filter_upwards [hw.prod_right_ae,ae_restrict_mem measurableSet_Ioc] with r hwr hr
  have hr' : r ∈ Icc 0 (T : ℝ) := ⟨hr.1.le,hr.2⟩
  have hs : Integrable (fun ω => ⟪U.sampler r ω-V.sampler r ω,
      D.samplerWeight (M.drift (M.parameter (U.optimizer r)) (U.sampler r ω)-
        M.drift (M.parameter (V.optimizer r)) (V.sampler r ω))⟫_ℝ) Q := by
    have hh := hwr.sub (integrable_const
      ⟪U.optimizer r-V.optimizer r,D.optimizerWeight (U.optimizerDrift r-V.optimizerDrift r)⟫_ℝ)
    convert hh using 1
    ext ω
    simp only [Pi.sub_apply,rawMetricBilinear_apply,pairState,pairDrift]
    ring
  have h := original_work_le Q M D ρ hmono hσ hb r hr'.1 (U.optimizer r) (V.optimizer r)
    (U.sampler r) (V.sampler r) U.sampler_strong.of_uncurry_left V.sampler_strong.of_uncurry_left
    (U.sampler_square r hr') (V.sampler_square r hr')
    (U.observation_integrable r hr') (V.observation_integrable r hr') hs
  simpa only [rawMetricBilinear_apply,pairState,pairDrift,TwistedGeometry.optimizerSq,
    TwistedGeometry.samplerSq,U.optimizerDrift_realizes r hr',V.optimizerDrift_realizes r hr'] using h


/-- Original optimizer integral equations give the required continuity. -/
theorem Data.optimizer_continuous (U : Data Q M W T L) :
    ContinuousOn U.optimizer (Icc 0 (T : ℝ)) := by
  have hc : ContinuousOn (fun r => U.optimizer 0 + ∫ s in 0..r, U.optimizerDrift s)
      (uIcc 0 (T : ℝ)) :=
    continuousOn_const.add (intervalIntegral.continuousOn_primitive_interval'
      U.optimizerDrift_integrable (show (0 : ℝ) ∈ uIcc 0 (T : ℝ) from left_mem_uIcc))
  rw [uIcc_of_le T.coe_nonneg] at hc
  exact hc.congr U.optimizer_equation

/-- Original deterministic optimizer work is time-integrable. Thus positive
sampler work suffices for positive total pair work. -/
theorem positive_work_of_sampler (U : Data Q M W T L) (V : Data Q M W T K)
    (hs : Integrable (fun p : ℝ × Ω => max
      ⟪U.sampler p.1 p.2-V.sampler p.1 p.2,
        D.samplerWeight (M.drift (M.parameter (U.optimizer p.1)) (U.sampler p.1 p.2)-
          M.drift (M.parameter (V.optimizer p.1)) (V.sampler p.1 p.2))⟫_ℝ 0)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) :
    Integrable (fun p : ℝ × Ω =>
      max (rawMetricBilinear D (pairState Q M U V p.1 p.2)
        (pairDrift Q M U V p.1 p.2)) 0)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := by
  let B : S →L[ℝ] S →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp (ContinuousLinearMap.id ℝ S) D.optimizerWeight
  have hc : ContinuousOn (fun r => U.optimizer r-V.optimizer r) (uIcc 0 (T : ℝ)) := by
    change ContinuousOn (U.optimizer-V.optimizer) (uIcc 0 (T : ℝ))
    rw [uIcc_of_le T.coe_nonneg]
    exact (Data.optimizer_continuous Q M U).sub (Data.optimizer_continuous Q M V)
  have ho := IntegralQuadraticEnergy.bilinear_continuous_integrable B
    (fun r => U.optimizer r-V.optimizer r) (fun r => U.optimizerDrift r-V.optimizerDrift r)
    hc (U.optimizerDrift_integrable.sub V.optimizerDrift_integrable)
  have hoi := ((intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mp ho).norm.comp_fst Q
  have hm := (rawMetricBilinear D).continuous₂.comp_stronglyMeasurable
    ((pairState_strong Q M U V).prodMk (pairDrift_strong Q M U V))
  apply (hoi.add hs).mono'
    (continuous_max.comp_aestronglyMeasurable (hm.aestronglyMeasurable.prodMk aestronglyMeasurable_const))
  exact Eventually.of_forall (fun p => by
    rw [Real.norm_of_nonneg (le_max_right _ _)]
    change max (⟪U.optimizer p.1-V.optimizer p.1,
      D.optimizerWeight (U.optimizerDrift p.1-V.optimizerDrift p.1)⟫_ℝ + _) 0 ≤ _
    apply max_le
    · exact add_le_add (le_abs_self _) (le_max_left _ _)
    · exact add_nonneg (norm_nonneg _) (le_max_right _ _))

/-- Frozen sampler dissipation isolates the actual parameter-cross work. -/
theorem positive_work_of_parameter_cross (U : Data Q M W T L) (V : Data Q M W T K)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hmono : TwistedJointMonotonicity M D ρ)
    (hcross : Integrable (fun p : ℝ × Ω => ‖U.sampler p.1 p.2-V.sampler p.1 p.2‖ *
      ‖M.drift (M.parameter (U.optimizer p.1)) (V.sampler p.1 p.2)-
        M.drift (M.parameter (V.optimizer p.1)) (V.sampler p.1 p.2)‖)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) :
    Integrable (fun p : ℝ × Ω =>
      max (rawMetricBilinear D (pairState Q M U V p.1 p.2)
        (pairDrift Q M U V p.1 p.2)) 0)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) :=
  positive_work_of_sampler Q M D U V
    (ConstantNoiseWork.positive_work_integrable M D ρ hmono
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q)
      (fun p => U.optimizer p.1) (fun p => V.optimizer p.1)
      (fun p => U.sampler p.1 p.2) (fun p => V.sampler p.1 p.2)
      U.sampler_strong.aestronglyMeasurable V.sampler_strong.aestronglyMeasurable
      U.drift_strong.aestronglyMeasurable V.drift_strong.aestronglyMeasurable hρ hcross)

/-- The original raw common-Brownian model contracts under A3 and the
explicit parameter-cross-work condition. Frozen superlinear drift remains
allowed; the proof derives cancellation, Fubini, balance and Grönwall. -/
theorem energy_decay_of_parameter_cross (U : Data Q M W T L) (V : Data Q M W T K)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hmono : TwistedJointMonotonicity M D ρ)
    (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i)
    (hb : ∀ θ, Measurable (M.drift θ))
    (hcross : Integrable (fun p : ℝ × Ω => ‖U.sampler p.1 p.2-V.sampler p.1 p.2‖ *
      ‖M.drift (M.parameter (U.optimizer p.1)) (V.sampler p.1 p.2)-
        M.drift (M.parameter (V.optimizer p.1)) (V.sampler p.1 p.2)‖)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) :
    (∫ ω, rawMetricBilinear D (pairState Q M U V T ω) (pairState Q M U V T ω) ∂Q) ≤
      Real.exp (-2 * ρ * (T : ℝ)) *
        ∫ ω, rawMetricBilinear D (pairState Q M U V 0 ω) (pairState Q M U V 0 ω) ∂Q :=
  energy_decay Q M D U V ρ hmono hσ hb
    (positive_work_of_parameter_cross Q M D U V ρ hρ hmono hcross)


/-- A concrete additional sufficient condition: parameter-Lipschitz drift
with linear sampler growth, bounded projected-parameter gap, and actual
product-time state L². No growth bound on the frozen drift is imposed. -/
theorem energy_decay_of_parameter_growth (U : Data Q M W T L) (V : Data Q M W T K)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hmono : TwistedJointMonotonicity M D ρ)
    (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i)
    (hb : ∀ θ, Measurable (M.drift θ))
    (C P : ℝ) (hC : 0 ≤ C)
    (hparam : ∀ r ∈ Icc 0 (T : ℝ),
      ‖M.parameter (U.optimizer r)-M.parameter (V.optimizer r)‖ ≤ P)
    (hparamDrift : ∀ θ θ' z, ‖M.drift θ z-M.drift θ' z‖ ≤
      C * ‖θ-θ'‖ * (1+‖z‖))
    (hU2 : MemLp (Function.uncurry U.sampler) 2
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hV2 : MemLp (Function.uncurry V.sampler) 2
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) :
    (∫ ω, rawMetricBilinear D (pairState Q M U V T ω) (pairState Q M U V T ω) ∂Q) ≤
      Real.exp (-2 * ρ * (T : ℝ)) *
        ∫ ω, rawMetricBilinear D (pairState Q M U V 0 ω) (pairState Q M U V 0 ω) ∂Q := by
  apply energy_decay Q M D U V ρ hmono hσ hb
  apply positive_work_of_sampler Q M D U V
  let μ := (volume.restrict (Ioc 0 (T : ℝ))).prod Q
  have hi : Integrable (fun p : ℝ × Ω => ‖U.sampler p.1 p.2-V.sampler p.1 p.2‖ *
      (1+‖V.sampler p.1 p.2‖)) μ :=
    (hU2.sub hV2).norm.integrable_mul ((memLp_const (1 : ℝ)).add hV2.norm)
  have hm : AEStronglyMeasurable (fun p : ℝ × Ω =>
      ⟪U.sampler p.1 p.2-V.sampler p.1 p.2,
        D.samplerWeight (M.drift (M.parameter (U.optimizer p.1)) (U.sampler p.1 p.2)-
          M.drift (M.parameter (V.optimizer p.1)) (V.sampler p.1 p.2))⟫_ℝ) μ :=
    (U.sampler_strong.aestronglyMeasurable.sub V.sampler_strong.aestronglyMeasurable).inner
      (D.samplerWeight.continuous.comp_aestronglyMeasurable
        (U.drift_strong.aestronglyMeasurable.sub V.drift_strong.aestronglyMeasurable))
  have htime : ∀ᵐ p ∂μ, p.1 ∈ Icc 0 (T : ℝ) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact ae_of_all Q (fun _ => ⟨hr.1.le,hr.2⟩)
  apply (hi.const_mul (‖D.samplerWeight‖ * C * P)).mono'
    (continuous_max.comp_aestronglyMeasurable (hm.prodMk aestronglyMeasurable_const))
  filter_upwards [htime] with p hp
  rw [Real.norm_of_nonneg (le_max_right _ _)]
  calc
    _ ≤ ‖D.samplerWeight‖ * ‖U.sampler p.1 p.2-V.sampler p.1 p.2‖ *
        ‖M.drift (M.parameter (U.optimizer p.1)) (V.sampler p.1 p.2)-
          M.drift (M.parameter (V.optimizer p.1)) (V.sampler p.1 p.2)‖ :=
      ConstantNoiseWork.positive_work_le M D ρ hmono hρ _ _ _ _
    _ ≤ ‖D.samplerWeight‖ * ‖U.sampler p.1 p.2-V.sampler p.1 p.2‖ *
        (C * P * (1+‖V.sampler p.1 p.2‖)) := by
      gcongr
      exact (hparamDrift _ _ _).trans (by gcongr; exact hparam p.1 hp)
    _ = _ := by ring


/-- The actual raw energy equals the weighted energy of its literal L²
sections. This identification does not require L²-valued sampler drift. -/
theorem pair_energy_eq_lifted (U : Data Q M W T L) (V : Data Q M W T K)
    (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) :
    (∫ ω, rawMetricBilinear D (pairState Q M U V r ω) (pairState Q M U V r ω) ∂Q) =
      liftedMetricBilinear Q D
        (U.optimizer r-V.optimizer r,ProductLpSections.sectionLp Q U.sampler r-
          ProductLpSections.sectionLp Q V.sampler r)
        (U.optimizer r-V.optimizer r,ProductLpSections.sectionLp Q U.sampler r-
          ProductLpSections.sectionLp Q V.sampler r) := by
  let A := ProductLpSections.sectionLp Q U.sampler r
  let B := ProductLpSections.sectionLp Q V.sampler r
  have ha := ProductLpSections.sectionLp_ae Q U.sampler (U.sampler_square r hr)
  have hb := ProductLpSections.sectionLp_ae Q V.sampler (V.sampler_square r hr)
  have he : (fun ω => rawMetricBilinear D (pairState Q M U V r ω) (pairState Q M U V r ω)) =ᵐ[Q]
      fun ω => D.optimizerSq (U.optimizer r-V.optimizer r) +
        ⟪(A-B) ω,D.samplerWeight ((A-B) ω)⟫_ℝ := by
    filter_upwards [ha,hb,Lp.coeFn_sub A B] with ω ha hb hd
    simp only [Pi.sub_apply] at hd
    simp only [rawMetricBilinear_apply,pairState,TwistedGeometry.optimizerSq]
    rw [show (A-B) ω = U.sampler r ω-V.sampler r ω by exact hd.trans (by rw [ha,hb])]
  rw [integral_congr_ae he,integral_add (integrable_const _)
    (lp_weighted_pairing_integrable Q D.samplerWeight (A-B) (A-B)),integral_const,
    probReal_univ,one_smul,liftedMetricBilinear_apply]
  rfl

/-- The original joint optimizer/sampler RMS cost has exactly the source
condition-number prefactor under the explicit parameter-cross condition. -/
theorem rms_decay_of_parameter_cross (U : Data Q M W T L) (V : Data Q M W T K)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hmono : TwistedJointMonotonicity M D ρ)
    (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i)
    (hb : ∀ θ, Measurable (M.drift θ))
    (hcross : Integrable (fun p : ℝ × Ω => ‖U.sampler p.1 p.2-V.sampler p.1 p.2‖ *
      ‖M.drift (M.parameter (U.optimizer p.1)) (V.sampler p.1 p.2)-
        M.drift (M.parameter (V.optimizer p.1)) (V.sampler p.1 p.2)‖)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) :
    Real.sqrt (‖U.optimizer T-V.optimizer T‖ ^ 2+
      ‖ProductLpSections.sectionLp Q U.sampler T-ProductLpSections.sectionLp Q V.sampler T‖ ^ 2) ≤
      Real.sqrt D.conditionNumber * Real.exp (-ρ * (T : ℝ)) *
        Real.sqrt (‖U.optimizer 0-V.optimizer 0‖ ^ 2+
          ‖ProductLpSections.sectionLp Q U.sampler 0-ProductLpSections.sectionLp Q V.sampler 0‖ ^ 2) := by
  have hd := energy_decay_of_parameter_cross Q M D U V ρ hρ hmono hσ hb hcross
  rw [pair_energy_eq_lifted Q M D U V T ⟨T.coe_nonneg,le_rfl⟩,
    pair_energy_eq_lifted Q M D U V 0 ⟨le_rfl,T.coe_nonneg⟩] at hd
  let At := (U.optimizer T-V.optimizer T,ProductLpSections.sectionLp Q U.sampler T-
    ProductLpSections.sectionLp Q V.sampler T)
  let A0 := (U.optimizer 0-V.optimizer 0,ProductLpSections.sectionLp Q U.sampler 0-
    ProductLpSections.sectionLp Q V.sampler 0)
  have hlo := liftedMetricBilinear_lower Q D At
  have hup := liftedMetricBilinear_upper Q D A0
  have hκ : 0 ≤ D.conditionNumber := (by norm_num : (0 : ℝ) ≤ 1).trans D.conditionNumber_ge_one
  have hn (x : S × Lp Z 2 Q) : 0 ≤ liftedEuclideanSq Q x := add_nonneg (sq_nonneg _) (sq_nonneg _)
  change Real.sqrt (liftedEuclideanSq Q At) ≤
    Real.sqrt D.conditionNumber * Real.exp (-ρ * (T : ℝ)) * Real.sqrt (liftedEuclideanSq Q A0)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (hn _),mul_pow,mul_pow,Real.sq_sqrt hκ,Real.sq_sqrt (hn _)]
  have he : Real.exp (-ρ * (T : ℝ)) ^ 2 = Real.exp (-2 * ρ * (T : ℝ)) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  rw [he]
  apply (mul_le_mul_iff_of_pos_left D.lower_pos).mp
  have hupper := mul_le_mul_of_nonneg_left hup (Real.exp_pos (-2 * ρ * (T : ℝ))).le
  have heq : D.lower * (D.conditionNumber * Real.exp (-2 * ρ * (T : ℝ)) * liftedEuclideanSq Q A0) =
      Real.exp (-2 * ρ * (T : ℝ)) * (D.upper * liftedEuclideanSq Q A0) := by
    dsimp [TwistedGeometry.conditionNumber]
    field_simp [ne_of_gt D.lower_pos]
  rw [heq]
  exact hlo.trans (hd.trans hupper)


/-- The realized output joint law bounds the genuine sampler transport
infimum. This is a fixed common-source law bound, prior to the separate
arbitrary-initial-coupling construction. -/
theorem pair_law_distance_decay_of_parameter_cross
    (U : Data Q M W T L) (V : Data Q M W T K)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hmono : TwistedJointMonotonicity M D ρ)
    (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i)
    (hb : ∀ θ, Measurable (M.drift θ))
    (hcross : Integrable (fun p : ℝ × Ω => ‖U.sampler p.1 p.2-V.sampler p.1 p.2‖ *
      ‖M.drift (M.parameter (U.optimizer p.1)) (V.sampler p.1 p.2)-
        M.drift (M.parameter (V.optimizer p.1)) (V.sampler p.1 p.2)‖)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) :
    optimizerLawDistance (U.optimizer T) (V.optimizer T)
      (Q.map (U.sampler T)) (Q.map (V.sampler T)) ≤
      Real.sqrt D.conditionNumber * Real.exp (-ρ * (T : ℝ)) *
        Real.sqrt (‖U.optimizer 0-V.optimizer 0‖ ^ 2+
          ‖ProductLpSections.sectionLp Q U.sampler 0-ProductLpSections.sectionLp Q V.sampler 0‖ ^ 2) := by
  let A := ProductLpSections.sectionLp Q U.sampler T
  let B := ProductLpSections.sectionLp Q V.sampler T
  have hA : Q.map A = Q.map (U.sampler T) :=
    Measure.map_congr (ProductLpSections.sectionLp_ae Q U.sampler (U.sampler_square T ⟨T.coe_nonneg,le_rfl⟩))
  have hB : Q.map B = Q.map (V.sampler T) :=
    Measure.map_congr (ProductLpSections.sectionLp_ae Q V.sampler (V.sampler_square T ⟨T.coe_nonneg,le_rfl⟩))
  have hν : MemLp (fun z : Z => z) 2 (Q.map A) :=
    (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).mpr (lp_law_second_moment Q A)
  have hν' : MemLp (fun z : Z => z) 2 (Q.map B) :=
    (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).mpr (lp_law_second_moment Q B)
  let c : ULA.Coupling (Q.map A) (Q.map B) :=
    ⟨samplerPairLaw Q A B,(samplerPairLaw_coupling Q A B).1,(samplerPairLaw_coupling Q A B).2⟩
  have hc := coupling_difference_memLp (Q.map A) (Q.map B) hν hν' c
  have hbnd := wasserstein_le_finite_coupling (Q.map A) (Q.map B) c hc.eLpNorm_ne_top
  have hs := couplingCost_sq_eq_integral c.joint hc
  rw [IntegralModelContraction.samplerPairLaw_euclidean_integral] at hs
  apply le_trans _ (rms_decay_of_parameter_cross Q M D U V ρ hρ hmono hσ hb hcross)
  apply Real.sqrt_le_sqrt
  change ‖U.optimizer T-V.optimizer T‖ ^ 2+ULA.wasserstein2Real (Q.map (U.sampler T)) (Q.map (V.sampler T)) ^ 2 ≤
    ‖U.optimizer T-V.optimizer T‖ ^ 2+‖A-B‖ ^ 2
  rw [← hA,← hB]
  apply add_le_add le_rfl
  rw [← hs]
  exact (sq_le_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).mpr hbnd

end RawModel
end PBGSO.RawConstantNoiseContraction
