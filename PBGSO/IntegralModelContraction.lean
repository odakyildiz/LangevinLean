import PBGSO.IntegralQuadraticEnergy
import PBGSO.LawContraction

/-! # Source A3 contraction for actual integral martingale trajectories

This works with time-integrable drift, time-L² diffusion and original
integral optimizer equations. Continuous coefficients and pointwise time
derivatives are not required. Stochastic-integral realization and its
synchronous isometry remain explicit inputs; no source A1 equivalence is
asserted by this module.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace InnerProductSpace
namespace PBGSO.IntegralModelContraction
open QuadraticMartingale IntegralQuadraticEnergy

variable {Ω S Θ Z X I : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype I]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)

/-- A genuine finite-horizon integral trajectory. All equations concern the
original optimizer and sampler coefficients; no quadratic energy identity
or energy dissipation is a field. -/
structure ModelIntegralTrajectory (M : Model S Θ Z X I) (T : ℝ) where
  optimizer : ℝ → S
  optimizerDrift : ℝ → S
  sampler : ℝ → Lp Z 2 Q
  drift : ℝ → Lp Z 2 Q
  diffusion : ℝ → I → Lp Z 2 Q
  noise : ℝ → Ω → Z
  optimizer_continuous : ContinuousOn optimizer (Icc 0 T)
  sampler_continuous : ContinuousOn sampler (Icc 0 T)
  optimizerDrift_integrable : IntervalIntegrable optimizerDrift volume 0 T
  drift_integrable : IntervalIntegrable drift volume 0 T
  diffusion_timeL2 : ∀ i, MemLp (fun r => diffusion r i) 2 (volume.restrict (uIoc 0 T))
  optimizerDrift_realizes : ∀ t ∈ Icc 0 T, optimizerDrift t =
    M.optimizerField t (optimizer t) (Q.map (sampler t))
  optimizer_integral : ∀ t ∈ Icc 0 T,
    optimizer t = optimizer 0 + ∫ r in 0..t, optimizerDrift r
  drift_realizes : ∀ t ∈ Icc 0 T, drift t =ᵐ[Q]
    fun ω => M.drift (M.parameter (optimizer t)) (sampler t ω)
  diffusion_realizes : ∀ t ∈ Icc 0 T, ∀ i, diffusion t i =ᵐ[Q]
    fun ω => M.diffusion (M.parameter (optimizer t)) (sampler t ω) i
  martingale : Martingale noise ℱ Q
  noise_realizes : ∀ t ∈ Icc 0 T, noise t =ᵐ[Q] martingaleResidual Q sampler drift t
  initial_adapted : AEStronglyMeasurable[ℱ 0] (sampler 0) Q
  drift_adapted : ∀ t ∈ Ioc 0 T, AEStronglyMeasurable[ℱ t] (drift t) Q
  observation_integrable : ∀ t ∈ Icc 0 T, Integrable
    (fun z => M.observation (M.parameter (optimizer t)) (M.position z)) (Q.map (sampler t))

variable {Q ℱ} {M : Model S Θ Z X I} {T : ℝ}

/-- Restriction changes no actual trajectory or noise representative. -/
def ModelIntegralTrajectory.restrict (U : ModelIntegralTrajectory Q ℱ M T)
    {R : ℝ} (hR : R ∈ Icc 0 T) : ModelIntegralTrajectory Q ℱ M R where
  optimizer := U.optimizer
  optimizerDrift := U.optimizerDrift
  sampler := U.sampler
  drift := U.drift
  diffusion := U.diffusion
  noise := U.noise
  optimizer_continuous := U.optimizer_continuous.mono (Icc_subset_Icc le_rfl hR.2)
  sampler_continuous := U.sampler_continuous.mono (Icc_subset_Icc le_rfl hR.2)
  optimizerDrift_integrable := U.optimizerDrift_integrable.mono_set' (by
    rw [uIoc_of_le hR.1, uIoc_of_le (hR.1.trans hR.2)]
    exact Ioc_subset_Ioc_right hR.2)
  drift_integrable := U.drift_integrable.mono_set' (by
    rw [uIoc_of_le hR.1, uIoc_of_le (hR.1.trans hR.2)]
    exact Ioc_subset_Ioc_right hR.2)
  diffusion_timeL2 := fun i => (U.diffusion_timeL2 i).mono_measure
    (Measure.restrict_mono (by
      rw [uIoc_of_le hR.1, uIoc_of_le (hR.1.trans hR.2)]
      exact Ioc_subset_Ioc_right hR.2) le_rfl)
  optimizerDrift_realizes := fun r hr => U.optimizerDrift_realizes r ⟨hr.1, hr.2.trans hR.2⟩
  optimizer_integral := fun r hr => U.optimizer_integral r ⟨hr.1, hr.2.trans hR.2⟩
  drift_realizes := fun r hr => U.drift_realizes r ⟨hr.1, hr.2.trans hR.2⟩
  diffusion_realizes := fun r hr => U.diffusion_realizes r ⟨hr.1, hr.2.trans hR.2⟩
  martingale := U.martingale
  noise_realizes := fun r hr => U.noise_realizes r ⟨hr.1, hr.2.trans hR.2⟩
  initial_adapted := U.initial_adapted
  drift_adapted := fun r hr => U.drift_adapted r ⟨hr.1, hr.2.trans hR.2⟩
  observation_integrable := fun r hr => U.observation_integrable r ⟨hr.1, hr.2.trans hR.2⟩

/-- The actual sampler work is the pullback of weighted drift and diffusion
pairings of the realized L² columns. -/
theorem work_pullback_ae (D : TwistedGeometry S Z) (U V : ModelIntegralTrajectory Q ℱ M T)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    (fun ω => samplerCouplingWork M D (U.optimizer t) (V.optimizer t)
      (U.sampler t ω, V.sampler t ω)) =ᵐ[Q]
    fun ω => ⟪(U.sampler t - V.sampler t) ω,
      D.samplerWeight ((U.drift t - V.drift t) ω)⟫_ℝ +
      (1 / 2 : ℝ) * ∑ i, ⟪(U.diffusion t i - V.diffusion t i) ω,
        D.samplerWeight ((U.diffusion t i - V.diffusion t i) ω)⟫_ℝ := by
  have hσ : ∀ᵐ ω ∂Q, ∀ i,
      (U.diffusion t i - V.diffusion t i) ω =
        M.diffusion (M.parameter (U.optimizer t)) (U.sampler t ω) i -
        M.diffusion (M.parameter (V.optimizer t)) (V.sampler t ω) i := by
    rw [ae_all_iff]
    intro i
    filter_upwards [Lp.coeFn_sub (U.diffusion t i) (V.diffusion t i),
      U.diffusion_realizes t ht i, V.diffusion_realizes t ht i] with ω hs hu hv
    simp only [hs, Pi.sub_apply, hu, hv]
  filter_upwards [Lp.coeFn_sub (U.sampler t) (V.sampler t),
    Lp.coeFn_sub (U.drift t) (V.drift t), U.drift_realizes t ht, V.drift_realizes t ht,
    hσ] with ω hX hb hu hv hσ
  simp only [hX, hb, Pi.sub_apply, hu, hv, hσ, samplerCouplingWork, TwistedGeometry.samplerSq]

theorem work_pullback_integrable (D : TwistedGeometry S Z) (U V : ModelIntegralTrajectory Q ℱ M T)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    Integrable (fun ω => samplerCouplingWork M D (U.optimizer t) (V.optimizer t)
      (U.sampler t ω, V.sampler t ω)) Q := by
  apply (Integrable.add (lp_weighted_pairing_integrable Q D.samplerWeight _ _)
    ((integrable_finsetSum _ (fun i _ => lp_weighted_pairing_integrable Q D.samplerWeight
      (U.diffusion t i - V.diffusion t i) (U.diffusion t i - V.diffusion t i))).const_mul
        (1 / 2 : ℝ))).congr
  exact (work_pullback_ae D U V t ht).symm

/-- Only Borel measurability of the primitive coefficients is used here. -/
theorem work_measurable (D : TwistedGeometry S Z) (s s' : S)
    (hb : ∀ θ, Measurable (M.drift θ))
    (hσ : ∀ θ i, Measurable (fun z => M.diffusion θ z i)) :
    Measurable (samplerCouplingWork M D s s') := by
  have hz : Measurable (fun zz : Z × Z => zz.1 - zz.2) := measurable_fst.sub measurable_snd
  have hbb := ((hb (M.parameter s)).comp measurable_fst).sub
    ((hb (M.parameter s')).comp measurable_snd)
  have hinner : Continuous (fun p : Z × Z => ⟪p.1, p.2⟫_ℝ) := continuous_fst.inner continuous_snd
  have hpair := hinner.measurable.comp (hz.prodMk (D.samplerWeight.continuous.measurable.comp hbb))
  have hsum : Measurable (fun zz : Z × Z => ∑ i,
      D.samplerSq (M.diffusion (M.parameter s) zz.1 i -
        M.diffusion (M.parameter s') zz.2 i)) := by
    apply Finset.measurable_sum
    intro i _
    have hi := ((hσ (M.parameter s) i).comp measurable_fst).sub
      ((hσ (M.parameter s') i).comp measurable_snd)
    exact hinner.measurable.comp (hi.prodMk (D.samplerWeight.continuous.measurable.comp hi))
  exact hpair.add (hsum.const_mul (1 / 2 : ℝ))

theorem work_integrable (D : TwistedGeometry S Z) (U V : ModelIntegralTrajectory Q ℱ M T)
    (hb : ∀ θ, Measurable (M.drift θ))
    (hσ : ∀ θ i, Measurable (fun z => M.diffusion θ z i)) (t : ℝ) (ht : t ∈ Icc 0 T) :
    Integrable (samplerCouplingWork M D (U.optimizer t) (V.optimizer t))
      (samplerPairLaw Q (U.sampler t) (V.sampler t)) := by
  apply (integrable_map_measure (work_measurable D _ _ hb hσ).aestronglyMeasurable
    ((Lp.aestronglyMeasurable (U.sampler t)).aemeasurable.prodMk
      (Lp.aestronglyMeasurable (V.sampler t)).aemeasurable)).mpr
  exact work_pullback_integrable D U V t ht

theorem work_integral (D : TwistedGeometry S Z) (U V : ModelIntegralTrajectory Q ℱ M T)
    (hb : ∀ θ, Measurable (M.drift θ))
    (hσ : ∀ θ i, Measurable (fun z => M.diffusion θ z i)) (t : ℝ) (ht : t ∈ Icc 0 T) :
    (∫ zz, samplerCouplingWork M D (U.optimizer t) (V.optimizer t) zz
      ∂samplerPairLaw Q (U.sampler t) (V.sampler t)) =
      weightedPairing Q D.samplerWeight (U.sampler t - V.sampler t) (U.drift t - V.drift t) +
      (1 / 2 : ℝ) * ∑ i, weightedPairing Q D.samplerWeight
        (U.diffusion t i - V.diffusion t i) (U.diffusion t i - V.diffusion t i) := by
  rw [samplerPairLaw, integral_map
    ((Lp.aestronglyMeasurable (U.sampler t)).aemeasurable.prodMk
      (Lp.aestronglyMeasurable (V.sampler t)).aemeasurable)
    (work_measurable D _ _ hb hσ).aestronglyMeasurable]
  rw [integral_congr_ae (work_pullback_ae D U V t ht), integral_add
    (lp_weighted_pairing_integrable Q D.samplerWeight _ _)
    ((integrable_finsetSum _ (fun i _ => lp_weighted_pairing_integrable Q D.samplerWeight
      (U.diffusion t i - V.diffusion t i) (U.diffusion t i - V.diffusion t i))).const_mul
        (1 / 2 : ℝ)), integral_const_mul,
      integral_finsetSum _ (fun i _ => lp_weighted_pairing_integrable Q D.samplerWeight
        (U.diffusion t i - V.diffusion t i) (U.diffusion t i - V.diffusion t i))]
  simp only [weightedPairing_apply, lp_weighted_pairing_eq_integral]


/-- Conditional expectation needs representatives only at its two times.
This supports actual martingales stopped after the finite horizon. -/
theorem martingale_condExpL2_local (m : ℝ → Ω → Z) (hm : Martingale m ℱ Q)
    {s t : ℝ} (hst : s ≤ t) (Ms Mt : Lp Z 2 Q)
    (hs : m s =ᵐ[Q] Ms) (ht : m t =ᵐ[Q] Mt) :
    (condExpL2 Z ℝ (ℱ.le s) Mt : Lp Z 2 Q) = Ms := by
  apply Lp.ext
  have hCE : (condExpL2 Z ℝ (ℱ.le s) Mt : Ω → Z) =ᵐ[Q] Q[Mt | ℱ s] := by
    simpa only [Lp.toLp_coeFn] using
      (Lp.memLp Mt).condExpL2_ae_eq_condExp (𝕜 := ℝ) (ℱ.le s)
  exact hCE.trans ((condExp_congr_ae ht.symm).trans ((hm.condExp_ae_eq hst).trans hs))

/-- Weighted increment orthogonality on two actual finite-horizon times. -/
theorem martingale_orthogonal_local (W : Z →L[ℝ] Z)
    (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (Y Ms Mt : Lp Z 2 Q) (m : ℝ → Ω → Z) (hm : Martingale m ℱ Q)
    {s t : ℝ} (hst : s ≤ t) (hs : m s =ᵐ[Q] Ms) (ht : m t =ᵐ[Q] Mt)
    (hY : AEStronglyMeasurable[ℱ s] Y Q) : weightedPairing Q W Y (Mt - Ms) = 0 := by
  have hadapt : AEStronglyMeasurable[ℱ s] (W.compLpL 2 Q Y) Q :=
    (W.continuous.comp_aestronglyMeasurable hY).congr (W.coeFn_compLpL Y).symm
  have hcond : (condExpL2 Z ℝ (ℱ.le s) (Mt - Ms) : Lp Z 2 Q) = 0 := by
    simp only [map_sub, Submodule.coe_sub]
    rw [martingale_condExpL2_local m hm hst Ms Mt hs ht,
      martingale_condExpL2_local m hm le_rfl Ms Ms hs hs, sub_self]
  have hinner := inner_condExpL2_eq_inner_fun (𝕜 := ℝ) (ℱ.le s)
    (Mt - Ms) (W.compLpL 2 Q Y) hadapt
  rw [hcond, inner_zero_left] at hinner
  rw [weightedPairing_left Q W hW, real_inner_comm, ← hinner]

/-- The full deterministic/L² difference of two actual trajectories. -/
def pairState (U V : ModelIntegralTrajectory Q ℱ M T) (t : ℝ) :=
  (U.optimizer t - V.optimizer t, U.sampler t - V.sampler t)

def pairDrift (U V : ModelIntegralTrajectory Q ℱ M T) (t : ℝ) :=
  (U.optimizerDrift t - V.optimizerDrift t, U.drift t - V.drift t)

def pairDiffusion (U V : ModelIntegralTrajectory Q ℱ M T) (t : ℝ) (i : I) :=
  U.diffusion t i - V.diffusion t i

def pairMartingale (U V : ModelIntegralTrajectory Q ℱ M T) (t : ℝ) :=
  martingaleResidual Q U.sampler U.drift t - martingaleResidual Q V.sampler V.drift t

def pairEnergy (D : TwistedGeometry S Z) (U V : ModelIntegralTrajectory Q ℱ M T) (t : ℝ) :=
  liftedMetricBilinear Q D (pairState U V t) (pairState U V t)

theorem pairDiffusion_integrable (D : TwistedGeometry S Z) (U V : ModelIntegralTrajectory Q ℱ M T) :
    IntervalIntegrable (diffusionEnergy Q D.samplerWeight (pairDiffusion U V)) volume 0 T := by
  change IntervalIntegrable (fun r => ∑ i, weightedPairing Q D.samplerWeight
    (U.diffusion r i - V.diffusion r i) (U.diffusion r i - V.diffusion r i)) volume 0 T
  rw [intervalIntegrable_iff]
  exact integrable_finsetSum Finset.univ (fun i _ =>
    (quadratic_time_integrable (weightedPairing Q D.samplerWeight) _
      ((U.diffusion_timeL2 i).sub (V.diffusion_timeL2 i))).def')

/-- Actual joint law and coefficient realization derive A3 dissipation;
no lifted coefficient inequality is supplied. -/
theorem pair_dissipation (D : TwistedGeometry S Z) (U V : ModelIntegralTrajectory Q ℱ M T)
    (hb : ∀ θ, Measurable (M.drift θ))
    (hσ : ∀ θ i, Measurable (fun z => M.diffusion θ z i))
    (ρ : ℝ) (hmono : TwistedJointMonotonicity M D ρ) (t : ℝ) (ht : t ∈ Icc 0 T) :
    2 * liftedMetricBilinear Q D (pairState U V t) (pairDrift U V t) +
      diffusionEnergy Q D.samplerWeight (pairDiffusion U V) t ≤
      (-2 * ρ) * pairEnergy D U V t := by
  let ν := Q.map (U.sampler t)
  let ν' := Q.map (V.sampler t)
  have hν : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff
    (Lp.aestronglyMeasurable (U.sampler t)).aemeasurable).mpr inferInstance
  have hν' : IsProbabilityMeasure ν' := (Measure.isProbabilityMeasure_map_iff
    (Lp.aestronglyMeasurable (V.sampler t)).aemeasurable).mpr inferInstance
  have hh := hmono t ht.1 (U.optimizer t) (V.optimizer t) ν ν'
    (samplerPairLaw Q (U.sampler t) (V.sampler t))
    (samplerPairLaw_coupling Q _ _) hν hν'
    (lp_law_second_moment Q _) (lp_law_second_moment Q _)
    (U.observation_integrable t ht) (V.observation_integrable t ht)
    (work_integrable D U V hb hσ t ht)
    (samplerPairLaw_cost_integrable Q D _ _)
  rw [work_integral D U V hb hσ t ht, samplerPairLaw_cost_integral] at hh
  rw [← U.optimizerDrift_realizes t ht, ← V.optimizerDrift_realizes t ht] at hh
  change 2 * (⟪U.optimizer t - V.optimizer t,
      D.optimizerWeight (U.optimizerDrift t - V.optimizerDrift t)⟫_ℝ +
      weightedPairing Q D.samplerWeight (U.sampler t - V.sampler t) (U.drift t - V.drift t)) +
      (∑ i, weightedPairing Q D.samplerWeight (U.diffusion t i - V.diffusion t i)
        (U.diffusion t i - V.diffusion t i)) ≤
      (-2 * ρ) * (D.optimizerSq (U.optimizer t - V.optimizer t) +
      weightedPairing Q D.samplerWeight (U.sampler t - V.sampler t) (U.sampler t - V.sampler t))
  simp only [weightedPairing_apply] at *
  linarith

theorem pairDrift_integrable (U V : ModelIntegralTrajectory Q ℱ M T) :
    IntervalIntegrable (pairDrift U V) volume 0 T :=
  ⟨(U.optimizerDrift_integrable.1.sub V.optimizerDrift_integrable.1).prodMk
      (U.drift_integrable.1.sub V.drift_integrable.1),
    (U.optimizerDrift_integrable.2.sub V.optimizerDrift_integrable.2).prodMk
      (U.drift_integrable.2.sub V.drift_integrable.2)⟩

theorem pairState_continuous (U V : ModelIntegralTrajectory Q ℱ M T) :
    ContinuousOn (pairState U V) (Icc 0 T) :=
  (U.optimizer_continuous.sub V.optimizer_continuous).prodMk
    (U.sampler_continuous.sub V.sampler_continuous)

theorem pairMartingale_zero (U V : ModelIntegralTrajectory Q ℱ M T) :
    pairMartingale U V 0 = 0 := by simp [pairMartingale, martingaleResidual]

theorem pairMartingale_rep (U V : ModelIntegralTrajectory Q ℱ M T) (r : ℝ) (hr : r ∈ Icc 0 T) :
    (U.noise - V.noise) r =ᵐ[Q] pairMartingale U V r :=
  ((U.noise_realizes r hr).sub (V.noise_realizes r hr)).trans (Lp.coeFn_sub _ _).symm

/-- The full integral decomposition is derived from the original optimizer
equations and the actual sampler drift residuals. -/
theorem pair_decomposition (U V : ModelIntegralTrajectory Q ℱ M T)
    {r : ℝ} (hr : r ∈ Icc 0 T) :
    pairState U V r = pairState U V 0 + (∫ s in 0..r, pairDrift U V s) +
      (0, pairMartingale U V r) := by
  have hbU : IntervalIntegrable U.drift volume 0 r := U.drift_integrable.mono_set' (by
    simp only [uIoc_of_le hr.1, uIoc_of_le (hr.1.trans hr.2)]
    exact Ioc_subset_Ioc_right hr.2)
  have hbV : IntervalIntegrable V.drift volume 0 r := V.drift_integrable.mono_set' (by
    simp only [uIoc_of_le hr.1, uIoc_of_le (hr.1.trans hr.2)]
    exact Ioc_subset_Ioc_right hr.2)
  have hvU : IntervalIntegrable U.optimizerDrift volume 0 r := U.optimizerDrift_integrable.mono_set' (by
    simp only [uIoc_of_le hr.1, uIoc_of_le (hr.1.trans hr.2)]
    exact Ioc_subset_Ioc_right hr.2)
  have hvV : IntervalIntegrable V.optimizerDrift volume 0 r := V.optimizerDrift_integrable.mono_set' (by
    simp only [uIoc_of_le hr.1, uIoc_of_le (hr.1.trans hr.2)]
    exact Ioc_subset_Ioc_right hr.2)
  have hp : IntervalIntegrable (pairDrift U V) volume 0 r :=
    ⟨(hvU.1.sub hvV.1).prodMk (hbU.1.sub hbV.1),
      (hvU.2.sub hvV.2).prodMk (hbU.2.sub hbV.2)⟩
  have hint : (∫ s in 0..r, pairDrift U V s) =
      (∫ s in 0..r, U.optimizerDrift s - V.optimizerDrift s,
       ∫ s in 0..r, U.drift s - V.drift s) := by
    apply Prod.ext
    · exact ((ContinuousLinearMap.fst ℝ S (Lp Z 2 Q)).intervalIntegral_comp_comm hp).symm
    · exact ((ContinuousLinearMap.snd ℝ S (Lp Z 2 Q)).intervalIntegral_comp_comm hp).symm
  rw [hint]
  apply Prod.ext
  · change U.optimizer r - V.optimizer r =
      (U.optimizer 0 - V.optimizer 0) +
        (∫ s in 0..r, U.optimizerDrift s - V.optimizerDrift s) + 0
    rw [U.optimizer_integral r hr, V.optimizer_integral r hr,
      intervalIntegral.integral_sub hvU hvV]
    abel
  · change U.sampler r - V.sampler r = (U.sampler 0 - V.sampler 0) +
      (∫ s in 0..r, U.drift s - V.drift s) + pairMartingale U V r
    simp only [pairMartingale, martingaleResidual,
      intervalIntegral.integral_sub hbU hbV]
    abel

theorem liftedMetricBilinear_noise (D : TwistedGeometry S Z)
    (x : S × Lp Z 2 Q) (v : Lp Z 2 Q) :
    liftedMetricBilinear Q D x (0, v) = weightedPairing Q D.samplerWeight x.2 v := by
  change ⟪x.1, D.optimizerWeight 0⟫_ℝ + weightedPairing Q D.samplerWeight x.2 v = _
  simp

/-- Actual synchronous noise energy is the only stochastic-integral
interface. In the completion construction this follows from the proved
weighted increment isometry for the difference of the two integrands. -/
def SynchronousIsometry (D : TwistedGeometry S Z) (U V : ModelIntegralTrajectory Q ℱ M T) : Prop :=
  ∀ t ∈ Icc 0 T, weightedPairing Q D.samplerWeight
    (pairMartingale U V t) (pairMartingale U V t) =
      ∫ r in 0..t, diffusionEnergy Q D.samplerWeight (pairDiffusion U V) r

/-- The original optimizer integral equations, actual martingales and
synchronous increment isometry imply the full integral quadratic balance.
No energy balance or differentiability is assumed. -/
theorem pair_energy_integral (D : TwistedGeometry S Z)
    (U V : ModelIntegralTrajectory Q ℱ M T) (hT : 0 ≤ T)
    (hIso : SynchronousIsometry D U V) :
    pairEnergy D U V T = pairEnergy D U V 0 +
      ∫ r in 0..T, 2 * liftedMetricBilinear Q D (pairState U V r) (pairDrift U V r) +
        diffusionEnergy Q D.samplerWeight (pairDiffusion U V) r := by
  have hm : Martingale (U.noise - V.noise) ℱ Q := U.martingale.sub V.martingale
  have hrep := pairMartingale_rep U V
  have hzero := pairMartingale_zero U V
  have hinit : AEStronglyMeasurable[ℱ 0] (U.sampler 0 - V.sampler 0) Q :=
    (U.initial_adapted.sub V.initial_adapted).congr (Lp.coeFn_sub _ _).symm
  have hbadapt (r : ℝ) (hr : r ∈ Ioc 0 T) :
      AEStronglyMeasurable[ℱ r] (U.drift r - V.drift r) Q :=
    ((U.drift_adapted r hr).sub (V.drift_adapted r hr)).congr (Lp.coeFn_sub _ _).symm
  apply quadratic_balance (liftedMetricBilinear Q D) (liftedMetricBilinear_symmetric Q D)
    (pairState U V) (pairDrift U V) (fun r => (0, pairMartingale U V r))
    (diffusionEnergy Q D.samplerWeight (pairDiffusion U V)) hT
    (pairDrift_integrable U V) (pairDiffusion_integrable D U V) (pairState_continuous U V)
    (fun r hr => pair_decomposition U V hr)
  · rw [liftedMetricBilinear_noise]
    simpa only [pairState, hzero, sub_zero] using
      martingale_orthogonal_local D.samplerWeight D.sampler_symmetric
        (U.sampler 0 - V.sampler 0) (pairMartingale U V 0) (pairMartingale U V T)
        (U.noise - V.noise) hm hT (hrep 0 ⟨le_rfl, hT⟩) (hrep T ⟨hT, le_rfl⟩) hinit
  · intro r hr
    have hp : ((0 : S), pairMartingale U V T) - (0, pairMartingale U V r) =
        (0, pairMartingale U V T - pairMartingale U V r) := by ext <;> simp
    rw [hp]
    rw [liftedMetricBilinear_noise]
    exact martingale_orthogonal_local D.samplerWeight D.sampler_symmetric
      (U.drift r - V.drift r) (pairMartingale U V r) (pairMartingale U V T)
      (U.noise - V.noise) hm hr.2 (hrep r (Ioc_subset_Icc_self hr))
      (hrep T ⟨hT, le_rfl⟩) (hbadapt r hr)
  · rw [liftedMetricBilinear_noise]
    exact hIso T ⟨hT, le_rfl⟩

/-- Source A3 yields true expected joint quadratic contraction for actual
integral martingale trajectories. Time L¹ drift and time L² diffusion
replace continuous coefficients and pointwise-in-time derivatives. -/
theorem pair_energy_decay (D : TwistedGeometry S Z)
    (U V : ModelIntegralTrajectory Q ℱ M T) (hT : 0 ≤ T)
    (hb : ∀ θ, Measurable (M.drift θ))
    (hσ : ∀ θ i, Measurable (fun z => M.diffusion θ z i))
    (ρ : ℝ) (hmono : TwistedJointMonotonicity M D ρ)
    (hIso : SynchronousIsometry D U V) :
    pairEnergy D U V T ≤ Real.exp (-2 * ρ * T) * pairEnergy D U V 0 := by
  apply integral_gronwall (pairEnergy D U V)
    (fun r => 2 * liftedMetricBilinear Q D (pairState U V r) (pairDrift U V r) +
      diffusionEnergy Q D.samplerWeight (pairDiffusion U V) r) hT
  · apply IntervalIntegrable.add _ (pairDiffusion_integrable D U V)
    exact (bilinear_continuous_integrable (liftedMetricBilinear Q D)
      (pairState U V) (pairDrift U V)
      (by simpa [uIcc_of_le hT] using pairState_continuous U V)
      (pairDrift_integrable U V)).const_mul 2
  · intro r hr
    exact pair_energy_integral D (U.restrict hr) (V.restrict hr) hr.1
      (fun s hs => hIso s ⟨hs.1, hs.2.trans hr.2⟩)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact pair_dissipation D U V hb hσ ρ hmono r (Ioc_subset_Icc_self hr)

/-- The actual joint optimizer/sampler RMS cost contracts at the paper's
condition-number rate. This is a fixed synchronous realization theorem;
realization of arbitrary prescribed initial couplings is a separate step. -/
theorem pair_rms_decay (D : TwistedGeometry S Z)
    (U V : ModelIntegralTrajectory Q ℱ M T) (hT : 0 ≤ T)
    (hb : ∀ θ, Measurable (M.drift θ))
    (hσ : ∀ θ i, Measurable (fun z => M.diffusion θ z i))
    (ρ : ℝ) (hmono : TwistedJointMonotonicity M D ρ)
    (hIso : SynchronousIsometry D U V) :
    Real.sqrt (liftedEuclideanSq Q (pairState U V T)) ≤
      Real.sqrt D.conditionNumber * Real.exp (-ρ * T) *
        Real.sqrt (liftedEuclideanSq Q (pairState U V 0)) := by
  have hd := pair_energy_decay D U V hT hb hσ ρ hmono hIso
  have hlo := liftedMetricBilinear_lower Q D (pairState U V T)
  have hup := liftedMetricBilinear_upper Q D (pairState U V 0)
  have hκ : 0 ≤ D.conditionNumber := le_trans (by norm_num : (0 : ℝ) ≤ 1) D.conditionNumber_ge_one
  have hn (x : S × Lp Z 2 Q) : 0 ≤ liftedEuclideanSq Q x := add_nonneg (sq_nonneg _) (sq_nonneg _)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (hn _), mul_pow, mul_pow, Real.sq_sqrt hκ, Real.sq_sqrt (hn _)]
  have he : Real.exp (-ρ * T) ^ 2 = Real.exp (-2 * ρ * T) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  apply (mul_le_mul_iff_of_pos_left D.lower_pos).mp
  have hupper := mul_le_mul_of_nonneg_left hup (Real.exp_pos (-2 * ρ * T)).le
  have heq : D.lower * (D.conditionNumber * Real.exp (-2 * ρ * T) *
      liftedEuclideanSq Q (pairState U V 0)) =
      Real.exp (-2 * ρ * T) * (D.upper * liftedEuclideanSq Q (pairState U V 0)) := by
    dsimp [TwistedGeometry.conditionNumber]
    field_simp [ne_of_gt D.lower_pos]
  rw [heq]
  exact hlo.trans (hd.trans hupper)

/-- The actual joint sampler law has exactly the realized L² coupling cost. -/
theorem samplerPairLaw_euclidean_integral (U V : Lp Z 2 Q) :
    (∫ zz, ‖zz.1 - zz.2‖ ^ 2 ∂samplerPairLaw Q U V) = ‖U - V‖ ^ 2 := by
  have hf : Continuous (fun zz : Z × Z => ‖zz.1 - zz.2‖ ^ 2) := by fun_prop
  rw [samplerPairLaw, integral_map
    ((Lp.aestronglyMeasurable U).aemeasurable.prodMk (Lp.aestronglyMeasurable V).aemeasurable)
    hf.aestronglyMeasurable, ProximalLangevin.lp_norm_sq_eq_integral Q (U - V)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub U V] with ω hω
  rw [hω]
  rfl

/-- Contraction is an actual joint-law RMS statement, rather than a
formal state-space norm that has not been identified with a coupling law. -/
theorem pair_joint_law_rms_decay (D : TwistedGeometry S Z)
    (U V : ModelIntegralTrajectory Q ℱ M T) (hT : 0 ≤ T)
    (hb : ∀ θ, Measurable (M.drift θ))
    (hσ : ∀ θ i, Measurable (fun z => M.diffusion θ z i))
    (ρ : ℝ) (hmono : TwistedJointMonotonicity M D ρ)
    (hIso : SynchronousIsometry D U V) :
    Real.sqrt (‖U.optimizer T - V.optimizer T‖ ^ 2 +
      ∫ zz, ‖zz.1 - zz.2‖ ^ 2 ∂samplerPairLaw Q (U.sampler T) (V.sampler T)) ≤
      Real.sqrt D.conditionNumber * Real.exp (-ρ * T) *
        Real.sqrt (‖U.optimizer 0 - V.optimizer 0‖ ^ 2 +
          ∫ zz, ‖zz.1 - zz.2‖ ^ 2 ∂samplerPairLaw Q (U.sampler 0) (V.sampler 0)) := by
  simpa only [samplerPairLaw_euclidean_integral, liftedEuclideanSq, pairState] using
    pair_rms_decay D U V hT hb hσ ρ hmono hIso

/-- The realized true marginal-law distance is bounded by contraction of
this actual initial coupling. The infimum over arbitrary initial couplings
requires a law-preserving realization construction separately. -/
theorem pair_law_distance_decay (D : TwistedGeometry S Z)
    (U V : ModelIntegralTrajectory Q ℱ M T) (hT : 0 ≤ T)
    (hb : ∀ θ, Measurable (M.drift θ))
    (hσ : ∀ θ i, Measurable (fun z => M.diffusion θ z i))
    (ρ : ℝ) (hmono : TwistedJointMonotonicity M D ρ)
    (hIso : SynchronousIsometry D U V) :
    optimizerLawDistance (U.optimizer T) (V.optimizer T)
      (Q.map (U.sampler T)) (Q.map (V.sampler T)) ≤
      Real.sqrt D.conditionNumber * Real.exp (-ρ * T) *
        Real.sqrt (liftedEuclideanSq Q (pairState U V 0)) := by
  let ν := Q.map (U.sampler T)
  let ν' := Q.map (V.sampler T)
  have hν : MemLp (fun z : Z => z) 2 ν :=
    (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).mpr
      (lp_law_second_moment Q _)
  have hν' : MemLp (fun z : Z => z) 2 ν' :=
    (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).mpr
      (lp_law_second_moment Q _)
  let c : ULA.Coupling ν ν' := ⟨samplerPairLaw Q (U.sampler T) (V.sampler T),
    (samplerPairLaw_coupling Q _ _).1, (samplerPairLaw_coupling Q _ _).2⟩
  have hc := coupling_difference_memLp ν ν' hν hν' c
  have hbnd := wasserstein_le_finite_coupling ν ν' c hc.eLpNorm_ne_top
  have hs := couplingCost_sq_eq_integral c.joint hc
  rw [samplerPairLaw_euclidean_integral] at hs
  apply le_trans _ (pair_rms_decay D U V hT hb hσ ρ hmono hIso)
  apply Real.sqrt_le_sqrt
  change ‖U.optimizer T - V.optimizer T‖ ^ 2 + ULA.wasserstein2Real ν ν' ^ 2 ≤
    ‖U.optimizer T - V.optimizer T‖ ^ 2 + ‖U.sampler T - V.sampler T‖ ^ 2
  apply add_le_add le_rfl
  rw [← hs]
  exact (sq_le_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).mpr hbnd

end PBGSO.IntegralModelContraction
