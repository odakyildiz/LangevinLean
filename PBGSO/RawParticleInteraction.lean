import PBGSO.RawDampedState
import PBGSO.RawParticleForcing
import PBGSO.IntegralForcedEnergy
import PBGSO.LinearGrowthMoment

/-! # Exact raw finite-particle interaction under genuine local Ito dynamics
Damped localizations derive the sharp energy bound before threshold removal.
No global drift moment, final work bound, energy identity or iid interacting
law is assumed.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators RealInnerProductSpace InnerProductSpace
namespace PBGSO.RawParticleInteraction
open FilteredBrownian ConstructedItoParticle
variable {S Θ Z X I Ω : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [MeasurableSpace Θ] [BorelSpace Θ] [SecondCountableTopology Θ]
  [Fintype I] [DecidableEq I]
  {Q : Measure Ω} [IsProbabilityMeasure Q] {N : ℕ} {T : ℝ≥0}
  {Driver : FilteredBrownian.Driver (I := Fin N × I) Q}
  {L : RawLocalDiffusion (Z := PairHilbert N S Z) Q Driver T}

/-- Original raw particle/copy strong equation with its literal physical
coefficients. All local stochastic noise is the actually constructed local
integral; the ordinary raw drift need only be pathwise time-L¹. -/
structure Data (M : Model S Θ Z X I) (ν : ℝ → Measure Z)
    (L : RawLocalDiffusion (Z := PairHilbert N S Z) Q Driver T)
    extends RawDampedState.Data L where
  drift_realizes : ∀ t ∈ Icc 0 (T : ℝ), ∀ᵐ ω ∂Q,
    pairEquiv N (drift t ω) = particleCopyDrift M N (ν t) t (pairEquiv N (state t ω))
  sigma_realizes : ∀ t ∈ Icc 0 (T : ℝ), ∀ ij : Fin N × I, ∀ᵐ ω ∂Q,
    pairEquiv N (L.sigma ij t ω) = particleCopyDiffusion M N (pairEquiv N (state t ω)) ij

namespace Data
variable {M : Model S Θ Z X I} {ν : ℝ → Measure Z} (U : Data M ν L)

def energy (G : TwistedGeometry S Z) (n : ℕ) (ρ r : ℝ) :=
  ∫ ω, ⟪U.toData.dampedState n ρ r ω, metricWeight N G (U.toData.dampedState n ρ r ω)⟫_ℝ ∂Q

def work (G : TwistedGeometry S Z) (n : ℕ) (ρ r : ℝ) :=
  2 * (∫ ω, ⟪U.toData.dampedState n ρ r ω, metricWeight N G (U.toData.dampedDrift n ρ r ω)⟫_ℝ ∂Q) +
    ∫ ω, ∑ ij : Fin N × I, ⟪L.stoppedSigma n ij r ω,metricWeight N G (L.stoppedSigma n ij r ω)⟫_ℝ ∂Q

/-- The original empirical joint condition controls the actual raw work
on the active region, and exact damping supplies dissipation after stopping. -/
theorem pointwise_forcing (G : TwistedGeometry S Z) (ρ : ℝ)
    (hmono : TwistedJointMonotonicity M G ρ) (hN : 0 < N)
    (LΨ : ℝ≥0) (sbar : ℝ → S)
    (hΨ : ∀ t ∈ Icc 0 (T : ℝ), ∀ s g g',
      ‖M.optimizer t s g - M.optimizer t s g'‖ ≤ (LΨ : ℝ) * ‖g-g'‖)
    (hbar : ∀ t ∈ Icc 0 (T : ℝ), ∀ᵐ ω ∂Q, (pairEquiv N (U.state t ω)).2.1 = sbar t)
    (n : ℕ) (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) :
    ∀ᵐ ω ∂Q,
      2 * ⟪U.toData.dampedState n ρ r ω,metricWeight N G (U.toData.dampedDrift n ρ r ω)⟫_ℝ +
        (∑ ij : Fin N × I, ⟪L.stoppedSigma n ij r ω,metricWeight N G (L.stoppedSigma n ij r ω)⟫_ℝ) ≤
      -2 * ρ * ⟪U.toData.dampedState n ρ r ω,metricWeight N G (U.toData.dampedState n ρ r ω)⟫_ℝ +
        2 * ((LΨ : ℝ) * Real.sqrt G.upper) *
          Real.sqrt ⟪U.toData.dampedState n ρ r ω,metricWeight N G (U.toData.dampedState n ρ r ω)⟫_ℝ *
          ‖referenceObservationError M N (ν r) (sbar r) (pairEquiv N (U.state r ω))‖ := by
  filter_upwards [U.drift_realizes r hr,ae_all_iff.mpr (U.sigma_realizes r hr),hbar r hr]
    with ω hb hσ hbopt
  have hc : U.toData.clampedState r ω = U.state r ω := by
    rw [RawDampedState.Data.clampedState,RawDampedState.timeClamp_eq T hr]
  have hd := damped_raw_particle_generator_forcing_le M G ρ hmono N hN (ν r) r (L.stop n ω)
    hr.1 LΨ (hΨ r hr) (sbar r) (fun r => U.toData.clampedState r ω) (fun r => U.drift r ω)
    (fun ij r => L.sigma ij r ω) (by rwa [hc]) (fun ij => by simpa only [hc] using hσ ij) (by rwa [hc])
  simpa only [RawDampedState.Data.dampedState,RawDampedState.Data.dampedDrift,
    RawLocalDiffusion.stoppedSigma,LocalizedDiffusion.stoppedField,hc] using hd

/-- Actual iid reference variance and Cauchy--Schwarz derive expected
forcing for the damped state; its reference cloud is never declared iid. -/
theorem forcing_dissipation [∀ t, IsProbabilityMeasure (ν t)]
    (G : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M G ρ) (hN : 0 < N)
    (LΨ : ℝ≥0) (V : ℝ) (hV : 0 ≤ V) (sbar : ℝ → S)
    (hΨ : ∀ t ∈ Icc 0 (T : ℝ), ∀ s g g',
      ‖M.optimizer t s g - M.optimizer t s g'‖ ≤ (LΨ : ℝ) * ‖g-g'‖)
    (hF : ∀ t ∈ Icc 0 (T : ℝ), MemLp (fun z => M.observation (M.parameter (sbar t)) (M.position z)) 2 (ν t))
    (hCloud : ∀ t ∈ Icc 0 (T : ℝ), Q.map (fun ω => (pairEquiv N (U.state t ω)).2.2) =
      Measure.pi (fun _ : Fin N => ν t))
    (hbar : ∀ t ∈ Icc 0 (T : ℝ), ∀ᵐ ω ∂Q, (pairEquiv N (U.state t ω)).2.1 = sbar t)
    (hVar : ∀ t ∈ Icc 0 (T : ℝ),
      (∫ z, ‖M.observation (M.parameter (sbar t)) (M.position z) - M.meanGradient (ν t) (sbar t)‖ ^ 2 ∂ν t) ≤ V)
    (n : ℕ) : ∀ᵐ r ∂volume.restrict (Ioc 0 (T : ℝ)),
      U.work G n ρ r ≤ -2 * ρ * U.energy G n ρ r +
        2 * ((LΨ : ℝ) * Real.sqrt G.upper * Real.sqrt (V / (N : ℝ))) * Real.sqrt (U.energy G n ρ r) := by
  have hiw := U.toData.work_product_integrable n hρ.le (metricWeight N G)
  have hid := rawDiffusion_weighted_integrable Q T (L.stoppedSigma n)
    (L.stoppedSigma_strong n) (L.stoppedSigma_square n) (metricWeight N G)
  filter_upwards [hiw.prod_right_ae,hid.prod_right_ae,ae_restrict_mem measurableSet_Ioc] with r hw hd hr
  have hr' := Ioc_subset_Icc_self hr
  have hh := raw_particle_expected_forcing_le Q M G N hN (ν r) (sbar r) (hF r hr')
    (U.state r) (U.toData.dampedState n ρ r)
    U.state_strong.of_uncurry_left.aestronglyMeasurable
    (U.toData.dampedState_strong n ρ).of_uncurry_left.aestronglyMeasurable
    (U.toData.dampedState_square n hρ.le r) (hCloud r hr') ρ LΨ V hV (hVar r hr')
    _ ((hw.const_mul 2).add hd) (U.pointwise_forcing G ρ hmono hN LΨ sbar hΨ hbar n r hr')
  simp only [Pi.add_apply] at hh
  rw [integral_add (hw.const_mul 2) hd,integral_const_mul] at hh
  exact hh

/-- Exact sharp interaction energy at every genuine damped localization.
Its integral equation and forcing inequality were both derived from the
original raw particle/copy coefficients. -/
theorem damped_forced_energy_bound [∀ t, IsProbabilityMeasure (ν t)]
    (G : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M G ρ) (hN : 0 < N)
    (LΨ : ℝ≥0) (V : ℝ) (hV : 0 ≤ V) (sbar : ℝ → S)
    (hΨ : ∀ t ∈ Icc 0 (T : ℝ), ∀ s g g',
      ‖M.optimizer t s g - M.optimizer t s g'‖ ≤ (LΨ : ℝ) * ‖g-g'‖)
    (hF : ∀ t ∈ Icc 0 (T : ℝ), MemLp (fun z => M.observation (M.parameter (sbar t)) (M.position z)) 2 (ν t))
    (hCloud : ∀ t ∈ Icc 0 (T : ℝ), Q.map (fun ω => (pairEquiv N (U.state t ω)).2.2) =
      Measure.pi (fun _ : Fin N => ν t))
    (hbar : ∀ t ∈ Icc 0 (T : ℝ), ∀ᵐ ω ∂Q, (pairEquiv N (U.state t ω)).2.1 = sbar t)
    (hVar : ∀ t ∈ Icc 0 (T : ℝ),
      (∫ z, ‖M.observation (M.parameter (sbar t)) (M.position z) - M.meanGradient (ν t) (sbar t)‖ ^ 2 ∂ν t) ≤ V)
    (hinit : ∀ᵐ ω ∂Q, (pairEquiv N (U.state 0 ω)).1 = (pairEquiv N (U.state 0 ω)).2)
    (n : ℕ) : Real.sqrt (U.energy G n ρ T) ≤
      ((LΨ : ℝ) * Real.sqrt G.upper * Real.sqrt (V / (N : ℝ))) / ρ * (1 - Real.exp (-ρ * T)) := by
  have he := U.toData.energy_integral n hρ.le (metricWeight N G) (metricWeight_symmetric N G)
  apply IntegralForcedEnergy.forced_energy_bound (U.energy G n ρ) (U.work G n ρ) T.coe_nonneg hρ
    (by positivity) he.1
  · intro r hr
    have hh := he.2 r.toNNReal (by rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ hr.1]; exact hr.2)
    simpa only [energy,work,Real.coe_toNNReal _ hr.1] using hh
  · intro r hr
    exact integral_nonneg (fun ω => raw_particle_energy_nonneg N G _)
  · apply integral_eq_zero_of_ae
    filter_upwards [hinit] with ω hω
    rw [RawDampedState.Data.dampedState_zero,metricWeight_inner,
      particleQuadraticBilinear_diag,hω]
    simp [particleCouplingEnergy,TwistedGeometry.optimizerSq,TwistedGeometry.samplerSq]
  · exact U.forcing_dissipation G ρ hρ hmono hN LΨ V hV sbar hΨ hF hCloud hbar hVar n

theorem forced_energy_bound [∀ t, IsProbabilityMeasure (ν t)]
    (G : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M G ρ) (hN : 0 < N)
    (LΨ : ℝ≥0) (V : ℝ) (hV : 0 ≤ V) (sbar : ℝ → S)
    (hΨ : ∀ t ∈ Icc 0 (T : ℝ), ∀ s g g',
      ‖M.optimizer t s g - M.optimizer t s g'‖ ≤ (LΨ : ℝ) * ‖g-g'‖)
    (hF : ∀ t ∈ Icc 0 (T : ℝ), MemLp (fun z => M.observation (M.parameter (sbar t)) (M.position z)) 2 (ν t))
    (hCloud : ∀ t ∈ Icc 0 (T : ℝ), Q.map (fun ω => (pairEquiv N (U.state t ω)).2.2) =
      Measure.pi (fun _ : Fin N => ν t))
    (hbar : ∀ t ∈ Icc 0 (T : ℝ), ∀ᵐ ω ∂Q, (pairEquiv N (U.state t ω)).2.1 = sbar t)
    (hVar : ∀ t ∈ Icc 0 (T : ℝ),
      (∫ z, ‖M.observation (M.parameter (sbar t)) (M.position z) - M.meanGradient (ν t) (sbar t)‖ ^ 2 ∂ν t) ≤ V)
    (hinit : ∀ᵐ ω ∂Q, (pairEquiv N (U.state 0 ω)).1 = (pairEquiv N (U.state 0 ω)).2)
 :
    Integrable (fun ω => particleQuadraticBilinear G N (pairEquiv N (U.state T ω)) (pairEquiv N (U.state T ω))) Q ∧
    Real.sqrt (∫ ω, particleQuadraticBilinear G N (pairEquiv N (U.state T ω)) (pairEquiv N (U.state T ω)) ∂Q) ≤
      ((LΨ : ℝ) * Real.sqrt G.upper * Real.sqrt (V / (N : ℝ))) / ρ * (1 - Real.exp (-ρ * T)) := by
  let R := ((LΨ : ℝ) * Real.sqrt G.upper * Real.sqrt (V / (N : ℝ))) / ρ * (1 - Real.exp (-ρ * T))
  have hExp : Real.exp (-ρ * T) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [T.coe_nonneg])
  have hR : 0 ≤ R := mul_nonneg (div_nonneg (by positivity) hρ.le) (sub_nonneg.mpr hExp)
  let a (n : ℕ) (ω : Ω) := Real.sqrt ⟪U.toData.dampedState n ρ T ω,
    metricWeight N G (U.toData.dampedState n ρ T ω)⟫_ℝ
  let aStar (ω : Ω) := Real.sqrt (particleQuadraticBilinear G N
    (pairEquiv N (U.state T ω)) (pairEquiv N (U.state T ω)))
  have ha (n : ℕ) : MemLp (a n) 2 Q := by
    have hi := raw_particle_energy_integrable Q N G (U.toData.dampedState n ρ T)
      (U.toData.dampedState_strong n ρ).of_uncurry_left.aestronglyMeasurable
      (U.toData.dampedState_square n hρ.le T)
    exact sqrt_energy_memLp Q _ hi.aestronglyMeasurable hi
      (fun ω => raw_particle_energy_nonneg N G _)
  have hnorm (n : ℕ) : ‖(ha n).toLp (a n)‖ ^ 2 = U.energy G n ρ T := by
    rw [LinearGrowthMoment.toLp_norm_sq Q _ (ha n)]
    apply integral_congr_ae
    exact Eventually.of_forall (fun ω => by
      simp only [a,Real.norm_eq_abs,sq_abs,Real.sq_sqrt (raw_particle_energy_nonneg N G _)])
  have hb (n : ℕ) : ‖(ha n).toLp (a n)‖ ^ 2 ≤ R ^ 2 := by
    rw [hnorm n]
    have hh := U.damped_forced_energy_bound G ρ hρ hmono hN LΨ V hV sbar hΨ hF hCloud hbar hVar hinit n
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg (U.energy G n ρ T)) hh 2
    have hEn : 0 ≤ U.energy G n ρ T := integral_nonneg (fun ω => raw_particle_energy_nonneg N G _)
    rw [Real.sq_sqrt hEn] at hsq
    exact hsq
  have hlim : ∀ᵐ ω ∂Q, Tendsto (fun n => a n ω) atTop (𝓝 (aStar ω)) := by
    apply Eventually.of_forall
    intro ω
    apply tendsto_const_nhds.congr'
    filter_upwards [U.toData.dampedState_eventually_original ρ T ⟨T.coe_nonneg,le_rfl⟩ ω] with n hn
    simp only [a,aStar,hn,metricWeight_inner]
  obtain ⟨hA,hAB⟩ := LinearGrowthMoment.localized_limit_memLp Q a aStar (sq_nonneg R) ha hb hlim
  have hraw : Integrable (fun ω => particleQuadraticBilinear G N
      (pairEquiv N (U.state T ω)) (pairEquiv N (U.state T ω))) Q := by
    have hi := (memLp_two_iff_integrable_sq_norm hA.aestronglyMeasurable).mp hA
    apply hi.congr
    exact Eventually.of_forall (fun ω => by
      simp only [aStar,Real.norm_eq_abs,sq_abs,Real.sq_sqrt (particleQuadratic_nonneg G N _)])
  have he : ‖hA.toLp aStar‖ ^ 2 = ∫ ω, particleQuadraticBilinear G N
      (pairEquiv N (U.state T ω)) (pairEquiv N (U.state T ω)) ∂Q := by
    rw [LinearGrowthMoment.toLp_norm_sq Q aStar hA]
    apply integral_congr_ae
    exact Eventually.of_forall (fun ω => by
      simp only [aStar,Real.norm_eq_abs,sq_abs,Real.sq_sqrt (particleQuadratic_nonneg G N _)])
  refine ⟨hraw, ?_⟩
  rw [← he,Real.sqrt_sq (norm_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) hR).mp hAB

theorem finite_particle_interaction_bound [∀ t, IsProbabilityMeasure (ν t)]
    (G : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M G ρ) (hN : 0 < N)
    (LΨ : ℝ≥0) (V : ℝ) (hV : 0 ≤ V) (sbar : ℝ → S)
    (hΨ : ∀ t ∈ Icc 0 (T : ℝ), ∀ s g g',
      ‖M.optimizer t s g - M.optimizer t s g'‖ ≤ (LΨ : ℝ) * ‖g-g'‖)
    (hF : ∀ t ∈ Icc 0 (T : ℝ), MemLp (fun z => M.observation (M.parameter (sbar t)) (M.position z)) 2 (ν t))
    (hCloud : ∀ t ∈ Icc 0 (T : ℝ), Q.map (fun ω => (pairEquiv N (U.state t ω)).2.2) =
      Measure.pi (fun _ : Fin N => ν t))
    (hbar : ∀ t ∈ Icc 0 (T : ℝ), ∀ᵐ ω ∂Q, (pairEquiv N (U.state t ω)).2.1 = sbar t)
    (hVar : ∀ t ∈ Icc 0 (T : ℝ),
      (∫ z, ‖M.observation (M.parameter (sbar t)) (M.position z) - M.meanGradient (ν t) (sbar t)‖ ^ 2 ∂ν t) ≤ V)
    (hinit : ∀ᵐ ω ∂Q, (pairEquiv N (U.state 0 ω)).1 = (pairEquiv N (U.state 0 ω)).2)
 :
    Real.sqrt (∫ ω, particleEmpiricalDistanceSq N (pairEquiv N (U.state T ω)) ∂Q) ≤
      ((LΨ : ℝ) / ρ) * Real.sqrt (G.conditionNumber * V / (N : ℝ)) *
        (1 - Real.exp (-ρ * T)) := by
  obtain ⟨hraw,hE⟩ := U.forced_energy_bound G ρ hρ hmono hN LΨ V hV sbar hΨ hF hCloud hbar hVar hinit
  let p : Ω → ParticlePair N S Z := fun ω => pairEquiv N (U.state T ω)
  let Γ := Q.map p
  have hp : Measurable p := (pairEquiv N).continuous.measurable.comp U.state_strong.of_uncurry_left.measurable
  have hq : Measurable (fun p : ParticlePair N S Z => particleQuadraticBilinear G N p p) :=
    (IntegralParticleBound.quadratic_continuous (particleQuadraticBilinear G N)).measurable
  have hqΓ : Integrable (fun p => particleQuadraticBilinear G N p p) Γ :=
    (integrable_map_measure hq.aestronglyMeasurable hp.aemeasurable).mpr hraw
  have hm := particle_empirical_rms_le_energy G N hN Γ hqΓ
    (EmpiricalTransportMeasurable.particleEmpiricalDistanceSq_aestronglyMeasurable N hN Γ)
  rw [integral_map hp.aemeasurable
      (EmpiricalTransportMeasurable.particleEmpiricalDistanceSq_measurable N hN).aestronglyMeasurable,
    integral_map hp.aemeasurable hq.aestronglyMeasurable] at hm
  have he := div_le_div_of_nonneg_right hE (Real.sqrt_nonneg G.lower)
  have hκ : 0 ≤ G.conditionNumber := le_trans (by norm_num : (0 : ℝ) ≤ 1) G.conditionNumber_ge_one
  have hs : Real.sqrt (G.conditionNumber * V / (N : ℝ)) =
      (Real.sqrt G.upper / Real.sqrt G.lower) * Real.sqrt (V / (N : ℝ)) := by
    rw [show G.conditionNumber * V / (N : ℝ) = G.conditionNumber * (V / (N : ℝ)) by ring,
      Real.sqrt_mul hκ,G.sqrt_conditionNumber]
  apply hm.trans (he.trans_eq ?_)
  rw [hs]
  ring

end Data
end PBGSO.RawParticleInteraction
