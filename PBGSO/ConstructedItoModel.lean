import PBGSO.FilteredIntegralContinuity
import PBGSO.IntegralModelContraction

/-! # General model contraction from the actually constructed Brownian integral
The stochastic noise is the completed integral of the original diffusion
columns. Its martingale property and synchronous isometry are derived.
Continuous L² diffusion columns specify this realization subclass explicitly;
no equivalence with the paper's minimal strong-SDE A1 is asserted here.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology RealInnerProductSpace InnerProductSpace
namespace PBGSO.ConstructedItoModel
open FilteredBrownian QuadraticMartingale
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

/-- The same actual filtration indexed by real time, constant before zero. -/
def realFiltration : Filtration ℝ mΩ where
  seq t := D.filtration t.toNNReal
  mono' _ _ h := D.filtration.mono (Real.toNNReal_mono h)
  le' t := D.filtration.le t.toNNReal

/-- The actual completed noise, indexed by real time. -/
def integral (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q) (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q) (t : ℝ) : Lp Z 2 Q :=
  continuousIntegral Q D T u hu hU t.toNNReal

/-- Actual adapted representatives of the completed noise. -/
def noise (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q) (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q) (t : ℝ) : Ω → Z :=
  MartingaleL2Limit.representative Q D.filtration
    (continuousIntegral Q D T u hu hU) t.toNNReal

theorem noise_martingale (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q) (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q) :
    Martingale (noise Q D T u hu hU) (realFiltration Q D) Q := by
  have hm := continuous_integral_martingale Q D T u hu hU
  exact ⟨fun t => hm.stronglyAdapted t.toNNReal,
    fun s t hst => hm.condExp_ae_eq (Real.toNNReal_mono hst)⟩

theorem noise_ae (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q) (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q) (t : ℝ) :
    noise Q D T u hu hU t =ᵐ[Q] integral Q D T u hu hU t :=
  continuous_integral_representative_ae Q D T u hu hU t.toNNReal

theorem integral_continuous (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q) (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q) :
    Continuous (integral Q D T u hu hU) :=
  (continuousIntegral_continuous Q D T u hu hU).comp continuous_real_toNNReal

/-- The initial Brownian integral is exactly zero in the actual L² space. -/
theorem integral_zero (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q) (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q) :
    integral Q D T u hu hU 0 = 0 := by
  have hz : (continuousCutDomain Q D T u hu hU 0).val = 0 := by
    apply Lp.ext
    filter_upwards [continuousCutDomain_coe Q D T u hu hU 0,
      Lp.coeFn_zero (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ)] with r hr hz
    rw [hr, hz]
    simp
  apply norm_eq_zero.mp
  simp only [integral, Real.toNNReal_zero, continuousIntegral]
  rw [stochasticIntegral_norm, hz, norm_zero]

/-- An exact synchronous difference isometry of two actually constructed
noise processes, with their original coefficient columns on the right. -/
theorem difference_isometry (T : ℝ≥0)
    (u v : ℝ → ColumnHilbert (I := I) (Z := Z) Q) (hu : Continuous u) (hv : Continuous v)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q)
    (hV : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (v t i) Q)
    (W : Z →L[ℝ] Z) (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    weightedPairing Q W (integral Q D T u hu hU t - integral Q D T v hv hV t)
      (integral Q D T u hu hU t - integral Q D T v hv hV t) =
      ∫ r in 0..t, diffusionEnergy Q W (fun r i => u r i - v r i) r := by
  have he := stochasticIntegral_sub_weighted Q D W hW (GridIntegralCompletion.dyadicGrids T)
    (continuousCutDomain Q D T u hu hU t.toNNReal)
    (continuousCutDomain Q D T v hv hV t.toNNReal)
  change weightedPairing Q W (integral Q D T u hu hU t - integral Q D T v hv hV t)
      (integral Q D T u hu hU t - integral Q D T v hv hV t) = _ at he
  rw [continuousCutDomain_eq_timeCut, continuousCutDomain_eq_timeCut,
    ← timeCut_subtract, timeCut_weighted, Real.coe_toNNReal _ ht.1] at he
  rw [he, intervalIntegral.integral_of_le ht.1]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (continuousDomain_coe Q D T u hu hU),
    ae_restrict_of_ae (continuousDomain_coe Q D T v hv hV),
    ae_restrict_of_ae (Lp.coeFn_sub (continuousDomain Q D T u hu hU).val
      (continuousDomain Q D T v hv hV).val), ae_restrict_mem measurableSet_Ioc]
    with r hU hV hsub hr
  have hR : r ∈ Ioc 0 (T : ℝ) := ⟨hr.1, hr.2.trans ht.2⟩
  rw [Set.indicator_of_mem hR] at hU hV
  rw [hsub, Pi.sub_apply, hU, hV]
  rfl



section Model
variable {S Θ X : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  (M : Model S Θ Z X I) (T : ℝ≥0)

/-- Original model integral equations driven by the actual completed Brownian
integral. No martingale, isometry, quadratic energy, weak generator, or
coefficient-dissipation conclusion is a field. The explicit regularity subclass
is time L¹ drift and continuous adapted L² diffusion columns. -/
structure Data where
  optimizer : ℝ → S
  optimizerDrift : ℝ → S
  sampler : ℝ → Lp Z 2 Q
  drift : ℝ → Lp Z 2 Q
  diffusion : ℝ → ColumnHilbert (I := I) (Z := Z) Q
  optimizerDrift_integrable : IntervalIntegrable optimizerDrift volume 0 (T : ℝ)
  drift_integrable : IntervalIntegrable drift volume 0 (T : ℝ)
  diffusion_continuous : Continuous diffusion
  sampler_adapted : ∀ t : ℝ≥0, AEStronglyMeasurable[D.filtration t] (sampler t) Q
  diffusion_adapted : ∀ t : ℝ≥0, ∀ i,
    AEStronglyMeasurable[D.filtration t] (diffusion t i) Q
  optimizerDrift_realizes : ∀ t ∈ Icc 0 (T : ℝ), optimizerDrift t =
    M.optimizerField t (optimizer t) (Q.map (sampler t))
  optimizer_integral : ∀ t ∈ Icc 0 (T : ℝ),
    optimizer t = optimizer 0 + ∫ r in 0..t, optimizerDrift r
  sampler_integral : ∀ t ∈ Icc 0 (T : ℝ),
    sampler t = sampler 0 + (∫ r in 0..t, drift r) +
      integral Q D T diffusion diffusion_continuous diffusion_adapted t
  drift_realizes : ∀ t ∈ Icc 0 (T : ℝ), drift t =ᵐ[Q]
    fun ω => M.drift (M.parameter (optimizer t)) (sampler t ω)
  diffusion_realizes : ∀ t ∈ Icc 0 (T : ℝ), ∀ i, diffusion t i =ᵐ[Q]
    fun ω => M.diffusion (M.parameter (optimizer t)) (sampler t ω) i
  observation_integrable : ∀ t ∈ Icc 0 (T : ℝ), Integrable
    (fun z => M.observation (M.parameter (optimizer t)) (M.position z)) (Q.map (sampler t))

variable {M T Q D}

theorem Data.optimizer_continuous (U : Data Q D M T) :
    ContinuousOn U.optimizer (Icc 0 (T : ℝ)) := by
  have hi := (IntegralQuadraticEnergy.integral_absolutelyContinuous U.optimizerDrift
    U.optimizerDrift_integrable).continuousOn
  rw [uIcc_of_le T.coe_nonneg] at hi
  have hc : ContinuousOn (fun t => U.optimizer 0 + ∫ r in 0..t, U.optimizerDrift r)
      (Icc 0 (T : ℝ)) := continuousOn_const.add hi
  exact hc.congr (fun t ht => U.optimizer_integral t ht)

theorem Data.sampler_continuous (U : Data Q D M T) :
    ContinuousOn U.sampler (Icc 0 (T : ℝ)) := by
  have hi := (IntegralQuadraticEnergy.integral_absolutelyContinuous U.drift
    U.drift_integrable).continuousOn
  rw [uIcc_of_le T.coe_nonneg] at hi
  have hc : ContinuousOn (fun t => U.sampler 0 + (∫ r in 0..t, U.drift r) +
      integral Q D T U.diffusion U.diffusion_continuous U.diffusion_adapted t)
      (Icc 0 (T : ℝ)) := (continuousOn_const.add hi).add
        (integral_continuous Q D T U.diffusion U.diffusion_continuous U.diffusion_adapted).continuousOn
  exact hc.congr (fun t ht => U.sampler_integral t ht)

theorem Data.diffusion_timeL2 (U : Data Q D M T) (i : I) :
    MemLp (fun r => U.diffusion r i) 2 (volume.restrict (uIoc 0 (T : ℝ))) := by
  have hc : Continuous (fun r => U.diffusion r i) :=
    (PiLp.continuous_apply 2 (fun _ : I => Lp Z 2 Q) i).comp U.diffusion_continuous
  obtain ⟨P, _, hP⟩ := TimeGridContinuity.exists_horizon_bound T _ hc
  have hm := TimeGridContinuity.horizon_memLp T _ hc.aestronglyMeasurable P hP
  rw [memLp_indicator_iff_restrict measurableSet_Ioc] at hm
  simpa only [uIoc_of_le T.coe_nonneg] using hm

theorem Data.drift_adapted (U : Data Q D M T) (hb : ∀ θ, Measurable (M.drift θ))
    (t : ℝ) (ht : t ∈ Ioc 0 (T : ℝ)) :
    AEStronglyMeasurable[realFiltration Q D t] (U.drift t) Q := by
  have hs : AEStronglyMeasurable[D.filtration t.toNNReal] (U.sampler t) Q := by
    simpa only [Real.coe_toNNReal _ ht.1.le] using U.sampler_adapted t.toNNReal
  have hd : AEStronglyMeasurable[D.filtration t.toNNReal]
      (fun ω => M.drift (M.parameter (U.optimizer t)) (U.sampler t ω)) Q := by
    refine ⟨M.drift (M.parameter (U.optimizer t)) ∘ hs.mk (U.sampler t), ?_, ?_⟩
    · exact ((hb _).comp hs.stronglyMeasurable_mk.measurable).stronglyMeasurable
    · exact hs.ae_eq_mk.fun_comp _
  exact hd.congr (U.drift_realizes t ⟨ht.1.le, ht.2⟩).symm

/-- The original actual integral equation identifies the completed noise
with the genuine sampler drift residual. -/
theorem Data.residual_eq (U : Data Q D M T) (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    martingaleResidual Q U.sampler U.drift t =
      integral Q D T U.diffusion U.diffusion_continuous U.diffusion_adapted t := by
  dsimp only [martingaleResidual]
  rw [U.sampler_integral t ht]
  abel

/-- Actual integral model data produce the martingale trajectory interface,
with all stochastic and state-continuity fields proved. -/
def Data.trajectory (U : Data Q D M T) (hb : ∀ θ, Measurable (M.drift θ)) :
    IntegralModelContraction.ModelIntegralTrajectory Q (realFiltration Q D) M T where
  optimizer := U.optimizer
  optimizerDrift := U.optimizerDrift
  sampler := U.sampler
  drift := U.drift
  diffusion t i := U.diffusion t i
  noise := noise Q D T U.diffusion U.diffusion_continuous U.diffusion_adapted
  optimizer_continuous := U.optimizer_continuous
  sampler_continuous := U.sampler_continuous
  optimizerDrift_integrable := U.optimizerDrift_integrable
  drift_integrable := U.drift_integrable
  diffusion_timeL2 := U.diffusion_timeL2
  optimizerDrift_realizes := U.optimizerDrift_realizes
  optimizer_integral := U.optimizer_integral
  drift_realizes := U.drift_realizes
  diffusion_realizes := U.diffusion_realizes
  martingale := noise_martingale Q D T U.diffusion U.diffusion_continuous U.diffusion_adapted
  noise_realizes t ht := (noise_ae Q D T U.diffusion U.diffusion_continuous U.diffusion_adapted t).trans
    (by rw [U.residual_eq t ht])
  initial_adapted := by
    change AEStronglyMeasurable[D.filtration (0 : ℝ).toNNReal] (U.sampler 0) Q
    rw [Real.toNNReal_zero]
    simpa only [NNReal.coe_zero] using U.sampler_adapted 0
  drift_adapted := U.drift_adapted hb
  observation_integrable := U.observation_integrable

/-- Synchronous isometry is a theorem of the original constructed integral
equations; it is no longer a supplied stochastic-interface premise. -/
theorem synchronous_isometry (G : TwistedGeometry S Z) (U V : Data Q D M T)
    (hb : ∀ θ, Measurable (M.drift θ)) :
    IntegralModelContraction.SynchronousIsometry G (U.trajectory hb) (V.trajectory hb) := by
  intro t ht
  change weightedPairing Q G.samplerWeight
      (martingaleResidual Q U.sampler U.drift t - martingaleResidual Q V.sampler V.drift t)
      (martingaleResidual Q U.sampler U.drift t - martingaleResidual Q V.sampler V.drift t) = _
  rw [U.residual_eq t ht, V.residual_eq t ht]
  exact difference_isometry Q D T U.diffusion V.diffusion U.diffusion_continuous
    V.diffusion_continuous U.diffusion_adapted V.diffusion_adapted
    G.samplerWeight G.sampler_symmetric t ht

/-- Actual optimizer/sampler marginal-law contraction for original model
integral equations driven by constructed Brownian integrals. All noise
martingale and synchronous moment identities are proved internally. -/
theorem law_distance_decay (G : TwistedGeometry S Z) (U V : Data Q D M T)
    (hb : ∀ θ, Measurable (M.drift θ))
    (hσ : ∀ θ i, Measurable (fun z => M.diffusion θ z i))
    (ρ : ℝ) (hmono : TwistedJointMonotonicity M G ρ) :
    optimizerLawDistance (U.optimizer T) (V.optimizer T)
      (Q.map (U.sampler T)) (Q.map (V.sampler T)) ≤
      Real.sqrt G.conditionNumber * Real.exp (-ρ * T) *
        Real.sqrt (‖U.optimizer 0 - V.optimizer 0‖ ^ 2 + ‖U.sampler 0 - V.sampler 0‖ ^ 2) := by
  exact IntegralModelContraction.pair_law_distance_decay G (U.trajectory hb) (V.trajectory hb)
    T.coe_nonneg hb hσ ρ hmono (synchronous_isometry G U V hb)

end Model
end PBGSO.ConstructedItoModel
