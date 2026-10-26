import PBGSO.ConstructedItoModel
import PBGSO.IntegralParticleBound
import PBGSO.ParameterBound
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Original particle/copy dynamics with computed Brownian integrals
The raw particle coordinates are transported through an explicit Hilbert
encoding. Original coefficient identities, actual completed integrals and
finite Brownian drivers derive all martingale/isometry inputs of the
integral finite-particle theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option maxRecDepth 2000
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace InnerProductSpace
namespace PBGSO.ConstructedItoParticle
open FilteredBrownian QuadraticMartingale IntegralParticleBound

variable {S Z : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]

abbrev OneHilbert (N : ℕ) (S Z : Type*) := WithLp 2 (S × PiLp 2 (fun _ : Fin N => Z))
abbrev PairHilbert (N : ℕ) (S Z : Type*) := WithLp 2 (OneHilbert N S Z × OneHilbert N S Z)

/-- The exact Hilbert/sup-norm coordinate equivalence for one full particle state. -/
def oneEquiv (N : ℕ) : OneHilbert N S Z ≃L[ℝ] (S × (Fin N → Z)) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ S (PiLp 2 (fun _ : Fin N => Z))).trans
    (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ S)
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => Z)))

/-- Explicit invertible encoding of both original full particle states. -/
def pairEquiv (N : ℕ) : PairHilbert N S Z ≃L[ℝ] ParticlePair N S Z :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (OneHilbert N S Z) (OneHilbert N S Z)).trans
    (ContinuousLinearEquiv.prodCongr (oneEquiv N) (oneEquiv N))

def optimizerProjection (N : ℕ) : PairHilbert N S Z →L[ℝ] S :=
  (particleOptimizerDifference N).comp (pairEquiv (S := S) (Z := Z) N).toContinuousLinearMap

def samplerProjection (N : ℕ) (i : Fin N) : PairHilbert N S Z →L[ℝ] Z :=
  (particleSamplerDifference N i).comp (pairEquiv (S := S) (Z := Z) N).toContinuousLinearMap

/-- The actual normalized metric operator on Hilbert coordinates. It may
be semidefinite because equal interacting/reference states have zero cost. -/
def metricWeight (N : ℕ) (G : TwistedGeometry S Z) : PairHilbert N S Z →L[ℝ] PairHilbert N S Z :=
  (optimizerProjection (S := S) (Z := Z) N).adjoint.comp (G.optimizerWeight.comp (optimizerProjection (S := S) (Z := Z) N)) +
    (N : ℝ)⁻¹ • ∑ i : Fin N,
      (samplerProjection (S := S) (Z := Z) N i).adjoint.comp (G.samplerWeight.comp (samplerProjection (S := S) (Z := Z) N i))

theorem metricWeight_inner (N : ℕ) (G : TwistedGeometry S Z) (x y : PairHilbert N S Z) :
    ⟪x, metricWeight N G y⟫_ℝ =
      particleQuadraticBilinear G N (pairEquiv N x) (pairEquiv N y) := by
  simp only [metricWeight, add_apply, ContinuousLinearMap.comp_apply,
    smul_apply, sum_apply,
    inner_add_right, inner_smul_right, inner_sum]
  rw [(optimizerProjection (S := S) (Z := Z) N).adjoint_inner_right]
  simp_rw [(samplerProjection (S := S) (Z := Z) N _).adjoint_inner_right]
  rw [particleQuadraticBilinear_apply]
  rfl

theorem metricWeight_symmetric (N : ℕ) (G : TwistedGeometry S Z) :
    ∀ x y, ⟪x, metricWeight N G y⟫_ℝ = ⟪metricWeight N G x, y⟫_ℝ := by
  intro x y
  rw [metricWeight_inner, ← real_inner_comm (metricWeight N G x) y, metricWeight_inner]
  exact particleQuadraticBilinear_symmetric G N _ _

variable {Ω : Type*} [MeasurableSpace Ω]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- The Hilbert operator is exactly the original normalized L² particle
metric after the proved coordinate transport. -/
theorem particleBilinear_transport (N : ℕ) (G : TwistedGeometry S Z)
    (U V : Lp (PairHilbert N S Z) 2 Q) :
    particleBilinear Q N G ((pairEquiv (S := S) (Z := Z) N).toContinuousLinearMap.compLpL 2 Q U)
      ((pairEquiv (S := S) (Z := Z) N).toContinuousLinearMap.compLpL 2 Q V) =
      weightedPairing Q (metricWeight N G) U V := by
  rw [particleBilinear_integral, weightedPairing_apply, lp_weighted_pairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [(pairEquiv (S := S) (Z := Z) N).toContinuousLinearMap.coeFn_compLpL U,
    (pairEquiv (S := S) (Z := Z) N).toContinuousLinearMap.coeFn_compLpL V] with ω hu hv
  rw [hu, hv]
  exact (metricWeight_inner N G _ _).symm

section GeneralIntegral
variable {K H E F : Type*} [Fintype K] [DecidableEq K]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- Single-integral weighted isometry of the actual constructed Brownian
noise, directly from its completion norm identity. -/
theorem computed_isometry (Driver : Driver (I := K) Q) (T : ℝ≥0)
    (u : ℝ → ColumnHilbert (I := K) (Z := H) Q) (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[Driver.filtration t] (u t i) Q)
    (W : H →L[ℝ] H) (hW : ∀ x y, ⟪x, W y⟫_ℝ = ⟪W x, y⟫_ℝ)
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    weightedPairing Q W (ConstructedItoModel.integral Q Driver T u hu hU t)
      (ConstructedItoModel.integral Q Driver T u hu hU t) =
      ∫ r in 0..t, ∑ i, weightedPairing Q W (u r i) (u r i) := by
  have he := stochasticIntegral_weighted Q Driver W hW (GridIntegralCompletion.dyadicGrids T)
    (continuousCutDomain Q Driver T u hu hU t.toNNReal)
  change weightedPairing Q W (ConstructedItoModel.integral Q Driver T u hu hU t)
    (ConstructedItoModel.integral Q Driver T u hu hU t) = _ at he
  rw [continuousCutDomain_eq_timeCut, timeCut_weighted, Real.coe_toNNReal _ ht.1] at he
  rw [he, intervalIntegral.integral_of_le ht.1]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (continuousDomain_coe Q Driver T u hu hU),
    ae_restrict_mem measurableSet_Ioc] with r hr hrt
  have hR : r ∈ Ioc 0 (T : ℝ) := ⟨hrt.1, hrt.2.trans ht.2⟩
  rw [Set.indicator_of_mem hR] at hr
  rw [hr]

/-- Continuous linear maps between complete Banach spaces preserve actual
martingales, including the original raw particle product coordinates. -/
theorem martingale_banach_map [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (P : E →L[ℝ] F)
    (m : ℝ → Ω → E) (hm : Martingale m ℱ Q) :
    Martingale (fun t => P ∘ m t) ℱ Q := by
  constructor
  · intro t
    exact P.continuous.comp_stronglyMeasurable (hm.stronglyAdapted t)
  · intro s t hst
    exact (P.comp_condExp_comm (hm.integrable t)).symm.trans
      ((hm.condExp_ae_eq hst).fun_comp P)

end GeneralIntegral

variable {I Θ X : Type*} {N : ℕ} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace Θ] [BorelSpace Θ]
  (Driver : Driver (I := Fin N × I) Q) (M : Model S Θ Z X I)
  (ν : ℝ → Measure Z) (T : ℝ≥0)

/-- Original full particle/copy integral equations driven by the actual
completed finite-column Brownian integral. The exact Hilbert encoding is
fixed by pairEquiv; no martingale, isometry or energy bound is an input. -/
structure Data where
  state : ℝ → Lp (ParticlePair N S Z) 2 Q
  drift : ℝ → Lp (ParticlePair N S Z) 2 Q
  diffusion : ℝ → ColumnHilbert (I := Fin N × I) (Z := PairHilbert N S Z) Q
  drift_integrable : IntervalIntegrable drift volume 0 (T : ℝ)
  diffusion_continuous : Continuous diffusion
  state_adapted : ∀ t : ℝ≥0, AEStronglyMeasurable[Driver.filtration t] (state t) Q
  diffusion_adapted : ∀ t : ℝ≥0, ∀ ij,
    AEStronglyMeasurable[Driver.filtration t] (diffusion t ij) Q
  integral_equation : ∀ t ∈ Icc 0 (T : ℝ), state t = state 0 + (∫ r in 0..t, drift r) +
    (pairEquiv (S := S) (Z := Z) N).toContinuousLinearMap.compLpL 2 Q
      (ConstructedItoModel.integral Q Driver T diffusion diffusion_continuous diffusion_adapted t)
  drift_realizes : ∀ t ∈ Icc 0 (T : ℝ), drift t =ᵐ[Q]
    fun ω => particleCopyDrift M N (ν t) t (state t ω)
  diffusion_realizes : ∀ t ∈ Icc 0 (T : ℝ), ∀ ij,
    (pairEquiv (S := S) (Z := Z) N).toContinuousLinearMap.compLpL 2 Q (diffusion t ij) =ᵐ[Q]
      fun ω => particleCopyDiffusion M N (state t ω) ij
  drift_measurable : ∀ t ∈ Icc 0 (T : ℝ), Measurable (particleCopyDrift M N (ν t) t)
  diffusion_measurable : ∀ ij, Measurable (fun p => particleCopyDiffusion M N p ij)

variable {Q Driver M ν T}

def Data.physicalDiffusion (U : Data Q Driver M ν T) (t : ℝ) (ij : Fin N × I) :
    Lp (ParticlePair N S Z) 2 Q :=
  (pairEquiv (S := S) (Z := Z) N).toContinuousLinearMap.compLpL 2 Q (U.diffusion t ij)

def Data.noise (U : Data Q Driver M ν T) (t : ℝ) : Ω → ParticlePair N S Z :=
  (pairEquiv (S := S) (Z := Z) N).toContinuousLinearMap ∘
    ConstructedItoModel.noise Q Driver T U.diffusion U.diffusion_continuous U.diffusion_adapted t

theorem Data.continuous (U : Data Q Driver M ν T) : ContinuousOn U.state (Icc 0 (T : ℝ)) := by
  have hi := (IntegralQuadraticEnergy.integral_absolutelyContinuous U.drift U.drift_integrable).continuousOn
  rw [uIcc_of_le T.coe_nonneg] at hi
  have hnoise := ((pairEquiv (S := S) (Z := Z) N).toContinuousLinearMap.compLpL 2 Q).continuous.comp
    (ConstructedItoModel.integral_continuous Q Driver T U.diffusion U.diffusion_continuous U.diffusion_adapted)
  exact ((continuousOn_const.add hi).add hnoise.continuousOn).congr
    (fun t ht => U.integral_equation t ht)

theorem Data.diffusion_timeL2 (U : Data Q Driver M ν T) (ij : Fin N × I) :
    MemLp (fun r => U.physicalDiffusion r ij) 2 (volume.restrict (uIoc 0 (T : ℝ))) := by
  have hc : Continuous (fun r => U.diffusion r ij) :=
    (PiLp.continuous_apply 2 (fun _ : Fin N × I => Lp (PairHilbert N S Z) 2 Q) ij).comp
      U.diffusion_continuous
  obtain ⟨P, _, hP⟩ := TimeGridContinuity.exists_horizon_bound T _ hc
  have hm := TimeGridContinuity.horizon_memLp T _ hc.aestronglyMeasurable P hP
  rw [memLp_indicator_iff_restrict measurableSet_Ioc] at hm
  have hm' : MemLp (fun r => U.diffusion r ij) 2
      (volume.restrict (uIoc 0 (T : ℝ))) := by
    simpa only [uIoc_of_le T.coe_nonneg] using hm
  exact ((pairEquiv (S := S) (Z := Z) N).toContinuousLinearMap.compLpL 2 Q).comp_memLp' hm'

theorem Data.drift_adapted (U : Data Q Driver M ν T) (t : ℝ) (ht : t ∈ Ioc 0 (T : ℝ)) :
    AEStronglyMeasurable[ConstructedItoModel.realFiltration Q Driver t] (U.drift t) Q := by
  have hs : AEStronglyMeasurable[Driver.filtration t.toNNReal] (U.state t) Q := by
    simpa only [Real.coe_toNNReal _ ht.1.le] using U.state_adapted t.toNNReal
  have hd : AEStronglyMeasurable[Driver.filtration t.toNNReal]
      (fun ω => particleCopyDrift M N (ν t) t (U.state t ω)) Q := by
    refine ⟨particleCopyDrift M N (ν t) t ∘ hs.mk (U.state t), ?_, ?_⟩
    · exact ((U.drift_measurable t ⟨ht.1.le, ht.2⟩).comp hs.stronglyMeasurable_mk.measurable).stronglyMeasurable
    · filter_upwards [hs.ae_eq_mk] with ω hω
      exact congrArg (particleCopyDrift M N (ν t) t) hω
  exact hd.congr (U.drift_realizes t ⟨ht.1.le, ht.2⟩).symm

theorem Data.residual_eq (U : Data Q Driver M ν T) (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    driftResidual Q U.state U.drift t = (pairEquiv (S := S) (Z := Z) N).toContinuousLinearMap.compLpL 2 Q
      (ConstructedItoModel.integral Q Driver T U.diffusion U.diffusion_continuous U.diffusion_adapted t) := by
  dsimp only [driftResidual]
  rw [U.integral_equation t ht]
  abel

/-- All actual martingale and time-regularity fields are derived from the
original computed Brownian integral equation. -/
def Data.trajectory (U : Data Q Driver M ν T) :
    ParticleIntegralTrajectory Q N M ν T (ConstructedItoModel.realFiltration Q Driver) where
  state := U.state
  drift := U.drift
  diffusion := U.physicalDiffusion
  noise := U.noise
  continuous := U.continuous
  drift_integrable := U.drift_integrable
  diffusion_timeL2 := U.diffusion_timeL2
  drift_realizes := U.drift_realizes
  diffusion_realizes := U.diffusion_realizes
  drift_measurable := U.drift_measurable
  diffusion_measurable := U.diffusion_measurable
  martingale := by
    exact martingale_banach_map Q (pairEquiv (S := S) (Z := Z) N).toContinuousLinearMap _
      (ConstructedItoModel.noise_martingale Q Driver T U.diffusion U.diffusion_continuous U.diffusion_adapted)
  noise_realizes t ht := by
    have hn := ConstructedItoModel.noise_ae Q Driver T U.diffusion
      U.diffusion_continuous U.diffusion_adapted t
    have hc := (pairEquiv (S := S) (Z := Z) N).toContinuousLinearMap.coeFn_compLpL
      (ConstructedItoModel.integral Q Driver T U.diffusion U.diffusion_continuous U.diffusion_adapted t)
    rw [U.residual_eq t ht]
    filter_upwards [hn, hc] with ω hω hcω
    change (pairEquiv (S := S) (Z := Z) N)
      (ConstructedItoModel.noise Q Driver T U.diffusion U.diffusion_continuous U.diffusion_adapted t ω) = _
    rw [hω]
    exact hcω.symm
  initial_adapted := by
    change AEStronglyMeasurable[Driver.filtration (0 : ℝ).toNNReal] (U.state 0) Q
    rw [Real.toNNReal_zero]
    simpa only [NNReal.coe_zero] using U.state_adapted 0
  drift_adapted := U.drift_adapted

/-- The exact normalized synchronous isometry follows from the constructed
integral and proved Hilbert/raw coordinate metric identity. -/
theorem Data.synchronous_isometry (U : Data Q Driver M ν T) (G : TwistedGeometry S Z) :
    U.trajectory.SynchronousIsometry G := by
  intro t ht
  change particleBilinear Q N G (driftResidual Q U.state U.drift t)
    (driftResidual Q U.state U.drift t) = _
  rw [U.residual_eq t ht, particleBilinear_transport]
  rw [computed_isometry Q Driver T U.diffusion U.diffusion_continuous U.diffusion_adapted
    (metricWeight N G) (metricWeight_symmetric N G) t ht]
  apply intervalIntegral.integral_congr
  intro r _
  change (∑ ij, weightedPairing Q (metricWeight N G) (U.diffusion r ij) (U.diffusion r ij)) =
    ∑ ij, particleBilinear Q N G
      ((pairEquiv (S := S) (Z := Z) N).toContinuousLinearMap.compLpL 2 Q (U.diffusion r ij))
      ((pairEquiv (S := S) (Z := Z) N).toContinuousLinearMap.compLpL 2 Q (U.diffusion r ij))
  simp_rw [particleBilinear_transport]

/-- Actual fixed-time joint law of interacting particles and independent copies. -/
def Data.law (U : Data Q Driver M ν T) (t : ℝ) : Measure (ParticlePair N S Z) :=
  Q.map (U.state t)

instance Data.law_probability (U : Data Q Driver M ν T) (t : ℝ) :
    IsProbabilityMeasure (U.law t) := by
  exact (Measure.isProbabilityMeasure_map_iff (Lp.aestronglyMeasurable (U.state t)).aemeasurable).mpr inferInstance

/-- The actual completed Brownian integral supplies the synchronous isometry.
No martingale, quadratic energy identity or stochastic-isometry premise remains. -/
theorem Data.forced_energy_bound
    (U : Data Q Driver M ν T) (D : TwistedGeometry S Z)
    (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M D ρ) (LΨ : ℝ≥0) (V : ℝ) (hV : 0 ≤ V)
    (sbar : ℝ → S)
    (hν : ∀ r ∈ Icc 0 (T : ℝ), IsProbabilityMeasure (ν r))
    (hF : ∀ r ∈ Icc 0 (T : ℝ),
      MemLp (fun z => M.observation (M.parameter (sbar r)) (M.position z)) 2 (ν r))
    (hCloud : ∀ r ∈ Icc 0 (T : ℝ),
      (U.law r).map (fun p => p.2.2) = Measure.pi (fun _ : Fin N => ν r))
    (hbar : ∀ r ∈ Icc 0 (T : ℝ), ∀ᵐ p ∂U.law r, p.2.1 = sbar r)
    (hΨ : ∀ r ∈ Icc 0 (T : ℝ), ∀ s g g',
      ‖M.optimizer r s g - M.optimizer r s g'‖ ≤ (LΨ : ℝ) * ‖g - g'‖)
    (hVariance : ∀ r ∈ Icc 0 (T : ℝ),
      (∫ z, ‖M.observation (M.parameter (sbar r)) (M.position z) -
        M.meanGradient (ν r) (sbar r)‖ ^ 2 ∂ν r) ≤ V)
    (hSync : ∀ᵐ ω ∂Q, (U.state 0 ω).1 = (U.state 0 ω).2) :
    Real.sqrt (expectedParticleEnergy D N U.law T) ≤
      ((LΨ : ℝ) * Real.sqrt D.upper * Real.sqrt (V / (N : ℝ))) / ρ *
        (1 - Real.exp (-ρ * T)) := by
  exact U.trajectory.forced_energy_bound D T.coe_nonneg hN ρ hρ hmono LΨ V hV sbar
    hν hF hCloud hbar hΨ hVariance hSync (U.synchronous_isometry D)

/-- Source finite-particle interaction bound with the noise constructed from
finite Brownian columns. Only the reference cloud has the iid product law. -/
theorem Data.finite_particle_interaction_bound
    (U : Data Q Driver M ν T) (D : TwistedGeometry S Z)
    (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M D ρ) (LΨ : ℝ≥0) (V : ℝ) (hV : 0 ≤ V)
    (sbar : ℝ → S)
    (hν : ∀ r ∈ Icc 0 (T : ℝ), IsProbabilityMeasure (ν r))
    (hF : ∀ r ∈ Icc 0 (T : ℝ),
      MemLp (fun z => M.observation (M.parameter (sbar r)) (M.position z)) 2 (ν r))
    (hCloud : ∀ r ∈ Icc 0 (T : ℝ),
      (U.law r).map (fun p => p.2.2) = Measure.pi (fun _ : Fin N => ν r))
    (hbar : ∀ r ∈ Icc 0 (T : ℝ), ∀ᵐ p ∂U.law r, p.2.1 = sbar r)
    (hΨ : ∀ r ∈ Icc 0 (T : ℝ), ∀ s g g',
      ‖M.optimizer r s g - M.optimizer r s g'‖ ≤ (LΨ : ℝ) * ‖g - g'‖)
    (hVariance : ∀ r ∈ Icc 0 (T : ℝ),
      (∫ z, ‖M.observation (M.parameter (sbar r)) (M.position z) -
        M.meanGradient (ν r) (sbar r)‖ ^ 2 ∂ν r) ≤ V)
    (hSync : ∀ᵐ ω ∂Q, (U.state 0 ω).1 = (U.state 0 ω).2) :
    Real.sqrt (∫ p, particleEmpiricalDistanceSq N p ∂U.law T) ≤
      ((LΨ : ℝ) / ρ) * Real.sqrt (D.conditionNumber * V / (N : ℝ)) *
        (1 - Real.exp (-ρ * T)) := by
  exact U.trajectory.finite_particle_interaction_bound D T.coe_nonneg hN ρ hρ hmono LΨ V hV sbar
    hν hF hCloud hbar hΨ hVariance hSync (U.synchronous_isometry D)

/-- Parameter error of the actual interacting particle law. The triangle
inequality is proved on the actual joint law; deterministic mean-field
relaxation can subsequently be supplied by the constructed law contraction. -/
theorem Data.parameter_target_bound
    (U : Data Q Driver M ν T) (D : TwistedGeometry S Z)
    (hProjection : LipschitzWith 1 M.parameter) (sStar : S)
    (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M D ρ) (LΨ : ℝ≥0) (V : ℝ) (hV : 0 ≤ V)
    (sbar : ℝ → S)
    (hν : ∀ r ∈ Icc 0 (T : ℝ), IsProbabilityMeasure (ν r))
    (hF : ∀ r ∈ Icc 0 (T : ℝ),
      MemLp (fun z => M.observation (M.parameter (sbar r)) (M.position z)) 2 (ν r))
    (hCloud : ∀ r ∈ Icc 0 (T : ℝ),
      (U.law r).map (fun p => p.2.2) = Measure.pi (fun _ : Fin N => ν r))
    (hbar : ∀ r ∈ Icc 0 (T : ℝ), ∀ᵐ p ∂U.law r, p.2.1 = sbar r)
    (hΨ : ∀ r ∈ Icc 0 (T : ℝ), ∀ s g g',
      ‖M.optimizer r s g - M.optimizer r s g'‖ ≤ (LΨ : ℝ) * ‖g - g'‖)
    (hVariance : ∀ r ∈ Icc 0 (T : ℝ),
      (∫ z, ‖M.observation (M.parameter (sbar r)) (M.position z) -
        M.meanGradient (ν r) (sbar r)‖ ^ 2 ∂ν r) ≤ V)
    (hSync : ∀ᵐ ω ∂Q, (U.state 0 ω).1 = (U.state 0 ω).2) :
    MemLp (fun p : ParticlePair N S Z => M.parameter p.1.1 - M.parameter sStar) 2 (U.law T) ∧
    Real.sqrt (∫ p, ‖M.parameter p.1.1 - M.parameter sStar‖ ^ 2 ∂U.law T) ≤
      ((LΨ : ℝ) / ρ) * Real.sqrt (D.conditionNumber * V / (N : ℝ)) *
        (1 - Real.exp (-ρ * T)) + ‖sbar T - sStar‖ := by
  obtain ⟨hm, htriangle⟩ := PBGSO.parameter_target_rms_bound M D hProjection N
    (U.law T) (sbar T) sStar (hbar T ⟨T.coe_nonneg, le_rfl⟩)
    (U.trajectory.quadratic_integrable D T)
  refine ⟨hm, htriangle.trans (add_le_add ?_ le_rfl)⟩
  have hE := U.forced_energy_bound D hN ρ hρ hmono LΨ V hV sbar
    hν hF hCloud hbar hΨ hVariance hSync
  have he := div_le_div_of_nonneg_right hE (Real.sqrt_nonneg D.lower)
  have hκ : 0 ≤ D.conditionNumber := le_trans (by norm_num : (0 : ℝ) ≤ 1) D.conditionNumber_ge_one
  have hs : Real.sqrt (D.conditionNumber * V / (N : ℝ)) =
      (Real.sqrt D.upper / Real.sqrt D.lower) * Real.sqrt (V / (N : ℝ)) := by
    rw [show D.conditionNumber * V / (N : ℝ) = D.conditionNumber * (V / (N : ℝ)) by ring,
      Real.sqrt_mul hκ, D.sqrt_conditionNumber]
  apply he.trans_eq
  rw [hs]
  ring

end PBGSO.ConstructedItoParticle
