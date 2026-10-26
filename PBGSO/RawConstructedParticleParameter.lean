import PBGSO.RawConstructedParticleBounds
import PBGSO.RawNaturalConstantArbitraryLaw
import PBGSO.RawSamplerGrowthArbitraryLaw

/-! # Exact parameter bounds for the original constructed particle system
The original empirical strong solution is paired internally with independent
reference seeds. Physical coefficients, reference-cloud iid law, optimizer
matching, and local stochastic compatibility are proved by construction.
Source response/variance assumptions justify the constant-noise relaxation;
no paired-data record, final law bound or work hypothesis is an input.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.RawConstructedParticleParameter
open FilteredBrownian RawLocalStationarity RawConstructedParticleCopy ConstructedItoParticle ConstructedItoLaw
variable {Ω S Θ Z X I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace Θ] [BorelSpace Θ] [SecondCountableTopology Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (W : Driver (I := I) Q)
  {M : Model S Θ Z X I} {T : ℝ≥0} {N : ℕ}

/-- Particle interaction controls the actual native parameter. The paired
strong equation, iid reference law and all matching identities are built
inside this proof from the original empirical solution and primitive Borel
fields. -/
private theorem native_parameter_bias_bound
    (U : RawLocalStationarity.Data Q W M T)
    (Y : RawEmpiricalDynamics.Solution M N (IndependentCopies.seeds (J := Fin N) Q)
      (RawIndependentCopies.driver Q W N) T)
    (G : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M G ρ) (hN : 0 < N)
    (hProjection : LipschitzWith 1 M.parameter)
    (hF : Measurable (fun p : S × Z => M.observation (M.parameter p.1) (M.position p.2)))
    (hDrift : Measurable (fun p : S × Z => M.drift (M.parameter p.1) p.2))
    (hOptimizer : Measurable (fun p : ℝ × (S × Θ) => M.optimizer p.1 p.2.1 p.2.2))
    (LΨ : ℝ≥0) (VF : ℝ) (hVF : 0 ≤ VF) (sStar : S)
    (hΨ : ∀ r ∈ Icc 0 (T : ℝ), ∀ s g g',
      ‖M.optimizer r s g-M.optimizer r s g'‖ ≤ (LΨ : ℝ)*‖g-g'‖)
    (hU2 : ∀ r ∈ Icc 0 (T : ℝ), MemLp
      (fun z => M.observation (M.parameter (U.optimizer r)) (M.position z)) 2 (Q.map (U.sampler.state r)))
    (hVar : ∀ r ∈ Icc 0 (T : ℝ),
      (∫ z, ‖M.observation (M.parameter (U.optimizer r)) (M.position z)-
        M.meanGradient (Q.map (U.sampler.state r)) (U.optimizer r)‖^2 ∂Q.map (U.sampler.state r)) ≤ VF)
    (hinit : ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q,
      oneEquiv N (Y.state 0 ω) = (U.optimizer 0,RawIndependentCopies.cloud Q W N U 0 ω)) :
    MemLp (fun ω => M.parameter (oneEquiv N (Y.state T ω)).1-M.parameter sStar)
      2 (IndependentCopies.seeds (J := Fin N) Q) ∧
    Real.sqrt (∫ ω, ‖M.parameter (oneEquiv N (Y.state T ω)).1-M.parameter sStar‖^2
      ∂IndependentCopies.seeds (J := Fin N) Q) ≤
      ((LΨ : ℝ)/ρ)*Real.sqrt (G.conditionNumber*VF/(N : ℝ))*(1-Real.exp (-ρ*T))+
        ‖U.optimizer T-sStar‖ := by
  let C := build Q W M N U Y hF hDrift hOptimizer
  have hF' : ∀ r ∈ Icc 0 (T : ℝ), MemLp
      (fun z => M.observation (M.parameter (U.optimizer r)) (M.position z)) 2 (referenceLaw Q W M U r) := by
    intro r hr
    rw [referenceLaw_eq Q W M U r hr]
    exact hU2 r hr
  have hVar' : ∀ r ∈ Icc 0 (T : ℝ),
      (∫ z, ‖M.observation (M.parameter (U.optimizer r)) (M.position z)-
        M.meanGradient (referenceLaw Q W M U r) (U.optimizer r)‖^2 ∂referenceLaw Q W M U r) ≤ VF := by
    intro r hr
    rw [referenceLaw_eq Q W M U r hr]
    exact hVar r hr
  obtain ⟨hm,hb⟩ := RawParticleParameter.parameter_bias_bound C.data G ρ hρ hmono hN
    hProjection LΨ VF hVF U.optimizer sStar hΨ hF'
    (RawConstructedParticleBounds.reference_cloud_law Q W M N U Y C)
    (RawConstructedParticleBounds.reference_optimizer Q W M N U Y C) hVar'
    (RawConstructedParticleBounds.initial_coupling Q W M N U Y C hinit)
  have he : (fun ω => M.parameter (pairEquiv N (C.data.state T ω)).1.1-M.parameter sStar) =ᵐ[
      IndependentCopies.seeds (J := Fin N) Q]
      (fun ω => M.parameter (oneEquiv N (Y.state T ω)).1-M.parameter sStar) := by
    filter_upwards [C.interacting_state] with ω h
    rw [h T ⟨T.coe_nonneg,le_rfl⟩]
  refine ⟨(memLp_congr_ae he).mp hm,?_⟩
  have hi : (∫ ω, ‖M.parameter (pairEquiv N (C.data.state T ω)).1.1-M.parameter sStar‖^2
      ∂IndependentCopies.seeds (J := Fin N) Q) =
      ∫ ω, ‖M.parameter (oneEquiv N (Y.state T ω)).1-M.parameter sStar‖^2
        ∂IndependentCopies.seeds (J := Fin N) Q :=
    integral_congr_ae (he.fun_comp (fun z => ‖z‖^2))
  rwa [hi] at hb

/-- Source4's exact bound for the ORIGINAL native empirical solution.
Original mean-field and particle strong equations, their synchronous initial
conditions, primitive Borel coefficients, source A3/A4/A5, and actual A1
canonical/path-source existence/uniqueness instances are the inputs. There
is no paired equation, reference iid/matching premise, drift-growth or
positive-work assumption. The relaxation prefactor is the true initial law
distance. -/
theorem original_parameter_bound_constant
    (U : RawLocalStationarity.Data Q W M T)
    (Y : RawEmpiricalDynamics.Solution M N (IndependentCopies.seeds (J := Fin N) Q)
      (RawIndependentCopies.driver Q W N) T)
    (μ νStar : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure νStar]
    (hμ : MemLp (fun z : Z => z) 2 μ) (hν : MemLp (fun z : Z => z) 2 νStar)
    (hUlaw : Q.map (U.sampler.state 0) = μ)
    (A : RawLocalStationarity.Data (μ.prod (brownianProbability (I := I)))
      (CanonicalBrownianDriver.driver (I := I) μ) M T)
    (hA0 : A.optimizer 0 = U.optimizer 0)
    (hAz : A.sampler.state 0 =ᵐ[μ.prod (brownianProbability (I := I))] Prod.fst)
    (V : RawLocalStationarity.Data (νStar.prod (brownianProbability (I := I)))
      (CanonicalBrownianDriver.driver (I := I) νStar) M T)
    (hVz : V.sampler.state 0 =ᵐ[νStar.prod (brownianProbability (I := I))] Prod.fst)
    (huniqueU : PathwiseUniqueness Q (nullAugmentedDriver Q (continuousDriver Q W)) M T)
    (huniqueA : PathwiseUniqueness (μ.prod (brownianProbability (I := I)))
      (nullAugmentedDriver _ (continuousDriver _ (CanonicalBrownianDriver.driver (I := I) μ))) M T)
    (hpath : ∃ B : RawLocalStationarity.Data (BrownianPathDriver.probability (I := I) μ)
        (BrownianPathDriver.driver μ) M T,
      B.optimizer 0 = U.optimizer 0 ∧
      B.sampler.state 0 =ᵐ[BrownianPathDriver.probability (I := I) μ] Prod.fst)
    (G : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M G ρ) (hN : 0 < N)
    (hProjection : LipschitzWith 1 M.parameter)
    (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i)
    (hb : ∀ θ, Measurable (M.drift θ))
    (hF : Measurable (fun p : S × Z => M.observation (M.parameter p.1) (M.position p.2)))
    (hDrift : Measurable (fun p : S × Z => M.drift (M.parameter p.1) p.2))
    (hOptimizer : Measurable (fun p : ℝ × (S × Θ) => M.optimizer p.1 p.2.1 p.2.2))
    (LΨ : ℝ≥0) (VF : ℝ)
    (hΨ : ∀ r ∈ Icc 0 (T : ℝ), ∀ s g g',
      ‖M.optimizer r s g-M.optimizer r s g'‖ ≤ (LΨ : ℝ)*‖g-g'‖)
    (hU2 : ∀ r ∈ Icc 0 (T : ℝ), MemLp
      (fun z => M.observation (M.parameter (U.optimizer r)) (M.position z)) 2 (Q.map (U.sampler.state r)))
    (hVar : ∀ r ∈ Icc 0 (T : ℝ),
      (∫ z, ‖M.observation (M.parameter (U.optimizer r)) (M.position z)-
        M.meanGradient (Q.map (U.sampler.state r)) (U.optimizer r)‖^2 ∂Q.map (U.sampler.state r)) ≤ VF)
    (sStar : S)
    (hopt : ∀ r ∈ Icc 0 (T : ℝ), V.optimizer r = sStar)
    (hlaw : ∀ r ∈ Icc 0 (T : ℝ), (νStar.prod (brownianProbability (I := I))).map (V.sampler.state r) = νStar)
    (hobs : Integrable (fun z => M.observation (M.parameter sStar) (M.position z)) νStar)
    (hinit : ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q,
      oneEquiv N (Y.state 0 ω) = (U.optimizer 0,RawIndependentCopies.cloud Q W N U 0 ω)) :
    MemLp (fun ω => M.parameter (oneEquiv N (Y.state T ω)).1-M.parameter sStar)
      2 (IndependentCopies.seeds (J := Fin N) Q) ∧
    Real.sqrt (∫ ω, ‖M.parameter (oneEquiv N (Y.state T ω)).1-M.parameter sStar‖^2
      ∂IndependentCopies.seeds (J := Fin N) Q) ≤
      Real.sqrt G.conditionNumber*Real.exp (-ρ*(T : ℝ))*optimizerLawDistance (U.optimizer 0) sStar μ νStar+
      ((LΨ : ℝ)/ρ)*Real.sqrt (G.conditionNumber*VF/(N : ℝ))*(1-Real.exp (-ρ*T)) := by
  have hVF : 0 ≤ VF := (integral_nonneg (fun z => sq_nonneg _)).trans (hVar 0 ⟨le_rfl,T.coe_nonneg⟩)
  obtain ⟨hm,hp⟩ := native_parameter_bias_bound Q W U Y G ρ hρ hmono hN hProjection
    hF hDrift hOptimizer LΨ VF hVF sStar hΨ hU2 hVar hinit
  have hd := RawNaturalConstantArbitraryLaw.law_decay μ νStar hμ hν U hUlaw A hA0 hAz V hVz
    huniqueU huniqueA hpath G ρ hρ.le hmono hσ hb hF hDrift hOptimizer LΨ hΨ VF hU2 hVar sStar hopt hlaw hobs
  have ho := optimizer_norm_le_lawDistance (U.optimizer T) sStar (Q.map (U.sampler.state T)) νStar
  exact ⟨hm,(hp.trans (add_le_add le_rfl (ho.trans hd))).trans_eq (add_comm _ _)⟩

/-- Exact source4 bound for the original empirical equation in the general
state-dependent linear-growth branch. The canonical regularity records are
primitive realization/Borel/progressivity and linear growth, with no moments,
energy, output-law matching or coupling conclusions as fields. -/
theorem original_parameter_bound_linearGrowth
    (U : RawLocalStationarity.Data Q W M T)
    (Y : RawEmpiricalDynamics.Solution M N (IndependentCopies.seeds (J := Fin N) Q)
      (RawIndependentCopies.driver Q W N) T)
    (μ νStar : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure νStar]
    (hμ : MemLp (fun z : Z => z) 2 μ) (hν : MemLp (fun z : Z => z) 2 νStar)
    (hUlaw : Q.map (U.sampler.state 0) = μ)
    (A : RawLocalStationarity.Data (μ.prod (brownianProbability (I := I)))
      (CanonicalBrownianDriver.driver (I := I) μ) M T)
    (RA : RawSamplerGrowth.Regularity A)
    (hA0 : A.optimizer 0 = U.optimizer 0)
    (hAz : A.sampler.state 0 =ᵐ[μ.prod (brownianProbability (I := I))] Prod.fst)
    (V : RawLocalStationarity.Data (νStar.prod (brownianProbability (I := I)))
      (CanonicalBrownianDriver.driver (I := I) νStar) M T)
    (RV : RawSamplerGrowth.Regularity V)
    (hVz : V.sampler.state 0 =ᵐ[νStar.prod (brownianProbability (I := I))] Prod.fst)
    (huniqueU : PathwiseUniqueness Q (nullAugmentedDriver Q (continuousDriver Q W)) M T)
    (huniqueA : PathwiseUniqueness (μ.prod (brownianProbability (I := I)))
      (nullAugmentedDriver _ (continuousDriver _ (CanonicalBrownianDriver.driver (I := I) μ))) M T)
    (huniqueV : PathwiseUniqueness (νStar.prod (brownianProbability (I := I)))
      (nullAugmentedDriver _ (continuousDriver _ (CanonicalBrownianDriver.driver (I := I) νStar))) M T)
    (hpathμ : ∃ B : RawLocalStationarity.Data (BrownianPathDriver.probability (I := I) μ)
        (BrownianPathDriver.driver μ) M T,
      B.optimizer 0 = U.optimizer 0 ∧
      B.sampler.state 0 =ᵐ[BrownianPathDriver.probability (I := I) μ] Prod.fst)
    (hpathν : ∃ B : RawLocalStationarity.Data (BrownianPathDriver.probability (I := I) νStar)
        (BrownianPathDriver.driver νStar) M T,
      B.optimizer 0 = V.optimizer 0 ∧
      B.sampler.state 0 =ᵐ[BrownianPathDriver.probability (I := I) νStar] Prod.fst)
    (G : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M G ρ) (hN : 0 < N)
    (hProjection : LipschitzWith 1 M.parameter)
    (hF : Measurable (fun p : S × Z => M.observation (M.parameter p.1) (M.position p.2)))
    (hDrift : Measurable (fun p : S × Z => M.drift (M.parameter p.1) p.2))
    (hOptimizer : Measurable (fun p : ℝ × (S × Θ) => M.optimizer p.1 p.2.1 p.2.2))
    (LΨ : ℝ≥0) (VF : ℝ)
    (hΨ : ∀ r ∈ Icc 0 (T : ℝ), ∀ s g g',
      ‖M.optimizer r s g-M.optimizer r s g'‖ ≤ (LΨ : ℝ)*‖g-g'‖)
    (hU2 : ∀ r ∈ Icc 0 (T : ℝ), MemLp
      (fun z => M.observation (M.parameter (U.optimizer r)) (M.position z)) 2 (Q.map (U.sampler.state r)))
    (hVar : ∀ r ∈ Icc 0 (T : ℝ),
      (∫ z, ‖M.observation (M.parameter (U.optimizer r)) (M.position z)-
        M.meanGradient (Q.map (U.sampler.state r)) (U.optimizer r)‖^2 ∂Q.map (U.sampler.state r)) ≤ VF)
    (sStar : S)
    (hopt : ∀ r ∈ Icc 0 (T : ℝ), V.optimizer r = sStar)
    (hlaw : ∀ r ∈ Icc 0 (T : ℝ), (νStar.prod (brownianProbability (I := I))).map (V.sampler.state r) = νStar)
    (hinit : ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q,
      oneEquiv N (Y.state 0 ω) = (U.optimizer 0,RawIndependentCopies.cloud Q W N U 0 ω)) :
    MemLp (fun ω => M.parameter (oneEquiv N (Y.state T ω)).1-M.parameter sStar)
      2 (IndependentCopies.seeds (J := Fin N) Q) ∧
    Real.sqrt (∫ ω, ‖M.parameter (oneEquiv N (Y.state T ω)).1-M.parameter sStar‖^2
      ∂IndependentCopies.seeds (J := Fin N) Q) ≤
      Real.sqrt G.conditionNumber*Real.exp (-ρ*(T : ℝ))*optimizerLawDistance (U.optimizer 0) sStar μ νStar+
      ((LΨ : ℝ)/ρ)*Real.sqrt (G.conditionNumber*VF/(N : ℝ))*(1-Real.exp (-ρ*T)) := by
  have hVF : 0 ≤ VF := (integral_nonneg (fun z => sq_nonneg _)).trans (hVar 0 ⟨le_rfl,T.coe_nonneg⟩)
  obtain ⟨hm,hp⟩ := native_parameter_bias_bound Q W U Y G ρ hρ hmono hN hProjection
    hF hDrift hOptimizer LΨ VF hVF sStar hΨ hU2 hVar hinit
  have hVlaw0 : (νStar.prod (brownianProbability (I := I))).map (V.sampler.state 0) = νStar :=
    hlaw 0 ⟨le_rfl,T.coe_nonneg⟩
  let AC : RawSamplerGrowthArbitraryLaw.CanonicalSolution (M := M) (T := T) μ (U.optimizer 0) :=
    ⟨A,RA,hA0,hAz⟩
  let VC : RawSamplerGrowthArbitraryLaw.CanonicalSolution (M := M) (T := T) νStar (V.optimizer 0) :=
    ⟨V,RV,rfl,hVz⟩
  have hd := RawSamplerGrowthArbitraryLaw.law_distance_decay U V μ νStar hμ hν hUlaw hVlaw0 AC VC
    huniqueU huniqueV huniqueA huniqueV hpathμ hpathν G ρ hmono
  rw [hopt T ⟨T.coe_nonneg,le_rfl⟩,hlaw T ⟨T.coe_nonneg,le_rfl⟩,hopt 0 ⟨le_rfl,T.coe_nonneg⟩] at hd
  have ho := optimizer_norm_le_lawDistance (U.optimizer T) sStar (Q.map (U.sampler.state T)) νStar
  exact ⟨hm,(hp.trans (add_le_add le_rfl (ho.trans hd))).trans_eq (add_comm _ _)⟩

end PBGSO.RawConstructedParticleParameter
