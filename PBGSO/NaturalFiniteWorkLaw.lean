import PBGSO.NaturalFiniteWorkContraction
import PBGSO.RawSamplerGrowthLaw

/-! # Genuine law contraction under finite signed coupling work
Each original canonical raw equation is transported to every actual initial
coupling. Proven coercive moments and universal finite signed work derive
all analytic and stochastic comparison premises before taking the infimum.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.NaturalFiniteWorkLaw
open FilteredBrownian RawLocalStationarity RawSamplerGrowth ConstructedItoLaw
variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S] [FiniteDimensional ℝ S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace Θ] [BorelSpace Θ] [SecondCountableTopology Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z] [FiniteDimensional ℝ Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype I] [DecidableEq I]
  (μ ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  (hμ : MemLp (fun z : Z => z) 2 μ) (hν : MemLp (fun z : Z => z) 2 ν)

include hμ hν

/-- Source constant-diffusion law contraction over the genuine infimum of
all initial couplings, under the explicit finite signed-work reading of A3.
Original raw equations and primitive Borel fields derive every state moment,
positive-work bound, stochastic match and Fubini premise. -/
theorem law_distance_decay {M : Model S Θ Z X I} {T : ℝ≥0}
    (U : RawLocalStationarity.Data (μ.prod (brownianProbability (I := I)))
      (CanonicalBrownianDriver.driver (I := I) μ) M T)
    (V : RawLocalStationarity.Data (ν.prod (brownianProbability (I := I)))
      (CanonicalBrownianDriver.driver (I := I) ν) M T)
    (hU0 : U.sampler.state 0 =ᵐ[μ.prod (brownianProbability (I := I))] fun ω => ω.1)
    (hV0 : V.sampler.state 0 =ᵐ[ν.prod (brownianProbability (I := I))] fun ω => ω.1)
    (G : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M G ρ)
    (hfull : DiracOptimizerGrowth.FiniteCouplingWork M G)
    (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i)
    (hb : ∀ θ, Measurable (M.drift θ))
    (hObs : Measurable (fun p : S × Z => M.observation (M.parameter p.1) (M.position p.2)))
    (hDrift : Measurable (fun p : S × Z => M.drift (M.parameter p.1) p.2))
    (hOptimizer : Measurable (fun p : ℝ × (S × Θ) => M.optimizer p.1 p.2.1 p.2.2)) :
    optimizerLawDistance (U.optimizer T) (V.optimizer T)
      ((μ.prod (brownianProbability (I := I))).map (U.sampler.state T))
      ((ν.prod (brownianProbability (I := I))).map (V.sampler.state T)) ≤
      Real.sqrt G.conditionNumber * Real.exp (-ρ * (T : ℝ)) *
        optimizerLawDistance (U.optimizer 0) (V.optimizer 0) μ ν := by
  have hUI : ProductLpSections.sectionLp (μ.prod (brownianProbability (I := I))) U.sampler.state 0 =
      AdditiveCanonical.initialSampler (brownianProbability (I := I)) μ hμ := by
    apply Lp.ext
    exact (ProductLpSections.sectionLp_ae _ U.sampler.state
      (sampler_memLp _ U 0 ⟨le_rfl,T.coe_nonneg⟩)).trans
      (hU0.trans (AdditiveCanonical.initialSampler_coe _ μ hμ).symm)
  have hVI : ProductLpSections.sectionLp (ν.prod (brownianProbability (I := I))) V.sampler.state 0 =
      AdditiveCanonical.initialSampler (brownianProbability (I := I)) ν hν := by
    apply Lp.ext
    exact (ProductLpSections.sectionLp_ae _ V.sampler.state
      (sampler_memLp _ V 0 ⟨le_rfl,T.coe_nonneg⟩)).trans
      (hV0.trans (AdditiveCanonical.initialSampler_coe _ ν hν).symm)
  apply bound_of_all_finite_couplings μ ν (ULA.wasserstein2_ne_top_of_memLp μ ν hμ hν)
    (fun c => Real.sqrt G.conditionNumber * Real.exp (-ρ * (T : ℝ)) *
      Real.sqrt (‖U.optimizer 0-V.optimizer 0‖ ^ 2+c ^ 2)) (by fun_prop)
  intro c hc
  let Q := ULA.initialExtension c (brownianProbability (I := I))
  letI : IsProbabilityMeasure c.joint := c.isProbabilityMeasure
  letI : IsProbabilityMeasure Q := ULA.initialExtension_isProbabilityMeasure c _
  letI : IsSeparable Q := CanonicalSeparable.initial_vector_isSeparable (I := I) c.joint
  let hf := AdditiveCanonical.extension_left_preserving (brownianProbability (I := I)) μ ν c
  let hg := AdditiveCanonical.extension_right_preserving (brownianProbability (I := I)) μ ν c
  let E := CoupledBrownianFiltration.fullDriver (I := I) μ ν c
  have hp : ∀ i t, (pullbackDriver hf (CanonicalBrownianDriver.driver (I := I) μ)).process i t =ᵐ[Q]
      E.process i t := fun i t => Filter.EventuallyEq.of_eq
        (congrFun (congrFun (CoupledBrownianFiltration.left_process_eq μ ν c) i) t)
  have hq : ∀ i t, (pullbackDriver hg (CanonicalBrownianDriver.driver (I := I) ν)).process i t =ᵐ[Q]
      E.process i t := fun i t => Filter.EventuallyEq.of_eq
        (congrFun (congrFun (CoupledBrownianFiltration.right_process_eq μ ν c) i) t)
  let he := CoupledBrownianFiltration.left_filtration_le (I := I) μ ν c
  let hk := CoupledBrownianFiltration.right_filtration_le (I := I) μ ν c
  let Uc := U.pullback hf E he hp
  let Vc := V.pullback hg E hk hq
  have h := NaturalFiniteWorkContraction.pair_law_distance_decay Uc Vc G ρ hρ hmono
    hfull hσ hb hObs hDrift hOptimizer
  have huLaw : Q.map (Uc.sampler.state T) = (μ.prod (brownianProbability (I := I))).map (U.sampler.state T) :=
    U.sampler.pullback_law hf E he hp T ⟨T.coe_nonneg,le_rfl⟩
  have hvLaw : Q.map (Vc.sampler.state T) = (ν.prod (brownianProbability (I := I))).map (V.sampler.state T) :=
    V.sampler.pullback_law hg E hk hq T ⟨T.coe_nonneg,le_rfl⟩
  rw [huLaw,hvLaw] at h
  change optimizerLawDistance (U.optimizer T) (V.optimizer T)
    ((μ.prod (brownianProbability (I := I))).map (U.sampler.state T))
    ((ν.prod (brownianProbability (I := I))).map (V.sampler.state T)) ≤
    Real.sqrt G.conditionNumber * Real.exp (-ρ * (T : ℝ)) *
      Real.sqrt (‖U.optimizer 0-V.optimizer 0‖ ^ 2+
        ‖ProductLpSections.sectionLp Q Uc.sampler.state 0-
          ProductLpSections.sectionLp Q Vc.sampler.state 0‖ ^ 2) at h
  rw [pullback_section (ht := ⟨le_rfl,T.coe_nonneg⟩),
    pullback_section (ht := ⟨le_rfl,T.coe_nonneg⟩),hUI,hVI,
    initial_difference_norm_sq μ ν hμ hν c] at h
  exact h

end PBGSO.NaturalFiniteWorkLaw
