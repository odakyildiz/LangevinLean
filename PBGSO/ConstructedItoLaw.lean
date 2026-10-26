import PBGSO.ConstructedItoPullback

/-! # Wasserstein contraction of actual canonical state-dependent model laws
Both canonical processes are transported into the genuine full coupled past.
Their original marginal laws and their computed Brownian integrals are
preserved. Taking the infimum requires no optimal coupling or supplied
all-couplings realization, martingale, isometry, or energy identity.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.ConstructedItoLaw
open ConstructedItoModel FilteredBrownian
variable {I Z S Θ X : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  (μ ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  (hμ : MemLp (fun z : Z => z) 2 μ) (hν : MemLp (fun z : Z => z) 2 ν)

abbrev brownianProbability : Measure (ULA.CanonicalBrownian.VectorSample I) :=
  ULA.CanonicalBrownian.vectorProbability I

/-- Exact initial coupling cost on the actual independent Brownian extension. -/
theorem initial_difference_norm_sq (c : ULA.Coupling μ ν) :
    ‖lpPullbackCLM (AdditiveCanonical.extension_left_preserving (brownianProbability (I := I)) μ ν c)
      (AdditiveCanonical.initialSampler (brownianProbability (I := I)) μ hμ) -
      lpPullbackCLM (AdditiveCanonical.extension_right_preserving (brownianProbability (I := I)) μ ν c)
      (AdditiveCanonical.initialSampler (brownianProbability (I := I)) ν hν)‖ ^ 2 =
      (ULA.couplingCost c.joint).toReal ^ 2 := by
  let Q := ULA.initialExtension c (brownianProbability (I := I))
  letI : IsProbabilityMeasure c.joint := c.isProbabilityMeasure
  letI : IsProbabilityMeasure Q := ULA.initialExtension_isProbabilityMeasure c _
  let hf := AdditiveCanonical.extension_left_preserving (brownianProbability (I := I)) μ ν c
  let hg := AdditiveCanonical.extension_right_preserving (brownianProbability (I := I)) μ ν c
  let U := lpPullbackCLM hf (AdditiveCanonical.initialSampler (brownianProbability (I := I)) μ hμ)
  let V := lpPullbackCLM hg (AdditiveCanonical.initialSampler (brownianProbability (I := I)) ν hν)
  have hU : U =ᵐ[Q] fun p => p.1.1 :=
    (lpPullback_coe hf _).trans (hf.quasiMeasurePreserving.ae_eq_comp
      (AdditiveCanonical.initialSampler_coe _ μ hμ))
  have hV : V =ᵐ[Q] fun p => p.1.2 :=
    (lpPullback_coe hg _).trans (hg.quasiMeasurePreserving.ae_eq_comp
      (AdditiveCanonical.initialSampler_coe _ ν hν))
  have hpair : samplerPairLaw Q U V = c.joint := by
    rw [samplerPairLaw, Measure.map_congr (hU.prodMk hV)]
    exact ULA.initialExtension_joint c _
  calc
    ‖U - V‖ ^ 2 = ∫ p, ‖p.1 - p.2‖ ^ 2 ∂samplerPairLaw Q U V :=
      (IntegralModelContraction.samplerPairLaw_euclidean_integral (Q := Q) U V).symm
    _ = (ULA.couplingCost c.joint).toReal ^ 2 := by
      rw [hpair]
      exact (couplingCost_sq_eq_integral c.joint (coupling_difference_memLp μ ν hμ hν c)).symm

/-- Source A3 contracts the actual canonical state-dependent marginal laws.
The explicit realization subclass is L¹-time L² drift and continuous adapted
L² diffusion; all stochastic and arbitrary-initial-coupling conclusions are
proved from the original integral equations. -/
theorem law_distance_decay {M : Model S Θ Z X I} {T : ℝ≥0}
    (U : Data (μ.prod (brownianProbability (I := I)))
      (CanonicalBrownianDriver.driver (I := I) μ) M T)
    (V : Data (ν.prod (brownianProbability (I := I)))
      (CanonicalBrownianDriver.driver (I := I) ν) M T)
    (hU0 : U.sampler 0 = AdditiveCanonical.initialSampler (brownianProbability (I := I)) μ hμ)
    (hV0 : V.sampler 0 = AdditiveCanonical.initialSampler (brownianProbability (I := I)) ν hν)
    (G : TwistedGeometry S Z)
    (hb : ∀ θ, Measurable (M.drift θ))
    (hσ : ∀ θ i, Measurable (fun z => M.diffusion θ z i))
    (ρ : ℝ) (hmono : TwistedJointMonotonicity M G ρ) :
    optimizerLawDistance (U.optimizer T) (V.optimizer T)
      ((μ.prod (brownianProbability (I := I))).map (U.sampler T))
      ((ν.prod (brownianProbability (I := I))).map (V.sampler T)) ≤
      Real.sqrt G.conditionNumber * Real.exp (-ρ * T) *
        optimizerLawDistance (U.optimizer 0) (V.optimizer 0) μ ν := by
  apply bound_of_all_finite_couplings μ ν (ULA.wasserstein2_ne_top_of_memLp μ ν hμ hν)
    (fun c => Real.sqrt G.conditionNumber * Real.exp (-ρ * T) *
      Real.sqrt (‖U.optimizer 0 - V.optimizer 0‖ ^ 2 + c ^ 2)) (by fun_prop)
  intro c hc
  let Q := ULA.initialExtension c (brownianProbability (I := I))
  letI : IsProbabilityMeasure c.joint := c.isProbabilityMeasure
  letI : IsProbabilityMeasure Q := ULA.initialExtension_isProbabilityMeasure c _
  let hf := AdditiveCanonical.extension_left_preserving (brownianProbability (I := I)) μ ν c
  let hg := AdditiveCanonical.extension_right_preserving (brownianProbability (I := I)) μ ν c
  let E := CoupledBrownianFiltration.fullDriver (I := I) μ ν c
  let Uc := U.pullback hf E (CoupledBrownianFiltration.left_process_eq μ ν c)
    (CoupledBrownianFiltration.left_filtration_le μ ν c)
  let Vc := V.pullback hg E (CoupledBrownianFiltration.right_process_eq μ ν c)
    (CoupledBrownianFiltration.right_filtration_le μ ν c)
  have h := ConstructedItoModel.law_distance_decay G Uc Vc hb hσ ρ hmono
  change optimizerLawDistance (U.optimizer T) (V.optimizer T)
    (Q.map (lpPullbackCLM hf (U.sampler T))) (Q.map (lpPullbackCLM hg (V.sampler T))) ≤
    Real.sqrt G.conditionNumber * Real.exp (-ρ * T) *
      Real.sqrt (‖U.optimizer 0 - V.optimizer 0‖ ^ 2 +
        ‖lpPullbackCLM hf (U.sampler 0) - lpPullbackCLM hg (V.sampler 0)‖ ^ 2) at h
  rw [lpPullback_law hf, lpPullback_law hg, hU0, hV0,
    initial_difference_norm_sq μ ν hμ hν c] at h
  exact h

end PBGSO.ConstructedItoLaw
