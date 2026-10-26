import PBGSO.RawConstantNoisePullback
import PBGSO.CanonicalSeparable
import PBGSO.ConstructedItoLaw

/-! # Genuine law infimum for raw constant-diffusion solutions
Every initial coupling is realized on its actual Brownian extension. Raw
original equations and their marginal laws transport internally. The only
additional one-sided analytic condition is parameter-cross work L¹ on those
actual joint realizations; no Wasserstein bound or output coupling is assumed.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.RawConstantNoiseLaw
open FilteredBrownian ConstructedItoLaw RawConstantNoiseContraction
variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype I] [DecidableEq I]
  (μ ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  (hμ : MemLp (fun z : Z => z) 2 μ) (hν : MemLp (fun z : Z => z) 2 ν)

include hμ hν

/-- Actual original raw constant-diffusion laws contract after taking the
infimum over all genuine initial couplings. Parameter-cross integrability is
explicit and is not claimed to follow from minimal source A1(i). -/
theorem law_distance_decay {M : Model S Θ Z X I} {T : ℝ≥0}
    {L : RawLocalDiffusion (Z := Z) (μ.prod (brownianProbability (I := I)))
      (CanonicalBrownianDriver.driver (I := I) μ) T}
    {K : RawLocalDiffusion (Z := Z) (ν.prod (brownianProbability (I := I)))
      (CanonicalBrownianDriver.driver (I := I) ν) T}
    (U : Data (μ.prod (brownianProbability (I := I))) M
      (CanonicalBrownianDriver.driver (I := I) μ) T L)
    (V : Data (ν.prod (brownianProbability (I := I))) M
      (CanonicalBrownianDriver.driver (I := I) ν) T K)
    (hU0 : U.sampler 0 =ᵐ[μ.prod (brownianProbability (I := I))] fun ω => ω.1)
    (hV0 : V.sampler 0 =ᵐ[ν.prod (brownianProbability (I := I))] fun ω => ω.1)
    (G : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hmono : TwistedJointMonotonicity M G ρ)
    (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i)
    (hb : ∀ θ, Measurable (M.drift θ))
    (hcross : ∀ c : ULA.Coupling μ ν,
      Integrable (fun p : ℝ × ((Z × Z) × ULA.CanonicalBrownian.VectorSample I) =>
        ‖U.sampler p.1 (p.2.1.1,p.2.2)-V.sampler p.1 (p.2.1.2,p.2.2)‖ *
        ‖M.drift (M.parameter (U.optimizer p.1)) (V.sampler p.1 (p.2.1.2,p.2.2))-
          M.drift (M.parameter (V.optimizer p.1)) (V.sampler p.1 (p.2.1.2,p.2.2))‖)
        ((volume.restrict (Ioc 0 (T : ℝ))).prod (ULA.initialExtension c (brownianProbability (I := I))))) :
    optimizerLawDistance (U.optimizer T) (V.optimizer T)
      ((μ.prod (brownianProbability (I := I))).map (U.sampler T))
      ((ν.prod (brownianProbability (I := I))).map (V.sampler T)) ≤
      Real.sqrt G.conditionNumber * Real.exp (-ρ * (T : ℝ)) *
        optimizerLawDistance (U.optimizer 0) (V.optimizer 0) μ ν := by
  have hUI : ProductLpSections.sectionLp (μ.prod (brownianProbability (I := I))) U.sampler 0 =
      AdditiveCanonical.initialSampler (brownianProbability (I := I)) μ hμ := by
    apply Lp.ext
    exact (ProductLpSections.sectionLp_ae _ U.sampler (U.sampler_square 0 ⟨le_rfl,T.coe_nonneg⟩)).trans
      (hU0.trans (AdditiveCanonical.initialSampler_coe _ μ hμ).symm)
  have hVI : ProductLpSections.sectionLp (ν.prod (brownianProbability (I := I))) V.sampler 0 =
      AdditiveCanonical.initialSampler (brownianProbability (I := I)) ν hν := by
    apply Lp.ext
    exact (ProductLpSections.sectionLp_ae _ V.sampler (V.sampler_square 0 ⟨le_rfl,T.coe_nonneg⟩)).trans
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
  let Uc := U.pullback hf E (CoupledBrownianFiltration.left_process_eq μ ν c)
    (CoupledBrownianFiltration.left_filtration_le μ ν c) hσ
  let Vc := V.pullback hg E (CoupledBrownianFiltration.right_process_eq μ ν c)
    (CoupledBrownianFiltration.right_filtration_le μ ν c) hσ
  have h := pair_law_distance_decay_of_parameter_cross Q M G Uc Vc ρ hρ hmono hσ hb (hcross c)
  rw [Data.pullback_law,Data.pullback_law] at h
  change optimizerLawDistance (U.optimizer T) (V.optimizer T)
    ((μ.prod (brownianProbability (I := I))).map (U.sampler T))
    ((ν.prod (brownianProbability (I := I))).map (V.sampler T)) ≤
    Real.sqrt G.conditionNumber * Real.exp (-ρ * (T : ℝ)) *
      Real.sqrt (‖U.optimizer 0-V.optimizer 0‖ ^ 2+
        ‖ProductLpSections.sectionLp Q Uc.sampler 0-ProductLpSections.sectionLp Q Vc.sampler 0‖ ^ 2) at h
  rw [Data.pullback_section (ht := ⟨le_rfl,T.coe_nonneg⟩),
    Data.pullback_section (ht := ⟨le_rfl,T.coe_nonneg⟩),hUI,hVI,
    initial_difference_norm_sq μ ν hμ hν c] at h
  exact h

end PBGSO.RawConstantNoiseLaw
