import PBGSO.RawNaturalConstantParameter
import PBGSO.RawSamplerGrowthLaw

/-! # Natural constant-noise relaxation over the genuine law infimum
Each initial coupling is realized on its actual Brownian extension. Natural
raw equations are transported internally, and source response/variance
assumptions derive the required positive work on each realization. The final
relaxation prefactor is the true initial optimizer/Wasserstein distance.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.RawNaturalConstantLaw
open FilteredBrownian RawLocalStationarity RawSamplerGrowth ConstructedItoLaw
variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace Θ] [BorelSpace Θ] [SecondCountableTopology Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [Fintype I] [DecidableEq I]
  (μ νStar : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure νStar]
  (hμ : MemLp (fun z : Z => z) 2 μ) (hν : MemLp (fun z : Z => z) 2 νStar)
include hμ hν

/-- The source parameter assumptions imply genuine law relaxation for
natural original constant-diffusion solutions. All stochastic and Fubini
premises are derived; no drift-growth or positive-work assumption is added. -/
theorem law_decay {M : Model S Θ Z X I} {T : ℝ≥0}
    (U : RawLocalStationarity.Data (μ.prod (brownianProbability (I := I)))
      (CanonicalBrownianDriver.driver (I := I) μ) M T)
    (V : RawLocalStationarity.Data (νStar.prod (brownianProbability (I := I)))
      (CanonicalBrownianDriver.driver (I := I) νStar) M T)
    (hU0 : U.sampler.state 0 =ᵐ[μ.prod (brownianProbability (I := I))] Prod.fst)
    (hV0 : V.sampler.state 0 =ᵐ[νStar.prod (brownianProbability (I := I))] Prod.fst)
    (D : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hmono : TwistedJointMonotonicity M D ρ)
    (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i)
    (hb : ∀ θ, Measurable (M.drift θ))
    (hF : Measurable (fun p : S × Z => M.observation (M.parameter p.1) (M.position p.2)))
    (hDrift : Measurable (fun p : S × Z => M.drift (M.parameter p.1) p.2))
    (hOptimizer : Measurable (fun p : ℝ × (S × Θ) => M.optimizer p.1 p.2.1 p.2.2))
    (LΨ : ℝ≥0)
    (hΨ : ∀ r ∈ Icc 0 (T : ℝ), ∀ s g g',
      ‖M.optimizer r s g-M.optimizer r s g'‖ ≤ (LΨ : ℝ)*‖g-g'‖)
    (V0 : ℝ)
    (hU2 : ∀ r ∈ Icc 0 (T : ℝ),
      MemLp (fun z => M.observation (M.parameter (U.optimizer r)) (M.position z))
        2 ((μ.prod (brownianProbability (I := I))).map (U.sampler.state r)))
    (hVar : ∀ r ∈ Icc 0 (T : ℝ),
      (∫ z, ‖M.observation (M.parameter (U.optimizer r)) (M.position z)-
        M.meanGradient ((μ.prod (brownianProbability (I := I))).map (U.sampler.state r)) (U.optimizer r)‖ ^ 2
        ∂(μ.prod (brownianProbability (I := I))).map (U.sampler.state r)) ≤ V0)
    (sStar : S)
    (hopt : ∀ r ∈ Icc 0 (T : ℝ), V.optimizer r = sStar)
    (hlaw : ∀ r ∈ Icc 0 (T : ℝ),
      (νStar.prod (brownianProbability (I := I))).map (V.sampler.state r) = νStar)
    (hobs : Integrable (fun z => M.observation (M.parameter sStar) (M.position z)) νStar) :
    optimizerLawDistance (U.optimizer T) sStar
      ((μ.prod (brownianProbability (I := I))).map (U.sampler.state T)) νStar ≤
      Real.sqrt D.conditionNumber * Real.exp (-ρ * (T : ℝ)) *
        optimizerLawDistance (U.optimizer 0) sStar μ νStar := by
  have hUI : ProductLpSections.sectionLp (μ.prod (brownianProbability (I := I))) U.sampler.state 0 =
      AdditiveCanonical.initialSampler (brownianProbability (I := I)) μ hμ := by
    apply Lp.ext
    exact (ProductLpSections.sectionLp_ae _ U.sampler.state
      (sampler_memLp _ U 0 ⟨le_rfl,T.coe_nonneg⟩)).trans
      (hU0.trans (AdditiveCanonical.initialSampler_coe _ μ hμ).symm)
  have hVI : ProductLpSections.sectionLp (νStar.prod (brownianProbability (I := I))) V.sampler.state 0 =
      AdditiveCanonical.initialSampler (brownianProbability (I := I)) νStar hν := by
    apply Lp.ext
    exact (ProductLpSections.sectionLp_ae _ V.sampler.state
      (sampler_memLp _ V 0 ⟨le_rfl,T.coe_nonneg⟩)).trans
      (hV0.trans (AdditiveCanonical.initialSampler_coe _ νStar hν).symm)
  apply bound_of_all_finite_couplings μ νStar (ULA.wasserstein2_ne_top_of_memLp μ νStar hμ hν)
    (fun c => Real.sqrt D.conditionNumber * Real.exp (-ρ * (T : ℝ)) *
      Real.sqrt (‖U.optimizer 0-sStar‖ ^ 2+c ^ 2)) (by fun_prop)
  intro c hc
  let Q := ULA.initialExtension c (brownianProbability (I := I))
  letI : IsProbabilityMeasure c.joint := c.isProbabilityMeasure
  letI : IsProbabilityMeasure Q := ULA.initialExtension_isProbabilityMeasure c _
  letI : IsSeparable Q := CanonicalSeparable.initial_vector_isSeparable (I := I) c.joint
  let hf := AdditiveCanonical.extension_left_preserving (brownianProbability (I := I)) μ νStar c
  let hg := AdditiveCanonical.extension_right_preserving (brownianProbability (I := I)) μ νStar c
  let E := CoupledBrownianFiltration.fullDriver (I := I) μ νStar c
  have hp : ∀ i t, (pullbackDriver hf (CanonicalBrownianDriver.driver (I := I) μ)).process i t =ᵐ[Q]
      E.process i t := fun i t => Filter.EventuallyEq.of_eq
        (congrFun (congrFun (CoupledBrownianFiltration.left_process_eq μ νStar c) i) t)
  have hq : ∀ i t, (pullbackDriver hg (CanonicalBrownianDriver.driver (I := I) νStar)).process i t =ᵐ[Q]
      E.process i t := fun i t => Filter.EventuallyEq.of_eq
        (congrFun (congrFun (CoupledBrownianFiltration.right_process_eq μ νStar c) i) t)
  let he := CoupledBrownianFiltration.left_filtration_le (I := I) μ νStar c
  let hk := CoupledBrownianFiltration.right_filtration_le (I := I) μ νStar c
  let Uc := U.pullback hf E he hp
  let Vc := V.pullback hg E hk hq
  have huLaw (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) :
      Q.map (Uc.sampler.state r) = (μ.prod (brownianProbability (I := I))).map (U.sampler.state r) :=
    U.sampler.pullback_law hf E he hp r hr
  have hvLaw (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) :
      Q.map (Vc.sampler.state r) = (νStar.prod (brownianProbability (I := I))).map (V.sampler.state r) :=
    V.sampler.pullback_law hg E hk hq r hr
  have h := RawNaturalConstantParameter.reference_law_decay Uc Vc D ρ hρ hmono hσ hb hF hDrift hOptimizer
    LΨ hΨ V0
    (fun r hr => by rw [huLaw r hr]; exact hU2 r hr)
    (fun r hr => by rw [huLaw r hr]; exact hVar r hr)
    sStar νStar hopt (fun r hr => (hvLaw r hr).trans (hlaw r hr)) hobs
  rw [huLaw T ⟨T.coe_nonneg,le_rfl⟩] at h
  change optimizerLawDistance (U.optimizer T) sStar
    ((μ.prod (brownianProbability (I := I))).map (U.sampler.state T)) νStar ≤
    Real.sqrt D.conditionNumber * Real.exp (-ρ * (T : ℝ)) *
      Real.sqrt (‖U.optimizer 0-sStar‖ ^ 2+
        ‖ProductLpSections.sectionLp Q Uc.sampler.state 0-
          ProductLpSections.sectionLp Q Vc.sampler.state 0‖ ^ 2) at h
  rw [pullback_section (ht := ⟨le_rfl,T.coe_nonneg⟩),
    pullback_section (ht := ⟨le_rfl,T.coe_nonneg⟩),hUI,hVI,
    initial_difference_norm_sq μ νStar hμ hν c] at h
  exact h

end PBGSO.RawNaturalConstantLaw
