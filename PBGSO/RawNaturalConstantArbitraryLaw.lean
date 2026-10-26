import PBGSO.RawNaturalConstantLaw
import PBGSO.RawSolutionLawUniqueness

/-! # Natural constant-noise relaxation on arbitrary original sources
An original solution is identified with the actual canonical Gaussian-source
solution through one genuine Wiener-path-source existence witness. Initial
conditions and pathwise uniqueness yield every output-law equality. Source
response/variance conditions then provide the exact law-infimum relaxation.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.RawNaturalConstantArbitraryLaw
open FilteredBrownian RawLocalStationarity ConstructedItoLaw
variable {Ω S Θ Z X I : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace Θ] [BorelSpace Θ] [SecondCountableTopology Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [Fintype I] [DecidableEq I]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {W : Driver (I := I) Q} {M : Model S Θ Z X I} {T : ℝ≥0}
  (μ νStar : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure νStar]
  (hμ : MemLp (fun z : Z => z) 2 μ) (hν : MemLp (fun z : Z => z) 2 νStar)
include hμ hν

/-- Exact relaxation of an original natural raw solution on any Brownian
source. The auxiliary existence/uniqueness inputs are direct A1 instances;
output-law and stochastic matching are derived, and no drift-growth or work
assumption is added to the source parameter hypotheses. -/
theorem law_decay
    (U : RawLocalStationarity.Data Q W M T)
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
        2 (Q.map (U.sampler.state r)))
    (hVar : ∀ r ∈ Icc 0 (T : ℝ),
      (∫ z, ‖M.observation (M.parameter (U.optimizer r)) (M.position z)-
        M.meanGradient (Q.map (U.sampler.state r)) (U.optimizer r)‖ ^ 2 ∂Q.map (U.sampler.state r)) ≤ V0)
    (sStar : S)
    (hopt : ∀ r ∈ Icc 0 (T : ℝ), V.optimizer r = sStar)
    (hlaw : ∀ r ∈ Icc 0 (T : ℝ),
      (νStar.prod (brownianProbability (I := I))).map (V.sampler.state r) = νStar)
    (hobs : Integrable (fun z => M.observation (M.parameter sStar) (M.position z)) νStar) :
    optimizerLawDistance (U.optimizer T) sStar (Q.map (U.sampler.state T)) νStar ≤
      Real.sqrt D.conditionNumber * Real.exp (-ρ * (T : ℝ)) *
        optimizerLawDistance (U.optimizer 0) sStar μ νStar := by
  have hAlaw0 : (μ.prod (brownianProbability (I := I))).map (A.sampler.state 0) = μ := by
    rw [Measure.map_congr hAz,Measure.map_fst_prod,measure_univ,one_smul]
  have hUA (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) :=
    law_unique_two_sources U A μ hUlaw hAlaw0 hA0.symm huniqueU huniqueA hpath r hr
  have hA2 : ∀ r ∈ Icc 0 (T : ℝ),
      MemLp (fun z => M.observation (M.parameter (A.optimizer r)) (M.position z))
        2 ((μ.prod (brownianProbability (I := I))).map (A.sampler.state r)) := by
    intro r hr
    rw [← (hUA r hr).1,← (hUA r hr).2]
    exact hU2 r hr
  have hAVar : ∀ r ∈ Icc 0 (T : ℝ),
      (∫ z, ‖M.observation (M.parameter (A.optimizer r)) (M.position z)-
        M.meanGradient ((μ.prod (brownianProbability (I := I))).map (A.sampler.state r)) (A.optimizer r)‖ ^ 2
        ∂(μ.prod (brownianProbability (I := I))).map (A.sampler.state r)) ≤ V0 := by
    intro r hr
    rw [← (hUA r hr).1,← (hUA r hr).2]
    exact hVar r hr
  have h := RawNaturalConstantLaw.law_decay μ νStar hμ hν A V hAz hVz D ρ hρ hmono
    hσ hb hF hDrift hOptimizer LΨ hΨ V0 hA2 hAVar sStar hopt hlaw hobs
  rw [hA0,← (hUA T ⟨T.coe_nonneg,le_rfl⟩).1,← (hUA T ⟨T.coe_nonneg,le_rfl⟩).2] at h
  exact h

end PBGSO.RawNaturalConstantArbitraryLaw
