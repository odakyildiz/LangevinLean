import PBGSO.RawLinearGrowthModel
import PBGSO.CanonicalSeparable
import PBGSO.ConstructedPredictableLaw

/-! # Actual raw-law contraction in the source linear-growth branch
Primitive local strong model equations and linear growth derive all global
moments, computed noise compatibility and actual marginal-law identities.
Arbitrary initial couplings and their transport infimum are handled internally.
The observation domain and original coefficient measurability are explicit.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace PBGSO.RawLinearGrowthLaw
open FilteredBrownian ConstructedItoLaw RawLinearGrowthModel
variable {I Z S Θ X : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  (μ ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  (hμ : MemLp (fun z : Z => z) 2 μ) (hν : MemLp (fun z : Z => z) 2 ν)
include hμ hν

/-- Source A3 contracts the actual original raw solution laws under the
source linear-growth A1 branch. No time-L¹(L²) drift, global diffusion moment,
noise matching, supplied transport coupling or output-law premise is required.
The raw initial variables are the original canonical initial coordinates. -/
theorem law_distance_decay {M : Model S Θ Z X I} {T : ℝ≥0}
    {Kμ Pμ Kν Pν : ℝ}
    (Lμ : RawLocalDiffusion (Z := Z) (μ.prod (brownianProbability (I := I)))
      (CanonicalBrownianDriver.driver (I := I) μ) T)
    (Lν : RawLocalDiffusion (Z := Z) (ν.prod (brownianProbability (I := I)))
      (CanonicalBrownianDriver.driver (I := I) ν) T)
    (U : RawLinearGrowthState.Data Lμ Kμ Pμ) (V : RawLinearGrowthState.Data Lν Kν Pν)
    (R : Realization M Lμ Kμ Pμ U) (R' : Realization M Lν Kν Pν V)
    (hU0 : U.state 0 =ᵐ[μ.prod (brownianProbability (I := I))] fun ω => ω.1)
    (hV0 : V.state 0 =ᵐ[ν.prod (brownianProbability (I := I))] fun ω => ω.1)
    (G : TwistedGeometry S Z) (hb : ∀ θ, Measurable (M.drift θ))
    (hσ : ∀ θ i, Measurable (fun z => M.diffusion θ z i))
    (ρ : ℝ) (hmono : TwistedJointMonotonicity M G ρ) :
    optimizerLawDistance (R.optimizer T) (R'.optimizer T)
      ((μ.prod (brownianProbability (I := I))).map (U.state T))
      ((ν.prod (brownianProbability (I := I))).map (V.state T)) ≤
      Real.sqrt G.conditionNumber * Real.exp (-ρ * T) *
        optimizerLawDistance (R.optimizer 0) (R'.optimizer 0) μ ν := by
  have hRU0 : R.predictableData.sampler 0 =
      AdditiveCanonical.initialSampler (brownianProbability (I := I)) μ hμ := by
    apply Lp.ext
    exact (ProductLpSections.sectionLp_ae _ U.state (U.state_memLp 0 ⟨le_rfl, T.coe_nonneg⟩)).trans
      (hU0.trans (AdditiveCanonical.initialSampler_coe (brownianProbability (I := I)) μ hμ).symm)
  have hRV0 : R'.predictableData.sampler 0 =
      AdditiveCanonical.initialSampler (brownianProbability (I := I)) ν hν := by
    apply Lp.ext
    exact (ProductLpSections.sectionLp_ae _ V.state (V.state_memLp 0 ⟨le_rfl, T.coe_nonneg⟩)).trans
      (hV0.trans (AdditiveCanonical.initialSampler_coe (brownianProbability (I := I)) ν hν).symm)
  have he := ConstructedPredictableLaw.law_distance_decay μ ν hμ hν
    R.predictableData R'.predictableData hRU0 hRV0 G hb hσ ρ hmono
  change optimizerLawDistance (R.optimizer T) (R'.optimizer T)
    ((μ.prod (brownianProbability (I := I))).map (R.predictableData.sampler T))
    ((ν.prod (brownianProbability (I := I))).map (R'.predictableData.sampler T)) ≤
      Real.sqrt G.conditionNumber * Real.exp (-ρ * T) *
        optimizerLawDistance (R.optimizer 0) (R'.optimizer 0) μ ν at he
  rw [R.predictableData_law T ⟨T.coe_nonneg, le_rfl⟩,
    R'.predictableData_law T ⟨T.coe_nonneg, le_rfl⟩] at he
  exact he

end PBGSO.RawLinearGrowthLaw
