import PBGSO.NaturalFiniteWorkLaw
import PBGSO.RawSolutionLawUniqueness

/-! # Finite-signed-work constant-diffusion contraction on arbitrary original probability spaces
Original solution laws are identified with actual canonical Gaussian-source
strong solutions through one genuine Wiener-path-source solution per initial
law. These are direct strong-well-posedness instances; no output-law match or
common frozen realization is assumed. The canonical equations satisfy the
explicit unconditional finite signed-work convention.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.NaturalFiniteWorkArbitraryLaw
open FilteredBrownian RawLocalStationarity RawSamplerGrowth ConstructedItoLaw
variable {Ω Ω' S Θ Z X I : Type*}
  [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S] [FiniteDimensional ℝ S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace Θ] [BorelSpace Θ] [SecondCountableTopology Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z] [FiniteDimensional ℝ Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {R : Measure Ω'} [IsProbabilityMeasure R]
  {D : Driver (I := I) Q} {E : Driver (I := I) R}
  {M : Model S Θ Z X I} {T : ℝ≥0}

/-- Actual canonical strong existence on the genuine Gaussian probability source. The only identities are the original initial conditions. -/
structure CanonicalSolution (μ : Measure Z) [IsProbabilityMeasure μ] (s : S) where
  data : RawLocalStationarity.Data (μ.prod (brownianProbability (I := I)))
    (CanonicalBrownianDriver.driver (I := I) μ) M T
  initial_optimizer : data.optimizer 0 = s
  initial_sampler : data.sampler.state 0 =ᵐ[μ.prod (brownianProbability (I := I))] Prod.fst

/-- Source A3 law contraction under finite signed coupling work for original raw solutions on two arbitrary
filtered Brownian sources. Strong well-posedness is used through actual
canonical/path-source existence and original-source pathwise uniqueness;
all marginal-law and stochastic matching conclusions are proved. -/
theorem law_distance_decay
    (U : RawLocalStationarity.Data Q D M T) (V : RawLocalStationarity.Data R E M T)
    (μ ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp (fun z : Z => z) 2 μ) (hν : MemLp (fun z : Z => z) 2 ν)
    (hU : Q.map (U.sampler.state 0) = μ) (hV : R.map (V.sampler.state 0) = ν)
    (A : CanonicalSolution (M := M) (T := T) μ (U.optimizer 0))
    (B : CanonicalSolution (M := M) (T := T) ν (V.optimizer 0))
    (huniqueU : PathwiseUniqueness Q (nullAugmentedDriver Q (continuousDriver Q D)) M T)
    (huniqueV : PathwiseUniqueness R (nullAugmentedDriver R (continuousDriver R E)) M T)
    (huniqueA : PathwiseUniqueness (μ.prod (brownianProbability (I := I)))
      (nullAugmentedDriver _ (continuousDriver _ (CanonicalBrownianDriver.driver (I := I) μ))) M T)
    (huniqueB : PathwiseUniqueness (ν.prod (brownianProbability (I := I)))
      (nullAugmentedDriver _ (continuousDriver _ (CanonicalBrownianDriver.driver (I := I) ν))) M T)
    (hpathμ : ∃ W : RawLocalStationarity.Data (BrownianPathDriver.probability (I := I) μ)
        (BrownianPathDriver.driver μ) M T,
      W.optimizer 0 = U.optimizer 0 ∧
      W.sampler.state 0 =ᵐ[BrownianPathDriver.probability (I := I) μ] Prod.fst)
    (hpathν : ∃ W : RawLocalStationarity.Data (BrownianPathDriver.probability (I := I) ν)
        (BrownianPathDriver.driver ν) M T,
      W.optimizer 0 = V.optimizer 0 ∧
      W.sampler.state 0 =ᵐ[BrownianPathDriver.probability (I := I) ν] Prod.fst)
    (G : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M G ρ)
    (hfull : DiracOptimizerGrowth.FiniteCouplingWork M G)
    (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i)
    (hb : ∀ θ, Measurable (M.drift θ))
    (hObs : Measurable (fun p : S × Z => M.observation (M.parameter p.1) (M.position p.2)))
    (hDrift : Measurable (fun p : S × Z => M.drift (M.parameter p.1) p.2))
    (hOptimizer : Measurable (fun p : ℝ × (S × Θ) => M.optimizer p.1 p.2.1 p.2.2)) :
    optimizerLawDistance (U.optimizer T) (V.optimizer T)
      (Q.map (U.sampler.state T)) (R.map (V.sampler.state T)) ≤
      Real.sqrt G.conditionNumber * Real.exp (-ρ * (T : ℝ)) *
        optimizerLawDistance (U.optimizer 0) (V.optimizer 0) μ ν := by
  have hA0 : (μ.prod (brownianProbability (I := I))).map (A.data.sampler.state 0) = μ := by
    rw [Measure.map_congr A.initial_sampler,Measure.map_fst_prod,measure_univ,one_smul]
  have hB0 : (ν.prod (brownianProbability (I := I))).map (B.data.sampler.state 0) = ν := by
    rw [Measure.map_congr B.initial_sampler,Measure.map_fst_prod,measure_univ,one_smul]
  have hUA := law_unique_two_sources U A.data μ hU hA0 A.initial_optimizer.symm
    huniqueU huniqueA hpathμ T ⟨T.coe_nonneg,le_rfl⟩
  have hVB := law_unique_two_sources V B.data ν hV hB0 B.initial_optimizer.symm
    huniqueV huniqueB hpathν T ⟨T.coe_nonneg,le_rfl⟩
  have h := NaturalFiniteWorkLaw.law_distance_decay μ ν hμ hν A.data B.data
    A.initial_sampler B.initial_sampler G ρ hρ hmono hfull hσ hb hObs hDrift hOptimizer
  rw [A.initial_optimizer,B.initial_optimizer] at h
  rw [hUA.1,hVB.1,hUA.2,hVB.2]
  exact h

end PBGSO.NaturalFiniteWorkArbitraryLaw
