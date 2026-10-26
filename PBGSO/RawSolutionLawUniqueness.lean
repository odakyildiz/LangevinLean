import PBGSO.RawPathSolutionTransfer

/-! # Original strong-solution law uniqueness across arbitrary sources
Both original equations are compared with one actual strong solution on the
proved initial-law / Wiener-path probability space. The initial/noise maps
and stochastic-integral transport are derived, and output-law equality is a
conclusion. Existence on that single genuine source and pathwise uniqueness
on the two original augmented sources are direct well-posedness instances.
-/
noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.RawLocalStationarity
open FilteredBrownian
variable {Ω Ω' S Θ Z X I : Type*}
  [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {R : Measure Ω'} [IsProbabilityMeasure R]
  {D : Driver (I := I) Q} {E : Driver (I := I) R}
  {M : Model S Θ Z X I} {T : ℝ≥0}

/-- A1 uniqueness on two original sources and existence on their common
initial-law/Wiener-path source imply actual optimizer and marginal-law
uniqueness. No common-space output coupling or output-law match is assumed. -/
theorem law_unique_two_sources (U : Data Q D M T) (V : Data R E M T)
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (hU : Q.map (U.sampler.state 0) = μ)
    (hV : R.map (V.sampler.state 0) = μ)
    (hs : U.optimizer 0 = V.optimizer 0)
    (huniqueU : PathwiseUniqueness Q (nullAugmentedDriver Q (continuousDriver Q D)) M T)
    (huniqueV : PathwiseUniqueness R (nullAugmentedDriver R (continuousDriver R E)) M T)
    (hexists : ∃ W : Data (BrownianPathDriver.probability (I := I) μ)
        (BrownianPathDriver.driver μ) M T,
      W.optimizer 0 = U.optimizer 0 ∧
      W.sampler.state 0 =ᵐ[BrownianPathDriver.probability (I := I) μ] Prod.fst)
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    U.optimizer t = V.optimizer t ∧ Q.map (U.sampler.state t) = R.map (V.sampler.state t) := by
  obtain ⟨W,hsW,hzW⟩ := hexists
  have hu := U.law_eq_pathspace_solution μ hU huniqueU W hsW.symm hzW t ht
  have hv := V.law_eq_pathspace_solution μ hV huniqueV W (hs.symm.trans hsW.symm) hzW t ht
  exact ⟨hu.1.trans hv.1.symm,hu.2.trans hv.2.symm⟩

end PBGSO.RawLocalStationarity
