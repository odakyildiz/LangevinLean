import PBGSO.RawSamplerCoerciveMoment
import PBGSO.FiniteWorkPositiveIntegrability
import PBGSO.RawNaturalConstantNoise
import PBGSO.ConstantNoiseFluctuation

/-! # Natural constant-noise contraction under finite signed coupling work
Original raw equations and joint monotonicity derive uniform state moments
by genuine stopped coercivity. The explicit finite-integral reading of A3
then derives positive-work Fubini and contraction. No optimizer response
Lipschitzness, drift growth, supplied moments, noise match or energy balance
is assumed. Extended-negative-work interpretations remain separate.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.NaturalFiniteWorkContraction
open FilteredBrownian RawLocalStationarity RawNaturalConstantNoise RawConstantNoiseContraction
variable {Ω S Θ Z X I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S] [FiniteDimensional ℝ S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace Θ] [BorelSpace Θ] [SecondCountableTopology Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z] [FiniteDimensional ℝ Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {Q : Measure Ω} [IsProbabilityMeasure Q] {W : Driver (I := I) Q}
  {M : Model S Θ Z X I} {T : ℝ≥0}

/-- Actual product-space state moments survive the proved single-event
whole-horizon raw realization. -/
theorem realization_product_memLp (U : RawLocalStationarity.Data Q W M T)
    (A : Realization U)
    (hU : MemLp (Function.uncurry U.sampler.state) 2
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) :
    MemLp (Function.uncurry A.data.sampler) 2 ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := by
  have he : Function.uncurry A.data.sampler =ᵐ[(volume.restrict (Ioc 0 (T : ℝ))).prod Q]
      Function.uncurry U.sampler.state := by
    have hx := (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (Ioc 0 (T : ℝ))) (ν := Q)).ae A.sampler_eq
    have hr := (Measure.quasiMeasurePreserving_fst
      (μ := volume.restrict (Ioc 0 (T : ℝ))) (ν := Q)).ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hx,hr] with p hx hr
    exact hx p.1 (Ioc_subset_Icc_self hr)
  exact (memLp_congr_ae he).mpr hU

/-- Natural original equations derive the positive-work Fubini premise.
The finite signed coupling-work convention is independent of observation
domains and of the conditional joint inequality. -/
theorem realized_positive_work_integrable
    (U V : RawLocalStationarity.Data Q W M T) (A : Realization U) (B : Realization V)
    (D : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M D ρ)
    (hfull : DiracOptimizerGrowth.FiniteCouplingWork M D)
    (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i)
    (hDrift : Measurable (fun p : S × Z => M.drift (M.parameter p.1) p.2)) :
    Integrable (fun p : ℝ × Ω => max (rawMetricBilinear D
      (pairState Q M A.data B.data p.1 p.2) (pairDrift Q M A.data B.data p.1 p.2)) 0)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := by
  have hU := (RawSamplerCoerciveMoment.natural_moments U hDrift D ρ hρ hmono hσ).2
  have hV := (RawSamplerCoerciveMoment.natural_moments V hDrift D ρ hρ hmono hσ).2
  exact FiniteWorkPositiveIntegrability.positive_work_integrable A.data B.data D ρ hρ.le hmono
    hfull hσ (realization_product_memLp U A hU) (realization_product_memLp V B hV)

/-- Original whole-state RMS contraction in the source constant-diffusion
branch, under the explicit ordinary finite-integral reading of A3. Every
state moment, local-noise cancellation, and Fubini premise is derived. -/
theorem rms_decay (U V : RawLocalStationarity.Data Q W M T)
    (D : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M D ρ)
    (hfull : DiracOptimizerGrowth.FiniteCouplingWork M D)
    (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i)
    (hb : ∀ θ, Measurable (M.drift θ))
    (hObs : Measurable (fun p : S × Z => M.observation (M.parameter p.1) (M.position p.2)))
    (hDrift : Measurable (fun p : S × Z => M.drift (M.parameter p.1) p.2))
    (hOptimizer : Measurable (fun p : ℝ × (S × Θ) => M.optimizer p.1 p.2.1 p.2.2)) :
    Real.sqrt (‖U.optimizer T-V.optimizer T‖ ^ 2+
      ‖ProductLpSections.sectionLp Q U.sampler.state T-
        ProductLpSections.sectionLp Q V.sampler.state T‖ ^ 2) ≤
      Real.sqrt D.conditionNumber * Real.exp (-ρ * (T : ℝ)) *
        Real.sqrt (‖U.optimizer 0-V.optimizer 0‖ ^ 2+
          ‖ProductLpSections.sectionLp Q U.sampler.state 0-
            ProductLpSections.sectionLp Q V.sampler.state 0‖ ^ 2) := by
  let A := build U hσ hObs hDrift hOptimizer
  let B := build V hσ hObs hDrift hOptimizer
  have h := ConstantNoiseFluctuation.rms_decay_of_positive_work M D Q A.data B.data
    ρ hρ.le hmono hσ hb (realized_positive_work_integrable U V A B D ρ hρ hmono hfull hσ hDrift)
  rw [A.optimizer_eq T ⟨T.coe_nonneg,le_rfl⟩,B.optimizer_eq T ⟨T.coe_nonneg,le_rfl⟩,
    A.optimizer_eq 0 ⟨le_rfl,T.coe_nonneg⟩,B.optimizer_eq 0 ⟨le_rfl,T.coe_nonneg⟩,
    A.sampler_section T ⟨T.coe_nonneg,le_rfl⟩,B.sampler_section T ⟨T.coe_nonneg,le_rfl⟩,
    A.sampler_section 0 ⟨le_rfl,T.coe_nonneg⟩,B.sampler_section 0 ⟨le_rfl,T.coe_nonneg⟩] at h
  exact h

/-- Actual output laws contract through their genuine realized raw coupling;
no final coupling, weak-generator equation or output-law match is supplied. -/
theorem pair_law_distance_decay (U V : RawLocalStationarity.Data Q W M T)
    (D : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M D ρ)
    (hfull : DiracOptimizerGrowth.FiniteCouplingWork M D)
    (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i)
    (hb : ∀ θ, Measurable (M.drift θ))
    (hObs : Measurable (fun p : S × Z => M.observation (M.parameter p.1) (M.position p.2)))
    (hDrift : Measurable (fun p : S × Z => M.drift (M.parameter p.1) p.2))
    (hOptimizer : Measurable (fun p : ℝ × (S × Θ) => M.optimizer p.1 p.2.1 p.2.2)) :
    optimizerLawDistance (U.optimizer T) (V.optimizer T)
      (Q.map (U.sampler.state T)) (Q.map (V.sampler.state T)) ≤
      Real.sqrt D.conditionNumber * Real.exp (-ρ * (T : ℝ)) *
        Real.sqrt (‖U.optimizer 0-V.optimizer 0‖ ^ 2+
          ‖ProductLpSections.sectionLp Q U.sampler.state 0-
            ProductLpSections.sectionLp Q V.sampler.state 0‖ ^ 2) := by
  let A := build U hσ hObs hDrift hOptimizer
  let B := build V hσ hObs hDrift hOptimizer
  have h := ConstantNoiseFluctuation.pair_law_distance_decay_of_positive_work M D Q A.data B.data
    ρ hρ.le hmono hσ hb (realized_positive_work_integrable U V A B D ρ hρ hmono hfull hσ hDrift)
  rw [A.optimizer_eq T ⟨T.coe_nonneg,le_rfl⟩,B.optimizer_eq T ⟨T.coe_nonneg,le_rfl⟩,
    A.optimizer_eq 0 ⟨le_rfl,T.coe_nonneg⟩,B.optimizer_eq 0 ⟨le_rfl,T.coe_nonneg⟩,
    A.sampler_law T ⟨T.coe_nonneg,le_rfl⟩,B.sampler_law T ⟨T.coe_nonneg,le_rfl⟩,
    A.sampler_section 0 ⟨le_rfl,T.coe_nonneg⟩,B.sampler_section 0 ⟨le_rfl,T.coe_nonneg⟩] at h
  exact h

end PBGSO.NaturalFiniteWorkContraction
