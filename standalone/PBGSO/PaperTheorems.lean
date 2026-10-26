import PBGSO.RawPathSolutionTransfer
import PBGSO.RawStationaryUniqueness
import PBGSO.NaturalFiniteWorkArbitraryLaw
import PBGSO.RawSamplerGrowthArbitraryLaw
import PBGSO.RawConstructedParticleBounds
import PBGSO.RawConstructedParticleParameter
import PBGSO.RawConstructedParticleJointLimit
import PBGSO.SmallGainSpectrum
import PBGSO.ProjectedFiniteWork
import PBGSO.HypocoerciveCriterion
import PBGSO.ContinuousFlowMeasure
import PBGSO.DiscreteVolume

/-!
# Original PBGSO paper: inspectable theorem statements

Read the declarations below to inspect the exact assumptions and conclusions;
each proof is only an application of the checked library result. No energy
identity, stochastic matching assertion, moment bound or final error estimate
has been added as a premise.

Notation: `S` is the full optimiser state, `Θ` its parameter, `Z` the full
sampler state, `X` its position and `I` the finite Brownian coordinate index.
`M : Model S Θ Z X I` contains the independent observation, optimiser,
sampler-drift and diffusion maps; it imposes no IPLA or common-potential form.
`G : TwistedGeometry S Z` supplies positive quadratic weights and their
certified lower/upper comparisons. `optimizerLawDistance` is the square root
of optimiser squared distance plus the squared 2-Wasserstein distance.

`RawLocalStationarity.Data` is an original raw integral SDE/optimiser solution,
with local pathwise integrability and adaptation, not an energy equation.
`PathwiseUniqueness` and the canonical/path-source initial-value witnesses
are the exact strong well-posedness instances used from A1. `Regularity`
records primitive measurability, progressivity and linear coefficient growth.
`FrozenSamplerData` is an actual invariant frozen sampler equation (A2).
`Family` below records actual trajectories/existence/uniqueness; stationarity
is a comparison-class premise for uniqueness, not an assumed decay result.

The constant-diffusion Theorem 2 explicitly uses `FiniteCouplingWork`: ordinary
finite signed sampler work for EVERY finite-second-moment coupling. It is
an interpretation/domain assumption separate from the conditional A3
inequality. The more general extended-negative-work reading is not claimed.
Theorem 4's constant branch uses A4/A5 and does not need this assumption.

To export this file with its complete Mathlib-only proof closure:
  python3 scripts/check-pbgso-standalone.py --endpoint paper --output /tmp/pbgso-paper --check
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal Topology BigOperators InnerProductSpace RealInnerProductSpace
  MatrixOrder Matrix.Norms.L2Operator
namespace PBGSO.Standalone.PaperTheorems


/-! ## Theorem 1 — stationary product law -/
section
open PBGSO.RawLocalStationarity
open PBGSO.FilteredBrownian
variable {Ω S Θ Z X I : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)
  {M : Model S Θ Z X I} {T : ℝ≥0}

variable {Q D}
variable {Ωw : Type*} [MeasurableSpace Ωw]
  (Qw : Measure Ωw) [IsProbabilityMeasure Qw]
  (Dw : Driver (I := I) Qw)

theorem theorem1_stationary_product [MeasurableSpace S]
    {sStar : S} {νStar : Measure Z} [IsProbabilityMeasure νStar]
    (F : FrozenSamplerData Qw Dw M T sStar νStar)
    (hint : Integrable (fun z => M.observation (M.parameter sStar) (M.position z)) νStar)
    (hg : M.meanGradient νStar sStar = 0)
    (hfix : ∀ t ∈ Icc 0 (T : ℝ), M.optimizer t sStar 0 = 0)
    (huniquew : PathwiseUniqueness Qw (nullAugmentedDriver Qw (continuousDriver Qw Dw)) M T)
    (hexists : ∃ V : Data (BrownianPathDriver.probability (I := I) νStar)
        (BrownianPathDriver.driver νStar) M T,
      V.optimizer 0 = sStar ∧ V.sampler.state 0 =ᵐ[
        BrownianPathDriver.probability (I := I) νStar] Prod.fst)
    (U : Data Q D M T)
    (hunique : PathwiseUniqueness Q (nullAugmentedDriver Q (continuousDriver Q D)) M T)
    (hs : U.optimizer 0 = sStar) (hν : Q.map (U.sampler.state 0) = νStar)
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    Q.map (fun ω => (U.optimizer t, U.sampler.state t ω)) = (Measure.dirac sStar).prod νStar := by
  exact PBGSO.RawLocalStationarity.stationary_product_law_of_weak_frozen Qw Dw F hint hg hfix huniquew hexists U hunique hs hν t ht

#print axioms PBGSO.Standalone.PaperTheorems.theorem1_stationary_product

end


/-! ## Theorem 2 — constant diffusion, ordinary finite signed work -/
section
open PBGSO.NaturalFiniteWorkArbitraryLaw
open PBGSO.FilteredBrownian PBGSO.RawLocalStationarity PBGSO.ConstructedItoLaw
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

theorem theorem2_constant_diffusion
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
  apply PBGSO.NaturalFiniteWorkArbitraryLaw.law_distance_decay <;> assumption

#print axioms PBGSO.Standalone.PaperTheorems.theorem2_constant_diffusion

end


/-! ## Theorem 2 — state-dependent linear growth -/
section
open PBGSO.RawSamplerGrowthArbitraryLaw
open PBGSO.FilteredBrownian PBGSO.RawLocalStationarity PBGSO.RawSamplerGrowth PBGSO.ConstructedItoLaw
variable {Ω Ω' S Θ Z X I : Type*}
  [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {R : Measure Ω'} [IsProbabilityMeasure R]
  {D : Driver (I := I) Q} {E : Driver (I := I) R}
  {M : Model S Θ Z X I} {T : ℝ≥0}


theorem theorem2_linear_growth
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
    (G : TwistedGeometry S Z) (ρ : ℝ) (hmono : TwistedJointMonotonicity M G ρ) :
    optimizerLawDistance (U.optimizer T) (V.optimizer T)
      (Q.map (U.sampler.state T)) (R.map (V.sampler.state T)) ≤
      Real.sqrt G.conditionNumber * Real.exp (-ρ * (T : ℝ)) *
        optimizerLawDistance (U.optimizer 0) (V.optimizer 0) μ ν := by
  apply PBGSO.RawSamplerGrowthArbitraryLaw.law_distance_decay <;> assumption

#print axioms PBGSO.Standalone.PaperTheorems.theorem2_linear_growth

end


/-! ## Theorem 2 — uniqueness of stationary laws -/
section
open PBGSO.RawStationaryUniqueness
open PBGSO.FilteredBrownian PBGSO.RawLocalStationarity PBGSO.ConstructedItoLaw
variable {Ω Ω' S Θ Z X I : Type*}
  [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S] [FiniteDimensional ℝ S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace Θ] [BorelSpace Θ] [SecondCountableTopology Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z] [FiniteDimensional ℝ Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)
  (M : Model S Θ Z X I) (s : S) (ν : Measure Z) [IsProbabilityMeasure ν]
variable {Q D M s ν}
variable {R : Measure Ω'} [IsProbabilityMeasure R] {E : Driver (I := I) R}
  {s' : S} {ν' : Measure Z} [IsProbabilityMeasure ν']

theorem theorem2_stationary_unique_constant
    (F : Family Q D M s ν) (H : Family R E M s' ν')
    (hν : MemLp (fun z : Z => z) 2 ν) (hν' : MemLp (fun z : Z => z) 2 ν')
    (G : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M G ρ)
    (hfull : DiracOptimizerGrowth.FiniteCouplingWork M G)
    (hσ : ∀ a a' z w i, M.diffusion (M.parameter a) z i = M.diffusion (M.parameter a') w i)
    (hb : ∀ θ, Measurable (M.drift θ))
    (hObs : Measurable (fun p : S × Z => M.observation (M.parameter p.1) (M.position p.2)))
    (hDrift : Measurable (fun p : S × Z => M.drift (M.parameter p.1) p.2))
    (hOptimizer : Measurable (fun p : ℝ × (S × Θ) => M.optimizer p.1 p.2.1 p.2.2)) :
    s = s' ∧ ν = ν' := by
  exact PBGSO.RawStationaryUniqueness.stationary_laws_unique_constant F H hν hν' G ρ hρ hmono hfull hσ hb hObs hDrift hOptimizer

#print axioms PBGSO.Standalone.PaperTheorems.theorem2_stationary_unique_constant

theorem theorem2_stationary_unique_linear_growth
    (F : Family Q D M s ν) (H : Family R E M s' ν')
    (RF : ∀ T : ℝ≥0, RawSamplerGrowth.Regularity (F.canonical T).data)
    (RH : ∀ T : ℝ≥0, RawSamplerGrowth.Regularity (H.canonical T).data)
    (hν : MemLp (fun z : Z => z) 2 ν) (hν' : MemLp (fun z : Z => z) 2 ν')
    (G : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M G ρ) : s = s' ∧ ν = ν' := by
  exact PBGSO.RawStationaryUniqueness.stationary_laws_unique_linearGrowth F H RF RH hν hν' G ρ hρ hmono

#print axioms PBGSO.Standalone.PaperTheorems.theorem2_stationary_unique_linear_growth

end


/-! ## Theorem 3 — native empirical interaction -/
section
open PBGSO.RawConstructedParticleBounds
open PBGSO.FilteredBrownian PBGSO.ConstructedItoParticle PBGSO.RawConstructedParticleCopy
variable {Ω S Θ Z X I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace Θ] [BorelSpace Θ] [SecondCountableTopology Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)
  (M : Model S Θ Z X I) (N : ℕ) {T : ℝ≥0}
  (U : RawLocalStationarity.Data Q D M T)
  (Y : RawEmpiricalDynamics.Solution M N
    (IndependentCopies.seeds (J := Fin N) Q) (RawIndependentCopies.driver Q D N) T)

theorem theorem3_particle_interaction
    (hBorelF : Measurable (fun p : S × Z => M.observation (M.parameter p.1) (M.position p.2)))
    (hBorelb : Measurable (fun p : S × Z => M.drift (M.parameter p.1) p.2))
    (hBorelΨ : Measurable (fun p : ℝ × (S × Θ) => M.optimizer p.1 p.2.1 p.2.2))
    (G : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M G ρ) (hN : 0 < N)
    (LΨ : ℝ≥0) (V : ℝ) (hV : 0 ≤ V)
    (hΨ : ∀ t ∈ Icc 0 (T : ℝ), ∀ s g g',
      ‖M.optimizer t s g-M.optimizer t s g'‖ ≤ (LΨ : ℝ)*‖g-g'‖)
    (hF : ∀ t ∈ Icc 0 (T : ℝ), MemLp
      (fun z => M.observation (M.parameter (U.optimizer t)) (M.position z)) 2
      (Q.map (U.sampler.state t)))
    (hVar : ∀ t ∈ Icc 0 (T : ℝ),
      (∫ z, ‖M.observation (M.parameter (U.optimizer t)) (M.position z)-
        M.meanGradient (Q.map (U.sampler.state t)) (U.optimizer t)‖^2
          ∂Q.map (U.sampler.state t)) ≤ V)
    (hinit : ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q,
      oneEquiv N (Y.state 0 ω) = (U.optimizer 0,RawIndependentCopies.cloud Q D N U 0 ω)) :
    Real.sqrt (∫ ω, particleEmpiricalDistanceSq N (originalPair Q D M N U Y T ω)
      ∂IndependentCopies.seeds (J := Fin N) Q) ≤
      ((LΨ : ℝ)/ρ)*Real.sqrt (G.conditionNumber*V/(N : ℝ))*(1-Real.exp (-ρ*T)) := by
  apply PBGSO.RawConstructedParticleBounds.original_finite_particle_interaction_bound <;> assumption

#print axioms PBGSO.Standalone.PaperTheorems.theorem3_particle_interaction

end


/-! ## Theorem 4 — native parameter error, both A1 branches -/
section
open PBGSO.RawConstructedParticleParameter
open PBGSO.FilteredBrownian PBGSO.RawLocalStationarity PBGSO.ConstructedItoParticle PBGSO.ConstructedItoLaw
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


theorem theorem4_parameter_constant
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
  apply PBGSO.RawConstructedParticleParameter.original_parameter_bound_constant <;> assumption

#print axioms PBGSO.Standalone.PaperTheorems.theorem4_parameter_constant

theorem theorem4_parameter_linear_growth
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
  apply PBGSO.RawConstructedParticleParameter.original_parameter_bound_linearGrowth <;> assumption

#print axioms PBGSO.Standalone.PaperTheorems.theorem4_parameter_linear_growth

end


/-! ## Theorem 4 — joint time/particle limit -/
section
open PBGSO.RawConstructedParticleJointLimit
open PBGSO.FilteredBrownian PBGSO.RawLocalStationarity PBGSO.ConstructedItoParticle PBGSO.ConstructedItoLaw
variable {Ω S Θ Z X I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace Θ] [BorelSpace Θ] [SecondCountableTopology Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (W : Driver (I := I) Q)
  (M : Model S Θ Z X I) (μ νStar : Measure Z)
  [IsProbabilityMeasure μ] [IsProbabilityMeasure νStar] (s0 sStar : S)
variable (F : Family Q W M μ νStar s0 sStar)

theorem theorem4_joint_limit
    (hμ : MemLp (fun z : Z => z) 2 μ) (hν : MemLp (fun z : Z => z) 2 νStar)
    (G : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M G ρ)
    (hProjection : LipschitzWith 1 M.parameter)
    (hb : ∀ θ, Measurable (M.drift θ))
    (hF : Measurable (fun p : S × Z => M.observation (M.parameter p.1) (M.position p.2)))
    (hDrift : Measurable (fun p : S × Z => M.drift (M.parameter p.1) p.2))
    (hOptimizer : Measurable (fun p : ℝ × (S × Θ) => M.optimizer p.1 p.2.1 p.2.2))
    (LΨ : ℝ≥0) (VF : ℝ)
    (hΨ : ∀ r, 0 ≤ r → ∀ s g g',
      ‖M.optimizer r s g-M.optimizer r s g'‖ ≤ (LΨ : ℝ)*‖g-g'‖)
    (hU2 : ∀ T : ℝ≥0, ∀ r ∈ Icc 0 (T : ℝ), MemLp
      (fun z => M.observation (M.parameter ((F.reference T).optimizer r)) (M.position z))
        2 (Q.map ((F.reference T).sampler.state r)))
    (hVar : ∀ T : ℝ≥0, ∀ r ∈ Icc 0 (T : ℝ),
      (∫ z, ‖M.observation (M.parameter ((F.reference T).optimizer r)) (M.position z)-
        M.meanGradient (Q.map ((F.reference T).sampler.state r)) ((F.reference T).optimizer r)‖^2
        ∂Q.map ((F.reference T).sampler.state r)) ≤ VF)
    (hobs : Integrable (fun z => M.observation (M.parameter sStar) (M.position z)) νStar)
    (hbranch : Branch Q W M μ νStar s0 sStar F) :
    Tendsto (fun p : ℕ × ℝ => parameterError Q W M μ νStar s0 sStar F p.1 p.2)
      (atTop ×ˢ atTop) (𝓝 0) := by
  apply PBGSO.RawConstructedParticleJointLimit.parameter_joint_limit <;> assumption

#print axioms PBGSO.Standalone.PaperTheorems.theorem4_joint_limit

end


/-! ## Appendix corollary — separated small gain -/
section
open PBGSO
variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype I]

theorem appendix_separated_criterion (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    (rO rS : ℝ) (LΨ LF Lb Lσ : ℝ≥0)
    (H : SeparatedAssumptions M D rO rS LΨ LF Lb Lσ)
    (hO : 0 < 2 * rO - D.conditionNumber * (Lσ : ℝ) ^ 2)
    (hS : 0 < 2 * rS - D.conditionNumber * (Lσ : ℝ) ^ 2)
    (hdet : D.conditionNumber * ((LΨ : ℝ) * (LF : ℝ) + (Lb : ℝ)) ^ 2 <
      (2 * rO - D.conditionNumber * (Lσ : ℝ) ^ 2) *
        (2 * rS - D.conditionNumber * (Lσ : ℝ) ^ 2)) :
    (separatedSmallGainMatrix D rO rS LΨ LF Lb Lσ).PosDef ∧
      0 < separatedMinimumEigenvalue D rO rS LΨ LF Lb Lσ ∧
      TwistedJointMonotonicity M D (separatedMinimumEigenvalue D rO rS LΨ LF Lb Lσ) := by
  apply PBGSO.separated_source_criterion <;> assumption

#print axioms PBGSO.Standalone.PaperTheorems.appendix_separated_criterion

end


/-! ## Appendix corollary — projected generalized spectrum -/
section
open PBGSO.CanonicalProjected
open PBGSO.GeneralizedSpectrum
variable {a u x v I : Type*}
  [Fintype a] [DecidableEq a] [Nonempty a] [Fintype u] [DecidableEq u]
  [Fintype x] [DecidableEq x] [Nonempty x] [Fintype v] [DecidableEq v] [Fintype I]


theorem appendix_projected_criterion
    (M : Model (BlockSpace a u) (EuclideanSpace ℝ a) (BlockSpace x v) (EuclideanSpace ℝ x) I)
    (hparameter : M.parameter = WithLp.fst) (hposition : M.position = WithLp.fst)
    (H : EuclideanSpace ℝ a → EuclideanSpace ℝ x → EuclideanSpace ℝ x)
    (DOpt : Matrix (a ⊕ u) (a ⊕ u) ℝ) (DSam : Matrix (x ⊕ v) (x ⊕ v) ℝ)
    (Dm : Matrix u u ℝ) (Dv : Matrix v v ℝ)
    (hDOpt : DOpt.PosDef) (hDSam : DSam.PosDef) (hDm : Dm.PosDef) (hDv : Dv.PosDef)
    (β r AOpt ASam : ℝ) (hβ : 0 ≤ β) (hc : 0 < β * r - AOpt - ASam)
    (hmono : (canonicalData M hparameter hposition H Dm Dv).StrongMonotonicity r)
    (haux : ProjectedAuxiliaryDissipation M (canonicalGeometry DOpt DSam hDOpt hDSam)
      (canonicalData M hparameter hposition H Dm Dv) β AOpt ASam)
    (σ : I → BlockSpace x v) (hσ : ∀ θ z, M.diffusion θ z = σ)
    (hInt : ∀ s s' ν ν' Λ,
      ProjectedAdmissibleCoupling M (canonicalGeometry DOpt DSam hDOpt hDSam) s s' ν ν' Λ →
      (canonicalData M hparameter hposition H Dm Dv).Integrability s s' Λ) :
    let ρ := min
      (generalizedMinimum hDOpt (blockK_posDef (a := a) _ hc Dm hDm))
      (generalizedMinimum hDSam (blockK_posDef (a := x) _ hc Dv hDv))
    0 < ρ ∧ TwistedJointMonotonicity M (canonicalGeometry DOpt DSam hDOpt hDSam) ρ := by
  apply PBGSO.CanonicalProjected.canonical_projected_source_criterion <;> assumption

#print axioms PBGSO.Standalone.PaperTheorems.appendix_projected_criterion

end


/-! ## Appendix corollary — projected finite signed-work domain -/
section
open PBGSO.CanonicalProjected
open PBGSO.GeneralizedSpectrum
variable {a u x v I : Type*}
  [Fintype a] [DecidableEq a] [Nonempty a] [Fintype u] [DecidableEq u]
  [Fintype x] [DecidableEq x] [Nonempty x] [Fintype v] [DecidableEq v] [Fintype I]


theorem appendix_projected_finite_work
    (M : Model (BlockSpace a u) (EuclideanSpace ℝ a) (BlockSpace x v) (EuclideanSpace ℝ x) I)
    (hparameter : M.parameter = WithLp.fst) (hposition : M.position = WithLp.fst)
    (H : EuclideanSpace ℝ a → EuclideanSpace ℝ x → EuclideanSpace ℝ x)
    (DOpt : Matrix (a ⊕ u) (a ⊕ u) ℝ) (DSam : Matrix (x ⊕ v) (x ⊕ v) ℝ)
    (Dm : Matrix u u ℝ) (Dv : Matrix v v ℝ)
    (hDOpt : DOpt.PosDef) (hDSam : DSam.PosDef) (hDm : Dm.PosDef) (hDv : Dv.PosDef)
    (β r AOpt ASam : ℝ) (hβ : 0 ≤ β) (hc : 0 < β * r - AOpt - ASam)
    (hmono : (canonicalData M hparameter hposition H Dm Dv).StrongMonotonicity r)
    (haux : ProjectedAuxiliaryDissipation M (canonicalGeometry DOpt DSam hDOpt hDSam)
      (canonicalData M hparameter hposition H Dm Dv) β AOpt ASam)
    (σ : I → BlockSpace x v) (hσ : ∀ θ z, M.diffusion θ z = σ)
    (hInt : ∀ s s' ν ν' Λ,
      ProjectedAdmissibleCoupling M (canonicalGeometry DOpt DSam hDOpt hDSam) s s' ν ν' Λ →
      (canonicalData M hparameter hposition H Dm Dv).Integrability s s' Λ)
    (hfinite : FiniteSamplerDriftDomain M (canonicalGeometry DOpt DSam hDOpt hDSam)) :
    let ρ := min
      (generalizedMinimum hDOpt (blockK_posDef (a := a) _ hc Dm hDm))
      (generalizedMinimum hDSam (blockK_posDef (a := x) _ hc Dv hDv))
    0 < ρ ∧ TwistedJointMonotonicity M (canonicalGeometry DOpt DSam hDOpt hDSam) ρ ∧
      DiracOptimizerGrowth.FiniteCouplingWork M (canonicalGeometry DOpt DSam hDOpt hDSam) := by
  apply PBGSO.CanonicalProjected.canonical_projected_source_criterion_finite <;> assumption

#print axioms PBGSO.Standalone.PaperTheorems.appendix_projected_finite_work

end


/-! ## Appendix proposition — heavy-ball criterion -/
section
open PBGSO
variable {A X I : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [Fintype I]


theorem appendix_heavy_ball_criterion (γ r : ℝ) (L : ℝ≥0)
    (hγ : 0 < γ) (hr : 0 < r)
    (hsource : Real.sqrt 2 * (L : ℝ) / Real.sqrt r < γ)
    (F : A → X → A) (H : A → X → X) (σ : I → HypocoercivePhase X)
    (hmono : ∀ θ θ' x x', r * (‖θ - θ'‖ ^ 2 + ‖x - x'‖ ^ 2) ≤
      ⟪θ - θ', F θ x - F θ' x'⟫_ℝ + ⟪x - x', H θ x - H θ' x'⟫_ℝ)
    (hLip : LipschitzWith L (heavyBallProjectedField F H)) :
    0 < hypocoerciveRate γ r L ∧
      TwistedJointMonotonicity (heavyBallModel γ F H σ) (hypocoerciveGeometry γ hγ)
        (hypocoerciveRate γ r L) := by
  apply PBGSO.heavyBall_source_criterion <;> assumption

#print axioms PBGSO.Standalone.PaperTheorems.appendix_heavy_ball_criterion

end


/-! ## Volume lemma — continuous flow -/
section
open PBGSO.ContinuousFlowMeasure
open scoped ContDiff
variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

theorem continuous_flow_volume
    (F : (ι → ℝ) → (ι → ℝ)) (hF : ContDiff ℝ 1 F)
    (Φ : ℝ × ContinuousVolume.Phase ι → ContinuousVolume.Phase ι)
    (hODE : ∀ t x, HasDerivAt (fun s => Φ (s, x))
      (ContinuousVolume.phaseField F (Φ (t, x))) t)
    (hinit : ∀ x, Φ (0, x) = x) (t : ℝ) :
    MeasurePreserving (fun x => Φ (t, x)) volume volume := by
  apply PBGSO.ContinuousFlowMeasure.phase_flow_measurePreserving_source <;> assumption

#print axioms PBGSO.Standalone.PaperTheorems.continuous_flow_volume

end


/-! ## Volume lemma — continuous signed Jacobian -/
section
open PBGSO.FlowSourceRegularity
open PBGSO.ContinuousVolume
open scoped ContDiff
variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

theorem continuous_jacobian_one
    (F : (ι → ℝ) → (ι → ℝ)) (hF : ContDiff ℝ 1 F)
    (Φ : ℝ × Phase ι → Phase ι)
    (hODE : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (phaseField F (Φ (t, x))) t)
    (hinit : ∀ x, Φ (0, x) = x) (t : ℝ) (x : Phase ι) :
    (fderiv ℝ (fun y => Φ (t, y)) x).det = 1 := by
  apply PBGSO.FlowSourceRegularity.phase_flow_fderiv_det_one_source <;> assumption

#print axioms PBGSO.Standalone.PaperTheorems.continuous_jacobian_one

end


/-! ## Volume lemma — discrete measure preservation -/
section
open PBGSO
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
  [CompleteSpace Q] [MeasurableSpace Q] [BorelSpace Q] [SecondCountableTopology Q]

theorem discrete_volume (μ : Measure Q) [SFinite μ]
    [Measure.IsAddLeftInvariant μ] (F : Q → Q) (hF : Measurable F) (h : ℝ) :
    MeasurePreserving (interwovenBAB F h) (μ.prod μ) (μ.prod μ) := by
  apply PBGSO.interwovenBAB_preserves <;> assumption

#print axioms PBGSO.Standalone.PaperTheorems.discrete_volume

end


/-! ## Volume lemma — discrete signed Jacobian -/
section
open PBGSO

theorem discrete_jacobian_one
    {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
    [CompleteSpace Q] [MeasurableSpace Q] [BorelSpace Q] [SecondCountableTopology Q]
    [FiniteDimensional ℝ Q] (F : Q → Q) (hF : Differentiable ℝ F)
    (h : ℝ) (z : Q × Q) :
    (fderiv ℝ (interwovenBAB F h) z).det = 1 := by
  apply PBGSO.interwovenBAB_fderiv_det_one <;> assumption

#print axioms PBGSO.Standalone.PaperTheorems.discrete_jacobian_one

end

end PBGSO.Standalone.PaperTheorems
