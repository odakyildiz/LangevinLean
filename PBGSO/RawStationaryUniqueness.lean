import PBGSO.NaturalFiniteWorkArbitraryLaw
import PBGSO.RawSamplerGrowthArbitraryLaw

/-! # Original stationary product-law uniqueness
Actual stationary original solutions and direct source A1 instances are
compared on every finite horizon. Both source branches derive the raw law
contraction internally; no synchronous weak-generator realization, energy
identity, or contraction estimate is an input.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.RawStationaryUniqueness
open FilteredBrownian RawLocalStationarity ConstructedItoLaw
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

/-- Stationarity is stated for actual raw strong solutions on each finite
horizon. The remaining fields are only direct A1 strong-existence and
same-driver uniqueness instances, with their original initial conditions. -/
structure Family where
  trajectory : ∀ T : ℝ≥0, Data Q D M T
  optimizer_eq : ∀ T : ℝ≥0, ∀ t ∈ Icc 0 (T : ℝ), (trajectory T).optimizer t = s
  law_eq : ∀ T : ℝ≥0, ∀ t ∈ Icc 0 (T : ℝ), Q.map ((trajectory T).sampler.state t) = ν
  unique : ∀ T : ℝ≥0, PathwiseUniqueness Q
    (nullAugmentedDriver Q (continuousDriver Q D)) M T
  canonical : ∀ T : ℝ≥0, NaturalFiniteWorkArbitraryLaw.CanonicalSolution (M := M) (T := T) ν s
  unique_canonical : ∀ T : ℝ≥0, PathwiseUniqueness (ν.prod (brownianProbability (I := I)))
    (nullAugmentedDriver _ (continuousDriver _ (CanonicalBrownianDriver.driver (I := I) ν))) M T
  path : ∀ T : ℝ≥0, ∃ W : Data (BrownianPathDriver.probability (I := I) ν)
      (BrownianPathDriver.driver ν) M T,
    W.optimizer 0 = s ∧ W.sampler.state 0 =ᵐ[BrownianPathDriver.probability (I := I) ν] Prod.fst

variable {Q D M s ν}

private theorem lawDistance_zero_separates (s s' : S) (ν ν' : Measure Z)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hν : MemLp (fun z : Z => z) 2 ν) (hν' : MemLp (fun z : Z => z) 2 ν')
    (hd : optimizerLawDistance s s' ν ν' = 0) : s = s' ∧ ν = ν' := by
  have hs := Real.sq_sqrt (add_nonneg (sq_nonneg ‖s-s'‖)
    (sq_nonneg (ULA.wasserstein2Real ν ν')))
  change optimizerLawDistance s s' ν ν' ^ 2 = _ at hs
  rw [hd, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hs
  have hn : ‖s-s'‖ = 0 := by nlinarith [sq_nonneg (ULA.wasserstein2Real ν ν')]
  have hw : ULA.wasserstein2Real ν ν' = 0 := by nlinarith [sq_nonneg ‖s-s'‖]
  exact ⟨sub_eq_zero.mp (norm_eq_zero.mp hn),
    measure_eq_of_finite_wasserstein2Real_zero ν ν'
      (ULA.wasserstein2_ne_top_of_memLp ν ν' hν hν') hw⟩

variable {R : Measure Ω'} [IsProbabilityMeasure R] {E : Driver (I := I) R}
  {s' : S} {ν' : Measure Z} [IsProbabilityMeasure ν']

/-- Uniqueness among original stationary finite-second-moment product laws
in source A1(i), under the explicitly named finite signed-work reading of
A3. No weak-generator realization or final comparison is assumed. -/
theorem stationary_laws_unique_constant
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
  apply lawDistance_zero_separates s s' ν ν' hν hν'
  apply stationary_distance_zero (Real.sqrt_nonneg _) hρ
    (C := Real.sqrt G.conditionNumber)
  intro t ht
  let T : ℝ≥0 := ⟨t,ht⟩
  have htime : (T : ℝ) = t := rfl
  have h0 : (0 : ℝ) ∈ Icc 0 (T : ℝ) := ⟨le_rfl,ht⟩
  have hT : (T : ℝ) ∈ Icc 0 (T : ℝ) := ⟨ht,le_rfl⟩
  let A : NaturalFiniteWorkArbitraryLaw.CanonicalSolution (M := M) (T := T) ν
      ((F.trajectory T).optimizer 0) := {
    data := (F.canonical T).data
    initial_optimizer := (F.canonical T).initial_optimizer.trans (F.optimizer_eq T 0 h0).symm
    initial_sampler := (F.canonical T).initial_sampler }
  let B : NaturalFiniteWorkArbitraryLaw.CanonicalSolution (M := M) (T := T) ν'
      ((H.trajectory T).optimizer 0) := {
    data := (H.canonical T).data
    initial_optimizer := (H.canonical T).initial_optimizer.trans (H.optimizer_eq T 0 h0).symm
    initial_sampler := (H.canonical T).initial_sampler }
  have hpF : ∃ W : Data (BrownianPathDriver.probability (I := I) ν)
      (BrownianPathDriver.driver ν) M T,
      W.optimizer 0 = (F.trajectory T).optimizer 0 ∧
      W.sampler.state 0 =ᵐ[BrownianPathDriver.probability (I := I) ν] Prod.fst := by
    simpa only [F.optimizer_eq T 0 h0] using F.path T
  have hpH : ∃ W : Data (BrownianPathDriver.probability (I := I) ν')
      (BrownianPathDriver.driver ν') M T,
      W.optimizer 0 = (H.trajectory T).optimizer 0 ∧
      W.sampler.state 0 =ᵐ[BrownianPathDriver.probability (I := I) ν'] Prod.fst := by
    simpa only [H.optimizer_eq T 0 h0] using H.path T
  have hd := NaturalFiniteWorkArbitraryLaw.law_distance_decay (F.trajectory T) (H.trajectory T)
    ν ν' hν hν' (F.law_eq T 0 h0) (H.law_eq T 0 h0) A B
    (F.unique T) (H.unique T) (F.unique_canonical T) (H.unique_canonical T) hpF hpH
    G ρ hρ hmono hfull hσ hb hObs hDrift hOptimizer
  rw [F.optimizer_eq T T hT,H.optimizer_eq T T hT,F.law_eq T T hT,H.law_eq T T hT,
    F.optimizer_eq T 0 h0,H.optimizer_eq T 0 h0] at hd
  simpa only [htime, optimizerLawDistance] using hd

/-- Uniqueness among original stationary finite-second-moment product laws
in source A1(ii). The extra records contain only primitive coefficient
measurability/progressivity and linear growth; no stochastic or comparison
conclusion is supplied. -/
theorem stationary_laws_unique_linearGrowth
    (F : Family Q D M s ν) (H : Family R E M s' ν')
    (RF : ∀ T : ℝ≥0, RawSamplerGrowth.Regularity (F.canonical T).data)
    (RH : ∀ T : ℝ≥0, RawSamplerGrowth.Regularity (H.canonical T).data)
    (hν : MemLp (fun z : Z => z) 2 ν) (hν' : MemLp (fun z : Z => z) 2 ν')
    (G : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M G ρ) : s = s' ∧ ν = ν' := by
  apply lawDistance_zero_separates s s' ν ν' hν hν'
  apply stationary_distance_zero (Real.sqrt_nonneg _) hρ
    (C := Real.sqrt G.conditionNumber)
  intro t ht
  let T : ℝ≥0 := ⟨t,ht⟩
  have htime : (T : ℝ) = t := rfl
  have h0 : (0 : ℝ) ∈ Icc 0 (T : ℝ) := ⟨le_rfl,ht⟩
  have hT : (T : ℝ) ∈ Icc 0 (T : ℝ) := ⟨ht,le_rfl⟩
  let A : RawSamplerGrowthArbitraryLaw.CanonicalSolution (M := M) (T := T) ν
      ((F.trajectory T).optimizer 0) := {
    data := (F.canonical T).data
    regularity := RF T
    initial_optimizer := (F.canonical T).initial_optimizer.trans (F.optimizer_eq T 0 h0).symm
    initial_sampler := (F.canonical T).initial_sampler }
  let B : RawSamplerGrowthArbitraryLaw.CanonicalSolution (M := M) (T := T) ν'
      ((H.trajectory T).optimizer 0) := {
    data := (H.canonical T).data
    regularity := RH T
    initial_optimizer := (H.canonical T).initial_optimizer.trans (H.optimizer_eq T 0 h0).symm
    initial_sampler := (H.canonical T).initial_sampler }
  have hpF : ∃ W : Data (BrownianPathDriver.probability (I := I) ν)
      (BrownianPathDriver.driver ν) M T,
      W.optimizer 0 = (F.trajectory T).optimizer 0 ∧
      W.sampler.state 0 =ᵐ[BrownianPathDriver.probability (I := I) ν] Prod.fst := by
    simpa only [F.optimizer_eq T 0 h0] using F.path T
  have hpH : ∃ W : Data (BrownianPathDriver.probability (I := I) ν')
      (BrownianPathDriver.driver ν') M T,
      W.optimizer 0 = (H.trajectory T).optimizer 0 ∧
      W.sampler.state 0 =ᵐ[BrownianPathDriver.probability (I := I) ν'] Prod.fst := by
    simpa only [H.optimizer_eq T 0 h0] using H.path T
  have hd := RawSamplerGrowthArbitraryLaw.law_distance_decay (F.trajectory T) (H.trajectory T)
    ν ν' hν hν' (F.law_eq T 0 h0) (H.law_eq T 0 h0) A B
    (F.unique T) (H.unique T) (F.unique_canonical T) (H.unique_canonical T) hpF hpH G ρ hmono
  rw [F.optimizer_eq T T hT,H.optimizer_eq T T hT,F.law_eq T T hT,H.law_eq T T hT,
    F.optimizer_eq T 0 h0,H.optimizer_eq T 0 h0] at hd
  simpa only [htime, optimizerLawDistance] using hd

end PBGSO.RawStationaryUniqueness
