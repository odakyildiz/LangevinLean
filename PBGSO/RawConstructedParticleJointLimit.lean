import PBGSO.RawConstructedParticleParameter

/-! # Joint time/population convergence of original native particle parameters
Every member is an actual original empirical strong solution on the proved
independent seed source. The family contains original equations and direct
well-posedness/stationarity witnesses, not an error-bound interface. Either
source constant diffusion or primitive linear-growth realization regularity
is used to derive each sharp estimate before taking the joint limit.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.RawConstructedParticleJointLimit
open FilteredBrownian RawLocalStationarity ConstructedItoParticle ConstructedItoLaw
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

/-- Actual original strong equations on each observation horizon, with
A1 initial/path-source witnesses and the actual stationary target. No paired
particle/copy equation, iid output law, moment bound or final error estimate
is among these fields. -/
structure Family where
  reference : ∀ T : ℝ≥0, RawLocalStationarity.Data Q W M T
  canonical : ∀ T : ℝ≥0, RawLocalStationarity.Data (μ.prod (brownianProbability (I := I)))
    (CanonicalBrownianDriver.driver (I := I) μ) M T
  target : ∀ T : ℝ≥0, RawLocalStationarity.Data (νStar.prod (brownianProbability (I := I)))
    (CanonicalBrownianDriver.driver (I := I) νStar) M T
  reference_initial : ∀ T : ℝ≥0, (reference T).optimizer 0 = s0
  reference_initial_law : ∀ T : ℝ≥0, Q.map ((reference T).sampler.state 0) = μ
  canonical_initial : ∀ T : ℝ≥0, (canonical T).optimizer 0 = (reference T).optimizer 0
  canonical_initial_sampler : ∀ T : ℝ≥0, (canonical T).sampler.state 0 =ᵐ[
    μ.prod (brownianProbability (I := I))] Prod.fst
  target_initial_sampler : ∀ T : ℝ≥0, (target T).sampler.state 0 =ᵐ[
    νStar.prod (brownianProbability (I := I))] Prod.fst
  target_optimizer : ∀ T : ℝ≥0, ∀ r ∈ Icc 0 (T : ℝ), (target T).optimizer r = sStar
  target_law : ∀ T : ℝ≥0, ∀ r ∈ Icc 0 (T : ℝ),
    (νStar.prod (brownianProbability (I := I))).map ((target T).sampler.state r) = νStar
  unique_reference : ∀ T : ℝ≥0, PathwiseUniqueness Q (nullAugmentedDriver Q (continuousDriver Q W)) M T
  unique_canonical : ∀ T : ℝ≥0, PathwiseUniqueness (μ.prod (brownianProbability (I := I)))
    (nullAugmentedDriver _ (continuousDriver _ (CanonicalBrownianDriver.driver (I := I) μ))) M T
  path_reference : ∀ T : ℝ≥0, ∃ B : RawLocalStationarity.Data (BrownianPathDriver.probability (I := I) μ)
      (BrownianPathDriver.driver μ) M T,
    B.optimizer 0 = (reference T).optimizer 0 ∧
    B.sampler.state 0 =ᵐ[BrownianPathDriver.probability (I := I) μ] Prod.fst
  native : ∀ (n : ℕ) (T : ℝ≥0), RawEmpiricalDynamics.Solution M (n+1)
    (IndependentCopies.seeds (J := Fin (n+1)) Q) (RawIndependentCopies.driver Q W (n+1)) T
  synchronous_initial : ∀ n T, ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin (n+1)) Q,
    oneEquiv (n+1) ((native n T).state 0 ω) = ((reference T).optimizer 0,
      RawIndependentCopies.cloud Q W (n+1) (reference T) 0 ω)

variable (F : Family Q W M μ νStar s0 sStar)

/-- The actual native parameter RMS on its original seed probability
space, for positive population n+1 and the requested observation horizon. -/
def parameterError (n : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt (∫ ω, ‖M.parameter (oneEquiv (n+1) ((F.native n t.toNNReal).state t.toNNReal ω)).1-
    M.parameter sStar‖^2 ∂IndependentCopies.seeds (J := Fin (n+1)) Q)

/-- The two primitive source A1 alternatives. The linear-growth option
records actual canonical realization regularity and target well-posedness;
it contains no comparison, energy or output-law conclusion. -/
inductive Branch : Prop
  | constant (hσ : ∀ s s' z w i,
      M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i)
  | linearGrowth
      (regularity_reference : ∀ T : ℝ≥0, RawSamplerGrowth.Regularity (F.canonical T))
      (regularity_target : ∀ T : ℝ≥0, RawSamplerGrowth.Regularity (F.target T))
      (unique_target : ∀ T : ℝ≥0, PathwiseUniqueness (νStar.prod (brownianProbability (I := I)))
        (nullAugmentedDriver _ (continuousDriver _ (CanonicalBrownianDriver.driver (I := I) νStar))) M T)
      (path_target : ∀ T : ℝ≥0, ∃ B : RawLocalStationarity.Data
          (BrownianPathDriver.probability (I := I) νStar) (BrownianPathDriver.driver νStar) M T,
        B.optimizer 0 = (F.target T).optimizer 0 ∧
        B.sampler.state 0 =ᵐ[BrownianPathDriver.probability (I := I) νStar] Prod.fst)

/-- The ORIGINAL native parameter errors converge jointly as time and
population grow. Each estimate is constructed from primitive source
hypotheses; neither a paired realization nor a final-bound premise is
supplied. In particular this proves the source iterated-limit consequence. -/
theorem parameter_joint_limit
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
  have hVF : 0 ≤ VF := (integral_nonneg (fun z => sq_nonneg _)).trans
    (hVar 0 0 ⟨le_rfl,le_rfl⟩)
  let d0 := optimizerLawDistance s0 sStar μ νStar
  let floor := fun n : ℕ => ((LΨ : ℝ)/ρ)*Real.sqrt (G.conditionNumber*VF/((n+1 : ℕ) : ℝ))
  let decay := fun t : ℝ => Real.sqrt G.conditionNumber*Real.exp (-ρ*t)*d0
  have hbound (n : ℕ) (T : ℝ≥0) :
      Real.sqrt (∫ ω, ‖M.parameter (oneEquiv (n+1) ((F.native n T).state T ω)).1-M.parameter sStar‖^2
        ∂IndependentCopies.seeds (J := Fin (n+1)) Q) ≤ decay T+floor n*(1-Real.exp (-ρ*T)) := by
    cases hbranch with
    | constant hσ =>
      have h := (RawConstructedParticleParameter.original_parameter_bound_constant Q W
        (F.reference T) (F.native n T) μ νStar hμ hν (F.reference_initial_law T)
        (F.canonical T) (F.canonical_initial T) (F.canonical_initial_sampler T)
        (F.target T) (F.target_initial_sampler T) (F.unique_reference T) (F.unique_canonical T)
        (F.path_reference T) G ρ hρ hmono (Nat.succ_pos n) hProjection hσ hb hF hDrift hOptimizer
        LΨ VF (fun r hr => hΨ r hr.1) (hU2 T) (hVar T) sStar (F.target_optimizer T)
        (F.target_law T) hobs (F.synchronous_initial n T)).2
      simpa only [F.reference_initial T,decay,d0,floor] using h
    | linearGrowth hRA hRV hUnique hPath =>
      have h := (RawConstructedParticleParameter.original_parameter_bound_linearGrowth Q W
        (F.reference T) (F.native n T) μ νStar hμ hν (F.reference_initial_law T)
        (F.canonical T) (hRA T) (F.canonical_initial T) (F.canonical_initial_sampler T)
        (F.target T) (hRV T) (F.target_initial_sampler T) (F.unique_reference T) (F.unique_canonical T)
        (hUnique T) (F.path_reference T) (hPath T) G ρ hρ hmono (Nat.succ_pos n)
        hProjection hF hDrift hOptimizer LΨ VF (fun r hr => hΨ r hr.1) (hU2 T) (hVar T)
        sStar (F.target_optimizer T) (F.target_law T) (F.synchronous_initial n T)).2
      simpa only [F.reference_initial T,decay,d0,floor] using h
  have hdiv : Tendsto (fun n : ℕ => G.conditionNumber*VF/((n+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (G.conditionNumber*VF)
    simpa only [Nat.cast_add,Nat.cast_one,mul_zero,mul_one_div] using h
  have hfloor : Tendsto floor atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.continuousAt.tendsto.comp hdiv).const_mul ((LΨ : ℝ)/ρ)
    simpa only [floor,Real.sqrt_zero,mul_zero,Function.comp_def] using h
  have hdecay : Tendsto decay atTop (𝓝 0) := by
    simpa only [decay,mul_zero,zero_mul] using
      ((relaxation_tendsto_zero hρ).const_mul (Real.sqrt G.conditionNumber)).mul_const d0
  have hsum : Tendsto (fun p : ℕ × ℝ => decay p.2+floor p.1) (atTop ×ˢ atTop) (𝓝 0) := by
    simpa only [add_zero,Function.comp_def] using (hdecay.comp tendsto_snd).add (hfloor.comp tendsto_fst)
  apply squeeze_zero' (Eventually.of_forall fun p => Real.sqrt_nonneg _) ?_ hsum
  filter_upwards [tendsto_snd.eventually (eventually_ge_atTop (0 : ℝ))] with p hp
  have h := hbound p.1 p.2.toNNReal
  have hfnonneg : 0 ≤ floor p.1 := by dsimp [floor]; positivity
  have hf : floor p.1*(1-Real.exp (-ρ*p.2)) ≤ floor p.1 := by
    nlinarith [Real.exp_pos (-ρ*p.2)]
  have h' : parameterError Q W M μ νStar s0 sStar F p.1 p.2 ≤
      decay p.2+floor p.1*(1-Real.exp (-ρ*p.2)) := by
    simpa only [parameterError,Real.coe_toNNReal p.2 hp] using h
  exact h'.trans (add_le_add le_rfl hf)

end PBGSO.RawConstructedParticleJointLimit
