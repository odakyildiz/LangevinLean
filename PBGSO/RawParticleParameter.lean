import PBGSO.RawParticleInteraction
import PBGSO.ParameterBound

/-! # Actual raw finite-particle parameter bounds
The original raw interacting parameter is controlled by the proved localized
particle estimate and the actual deterministic reference coordinate. The
stationary-target theorem uses an arbitrary reference weak solution, actual
frozen stationarity, and synchronous realizability of its initial couplings.
No particle energy identity, global drift moment or final parameter triangle
is assumed.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators RealInnerProductSpace InnerProductSpace
namespace PBGSO.RawParticleParameter
open FilteredBrownian ConstructedItoParticle
variable {S Θ Z X I Ω : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [MeasurableSpace Θ] [BorelSpace Θ] [SecondCountableTopology Θ]
  [Fintype I] [DecidableEq I]
  {Q : Measure Ω} [IsProbabilityMeasure Q] {N : ℕ} {T : ℝ≥0}
  {Driver : FilteredBrownian.Driver (I := Fin N × I) Q}
  {L : RawLocalDiffusion (Z := PairHilbert N S Z) Q Driver T}


variable {M : Model S Θ Z X I} {ν : ℝ → Measure Z}
  (U : RawParticleInteraction.Data M ν L)

/-- Actual raw parameter RMS is bounded by particle interaction plus the
reference optimizer's distance to any deterministic target. -/
theorem parameter_bias_bound [∀ t, IsProbabilityMeasure (ν t)]
    (G : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M G ρ) (hN : 0 < N)
    (hProjection : LipschitzWith 1 M.parameter)
    (LΨ : ℝ≥0) (V : ℝ) (hV : 0 ≤ V) (sbar : ℝ → S) (sStar : S)
    (hΨ : ∀ t ∈ Icc 0 (T : ℝ), ∀ s g g',
      ‖M.optimizer t s g - M.optimizer t s g'‖ ≤ (LΨ : ℝ) * ‖g-g'‖)
    (hF : ∀ t ∈ Icc 0 (T : ℝ), MemLp (fun z => M.observation (M.parameter (sbar t)) (M.position z)) 2 (ν t))
    (hCloud : ∀ t ∈ Icc 0 (T : ℝ), Q.map (fun ω => (pairEquiv N (U.state t ω)).2.2) =
      Measure.pi (fun _ : Fin N => ν t))
    (hbar : ∀ t ∈ Icc 0 (T : ℝ), ∀ᵐ ω ∂Q, (pairEquiv N (U.state t ω)).2.1 = sbar t)
    (hVar : ∀ t ∈ Icc 0 (T : ℝ),
      (∫ z, ‖M.observation (M.parameter (sbar t)) (M.position z) - M.meanGradient (ν t) (sbar t)‖ ^ 2 ∂ν t) ≤ V)
    (hinit : ∀ᵐ ω ∂Q, (pairEquiv N (U.state 0 ω)).1 = (pairEquiv N (U.state 0 ω)).2) :
    MemLp (fun ω => M.parameter (pairEquiv N (U.state T ω)).1.1 - M.parameter sStar) 2 Q ∧
    Real.sqrt (∫ ω, ‖M.parameter (pairEquiv N (U.state T ω)).1.1 - M.parameter sStar‖ ^ 2 ∂Q) ≤
      ((LΨ : ℝ) / ρ) * Real.sqrt (G.conditionNumber * V / (N : ℝ)) *
        (1 - Real.exp (-ρ * T)) + ‖sbar T - sStar‖ := by
  obtain ⟨hraw,hE⟩ := U.forced_energy_bound G ρ hρ hmono hN LΨ V hV sbar hΨ hF hCloud hbar hVar hinit
  let p : Ω → ParticlePair N S Z := fun ω => pairEquiv N (U.state T ω)
  let Γ := Q.map p
  have hp : Measurable p := (pairEquiv N).continuous.measurable.comp U.state_strong.of_uncurry_left.measurable
  have hq : Measurable (fun p : ParticlePair N S Z => particleQuadraticBilinear G N p p) :=
    (IntegralParticleBound.quadratic_continuous (particleQuadraticBilinear G N)).measurable
  have hqΓ : Integrable (fun p => particleQuadraticBilinear G N p p) Γ :=
    (integrable_map_measure hq.aestronglyMeasurable hp.aemeasurable).mpr hraw
  have hbarΓ : ∀ᵐ p ∂Γ, p.2.1 = sbar T := by
    exact (ae_map_iff hp.aemeasurable (isClosed_eq continuous_snd.fst continuous_const).measurableSet).mpr (hbar T ⟨T.coe_nonneg,le_rfl⟩)
  obtain ⟨hm,ht⟩ := parameter_target_rms_bound M G hProjection N Γ (sbar T) sStar hbarΓ hqΓ
  have hmQ := hm.comp_of_map hp.aemeasurable
  have hmstrong : AEStronglyMeasurable
      (fun p : ParticlePair N S Z => ‖M.parameter p.1.1 - M.parameter sStar‖ ^ 2) Γ :=
    hm.aestronglyMeasurable.norm.pow 2
  rw [integral_map hp.aemeasurable hmstrong,integral_map hp.aemeasurable hq.aestronglyMeasurable] at ht
  refine ⟨hmQ,ht.trans (add_le_add ?_ le_rfl)⟩
  have he := div_le_div_of_nonneg_right hE (Real.sqrt_nonneg G.lower)
  apply he.trans_eq
  have hκ : 0 ≤ G.conditionNumber := le_trans (by norm_num : (0 : ℝ) ≤ 1) G.conditionNumber_ge_one
  have hs : Real.sqrt (G.conditionNumber * V / (N : ℝ)) =
      (Real.sqrt G.upper / Real.sqrt G.lower) * Real.sqrt (V / (N : ℝ)) := by
    rw [show G.conditionNumber * V / (N : ℝ) = G.conditionNumber * (V / (N : ℝ)) by ring,
      Real.sqrt_mul hκ,G.sqrt_conditionNumber]
  rw [hs]
  ring

/-- Source parameter relaxation plus exact raw finite-particle interaction.
The mean-field reference is arbitrary; only its actual weak equations,
frozen-target stationarity and synchronous realizability are required. -/
theorem finite_particle_parameter_bound [∀ t, IsProbabilityMeasure (ν t)]
    (G : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M G ρ) (hN : 0 < N)
    (hProjection : LipschitzWith 1 M.parameter)
    (tests : Set (Z → ℝ)) (pairTests : Set (Z × Z → ℝ))
    (sbar : ℝ → S) (hmean : M.IsWeakSolution tests sbar ν)
    (sStar : S) (νStar : Measure Z)
    (hstationary : M.FrozenStationary tests (M.parameter sStar) νStar)
    (hgradient : Integrable (fun z => M.observation (M.parameter sStar) (M.position z)) νStar)
    (hgradientZero : M.meanGradient νStar sStar = 0)
    (hfix : ∀ r, 0 ≤ r → M.optimizer r sStar 0 = 0)
    (hpairQuad : couplingQuadratic G ∈ pairTests)
    (realize : ∀ c : ULA.Coupling (ν 0) νStar,
      ∃ Λ : ℝ → Measure (Z × Z),
        SynchronousCouplingData M pairTests sbar (fun _ => sStar) ν (fun _ => νStar) Λ ∧
          Λ 0 = c.joint)
    (LΨ : ℝ≥0) (V : ℝ) (hV : 0 ≤ V)
    (hΨ : ∀ t ∈ Icc 0 (T : ℝ), ∀ s g g',
      ‖M.optimizer t s g - M.optimizer t s g'‖ ≤ (LΨ : ℝ) * ‖g-g'‖)
    (hF : ∀ t ∈ Icc 0 (T : ℝ), MemLp (fun z => M.observation (M.parameter (sbar t)) (M.position z)) 2 (ν t))
    (hCloud : ∀ t ∈ Icc 0 (T : ℝ), Q.map (fun ω => (pairEquiv N (U.state t ω)).2.2) =
      Measure.pi (fun _ : Fin N => ν t))
    (hbar : ∀ t ∈ Icc 0 (T : ℝ), ∀ᵐ ω ∂Q, (pairEquiv N (U.state t ω)).2.1 = sbar t)
    (hVar : ∀ t ∈ Icc 0 (T : ℝ),
      (∫ z, ‖M.observation (M.parameter (sbar t)) (M.position z) - M.meanGradient (ν t) (sbar t)‖ ^ 2 ∂ν t) ≤ V)
    (hinit : ∀ᵐ ω ∂Q, (pairEquiv N (U.state 0 ω)).1 = (pairEquiv N (U.state 0 ω)).2) :
    MemLp (fun ω => M.parameter (pairEquiv N (U.state T ω)).1.1 - M.parameter sStar) 2 Q ∧
    Real.sqrt (∫ ω, ‖M.parameter (pairEquiv N (U.state T ω)).1.1 - M.parameter sStar‖ ^ 2 ∂Q) ≤
      Real.sqrt G.conditionNumber * Real.exp (-ρ * T) *
        optimizerLawDistance (sbar 0) sStar (ν 0) νStar +
      ((LΨ : ℝ) / ρ) * Real.sqrt (G.conditionNumber * V / (N : ℝ)) *
        (1 - Real.exp (-ρ * T)) := by
  obtain ⟨hm,ht⟩ := parameter_bias_bound U G ρ hρ hmono hN hProjection LΨ V hV sbar sStar
    hΨ hF hCloud hbar hVar hinit
  have hrelax := (optimizer_norm_le_lawDistance (sbar T) sStar (ν T) νStar).trans
    (stationary_target_law_bound M G tests pairTests sbar ν hmean sStar νStar hstationary
      hgradient hgradientZero hfix hpairQuad ρ T hmono realize T ⟨T.coe_nonneg,le_rfl⟩)
  refine ⟨hm,?_⟩
  exact (ht.trans (add_le_add le_rfl hrelax)).trans_eq (add_comm _ _)

end PBGSO.RawParticleParameter

namespace PBGSO.RawParticleParameterFamily
open FilteredBrownian ConstructedItoParticle
variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [MeasurableSpace Θ] [BorelSpace Θ] [SecondCountableTopology Θ]
  [Fintype I] [DecidableEq I]
  {ΩF : ℕ → Type*} [∀ n, MeasurableSpace (ΩF n)]
  (QF : ∀ n, Measure (ΩF n)) [∀ n, IsProbabilityMeasure (QF n)]
  (drivers : ∀ n, FilteredBrownian.Driver (I := Fin (n+1) × I) (QF n))
  (locals : ∀ (n : ℕ) (T : ℝ≥0), RawLocalDiffusion (Z := PairHilbert (n+1) S Z) (QF n) (drivers n) T)
  {M : Model S Θ Z X I} {ν : ℝ → Measure Z}
  (family : ∀ (n : ℕ) (T : ℝ≥0), RawParticleInteraction.Data M ν (locals n T))

/-- The actual raw parameter error, on its own probability space for each
particle count and with the horizon chosen by the observation time. -/
def parameterError (sStar : S) (n : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt (∫ ω, ‖M.parameter
    (pairEquiv (n+1) ((family n t.toNNReal).state t.toNNReal ω)).1.1 - M.parameter sStar‖ ^ 2 ∂QF n)

/-- Uniform primitive source assumptions imply joint large-time and
large-population convergence of the actual raw parameter errors. Different
particle counts may use different probability spaces; no global moment or
error-bound premise is supplied. -/
theorem parameter_joint_limit [∀ t, IsProbabilityMeasure (ν t)]
    (G : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M G ρ)
    (hProjection : LipschitzWith 1 M.parameter)
    (tests : Set (Z → ℝ)) (pairTests : Set (Z × Z → ℝ))
    (sbar : ℝ → S) (hmean : M.IsWeakSolution tests sbar ν)
    (sStar : S) (νStar : Measure Z)
    (hstationary : M.FrozenStationary tests (M.parameter sStar) νStar)
    (hgradient : Integrable (fun z => M.observation (M.parameter sStar) (M.position z)) νStar)
    (hgradientZero : M.meanGradient νStar sStar = 0)
    (hfix : ∀ r, 0 ≤ r → M.optimizer r sStar 0 = 0)
    (hpairQuad : couplingQuadratic G ∈ pairTests)
    (realize : ∀ c : ULA.Coupling (ν 0) νStar,
      ∃ Λ : ℝ → Measure (Z × Z),
        SynchronousCouplingData M pairTests sbar (fun _ => sStar) ν (fun _ => νStar) Λ ∧
          Λ 0 = c.joint)
    (LΨ : ℝ≥0) (V : ℝ) (hV : 0 ≤ V)
    (hΨ : ∀ t, 0 ≤ t → ∀ s g g',
      ‖M.optimizer t s g - M.optimizer t s g'‖ ≤ (LΨ : ℝ) * ‖g-g'‖)
    (hF : ∀ t, 0 ≤ t → MemLp (fun z => M.observation (M.parameter (sbar t)) (M.position z)) 2 (ν t))
    (hCloud : ∀ n (T : ℝ≥0), ∀ t ∈ Icc 0 (T : ℝ),
      (QF n).map (fun ω => (pairEquiv (n+1) ((family n T).state t ω)).2.2) =
        Measure.pi (fun _ : Fin (n+1) => ν t))
    (hbar : ∀ n (T : ℝ≥0), ∀ t ∈ Icc 0 (T : ℝ),
      ∀ᵐ ω ∂QF n, (pairEquiv (n+1) ((family n T).state t ω)).2.1 = sbar t)
    (hVar : ∀ t, 0 ≤ t →
      (∫ z, ‖M.observation (M.parameter (sbar t)) (M.position z) - M.meanGradient (ν t) (sbar t)‖ ^ 2 ∂ν t) ≤ V)
    (hinit : ∀ n (T : ℝ≥0), ∀ᵐ ω ∂QF n,
      (pairEquiv (n+1) ((family n T).state 0 ω)).1 =
        (pairEquiv (n+1) ((family n T).state 0 ω)).2) :
    Tendsto (fun p : ℕ × ℝ => parameterError QF drivers locals family sStar p.1 p.2)
      (atTop ×ˢ atTop) (𝓝 0) := by
  let d0 := optimizerLawDistance (sbar 0) sStar (ν 0) νStar
  let floor := fun n : ℕ => ((LΨ : ℝ) / ρ) *
    Real.sqrt (G.conditionNumber * V / ((n+1 : ℕ) : ℝ))
  let decay := fun t : ℝ => Real.sqrt G.conditionNumber * Real.exp (-ρ*t) * d0
  have hdiv : Tendsto (fun n : ℕ => G.conditionNumber * V / ((n+1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
    have hh := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (G.conditionNumber * V)
    simpa only [Nat.cast_add,Nat.cast_one,mul_zero,mul_one_div] using hh
  have hfloor : Tendsto floor atTop (𝓝 0) := by
    have hh := (Real.continuous_sqrt.continuousAt.tendsto.comp hdiv).const_mul ((LΨ : ℝ) / ρ)
    simpa only [floor,Real.sqrt_zero,mul_zero,Function.comp_def] using hh
  have hdecay : Tendsto decay atTop (𝓝 0) := by
    simpa only [decay,mul_zero,zero_mul] using
      ((relaxation_tendsto_zero hρ).const_mul (Real.sqrt G.conditionNumber)).mul_const d0
  have hsum : Tendsto (fun p : ℕ × ℝ => decay p.2 + floor p.1)
      (atTop ×ˢ atTop) (𝓝 0) := by
    simpa only [add_zero,Function.comp_def] using
      (hdecay.comp tendsto_snd).add (hfloor.comp tendsto_fst)
  apply squeeze_zero' (Eventually.of_forall fun p => Real.sqrt_nonneg _) ?_ hsum
  filter_upwards [tendsto_snd.eventually (eventually_ge_atTop (0 : ℝ))] with p hp
  have hb := (RawParticleParameter.finite_particle_parameter_bound (family p.1 p.2.toNNReal)
    G ρ hρ hmono (Nat.succ_pos p.1) hProjection tests pairTests sbar hmean sStar νStar
    hstationary hgradient hgradientZero hfix hpairQuad realize LΨ V hV
    (fun t ht => hΨ t ht.1) (fun t ht => hF t ht.1) (hCloud p.1 p.2.toNNReal)
    (hbar p.1 p.2.toNNReal) (fun t ht => hVar t ht.1) (hinit p.1 p.2.toNNReal)).2
  have he : ((LΨ : ℝ) / ρ) * Real.sqrt (G.conditionNumber * V / ((p.1+1 : ℕ) : ℝ)) *
      (1 - Real.exp (-ρ*p.2)) ≤ floor p.1 := by
    have hn : 0 ≤ floor p.1 := by dsimp [floor]; positivity
    change floor p.1 * (1 - Real.exp (-ρ*p.2)) ≤ floor p.1
    nlinarith [Real.exp_pos (-ρ*p.2)]
  have hb' : parameterError QF drivers locals family sStar p.1 p.2 ≤
      decay p.2 + ((LΨ : ℝ) / ρ) * Real.sqrt (G.conditionNumber * V / ((p.1+1 : ℕ) : ℝ)) *
        (1 - Real.exp (-ρ*p.2)) := by
    simpa only [parameterError,Real.coe_toNNReal p.2 hp,decay,d0] using hb
  exact hb'.trans (add_le_add le_rfl he)

end PBGSO.RawParticleParameterFamily
