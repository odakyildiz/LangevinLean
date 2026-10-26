import PBGSO.RawNaturalConstantNoise
import PBGSO.RawConstantParameter

/-! # Natural original constant-noise parameter bound
Joint representatives and exact constant coefficient/gauge compatibility are
constructed from the natural raw reference and target equations. The reference
variance supplies the positive-work Fubini condition; it is not a new input.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.RawNaturalConstantParameter
open FilteredBrownian ConstructedItoParticle
variable {S Θ Z X I Ω Ωp : Type*} [MeasurableSpace Ω] [MeasurableSpace Ωp]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [MeasurableSpace Θ] [BorelSpace Θ] [SecondCountableTopology Θ]
  [Fintype I] [DecidableEq I]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {Qp : Measure Ωp} [IsProbabilityMeasure Qp]
  {N : ℕ} {T : ℝ≥0} {M : Model S Θ Z X I}
  {W : Driver (I := I) Q}
  (U V : RawLocalStationarity.Data Q W M T)

/-- The original reference law relaxes under the parameter theorem's own
response/variance assumptions. The whole-path constant-noise realization and
all original marginal identities are derived from the natural raw equations. -/
theorem reference_law_decay
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
    (sStar : S) (νStar : Measure Z) [IsProbabilityMeasure νStar]
    (hopt : ∀ r ∈ Icc 0 (T : ℝ), V.optimizer r = sStar)
    (hlaw : ∀ r ∈ Icc 0 (T : ℝ), Q.map (V.sampler.state r) = νStar)
    (hobs : Integrable (fun z => M.observation (M.parameter sStar) (M.position z)) νStar) :
    optimizerLawDistance (U.optimizer T) sStar (Q.map (U.sampler.state T)) νStar ≤
      Real.sqrt D.conditionNumber * Real.exp (-ρ * (T : ℝ)) *
        Real.sqrt (‖U.optimizer 0-sStar‖ ^ 2+
          ‖ProductLpSections.sectionLp Q U.sampler.state 0-
            ProductLpSections.sectionLp Q V.sampler.state 0‖ ^ 2) := by
  let A := RawNaturalConstantNoise.build U hσ hF hDrift hOptimizer
  let B := RawNaturalConstantNoise.build V hσ hF hDrift hOptimizer
  have hA2 : ∀ r ∈ Icc 0 (T : ℝ),
      MemLp (fun z => M.observation (M.parameter (A.data.optimizer r)) (M.position z))
        2 (Q.map (A.data.sampler r)) := by
    intro r hr
    rw [A.optimizer_eq r hr,A.sampler_law r hr]
    exact hU2 r hr
  have hAV : ∀ r ∈ Icc 0 (T : ℝ),
      (∫ z, ‖M.observation (M.parameter (A.data.optimizer r)) (M.position z)-
        M.meanGradient (Q.map (A.data.sampler r)) (A.data.optimizer r)‖ ^ 2
          ∂Q.map (A.data.sampler r)) ≤ V0 := by
    intro r hr
    rw [A.optimizer_eq r hr,A.sampler_law r hr]
    exact hVar r hr
  have hd := ConstantNoiseFluctuation.law_decay_of_reference_variance_stationary_target
    M D Q A.data hF B.data ρ hρ hmono hσ hb LΨ hΨ V0 hA2 hAV sStar νStar
    (fun r hr => (B.optimizer_eq r hr).trans (hopt r hr))
    (fun r hr => (B.sampler_law r hr).trans (hlaw r hr)) hobs
  rw [A.optimizer_eq T ⟨T.coe_nonneg,le_rfl⟩,A.sampler_law T ⟨T.coe_nonneg,le_rfl⟩,
    A.optimizer_eq 0 ⟨le_rfl,T.coe_nonneg⟩,
    A.sampler_section 0 ⟨le_rfl,T.coe_nonneg⟩,
    B.sampler_section 0 ⟨le_rfl,T.coe_nonneg⟩] at hd
  exact hd

variable {Wp : Driver (I := Fin N × I) Qp}
  {Lp : RawLocalDiffusion (Z := PairHilbert N S Z) Qp Wp T}
  (P : RawParticleInteraction.Data M (fun r => Q.map (U.sampler.state r)) Lp)

/-- Exact raw parameter RMS for a natural original reference/target pair.
There is no supplied constant-noise realization, positive-work condition,
mean-field weak-coupling interface, or final energy inequality. -/
theorem parameter_bound
    (D : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M D ρ) (hN : 0 < N)
    (hProjection : LipschitzWith 1 M.parameter)
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
    (sStar : S) (νStar : Measure Z) [IsProbabilityMeasure νStar]
    (hopt : ∀ r ∈ Icc 0 (T : ℝ), V.optimizer r = sStar)
    (hlaw : ∀ r ∈ Icc 0 (T : ℝ), Q.map (V.sampler.state r) = νStar)
    (hobs : Integrable (fun z => M.observation (M.parameter sStar) (M.position z)) νStar)
    (hCloud : ∀ r ∈ Icc 0 (T : ℝ), Qp.map (fun ω => (pairEquiv N (P.state r ω)).2.2) =
      Measure.pi (fun _ : Fin N => Q.map (U.sampler.state r)))
    (hbar : ∀ r ∈ Icc 0 (T : ℝ), ∀ᵐ ω ∂Qp,
      (pairEquiv N (P.state r ω)).2.1 = U.optimizer r)
    (hinit : ∀ᵐ ω ∂Qp, (pairEquiv N (P.state 0 ω)).1 = (pairEquiv N (P.state 0 ω)).2) :
    MemLp (fun ω => M.parameter (pairEquiv N (P.state T ω)).1.1-M.parameter sStar) 2 Qp ∧
    Real.sqrt (∫ ω, ‖M.parameter (pairEquiv N (P.state T ω)).1.1-M.parameter sStar‖ ^ 2 ∂Qp) ≤
      Real.sqrt D.conditionNumber * Real.exp (-ρ * (T : ℝ)) *
        Real.sqrt (‖U.optimizer 0-sStar‖ ^ 2+
          ‖ProductLpSections.sectionLp Q U.sampler.state 0-
            ProductLpSections.sectionLp Q V.sampler.state 0‖ ^ 2) +
      ((LΨ : ℝ)/ρ)*Real.sqrt (D.conditionNumber*V0/(N : ℝ))*(1-Real.exp (-ρ*(T : ℝ))) := by
  let ν : ℝ → Measure Z := fun r => Q.map (U.sampler.state (RawDampedState.timeClamp T r))
  have hν (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) : ν r = Q.map (U.sampler.state r) := by
    dsimp only [ν]
    rw [RawDampedState.timeClamp_eq T hr]
  letI : ∀ r, IsProbabilityMeasure (ν r) := fun r =>
    (Measure.isProbabilityMeasure_map_iff
      (U.sampler.measurable _ (RawDampedState.timeClamp_mem T r)).aemeasurable).mpr inferInstance
  let Pc : RawParticleInteraction.Data M ν Lp := {
    toData := P.toData
    drift_realizes := by
      intro r hr
      rw [hν r hr]
      exact P.drift_realizes r hr
    sigma_realizes := P.sigma_realizes }
  have hV0 : 0 ≤ V0 :=
    (integral_nonneg (fun z => sq_nonneg
      ‖M.observation (M.parameter (U.optimizer 0)) (M.position z)-
        M.meanGradient (Q.map (U.sampler.state 0)) (U.optimizer 0)‖)).trans
      (hVar 0 ⟨le_rfl,T.coe_nonneg⟩)
  obtain ⟨hm,hp⟩ := RawParticleParameter.parameter_bias_bound Pc D ρ hρ hmono hN
    hProjection LΨ V0 hV0 U.optimizer sStar hΨ
    (fun r hr => by rw [hν r hr]; exact hU2 r hr)
    (fun r hr => by simpa only [hν r hr] using hCloud r hr)
    hbar (fun r hr => by rw [hν r hr]; exact hVar r hr) hinit
  have hd := reference_law_decay U V D ρ hρ.le hmono hσ hb hF hDrift hOptimizer
    LΨ hΨ V0 hU2 hVar sStar νStar hopt hlaw hobs
  have ho := optimizer_norm_le_lawDistance (U.optimizer T) sStar (Q.map (U.sampler.state T)) νStar
  exact ⟨hm,(hp.trans (add_le_add le_rfl (ho.trans hd))).trans_eq (add_comm _ _)⟩

end PBGSO.RawNaturalConstantParameter
