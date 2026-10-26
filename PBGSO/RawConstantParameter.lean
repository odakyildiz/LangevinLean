import PBGSO.ConstantNoiseFluctuation
import PBGSO.RawParticleParameter

/-! # Actual raw parameter error in the constant-diffusion branch
The original raw particle estimate is combined with relaxation of an actual
raw reference/target coupling. Positive-work Fubini follows from the parameter
theorem's own gradient-response and reference-variance assumptions.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators RealInnerProductSpace InnerProductSpace
namespace PBGSO.RawConstantParameter
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
  {W : FilteredBrownian.Driver (I := I) Q}
  {L K : RawLocalDiffusion (Z := Z) Q W T}
  (U : RawConstantNoiseContraction.Data Q M W T L)
  (V : RawConstantNoiseContraction.Data Q M W T K)
  {Wp : FilteredBrownian.Driver (I := Fin N × I) Qp}
  {Lp : RawLocalDiffusion (Z := PairHilbert N S Z) Qp Wp T}
  (P : RawParticleInteraction.Data M (fun r => Q.map (U.sampler r)) Lp)

/-- Actual parameter RMS has exact relaxation plus finite-particle error.
The initial relaxation cost is the genuine realized reference/target coupling;
choosing an optimal initial coupling gives the source transport prefactor.
No abstract mean-field weak solution, supplied energy or drift-growth premise
is needed beyond the original raw equations and actual reference laws. -/
theorem parameter_bound
    (D : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M D ρ) (hN : 0 < N)
    (hProjection : LipschitzWith 1 M.parameter)
    (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i)
    (hb : ∀ θ, Measurable (M.drift θ))
    (hF : Measurable (fun p : S × Z => M.observation (M.parameter p.1) (M.position p.2)))
    (LΨ : ℝ≥0)
    (hΨ : ∀ r ∈ Icc 0 (T : ℝ), ∀ s g g',
      ‖M.optimizer r s g-M.optimizer r s g'‖ ≤ (LΨ : ℝ)*‖g-g'‖)
    (V0 : ℝ)
    (hU2 : ∀ r ∈ Icc 0 (T : ℝ),
      MemLp (fun z => M.observation (M.parameter (U.optimizer r)) (M.position z))
        2 (Q.map (U.sampler r)))
    (hVar : ∀ r ∈ Icc 0 (T : ℝ),
      (∫ z, ‖M.observation (M.parameter (U.optimizer r)) (M.position z)-
        M.meanGradient (Q.map (U.sampler r)) (U.optimizer r)‖ ^ 2 ∂Q.map (U.sampler r)) ≤ V0)
    (sStar : S) (νStar : Measure Z) [IsProbabilityMeasure νStar]
    (hopt : ∀ r ∈ Icc 0 (T : ℝ), V.optimizer r = sStar)
    (hlaw : ∀ r ∈ Icc 0 (T : ℝ), Q.map (V.sampler r) = νStar)
    (hobs : Integrable (fun z => M.observation (M.parameter sStar) (M.position z)) νStar)
    (hCloud : ∀ r ∈ Icc 0 (T : ℝ), Qp.map (fun ω => (pairEquiv N (P.state r ω)).2.2) =
      Measure.pi (fun _ : Fin N => Q.map (U.sampler r)))
    (hbar : ∀ r ∈ Icc 0 (T : ℝ), ∀ᵐ ω ∂Qp,
      (pairEquiv N (P.state r ω)).2.1 = U.optimizer r)
    (hinit : ∀ᵐ ω ∂Qp, (pairEquiv N (P.state 0 ω)).1 = (pairEquiv N (P.state 0 ω)).2) :
    MemLp (fun ω => M.parameter (pairEquiv N (P.state T ω)).1.1 - M.parameter sStar) 2 Qp ∧
    Real.sqrt (∫ ω, ‖M.parameter (pairEquiv N (P.state T ω)).1.1 - M.parameter sStar‖ ^ 2 ∂Qp) ≤
      Real.sqrt D.conditionNumber * Real.exp (-ρ * (T : ℝ)) *
        Real.sqrt (‖U.optimizer 0-sStar‖ ^ 2+
          ‖ProductLpSections.sectionLp Q U.sampler 0-ProductLpSections.sectionLp Q V.sampler 0‖ ^ 2) +
      ((LΨ : ℝ) / ρ) * Real.sqrt (D.conditionNumber * V0 / (N : ℝ)) *
        (1-Real.exp (-ρ * (T : ℝ))) := by
  letI : ∀ r, IsProbabilityMeasure (Q.map (U.sampler r)) := fun r =>
    (Measure.isProbabilityMeasure_map_iff U.sampler_strong.of_uncurry_left.measurable.aemeasurable).mpr inferInstance
  have hV0 : 0 ≤ V0 :=
    (integral_nonneg (fun z => sq_nonneg
      ‖M.observation (M.parameter (U.optimizer 0)) (M.position z)-
        M.meanGradient (Q.map (U.sampler 0)) (U.optimizer 0)‖)).trans
      (hVar 0 ⟨le_rfl,T.coe_nonneg⟩)
  obtain ⟨hm,hp⟩ := RawParticleParameter.parameter_bias_bound P D ρ hρ hmono hN
    hProjection LΨ V0 hV0 U.optimizer sStar hΨ hU2 hCloud hbar hVar hinit
  have hd := ConstantNoiseFluctuation.law_decay_of_reference_variance_stationary_target
    M D Q U hF V ρ hρ.le hmono hσ hb LΨ hΨ V0 hU2 hVar sStar νStar hopt hlaw hobs
  have ho := optimizer_norm_le_lawDistance (U.optimizer T) sStar (Q.map (U.sampler T)) νStar
  exact ⟨hm,(hp.trans (add_le_add le_rfl (ho.trans hd))).trans_eq (add_comm _ _)⟩

end PBGSO.RawConstantParameter
