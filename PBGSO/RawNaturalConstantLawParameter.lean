import PBGSO.RawNaturalConstantLaw

/-! # Natural constant-noise parameter bound with the genuine law prefactor
Original raw particle interaction is combined with the internally proved
canonical law-infimum relaxation. No supplied weak coupling, energy, drift
moment, positive work, or reference stochastic-realization interface enters.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.RawNaturalConstantLawParameter
open FilteredBrownian RawLocalStationarity ConstructedItoLaw ConstructedItoParticle
variable {Ωp S Θ Z X I : Type*} [MeasurableSpace Ωp]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace Θ] [BorelSpace Θ] [SecondCountableTopology Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [Fintype I] [DecidableEq I]
  {Qp : Measure Ωp} [IsProbabilityMeasure Qp]
  (μ νStar : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure νStar]
  (hμ : MemLp (fun z : Z => z) 2 μ) (hν : MemLp (fun z : Z => z) 2 νStar)
include hμ hν

/-- Source4's exact exponential-plus-particle parameter estimate in the
natural constant-diffusion realization class. The initial relaxation cost
is the genuine optimizer/Wasserstein distance, obtained by infimizing over
all actual initial coupling realizations. -/
theorem parameter_bound {M : Model S Θ Z X I} {T : ℝ≥0}
    (U : RawLocalStationarity.Data (μ.prod (brownianProbability (I := I)))
      (CanonicalBrownianDriver.driver (I := I) μ) M T)
    (V : RawLocalStationarity.Data (νStar.prod (brownianProbability (I := I)))
      (CanonicalBrownianDriver.driver (I := I) νStar) M T)
    (hU0 : U.sampler.state 0 =ᵐ[μ.prod (brownianProbability (I := I))] Prod.fst)
    (hV0 : V.sampler.state 0 =ᵐ[νStar.prod (brownianProbability (I := I))] Prod.fst)
    {N : ℕ} {Wp : Driver (I := Fin N × I) Qp}
    {Lp : RawLocalDiffusion (Z := PairHilbert N S Z) Qp Wp T}
    (P : RawParticleInteraction.Data M
      (fun r => (μ.prod (brownianProbability (I := I))).map (U.sampler.state r)) Lp)
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
        2 ((μ.prod (brownianProbability (I := I))).map (U.sampler.state r)))
    (hVar : ∀ r ∈ Icc 0 (T : ℝ),
      (∫ z, ‖M.observation (M.parameter (U.optimizer r)) (M.position z)-
        M.meanGradient ((μ.prod (brownianProbability (I := I))).map (U.sampler.state r)) (U.optimizer r)‖ ^ 2
        ∂(μ.prod (brownianProbability (I := I))).map (U.sampler.state r)) ≤ V0)
    (sStar : S)
    (hopt : ∀ r ∈ Icc 0 (T : ℝ), V.optimizer r = sStar)
    (hlaw : ∀ r ∈ Icc 0 (T : ℝ),
      (νStar.prod (brownianProbability (I := I))).map (V.sampler.state r) = νStar)
    (hobs : Integrable (fun z => M.observation (M.parameter sStar) (M.position z)) νStar)
    (hCloud : ∀ r ∈ Icc 0 (T : ℝ), Qp.map (fun ω => (pairEquiv N (P.state r ω)).2.2) =
      Measure.pi (fun _ : Fin N => (μ.prod (brownianProbability (I := I))).map (U.sampler.state r)))
    (hbar : ∀ r ∈ Icc 0 (T : ℝ), ∀ᵐ ω ∂Qp,
      (pairEquiv N (P.state r ω)).2.1 = U.optimizer r)
    (hinit : ∀ᵐ ω ∂Qp, (pairEquiv N (P.state 0 ω)).1 = (pairEquiv N (P.state 0 ω)).2) :
    MemLp (fun ω => M.parameter (pairEquiv N (P.state T ω)).1.1-M.parameter sStar) 2 Qp ∧
    Real.sqrt (∫ ω, ‖M.parameter (pairEquiv N (P.state T ω)).1.1-M.parameter sStar‖ ^ 2 ∂Qp) ≤
      Real.sqrt D.conditionNumber * Real.exp (-ρ * (T : ℝ)) *
        optimizerLawDistance (U.optimizer 0) sStar μ νStar +
      ((LΨ : ℝ)/ρ)*Real.sqrt (D.conditionNumber*V0/(N : ℝ))*(1-Real.exp (-ρ*(T : ℝ))) := by
  let Q := μ.prod (brownianProbability (I := I))
  let ν : ℝ → Measure Z := fun r => Q.map (U.sampler.state (RawDampedState.timeClamp T r))
  have hνc (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) : ν r = Q.map (U.sampler.state r) := by
    dsimp only [ν]
    rw [RawDampedState.timeClamp_eq T hr]
  letI : ∀ r, IsProbabilityMeasure (ν r) := fun r =>
    (Measure.isProbabilityMeasure_map_iff
      (U.sampler.measurable _ (RawDampedState.timeClamp_mem T r)).aemeasurable).mpr inferInstance
  let Pc : RawParticleInteraction.Data M ν Lp := {
    toData := P.toData
    drift_realizes := by
      intro r hr
      rw [hνc r hr]
      exact P.drift_realizes r hr
    sigma_realizes := P.sigma_realizes }
  have hVarNonneg : 0 ≤ V0 := (integral_nonneg (fun z => sq_nonneg _)).trans
    (hVar 0 ⟨le_rfl,T.coe_nonneg⟩)
  obtain ⟨hm,hp⟩ := RawParticleParameter.parameter_bias_bound Pc D ρ hρ hmono hN
    hProjection LΨ V0 hVarNonneg U.optimizer sStar hΨ
    (fun r hr => by rw [hνc r hr]; exact hU2 r hr)
    (fun r hr => by simpa only [hνc r hr] using hCloud r hr)
    hbar (fun r hr => by rw [hνc r hr]; exact hVar r hr) hinit
  have hd := RawNaturalConstantLaw.law_decay μ νStar hμ hν U V hU0 hV0 D ρ hρ.le hmono
    hσ hb hF hDrift hOptimizer LΨ hΨ V0 hU2 hVar sStar hopt hlaw hobs
  have ho := optimizer_norm_le_lawDistance (U.optimizer T) sStar (Q.map (U.sampler.state T)) νStar
  exact ⟨hm,(hp.trans (add_le_add le_rfl (ho.trans hd))).trans_eq (add_comm _ _)⟩

end PBGSO.RawNaturalConstantLawParameter
