import PBGSO.ConstructedItoParticle
import PBGSO.DampedContinuation

/-! # Pointwise raw particle dissipation before and after damping
The original source joint monotonicity is applied to the actual empirical
coupling. The population residual is then bounded by the original optimiser
response and the literal iid-reference observation error.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators RealInnerProductSpace InnerProductSpace
namespace PBGSO
variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [MeasurableSpace Θ] [BorelSpace Θ] [SecondCountableTopology Θ]
  [Fintype I] [DecidableEq I]

/-- Original particle/copy generator dissipation is derived pointwise from
the source law-coupling condition and the actual empirical coupling. -/
theorem raw_particle_generator_forcing_le (M : Model S Θ Z X I)
    (D : TwistedGeometry S Z) (ρ : ℝ) (hmono : TwistedJointMonotonicity M D ρ)
    (N : ℕ) (hN : 0 < N) (ν : Measure Z) (t : ℝ) (ht : 0 ≤ t)
    (LΨ : ℝ≥0)
    (hΨ : ∀ s g g', ‖M.optimizer t s g - M.optimizer t s g'‖ ≤
      (LΨ : ℝ) * ‖g - g'‖) (sbar : S) (p : ParticlePair N S Z)
    (hbar : p.2.1 = sbar) :
    particleCopyGenerator M N ν t (fun p => particleQuadraticBilinear D N p p) p ≤
      -2 * ρ * particleQuadraticBilinear D N p p +
        2 * ((LΨ : ℝ) * Real.sqrt D.upper) *
          Real.sqrt (particleQuadraticBilinear D N p p) *
          ‖referenceObservationError M N ν sbar p‖ := by
  have hw := particleCouplingWork_le M D ρ hmono N hN t ht p.1.1 p.2.1 p.1.2 p.2.2
  have hr := particlePopulationResidual_abs_le M D N ν t LΨ hΨ sbar p hbar
  have hres := le_trans (le_abs_self (particlePopulationResidual M D N ν t p)) hr
  rw [particleCopyGenerator_quadratic]
  rw [← particleQuadraticBilinear_diag] at hw
  dsimp only [particlePopulationResidual] at hres
  nlinarith

/-- Before the stop, the work is the original empirical particle work.
After the stop, the ordinary damped extension has exact rateρ dissipation.
The same original reference observation fluctuation therefore controls both
regions, without asserting an iid law for the artificially damped cloud. -/
theorem damped_raw_particle_generator_forcing_le (M : Model S Θ Z X I)
    (D : TwistedGeometry S Z) (ρ : ℝ) (hmono : TwistedJointMonotonicity M D ρ)
    (N : ℕ) (hN : 0 < N) (ν : Measure Z) (t τ : ℝ) (ht : 0 ≤ t)
    (LΨ : ℝ≥0)
    (hΨ : ∀ s g g', ‖M.optimizer t s g - M.optimizer t s g'‖ ≤
      (LΨ : ℝ) * ‖g - g'‖) (sbar : S)
    (x b : ℝ → ConstructedItoParticle.PairHilbert N S Z)
    (σ : Fin N × I → ℝ → ConstructedItoParticle.PairHilbert N S Z)
    (hb : ConstructedItoParticle.pairEquiv N (b t) =
      particleCopyDrift M N ν t (ConstructedItoParticle.pairEquiv N (x t)))
    (hσ : ∀ ij, ConstructedItoParticle.pairEquiv N (σ ij t) =
      particleCopyDiffusion M N (ConstructedItoParticle.pairEquiv N (x t)) ij)
    (hbar : (ConstructedItoParticle.pairEquiv N (x t)).2.1 = sbar) :
    let W := ConstructedItoParticle.metricWeight N D
    let Y := DampedContinuation.extension ρ τ x t
    let β := DampedContinuation.drift ρ τ x b t
    2 * ⟪Y, W β⟫_ℝ + ∑ ij : Fin N × I,
      ⟪if t ≤ τ then σ ij t else 0, W (if t ≤ τ then σ ij t else 0)⟫_ℝ ≤
      -2 * ρ * ⟪Y, W Y⟫_ℝ +
        2 * ((LΨ : ℝ) * Real.sqrt D.upper) * Real.sqrt ⟪Y, W Y⟫_ℝ *
          ‖referenceObservationError M N ν sbar (ConstructedItoParticle.pairEquiv N (x t))‖ := by
  classical
  dsimp only
  by_cases h : t ≤ τ
  · rw [DampedContinuation.extension_before ρ τ x h]
    simp only [DampedContinuation.drift,ite_eq_left h]
    have he : 2 * ⟪x t, ConstructedItoParticle.metricWeight N D (b t)⟫_ℝ +
        ∑ ij : Fin N × I, ⟪σ ij t, ConstructedItoParticle.metricWeight N D (σ ij t)⟫_ℝ =
        particleCopyGenerator M N ν t (fun p => particleQuadraticBilinear D N p p)
          (ConstructedItoParticle.pairEquiv N (x t)) := by
      rw [IntegralParticleBound.particleCopyGenerator_bilinear]
      simp_rw [ConstructedItoParticle.metricWeight_inner]
      rw [hb]
      congr 1
      apply Finset.sum_congr rfl
      intro ij _
      rw [hσ ij]
    rw [he,ConstructedItoParticle.metricWeight_inner]
    exact raw_particle_generator_forcing_le M D ρ hmono N hN ν t ht LΨ hΨ sbar _ hbar
  · simp only [DampedContinuation.drift,ite_eq_right h,map_smul,inner_smul_right,
      map_zero,inner_zero_left,Finset.sum_const_zero]
    have hpos : 0 ≤ 2 * ((LΨ : ℝ) * Real.sqrt D.upper) *
        Real.sqrt ⟪DampedContinuation.extension ρ τ x t,
          ConstructedItoParticle.metricWeight N D (DampedContinuation.extension ρ τ x t)⟫_ℝ *
          ‖referenceObservationError M N ν sbar (ConstructedItoParticle.pairEquiv N (x t))‖ := by positivity
    nlinarith

end PBGSO
