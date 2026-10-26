import PBGSO.RawParticleDissipation

/-! # Actual iid-reference forcing for damped raw particle states
The random vector whose energy is bounded can be a damped localization.
Only the original reference cloud supplies the iid observation variance.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators RealInnerProductSpace InnerProductSpace
namespace PBGSO
variable {S Θ Z X I Ω : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [MeasurableSpace Θ] [BorelSpace Θ] [SecondCountableTopology Θ]
  [Fintype I] [DecidableEq I]

/-- The full encoded particle energy is nonnegative. -/
theorem raw_particle_energy_nonneg (N : ℕ) (D : TwistedGeometry S Z)
    (y : ConstructedItoParticle.PairHilbert N S Z) :
    0 ≤ ⟪y,ConstructedItoParticle.metricWeight N D y⟫_ℝ := by
  rw [ConstructedItoParticle.metricWeight_inner]
  exact particleQuadratic_nonneg D N _

/-- Genuine square-integrability of a raw state gives integrability of its
semidefinite particle energy, without a full metric inverse assumption. -/
theorem raw_particle_energy_integrable (Q : Measure Ω) (N : ℕ) (D : TwistedGeometry S Z)
    (y : Ω → ConstructedItoParticle.PairHilbert N S Z)
    (hy : AEStronglyMeasurable y Q) (hy2 : MemLp y 2 Q) :
    Integrable (fun ω => ⟪y ω,ConstructedItoParticle.metricWeight N D (y ω)⟫_ℝ) Q := by
  let W := ConstructedItoParticle.metricWeight N D
  apply ((memLp_two_iff_integrable_sq_norm hy).mp hy2 |>.const_mul ‖W‖).mono'
    (hy.inner (W.continuous.comp_aestronglyMeasurable hy))
  filter_upwards with ω
  exact (norm_inner_le_norm _ _).trans (by
    nlinarith [W.le_opNorm (y ω),norm_nonneg (y ω)])

/-- The actual original iid reference marginal and response Lipschitz
constant yield the sharp V/N forcing term for any actual L² damped state.
The pointwise work inequality is supplied by the proved empirical generator
lemma, not by a particle-energy recurrence. -/
theorem raw_particle_expected_forcing_le (Q : Measure Ω) [IsProbabilityMeasure Q]
    (M : Model S Θ Z X I) (D : TwistedGeometry S Z) (N : ℕ) (hN : 0 < N)
    (ν : Measure Z) [IsProbabilityMeasure ν] (sbar : S)
    (hF : MemLp (fun z => M.observation (M.parameter sbar) (M.position z)) 2 ν)
    (x y : Ω → ConstructedItoParticle.PairHilbert N S Z)
    (hx : AEStronglyMeasurable x Q) (hy : AEStronglyMeasurable y Q) (hy2 : MemLp y 2 Q)
    (hCloud : Q.map (fun ω => (ConstructedItoParticle.pairEquiv N (x ω)).2.2) =
      Measure.pi (fun _ : Fin N => ν))
    (ρ : ℝ) (LΨ : ℝ≥0) (V : ℝ) (hV : 0 ≤ V)
    (hVar : (∫ z, ‖M.observation (M.parameter sbar) (M.position z) - M.meanGradient ν sbar‖ ^ 2 ∂ν) ≤ V)
    (work : Ω → ℝ) (hwork : Integrable work Q)
    (hpoint : ∀ᵐ ω ∂Q, work ω ≤
      -2 * ρ * ⟪y ω,ConstructedItoParticle.metricWeight N D (y ω)⟫_ℝ +
        2 * ((LΨ : ℝ) * Real.sqrt D.upper) *
          Real.sqrt ⟪y ω,ConstructedItoParticle.metricWeight N D (y ω)⟫_ℝ *
          ‖referenceObservationError M N ν sbar (ConstructedItoParticle.pairEquiv N (x ω))‖) :
    (∫ ω, work ω ∂Q) ≤
      -2 * ρ * (∫ ω, ⟪y ω,ConstructedItoParticle.metricWeight N D (y ω)⟫_ℝ ∂Q) +
        2 * ((LΨ : ℝ) * Real.sqrt D.upper * Real.sqrt (V / (N : ℝ))) *
          Real.sqrt (∫ ω, ⟪y ω,ConstructedItoParticle.metricWeight N D (y ω)⟫_ℝ ∂Q) := by
  let energy : Ω → ℝ := fun ω => ⟪y ω,ConstructedItoParticle.metricWeight N D (y ω)⟫_ℝ
  let cloud : Ω → Fin N → Z := fun ω => (ConstructedItoParticle.pairEquiv N (x ω)).2.2
  let a : Ω → ℝ := fun ω => Real.sqrt (energy ω)
  let b : Ω → ℝ := fun ω => ‖M.particleGradient N sbar (cloud ω) - M.meanGradient ν sbar‖
  let C : ℝ := (LΨ : ℝ) * Real.sqrt D.upper
  have hiE : Integrable energy Q := raw_particle_energy_integrable Q N D y hy hy2
  have ha : MemLp a 2 Q := sqrt_energy_memLp Q energy hiE.aestronglyMeasurable hiE
    (fun ω => raw_particle_energy_nonneg N D (y ω))
  have hmCloud : AEMeasurable cloud Q :=
    (measurable_snd.comp measurable_snd).comp_aemeasurable
      ((ConstructedItoParticle.pairEquiv N).continuous.measurable.comp_aemeasurable hx.aemeasurable)
  have hb0 : MemLp (fun w => M.particleGradient N sbar w - M.meanGradient ν sbar) 2
      (Q.map cloud) := by
    rw [hCloud]
    exact (particleGradient_memLp M ν sbar hF N).sub (memLp_const _)
  have hb : MemLp b 2 Q := (hb0.comp_of_map hmCloud).norm
  have hab : Integrable (fun ω => C * (a ω * b ω)) Q :=
    (memLp_one_iff_integrable.mp (ha.mul hb)).const_mul C
  have hmajor : Integrable (fun ω => -2 * ρ * energy ω + 2 * (C * (a ω * b ω))) Q :=
    (hiE.const_mul (-2 * ρ)).add (hab.const_mul 2)
  have hpoint' : ∀ᵐ ω ∂Q, work ω ≤ -2 * ρ * energy ω + 2 * (C * (a ω * b ω)) :=
    hpoint.mono (fun ω hω => by simpa only [energy,a,b,C,cloud,referenceObservationError,mul_assoc] using hω)
  have hInt := integral_mono_ae hwork hmajor hpoint'
  rw [integral_add (hiE.const_mul (-2 * ρ)) (hab.const_mul 2),
    integral_const_mul,integral_const_mul,integral_const_mul] at hInt
  have hcs := integral_mul_le_sqrt_integrals Q a b ha hb
  have heA : (∫ ω, a ω ^ 2 ∂Q) = ∫ ω, energy ω ∂Q := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun ω => Real.sq_sqrt (raw_particle_energy_nonneg N D (y ω)))
  have heB : (∫ ω, b ω ^ 2 ∂Q) =
      (∫ z, ‖M.observation (M.parameter sbar) (M.position z) - M.meanGradient ν sbar‖ ^ 2 ∂ν) / (N : ℝ) :=
    gradient_sampling_variance_of_cloud_law Q M ν sbar hF N hN cloud hmCloud hCloud
  rw [heA,heB] at hcs
  have hv := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hVar (Nat.cast_nonneg N : (0 : ℝ) ≤ N))
  have hc0 : 0 ≤ C := mul_nonneg LΨ.coe_nonneg (Real.sqrt_nonneg _)
  have hcs' := mul_le_mul_of_nonneg_left hcs (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc0)
  have hvar' := mul_le_mul_of_nonneg_left hv
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc0) (Real.sqrt_nonneg (∫ ω, energy ω ∂Q)))
  dsimp only [C] at *
  change _ ≤ -2 * ρ * (∫ ω, energy ω ∂Q) + _
  nlinarith

end PBGSO
