import PBGSO.ParticleWeakEnergy
import PBGSO.Sampling
import PBGSO.SeparatedGeometry
import PBGSO.LawContraction

/-! # Expected particle forcing from the actual iid reference cloud

The observation fluctuation is evaluated on the reference cloud marginal of
the actual interacting/reference joint law. Its exact variance is proved to
be `V/N`. Weighted Cauchy--Schwarz bounds the optimiser forcing without
assuming independence of the interacting variables. The stochastic input is
an explicit forward-generator solution with the quadratic test in its domain.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace NNReal
namespace PBGSO

section RealCauchySchwarz
variable {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)

/-- The real L² norm is the root second moment of the actual function. -/
theorem toLp_real_norm_eq_sqrt_integral (f : Ω → ℝ) (hf : MemLp f 2 Q) :
    ‖hf.toLp f‖ = Real.sqrt (∫ ω, f ω ^ 2 ∂Q) := by
  have hn := ProximalLangevin.lp_norm_sq_eq_integral Q (hf.toLp f)
  have he : (∫ ω, ‖hf.toLp f ω‖ ^ 2 ∂Q) = ∫ ω, f ω ^ 2 ∂Q := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with ω hω
    simp only [hω, Real.norm_eq_abs, sq_abs]
  rw [he] at hn
  rw [← hn, Real.sqrt_sq (norm_nonneg _)]

/-- Probability-independent Cauchy--Schwarz for two real L² functions. -/
theorem integral_mul_le_sqrt_integrals (f g : Ω → ℝ)
    (hf : MemLp f 2 Q) (hg : MemLp g 2 Q) :
    (∫ ω, f ω * g ω ∂Q) ≤
      Real.sqrt (∫ ω, f ω ^ 2 ∂Q) * Real.sqrt (∫ ω, g ω ^ 2 ∂Q) := by
  have he : (∫ ω, f ω * g ω ∂Q) = inner ℝ (hf.toLp f) (hg.toLp g) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω hfω hgω
    simp [hfω, hgω, RCLike.inner_apply, mul_comm]
  rw [he, ← toLp_real_norm_eq_sqrt_integral Q f hf,
    ← toLp_real_norm_eq_sqrt_integral Q g hg]
  exact real_inner_le_norm _ _
end RealCauchySchwarz

variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [MeasurableSpace S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace Θ] [BorelSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [MeasurableSpace Z] [MeasurableSingletonClass Z] [Fintype I]

/-- Nonnegativity of the actual normalised particle coupling metric. -/
theorem particleQuadratic_nonneg (D : TwistedGeometry S Z) (N : ℕ)
    (p : ParticlePair N S Z) : 0 ≤ particleQuadraticBilinear D N p p := by
  rw [particleQuadraticBilinear_diag]
  exact add_nonneg (D.optimizerSq_nonneg _)
    (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => D.samplerSq_nonneg _))

/-- The optimiser contribution is part of the full positive particle metric. -/
theorem optimizerSq_le_particleQuadratic (D : TwistedGeometry S Z) (N : ℕ)
    (p : ParticlePair N S Z) :
    D.optimizerSq (p.1.1 - p.2.1) ≤ particleQuadraticBilinear D N p p := by
  rw [particleQuadraticBilinear_diag]
  exact le_add_of_nonneg_right
    (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => D.samplerSq_nonneg _))

/-- The exact optimiser fluctuation appearing in the particle generator. -/
def particlePopulationResidual (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    (N : ℕ) (ν : Measure Z) (t : ℝ) (p : ParticlePair N S Z) : ℝ :=
  ⟪p.1.1 - p.2.1, D.optimizerWeight
    (M.particleField N t p.2.1 p.2.2 - M.optimizerField t p.2.1 ν)⟫

/-- The reference observation error, with a deterministic mean-field
optimiser state and the actual reference cloud coordinate. -/
def referenceObservationError (M : Model S Θ Z X I) (N : ℕ)
    (ν : Measure Z) (sbar : S) (p : ParticlePair N S Z) : Θ :=
  M.particleGradient N sbar p.2.2 - M.meanGradient ν sbar

/-- The reference-cloud product marginal gives actual L² integrability,
without independence from any interacting coordinate. -/
theorem referenceObservationError_memLp (M : Model S Θ Z X I) (N : ℕ)
    (ν : Measure Z) [IsProbabilityMeasure ν] (sbar : S)
    (hF : MemLp (fun z => M.observation (M.parameter sbar) (M.position z)) 2 ν)
    (Q : Measure (ParticlePair N S Z))
    (hCloud : Q.map (fun p => p.2.2) = Measure.pi (fun _ : Fin N => ν)) :
    MemLp (referenceObservationError M N ν sbar) 2 Q := by
  have he := (particleGradient_memLp M ν sbar hF N).sub
    (memLp_const (M.meanGradient ν sbar))
  have hm : MemLp (fun w => M.particleGradient N sbar w - M.meanGradient ν sbar) 2
      (Q.map (fun p : ParticlePair N S Z => p.2.2)) := by rw [hCloud]; exact he
  exact hm.comp_of_map (measurable_snd.comp measurable_snd).aemeasurable

/-- Exact second moment of the actual reference observation fluctuation. -/
theorem referenceObservationError_variance (M : Model S Θ Z X I)
    (N : ℕ) (hN : 0 < N) (ν : Measure Z) [IsProbabilityMeasure ν] (sbar : S)
    (hF : MemLp (fun z => M.observation (M.parameter sbar) (M.position z)) 2 ν)
    (Q : Measure (ParticlePair N S Z)) [IsProbabilityMeasure Q]
    (hCloud : Q.map (fun p => p.2.2) = Measure.pi (fun _ : Fin N => ν)) :
    (∫ p, ‖referenceObservationError M N ν sbar p‖ ^ 2 ∂Q) =
      (∫ z, ‖M.observation (M.parameter sbar) (M.position z) -
        M.meanGradient ν sbar‖ ^ 2 ∂ν) / (N : ℝ) :=
  gradient_sampling_variance_of_cloud_law Q M ν sbar hF N hN
    (fun p => p.2.2) (measurable_snd.comp measurable_snd).aemeasurable hCloud

section ResidualMeasurability
variable [BorelSpace S] [SecondCountableTopology S]

/-- Residual measurability follows from primitive optimiser response
Lipschitz continuity and the actual iid reference-cloud marginal. The
reference optimiser is deterministic; no continuity in its random coordinate
is silently imposed. -/
theorem particlePopulationResidual_aestronglyMeasurable (M : Model S Θ Z X I)
    (D : TwistedGeometry S Z) (N : ℕ) (ν : Measure Z) [IsProbabilityMeasure ν]
    (sbar : S)
    (hF : MemLp (fun z => M.observation (M.parameter sbar) (M.position z)) 2 ν)
    (Q : Measure (ParticlePair N S Z))
    (hCloud : Q.map (fun p => p.2.2) = Measure.pi (fun _ : Fin N => ν))
    (hbar : ∀ᵐ p ∂Q, p.2.1 = sbar) (t : ℝ) (LΨ : ℝ≥0)
    (hΨ : ∀ g g', ‖M.optimizer t sbar g - M.optimizer t sbar g'‖ ≤
      (LΨ : ℝ) * ‖g - g'‖) :
    AEStronglyMeasurable (particlePopulationResidual M D N ν t) Q := by
  let f : Θ → S := fun e =>
    M.optimizer t sbar (e + M.meanGradient ν sbar) - M.optimizer t sbar (M.meanGradient ν sbar)
  have hf : LipschitzWith LΨ f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [f, dist_eq_norm, sub_sub_sub_cancel_right, add_sub_add_right_eq_sub] using
      hΨ (x + M.meanGradient ν sbar) (y + M.meanGradient ν sbar)
  have hE := (referenceObservationError_memLp M N ν sbar hF Q hCloud).aestronglyMeasurable
  have hW := D.optimizerWeight.continuous.comp_aestronglyMeasurable
    (hf.continuous.comp_aestronglyMeasurable hE)
  have hA : AEStronglyMeasurable (fun p : ParticlePair N S Z => p.1.1 - sbar) Q :=
    (measurable_fst.comp measurable_fst).aestronglyMeasurable.sub aestronglyMeasurable_const
  apply (hA.inner hW).congr
  filter_upwards [hbar] with p hp
  simp only [particlePopulationResidual, Model.particleField, Model.optimizerField, hp,
    f, referenceObservationError, sub_add_cancel]

end ResidualMeasurability

/-- The initial energy vanishes from actual synchronous initial optimiser
and particle coordinates, without assuming a scalar initial-energy equation. -/
theorem expectedParticleEnergy_zero_of_synchronous (D : TwistedGeometry S Z) (N : ℕ)
    (Γ : ℝ → Measure (ParticlePair N S Z)) (hinit : ∀ᵐ p ∂Γ 0, p.1 = p.2) :
    expectedParticleEnergy D N Γ 0 = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [hinit] with p hp
  rw [particleQuadraticBilinear_diag, hp]
  simp [particleCouplingEnergy, TwistedGeometry.optimizerSq, TwistedGeometry.samplerSq]

/-- Actual optimiser-response Lipschitz continuity gives a pointwise
weighted residual bound on the full interacting/reference state. -/
theorem particlePopulationResidual_abs_le (M : Model S Θ Z X I)
    (D : TwistedGeometry S Z) (N : ℕ) (ν : Measure Z) (t : ℝ) (LΨ : ℝ≥0)
    (hΨ : ∀ s g g', ‖M.optimizer t s g - M.optimizer t s g'‖ ≤
      (LΨ : ℝ) * ‖g - g'‖) (sbar : S) (p : ParticlePair N S Z)
    (hbar : p.2.1 = sbar) :
    |particlePopulationResidual M D N ν t p| ≤
      ((LΨ : ℝ) * Real.sqrt D.upper) *
        Real.sqrt (particleQuadraticBilinear D N p p) *
          ‖referenceObservationError M N ν sbar p‖ := by
  have hp := D.optimizer_pairing_bound (p.1.1 - p.2.1)
    (M.particleField N t p.2.1 p.2.2 - M.optimizerField t p.2.1 ν)
  have hl := hΨ p.2.1 (M.particleGradient N p.2.1 p.2.2) (M.meanGradient ν p.2.1)
  have hs := Real.sqrt_le_sqrt (optimizerSq_le_particleQuadratic D N p)
  have hu : 0 ≤ Real.sqrt D.upper := Real.sqrt_nonneg _
  have hm := mul_le_mul_of_nonneg_left hl
    (mul_nonneg (Real.sqrt_nonneg (D.optimizerSq (p.1.1 - p.2.1))) hu)
  have hx := mul_le_mul_of_nonneg_right hs
    (by positivity : 0 ≤ Real.sqrt D.upper * (LΨ : ℝ) *
      ‖M.particleGradient N p.2.1 p.2.2 - M.meanGradient ν p.2.1‖)
  dsimp only [particlePopulationResidual, Model.particleField, Model.optimizerField]
  unfold Model.particleField Model.optimizerField at hp
  unfold referenceObservationError
  rw [← hbar]
  nlinarith

/-- Weighted Cauchy--Schwarz and the actual iid cloud variance derive the
expected optimiser forcing. Measurability of the residual is explicit. -/
theorem expectedParticlePopulationResidual_le (M : Model S Θ Z X I)
    (D : TwistedGeometry S Z) (N : ℕ) (hN : 0 < N)
    (ν : Measure Z) [IsProbabilityMeasure ν] (sbar : S)
    (hF : MemLp (fun z => M.observation (M.parameter sbar) (M.position z)) 2 ν)
    (Q : Measure (ParticlePair N S Z)) [IsProbabilityMeasure Q]
    (hCloud : Q.map (fun p => p.2.2) = Measure.pi (fun _ : Fin N => ν))
    (hbar : ∀ᵐ p ∂Q, p.2.1 = sbar)
    (hquad : Integrable (fun p => particleQuadraticBilinear D N p p) Q)
    (t : ℝ) (LΨ : ℝ≥0)
    (hΨ : ∀ s g g', ‖M.optimizer t s g - M.optimizer t s g'‖ ≤
      (LΨ : ℝ) * ‖g - g'‖)
    (hR : AEStronglyMeasurable (particlePopulationResidual M D N ν t) Q) :
    Integrable (particlePopulationResidual M D N ν t) Q ∧
    (∫ p, particlePopulationResidual M D N ν t p ∂Q) ≤
      ((LΨ : ℝ) * Real.sqrt D.upper) *
        Real.sqrt (∫ p, particleQuadraticBilinear D N p p ∂Q) *
        Real.sqrt ((∫ z, ‖M.observation (M.parameter sbar) (M.position z) -
          M.meanGradient ν sbar‖ ^ 2 ∂ν) / (N : ℝ)) := by
  let a := fun p : ParticlePair N S Z => Real.sqrt (particleQuadraticBilinear D N p p)
  let b := fun p : ParticlePair N S Z => ‖referenceObservationError M N ν sbar p‖
  let C := (LΨ : ℝ) * Real.sqrt D.upper
  have ha : MemLp a 2 Q := sqrt_energy_memLp Q _ hquad.aestronglyMeasurable hquad
    (particleQuadratic_nonneg D N)
  have hb : MemLp b 2 Q := (referenceObservationError_memLp M N ν sbar hF Q hCloud).norm
  have hab : Integrable (fun p => C * (a p * b p)) Q := by
    have hh : MemLp (fun p => a p * b p) 1 Q := ha.mul hb
    exact (memLp_one_iff_integrable.mp hh).const_mul C
  have hbound : ∀ᵐ p ∂Q, |particlePopulationResidual M D N ν t p| ≤ C * (a p * b p) := by
    filter_upwards [hbar] with p hp
    simpa only [C, a, b, mul_assoc] using
      particlePopulationResidual_abs_le M D N ν t LΨ hΨ sbar p hp
  have hir : Integrable (particlePopulationResidual M D N ν t) Q :=
    hab.mono' hR (by simpa only [Real.norm_eq_abs] using hbound)
  refine ⟨hir, ?_⟩
  have hi := integral_mono_ae hir hab (hbound.mono fun p hp => (le_abs_self _).trans hp)
  rw [integral_const_mul] at hi
  have hcs := integral_mul_le_sqrt_integrals Q a b ha hb
  have heA : (∫ p, a p ^ 2 ∂Q) = ∫ p, particleQuadraticBilinear D N p p ∂Q := by
    apply integral_congr_ae
    exact ae_of_all Q fun p => Real.sq_sqrt (particleQuadratic_nonneg D N p)
  have heB : (∫ p, b p ^ 2 ∂Q) =
      (∫ z, ‖M.observation (M.parameter sbar) (M.position z) -
        M.meanGradient ν sbar‖ ^ 2 ∂ν) / (N : ℝ) :=
    referenceObservationError_variance M N hN ν sbar hF Q hCloud
  rw [heA, heB] at hcs
  have hc := mul_le_mul_of_nonneg_left hcs
    (show 0 ≤ C from mul_nonneg LΨ.coe_nonneg (Real.sqrt_nonneg _))
  exact hi.trans (by simpa [C, mul_assoc] using hc)

/-- Ordinary quadratic cost of the explicit paired particle coordinates. -/
def particleEuclideanEnergy (N : ℕ) (p : ParticlePair N S Z) : ℝ :=
  ‖p.1.1 - p.2.1‖ ^ 2 + (N : ℝ)⁻¹ * ∑ i, ‖p.1.2 i - p.2.2 i‖ ^ 2

/-- The ordinary paired-particle metric is dominated by the actual twisted
quadratic form, with the exact common lower eigenvalue bound. -/
theorem particleEuclideanEnergy_lower (D : TwistedGeometry S Z) (N : ℕ)
    (p : ParticlePair N S Z) :
    D.lower * particleEuclideanEnergy N p ≤ particleQuadraticBilinear D N p p := by
  have hs : D.lower * (∑ i : Fin N, ‖p.1.2 i - p.2.2 i‖ ^ 2) ≤
      ∑ i : Fin N, D.samplerSq (p.1.2 i - p.2.2 i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => D.sampler_lower (p.1.2 i - p.2.2 i))
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ (N : ℝ)⁻¹)
  have ho := D.optimizer_lower (p.1.1 - p.2.1)
  rw [particleQuadraticBilinear_diag]
  dsimp only [particleEuclideanEnergy, particleCouplingEnergy, TwistedGeometry.optimizerSq,
    TwistedGeometry.samplerSq] at *
  nlinarith

/-- The actual optimiser/empirical-cloud metric squared from the paper. -/
def particleEmpiricalDistanceSq (N : ℕ) (p : ParticlePair N S Z) : ℝ :=
  ‖p.1.1 - p.2.1‖ ^ 2 +
    ULA.wasserstein2Real (Model.empiricalLaw N p.1.2) (Model.empiricalLaw N p.2.2) ^ 2

section EmpiricalDistance
variable [BorelSpace Z] [SecondCountableTopology Z]

/-- The actual empirical transport metric is bounded by the particular
indexwise pairing, without an iid premise for the interacting cloud. -/
theorem particleEmpiricalDistanceSq_le (N : ℕ) (hN : 0 < N)
    (p : ParticlePair N S Z) : particleEmpiricalDistanceSq N p ≤ particleEuclideanEnergy N p :=
  add_le_add (le_refl _) (empiricalCloud_wasserstein_sq_le N hN p.1.2 p.2.2)

/-- The expected empirical transport distance is bounded by the actual
generator energy. The measurability of the empirical transport statistic is
an explicit premise; no totalised integral is treated as an expectation. -/
theorem particle_empirical_rms_le_energy (D : TwistedGeometry S Z) (N : ℕ) (hN : 0 < N)
    (Q : Measure (ParticlePair N S Z))
    (hq : Integrable (fun p => particleQuadraticBilinear D N p p) Q)
    (hmetric : AEStronglyMeasurable (particleEmpiricalDistanceSq (S := S) (Z := Z) N) Q) :
    Real.sqrt (∫ p, particleEmpiricalDistanceSq N p ∂Q) ≤
      Real.sqrt (∫ p, particleQuadraticBilinear D N p p ∂Q) / Real.sqrt D.lower := by
  have hpos (p : ParticlePair N S Z) : 0 ≤ particleEmpiricalDistanceSq N p :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hp (p : ParticlePair N S Z) :
      particleEmpiricalDistanceSq N p ≤ (D.lower)⁻¹ * particleQuadraticBilinear D N p p := by
    have h := (mul_le_mul_of_nonneg_left (particleEmpiricalDistanceSq_le N hN p)
      D.lower_pos.le).trans (particleEuclideanEnergy_lower D N p)
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ D.lower_pos).mpr (by simpa only [mul_comm] using h)
  have hi : Integrable (particleEmpiricalDistanceSq (S := S) (Z := Z) N) Q :=
    (hq.const_mul D.lower⁻¹).mono' hmetric
      (ae_of_all Q fun p => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hpos p)] using hp p)
  have hb := integral_mono hi (hq.const_mul D.lower⁻¹) hp
  rw [integral_const_mul] at hb
  have hnon : 0 ≤ ∫ p, particleQuadraticBilinear D N p p ∂Q :=
    integral_nonneg (particleQuadratic_nonneg D N)
  calc
    _ ≤ Real.sqrt (D.lower⁻¹ * ∫ p, particleQuadraticBilinear D N p p ∂Q) :=
      Real.sqrt_le_sqrt hb
    _ = Real.sqrt (∫ p, particleQuadraticBilinear D N p p ∂Q) / Real.sqrt D.lower := by
      rw [Real.sqrt_mul (inv_nonneg.mpr D.lower_pos.le), Real.sqrt_inv]
      ring

end EmpiricalDistance

namespace IsParticleCopyWeakSolution
variable {M : Model S Θ Z X I} {N : ℕ} {ν : ℝ → Measure Z}
  {tests : Set (ParticlePair N S Z → ℝ)} {Γ : ℝ → Measure (ParticlePair N S Z)}

/-- Finite-particle interaction energy for the actual synchronous weak
particle/copy dynamics. The reference optimiser is deterministic, its cloud
has the actual iid marginal, and its centred observation variance is bounded
by V. The dissipation inequality is derived from the model's joint condition,
the generator computation and the exact variance; it is not a premise. -/
theorem forced_energy_bound (hsol : IsParticleCopyWeakSolution M N ν tests Γ)
    (D : TwistedGeometry S Z) (hN : 0 < N)
    (hquad : (fun p => particleQuadraticBilinear D N p p) ∈ tests)
    (ρ : ℝ) (hρ : 0 < ρ) (hmono : TwistedJointMonotonicity M D ρ)
    (LΨ : ℝ≥0) (V T : ℝ) (hV : 0 ≤ V) (sbar : ℝ → S)
    (hν : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (ν r))
    (hF : ∀ r ∈ Icc 0 T,
      MemLp (fun z => M.observation (M.parameter (sbar r)) (M.position z)) 2 (ν r))
    (hCloud : ∀ r ∈ Icc 0 T,
      (Γ r).map (fun p => p.2.2) = Measure.pi (fun _ : Fin N => ν r))
    (hbar : ∀ r ∈ Icc 0 T, ∀ᵐ p ∂Γ r, p.2.1 = sbar r)
    (hΨ : ∀ r ∈ Icc 0 T, ∀ s g g',
      ‖M.optimizer r s g - M.optimizer r s g'‖ ≤ (LΨ : ℝ) * ‖g - g'‖)
    (hVariance : ∀ r ∈ Icc 0 T,
      (∫ z, ‖M.observation (M.parameter (sbar r)) (M.position z) -
        M.meanGradient (ν r) (sbar r)‖ ^ 2 ∂ν r) ≤ V)
    (hR : ∀ r ∈ Icc 0 T,
      AEStronglyMeasurable (particlePopulationResidual M D N (ν r) r) (Γ r))
    (hzero : expectedParticleEnergy D N Γ 0 = 0)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    Real.sqrt (expectedParticleEnergy D N Γ t) ≤
      ((LΨ : ℝ) * Real.sqrt D.upper * Real.sqrt (V / (N : ℝ))) / ρ *
        (1 - Real.exp (-ρ * t)) := by
  let E' : ℝ → ℝ := fun r => 2 * ∫ p,
    particleCouplingWork M D N r p.1.1 p.2.1 p.1.2 p.2.2 +
      particlePopulationResidual M D N (ν r) r p ∂Γ r
  let c : ℝ := (LΨ : ℝ) * Real.sqrt D.upper * Real.sqrt (V / (N : ℝ))
  have hd (r : ℝ) (hr : 0 ≤ r) :
      HasDerivWithinAt (expectedParticleEnergy D N Γ) (E' r) (Ici 0) r :=
    hsol.energy_hasDerivWithinAt D hquad r hr
  apply PBGSO.forced_energy_bound (E' := E') (T := T) hρ
    (show 0 ≤ c from mul_nonneg
      (mul_nonneg LΨ.coe_nonneg (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  · intro r hr
    exact (hd r hr.1).continuousWithinAt.mono Icc_subset_Ici_self
  · intro r hr
    exact (hd r hr.1).mono (Ici_subset_Ici.mpr hr.1)
  · intro r _
    exact integral_nonneg (particleQuadratic_nonneg D N)
  · exact hzero
  · intro r hr
    have hr' : r ∈ Icc 0 T := ⟨hr.1, hr.2.le⟩
    letI := hν r hr'
    letI := hsol.probability r hr.1
    have hq := hsol.test_integrable _ hquad r hr.1
    obtain ⟨hir, hres⟩ := expectedParticlePopulationResidual_le M D N hN (ν r) (sbar r)
      (hF r hr') (Γ r) (hCloud r hr') (hbar r hr') hq r LΨ (hΨ r hr') (hR r hr')
    have hsum : Integrable (fun p : ParticlePair N S Z =>
        particleCouplingWork M D N r p.1.1 p.2.1 p.1.2 p.2.2 +
          particlePopulationResidual M D N (ν r) r p) (Γ r) := by
      have hi := (hsol.generator_integrable _ hquad r hr.1).const_mul (1 / 2 : ℝ)
      convert hi using 1
      ext p
      rw [particleCopyGenerator_quadratic]
      dsimp only [particlePopulationResidual]
      ring
    have hiw : Integrable (fun p : ParticlePair N S Z =>
        particleCouplingWork M D N r p.1.1 p.2.1 p.1.2 p.2.2) (Γ r) := by
      convert hsum.sub hir using 1
      ext p
      exact (add_sub_cancel_right _ _).symm
    have hwork := integral_mono hiw (hq.const_mul (-ρ))
      (fun p : ParticlePair N S Z =>
        by simpa only [particleQuadraticBilinear_diag] using
          particleCouplingWork_le M D ρ hmono N hN r hr.1 p.1.1 p.2.1 p.1.2 p.2.2)
    rw [integral_const_mul] at hwork
    have hvar := Real.sqrt_le_sqrt
      (div_le_div_of_nonneg_right (hVariance r hr') (Nat.cast_nonneg N : (0 : ℝ) ≤ N))
    have hvar' := mul_le_mul_of_nonneg_left hvar
      (by positivity : 0 ≤ (LΨ : ℝ) * Real.sqrt D.upper *
        Real.sqrt (expectedParticleEnergy D N Γ r))
    change _ ≤ ((LΨ : ℝ) * Real.sqrt D.upper) *
      Real.sqrt (expectedParticleEnergy D N Γ r) * _ at hres
    dsimp only [E']
    rw [integral_add hiw hir]
    dsimp only [c, expectedParticleEnergy] at *
    nlinarith
  · exact ht

section EmpiricalBound
variable [BorelSpace Z] [SecondCountableTopology Z]

/-- The paper's finite-particle empirical interaction bound for the actual
synchronous weak-generator solution. The displayed assumptions identify the
reference iid cloud and retain the generator-domain and measurability inputs.
No expected-energy derivative, dissipation inequality or transport bound is
assumed. The interacting cloud is not required to be independent. -/
theorem finite_particle_interaction_bound (hsol : IsParticleCopyWeakSolution M N ν tests Γ)
    (D : TwistedGeometry S Z) (hN : 0 < N)
    (hquad : (fun p => particleQuadraticBilinear D N p p) ∈ tests)
    (ρ : ℝ) (hρ : 0 < ρ) (hmono : TwistedJointMonotonicity M D ρ)
    (LΨ : ℝ≥0) (V T : ℝ) (hV : 0 ≤ V) (sbar : ℝ → S)
    (hν : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (ν r))
    (hF : ∀ r ∈ Icc 0 T,
      MemLp (fun z => M.observation (M.parameter (sbar r)) (M.position z)) 2 (ν r))
    (hCloud : ∀ r ∈ Icc 0 T,
      (Γ r).map (fun p => p.2.2) = Measure.pi (fun _ : Fin N => ν r))
    (hbar : ∀ r ∈ Icc 0 T, ∀ᵐ p ∂Γ r, p.2.1 = sbar r)
    (hΨ : ∀ r ∈ Icc 0 T, ∀ s g g',
      ‖M.optimizer r s g - M.optimizer r s g'‖ ≤ (LΨ : ℝ) * ‖g - g'‖)
    (hVariance : ∀ r ∈ Icc 0 T,
      (∫ z, ‖M.observation (M.parameter (sbar r)) (M.position z) -
        M.meanGradient (ν r) (sbar r)‖ ^ 2 ∂ν r) ≤ V)
    (hR : ∀ r ∈ Icc 0 T,
      AEStronglyMeasurable (particlePopulationResidual M D N (ν r) r) (Γ r))
    (hzero : expectedParticleEnergy D N Γ 0 = 0)
    (t : ℝ) (ht : t ∈ Icc 0 T)
    (hmetric : AEStronglyMeasurable (particleEmpiricalDistanceSq (S := S) (Z := Z) N) (Γ t)) :
    Real.sqrt (∫ p, particleEmpiricalDistanceSq N p ∂Γ t) ≤
      ((LΨ : ℝ) / ρ) * Real.sqrt (D.conditionNumber * V / (N : ℝ)) *
        (1 - Real.exp (-ρ * t)) := by
  have hE := hsol.forced_energy_bound D hN hquad ρ hρ hmono LΨ V T hV sbar
    hν hF hCloud hbar hΨ hVariance hR hzero t ht
  have hm := particle_empirical_rms_le_energy D N hN (Γ t)
    (hsol.test_integrable _ hquad t ht.1) hmetric
  have he := div_le_div_of_nonneg_right hE (Real.sqrt_nonneg D.lower)
  have hκ : 0 ≤ D.conditionNumber := le_trans (by norm_num : (0 : ℝ) ≤ 1)
    D.conditionNumber_ge_one
  have hs : Real.sqrt (D.conditionNumber * V / (N : ℝ)) =
      (Real.sqrt D.upper / Real.sqrt D.lower) * Real.sqrt (V / (N : ℝ)) := by
    rw [show D.conditionNumber * V / (N : ℝ) = D.conditionNumber * (V / (N : ℝ)) by ring,
      Real.sqrt_mul hκ, D.sqrt_conditionNumber]
  apply hm.trans (he.trans_eq ?_)
  rw [hs]
  ring

end EmpiricalBound

end IsParticleCopyWeakSolution

end PBGSO
