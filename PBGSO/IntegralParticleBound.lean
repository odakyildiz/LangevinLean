import PBGSO.IntegralForcedEnergy
import PBGSO.IntegralModelContraction
import PBGSO.ParticleWeakBound
import PBGSO.ParticleAdditiveWeakRealization
import PBGSO.EmpiricalMeasurability

/-! # Integral particle/copy interaction bound
Actual original particle/copy coefficient realization, martingales and
stochastic increment isometry yield the finite-particle bound with merely
integrable time coefficients. No quadratic balance is an input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option maxRecDepth 2000
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace InnerProductSpace
namespace PBGSO.IntegralParticleBound
open QuadraticMartingale IntegralQuadraticEnergy IntegralModelContraction

section Projection
variable {Ω E H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

theorem quadratic_continuous (B : E →L[ℝ] E →L[ℝ] ℝ) :
    Continuous (fun x => B x x) := B.continuous.clm_apply continuous_id

theorem bilinear_continuous (B : E →L[ℝ] E →L[ℝ] ℝ) :
    Continuous (fun pq : E × E => B pq.1 pq.2) :=
  (B.continuous.comp continuous_fst).clm_apply continuous_snd

theorem polynomial_generator_measurable [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {J : Type*} [Fintype J]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (b : E → E) (σ : E → J → E)
    (hb : Measurable b) (hσ : ∀ j, Measurable (fun x => σ x j)) :
    Measurable (fun x => 2 * B x (b x) + ∑ j, B (σ x j) (σ x j)) := by
  have hB : Measurable (fun pq : E × E => B pq.1 pq.2) := (bilinear_continuous B).measurable
  have hwork := hB.comp (measurable_id.prodMk hb)
  have hsum : Measurable (fun x => ∑ j, B (σ x j) (σ x j)) := by
    apply Finset.measurable_sum
    intro j _
    exact hB.comp ((hσ j).prodMk (hσ j))
  exact (hwork.const_mul 2).add hsum

/-- The drift residual in an arbitrary complete Banach coordinate space. -/
def driftResidual (X b : ℝ → Lp E 2 Q) (t : ℝ) : Lp E 2 Q :=
  X t - X 0 - ∫ r in 0..t, b r

theorem driftResidual_decomposition (X b : ℝ → Lp E 2 Q) (t : ℝ) :
    X t = X 0 + (∫ r in 0..t, b r) + driftResidual Q X b t := by
  dsimp [driftResidual]
  abel

theorem projected_pair_integral (P : E →L[ℝ] H) (W : H →L[ℝ] H)
    (U V : Lp E 2 Q) : weightedPairing Q W (P.compLpL 2 Q U) (P.compLpL 2 Q V) =
      ∫ ω, ⟪P (U ω), W (P (V ω))⟫_ℝ ∂Q := by
  rw [weightedPairing_apply, lp_weighted_pairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [P.coeFn_compLpL U, P.coeFn_compLpL V] with ω hu hv
  rw [hu, hv]

theorem projected_pair_integrable (P : E →L[ℝ] H) (W : H →L[ℝ] H)
    (U V : Lp E 2 Q) : Integrable (fun ω => ⟪P (U ω), W (P (V ω))⟫_ℝ) Q := by
  apply (lp_weighted_pairing_integrable Q W (P.compLpL 2 Q U) (P.compLpL 2 Q V)).congr
  filter_upwards [P.coeFn_compLpL U, P.coeFn_compLpL V] with ω hu hv
  rw [hu, hv]

/-- Continuous linear projections preserve actual martingales. -/
theorem martingale_clm {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (P : E →L[ℝ] H)
    (m : ℝ → Ω → E) (hm : Martingale m ℱ Q) :
    Martingale (fun t => P ∘ m t) ℱ Q := by
  constructor
  · intro t
    exact P.continuous.comp_stronglyMeasurable (hm.stronglyAdapted t)
  · intro s t hst
    exact (P.comp_condExp_comm (hm.integrable t)).symm.trans
      ((hm.condExp_ae_eq hst).fun_comp P)

/-- Projected orthogonality only uses the actual noise representatives at
its two times, so stopped finite-horizon martingales are sufficient. -/
theorem projected_martingale_orthogonal (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (P : E →L[ℝ] H) (W : H →L[ℝ] H)
    (hW : ∀ x y, ⟪x, W y⟫_ℝ = ⟪W x, y⟫_ℝ)
    (Y Ms Mt : Lp E 2 Q) (m : ℝ → Ω → E) (hm : Martingale m ℱ Q)
    {s t : ℝ} (hst : s ≤ t) (hs : m s =ᵐ[Q] Ms) (ht : m t =ᵐ[Q] Mt)
    (hY : AEStronglyMeasurable[ℱ s] Y Q) :
    weightedPairing Q W (P.compLpL 2 Q Y) (P.compLpL 2 Q (Mt - Ms)) = 0 := by
  rw [map_sub]
  apply martingale_orthogonal_local W hW _ _ _ (fun t => P ∘ m t) (martingale_clm Q P m hm) hst
  · exact (hs.fun_comp P).trans (P.coeFn_compLpL Ms).symm
  · exact (ht.fun_comp P).trans (P.coeFn_compLpL Mt).symm
  · exact (P.continuous.comp_aestronglyMeasurable hY).congr (P.coeFn_compLpL Y).symm

end Projection

variable {Ω S Θ Z X I : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace Θ] [BorelSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype I]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (N : ℕ)

/-- The original normalized particle metric lifted to actual L² random
paired states. No Hilbert structure is invented for the raw product norm. -/
def particleBilinear (D : TwistedGeometry S Z) :
    Lp (ParticlePair N S Z) 2 Q →L[ℝ] Lp (ParticlePair N S Z) 2 Q →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp ((particleOptimizerDifference (S := S) (Z := Z) N).compLpL 2 Q)
    ((D.optimizerWeight.compLpL 2 Q).comp
      ((particleOptimizerDifference (S := S) (Z := Z) N).compLpL 2 Q)) +
  (N : ℝ)⁻¹ • ∑ i : Fin N, (innerSL ℝ).bilinearComp
    ((particleSamplerDifference (S := S) (Z := Z) N i).compLpL 2 Q)
    ((D.samplerWeight.compLpL 2 Q).comp
      ((particleSamplerDifference (S := S) (Z := Z) N i).compLpL 2 Q))

theorem particleBilinear_apply (D : TwistedGeometry S Z)
    (U V : Lp (ParticlePair N S Z) 2 Q) :
    particleBilinear Q N D U V =
      weightedPairing Q D.optimizerWeight
        ((particleOptimizerDifference N).compLpL 2 Q U) ((particleOptimizerDifference N).compLpL 2 Q V) +
      (N : ℝ)⁻¹ * ∑ i, weightedPairing Q D.samplerWeight
        ((particleSamplerDifference N i).compLpL 2 Q U) ((particleSamplerDifference N i).compLpL 2 Q V) := by
  simp [particleBilinear, weightedPairing, ContinuousLinearMap.bilinearComp_apply]

theorem particleBilinear_integral (D : TwistedGeometry S Z)
    (U V : Lp (ParticlePair N S Z) 2 Q) :
    particleBilinear Q N D U V =
      ∫ ω, particleQuadraticBilinear D N (U ω) (V ω) ∂Q := by
  rw [particleBilinear_apply, projected_pair_integral]
  simp_rw [projected_pair_integral]
  rw [← integral_finsetSum _ (fun i _ => projected_pair_integrable Q (particleSamplerDifference N i) D.samplerWeight U V),
    ← integral_const_mul, ← integral_add
      (projected_pair_integrable Q (particleOptimizerDifference N) D.optimizerWeight U V)
      ((integrable_finsetSum Finset.univ (fun i _ => projected_pair_integrable Q (particleSamplerDifference N i) D.samplerWeight U V)).const_mul _)]
  apply integral_congr_ae
  exact ae_of_all Q (fun ω => by
    simp [particleQuadraticBilinear_apply, particleOptimizerDifference, particleSamplerDifference])

theorem particleBilinear_symmetric (D : TwistedGeometry S Z)
    (U V : Lp (ParticlePair N S Z) 2 Q) :
    particleBilinear Q N D U V = particleBilinear Q N D V U := by
  rw [particleBilinear_integral, particleBilinear_integral]
  exact integral_congr_ae (ae_of_all Q (fun ω => particleQuadraticBilinear_symmetric D N (U ω) (V ω)))

theorem particleBilinear_orthogonal (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (D : TwistedGeometry S Z) (Y Ms Mt : Lp (ParticlePair N S Z) 2 Q)
    (m : ℝ → Ω → ParticlePair N S Z) (hm : Martingale m ℱ Q)
    {s t : ℝ} (hst : s ≤ t) (hs : m s =ᵐ[Q] Ms) (ht : m t =ᵐ[Q] Mt)
    (hY : AEStronglyMeasurable[ℱ s] Y Q) : particleBilinear Q N D Y (Mt - Ms) = 0 := by
  rw [particleBilinear_apply,
    projected_martingale_orthogonal Q ℱ (particleOptimizerDifference N) D.optimizerWeight D.optimizer_symmetric Y Ms Mt m hm hst hs ht hY]
  have hz (i : Fin N) := projected_martingale_orthogonal Q ℱ (particleSamplerDifference N i)
    D.samplerWeight D.sampler_symmetric Y Ms Mt m hm hst hs ht hY
  simp only [hz, Finset.sum_const_zero, mul_zero, add_zero]

/-- The exact quadratic generator formula in bounded bilinear notation. -/
theorem particleCopyGenerator_bilinear (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    (ν : Measure Z) (t : ℝ) (p : ParticlePair N S Z) :
    particleCopyGenerator M N ν t (fun p => particleQuadraticBilinear D N p p) p =
      2 * particleQuadraticBilinear D N p (particleCopyDrift M N ν t p) +
      ∑ ij : Fin N × I, particleQuadraticBilinear D N
        (particleCopyDiffusion M N p ij) (particleCopyDiffusion M N p ij) := by
  unfold particleCopyGenerator
  rw [(PBGSO.quadratic_hasFDerivAt (particleQuadraticBilinear D N) p).fderiv]
  simp_rw [PBGSO.quadratic_second_fderiv]
  simp only [add_apply, ContinuousLinearMap.flip_apply,
    particleQuadraticBilinear_symmetric D N (particleCopyDrift M N ν t p) p]
  simp only [← two_mul, ← Finset.mul_sum]
  ring

/-- Original interacting/reference coefficient realization and actual
martingale noise on a finite horizon. No generator equation or quadratic
energy balance is a field. The reference iid law is supplied separately. -/
structure ParticleIntegralTrajectory (M : Model S Θ Z X I) (ν : ℝ → Measure Z)
    (T : ℝ) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) where
  state : ℝ → Lp (ParticlePair N S Z) 2 Q
  drift : ℝ → Lp (ParticlePair N S Z) 2 Q
  diffusion : ℝ → (Fin N × I) → Lp (ParticlePair N S Z) 2 Q
  noise : ℝ → Ω → ParticlePair N S Z
  continuous : ContinuousOn state (Icc 0 T)
  drift_integrable : IntervalIntegrable drift volume 0 T
  diffusion_timeL2 : ∀ ij, MemLp (fun r => diffusion r ij) 2 (volume.restrict (uIoc 0 T))
  drift_realizes : ∀ t ∈ Icc 0 T, drift t =ᵐ[Q]
    fun ω => particleCopyDrift M N (ν t) t (state t ω)
  diffusion_realizes : ∀ t ∈ Icc 0 T, ∀ ij, diffusion t ij =ᵐ[Q]
    fun ω => particleCopyDiffusion M N (state t ω) ij
  drift_measurable : ∀ t ∈ Icc 0 T, Measurable (particleCopyDrift M N (ν t) t)
  diffusion_measurable : ∀ ij, Measurable (fun p => particleCopyDiffusion M N p ij)
  martingale : Martingale noise ℱ Q
  noise_realizes : ∀ t ∈ Icc 0 T, noise t =ᵐ[Q] driftResidual Q state drift t
  initial_adapted : AEStronglyMeasurable[ℱ 0] (state 0) Q
  drift_adapted : ∀ t ∈ Ioc 0 T, AEStronglyMeasurable[ℱ t] (drift t) Q

variable {Q N} {M : Model S Θ Z X I} {ν : ℝ → Measure Z} {T : ℝ}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- The joint interacting/reference law is the actual pushforward. -/
def ParticleIntegralTrajectory.law (U : ParticleIntegralTrajectory Q N M ν T ℱ) (t : ℝ) :=
  Q.map (U.state t)

instance ParticleIntegralTrajectory.law_probability (U : ParticleIntegralTrajectory Q N M ν T ℱ) (t : ℝ) :
    IsProbabilityMeasure (U.law t) :=
  (Measure.isProbabilityMeasure_map_iff (Lp.aestronglyMeasurable (U.state t)).aemeasurable).mpr inferInstance

/-- Every bounded bilinear work of two L² variables is integrable. -/
theorem bilinear_lp_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (U V : Lp E 2 Q) :
    Integrable (fun ω => B (U ω) (V ω)) Q := by
  have hh : MemLp (fun ω => ‖U ω‖ * ‖V ω‖) 1 Q := (Lp.memLp U).norm.mul (Lp.memLp V).norm
  apply ((memLp_one_iff_integrable.mp hh).const_mul ‖B‖).mono'
  · exact B.continuous₂.comp_aestronglyMeasurable
      ((Lp.aestronglyMeasurable U).prodMk (Lp.aestronglyMeasurable V))
  · filter_upwards with ω
    simpa only [mul_assoc] using B.le_opNorm₂ (U ω) (V ω)

theorem ParticleIntegralTrajectory.quadratic_integrable
    (U : ParticleIntegralTrajectory Q N M ν T ℱ) (D : TwistedGeometry S Z) (t : ℝ) :
    Integrable (fun p => particleQuadraticBilinear D N p p) (U.law t) := by
  apply (integrable_map_measure
    (quadratic_continuous (particleQuadraticBilinear D N)).aestronglyMeasurable
    (Lp.aestronglyMeasurable (U.state t)).aemeasurable).mpr
  exact bilinear_lp_integrable (particleQuadraticBilinear D N) _ _

theorem ParticleIntegralTrajectory.energy_eq
    (U : ParticleIntegralTrajectory Q N M ν T ℱ) (D : TwistedGeometry S Z) (t : ℝ) :
    expectedParticleEnergy D N U.law t = particleBilinear Q N D (U.state t) (U.state t) := by
  have hq : Continuous (fun p : ParticlePair N S Z => particleQuadraticBilinear D N p p) :=
    quadratic_continuous (particleQuadraticBilinear D N)
  rw [expectedParticleEnergy, ParticleIntegralTrajectory.law, integral_map
    (Lp.aestronglyMeasurable (U.state t)).aemeasurable hq.aestronglyMeasurable]
  exact (particleBilinear_integral Q N D _ _).symm

/-- Actual normalized noise energy from all common particle Brownian columns. -/
def ParticleIntegralTrajectory.noiseEnergy (U : ParticleIntegralTrajectory Q N M ν T ℱ)
    (D : TwistedGeometry S Z) (t : ℝ) :=
  ∑ ij : Fin N × I, particleBilinear Q N D (U.diffusion t ij) (U.diffusion t ij)

theorem ParticleIntegralTrajectory.noiseEnergy_integrable
    (U : ParticleIntegralTrajectory Q N M ν T ℱ) (D : TwistedGeometry S Z) :
    IntervalIntegrable (U.noiseEnergy D) volume 0 T := by
  rw [intervalIntegrable_iff]
  exact integrable_finsetSum Finset.univ (fun ij _ =>
    (quadratic_time_integrable (particleBilinear Q N D) _ (U.diffusion_timeL2 ij)).def')

/-- This is the actual stochastic-integral isometry in the normalized
particle metric, independently of the particle energy balance. -/
def ParticleIntegralTrajectory.SynchronousIsometry (U : ParticleIntegralTrajectory Q N M ν T ℱ)
    (D : TwistedGeometry S Z) : Prop :=
  ∀ t ∈ Icc 0 T, particleBilinear Q N D (driftResidual Q U.state U.drift t)
    (driftResidual Q U.state U.drift t) = ∫ r in 0..t, U.noiseEnergy D r

theorem ParticleIntegralTrajectory.generator_measurable
    (U : ParticleIntegralTrajectory Q N M ν T ℱ) (D : TwistedGeometry S Z)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    Measurable (particleCopyGenerator M N (ν t) t (fun p => particleQuadraticBilinear D N p p)) := by
  have hgen : particleCopyGenerator M N (ν t) t (fun p => particleQuadraticBilinear D N p p) =
      fun p => 2 * particleQuadraticBilinear D N p (particleCopyDrift M N (ν t) t p) +
        ∑ ij : Fin N × I, particleQuadraticBilinear D N
          (particleCopyDiffusion M N p ij) (particleCopyDiffusion M N p ij) :=
    funext (fun p => particleCopyGenerator_bilinear N M D (ν t) t p)
  have hm := polynomial_generator_measurable (particleQuadraticBilinear D N)
    (particleCopyDrift M N (ν t) t) (particleCopyDiffusion M N)
    (U.drift_measurable t ht) U.diffusion_measurable
  exact hgen.symm ▸ hm

theorem ParticleIntegralTrajectory.generator_realizes
    (U : ParticleIntegralTrajectory Q N M ν T ℱ) (D : TwistedGeometry S Z)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    (fun ω => particleCopyGenerator M N (ν t) t
      (fun p => particleQuadraticBilinear D N p p) (U.state t ω)) =ᵐ[Q]
    fun ω => 2 * particleQuadraticBilinear D N (U.state t ω) (U.drift t ω) +
      ∑ ij : Fin N × I, particleQuadraticBilinear D N (U.diffusion t ij ω) (U.diffusion t ij ω) := by
  filter_upwards [U.drift_realizes t ht, ae_all_iff.mpr (U.diffusion_realizes t ht)] with ω hb hσ
  rw [particleCopyGenerator_bilinear, ← hb]
  congr 1
  apply Finset.sum_congr rfl
  intro ij _
  rw [← hσ ij]

theorem ParticleIntegralTrajectory.generator_integrable
    (U : ParticleIntegralTrajectory Q N M ν T ℱ) (D : TwistedGeometry S Z)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    Integrable (particleCopyGenerator M N (ν t) t (fun p => particleQuadraticBilinear D N p p)) (U.law t) := by
  apply (integrable_map_measure (U.generator_measurable D t ht).aestronglyMeasurable
    (Lp.aestronglyMeasurable (U.state t)).aemeasurable).mpr
  apply ((bilinear_lp_integrable (particleQuadraticBilinear D N) (U.state t) (U.drift t)).const_mul 2 |>.add
    (integrable_finsetSum Finset.univ (fun ij _ =>
      bilinear_lp_integrable (particleQuadraticBilinear D N) (U.diffusion t ij) (U.diffusion t ij)))).congr
  exact (U.generator_realizes D t ht).symm

/-- The work in the actual integral balance is the original full
particle/copy generator expectation, with every coefficient identified. -/
theorem ParticleIntegralTrajectory.work_generator_integral
    (U : ParticleIntegralTrajectory Q N M ν T ℱ) (D : TwistedGeometry S Z)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    2 * particleBilinear Q N D (U.state t) (U.drift t) + U.noiseEnergy D t =
      ∫ p, particleCopyGenerator M N (ν t) t
        (fun p => particleQuadraticBilinear D N p p) p ∂U.law t := by
  rw [ParticleIntegralTrajectory.law, integral_map
    (Lp.aestronglyMeasurable (U.state t)).aemeasurable
    (U.generator_measurable D t ht).aestronglyMeasurable,
    integral_congr_ae (U.generator_realizes D t ht),
    integral_add ((bilinear_lp_integrable (particleQuadraticBilinear D N) (U.state t) (U.drift t)).const_mul 2)
      (integrable_finsetSum Finset.univ (fun ij _ =>
        bilinear_lp_integrable (particleQuadraticBilinear D N) (U.diffusion t ij) (U.diffusion t ij))),
    integral_const_mul, integral_finsetSum _ (fun ij _ =>
      bilinear_lp_integrable (particleQuadraticBilinear D N) (U.diffusion t ij) (U.diffusion t ij))]
  simp_rw [← particleBilinear_integral Q N D]
  rfl

/-- The exact integral particle energy equation is derived from actual
martingales and source coefficients, not passed to the bound as a premise. -/
theorem ParticleIntegralTrajectory.energy_integral
    (U : ParticleIntegralTrajectory Q N M ν T ℱ) (D : TwistedGeometry S Z) (hT : 0 ≤ T)
    (hIso : U.SynchronousIsometry D) :
    expectedParticleEnergy D N U.law T = expectedParticleEnergy D N U.law 0 +
      ∫ r in 0..T, 2 * particleBilinear Q N D (U.state r) (U.drift r) + U.noiseEnergy D r := by
  rw [U.energy_eq, U.energy_eq]
  have hzero : driftResidual Q U.state U.drift 0 = 0 := by simp [driftResidual]
  apply quadratic_balance (particleBilinear Q N D) (particleBilinear_symmetric Q N D)
    U.state U.drift (driftResidual Q U.state U.drift) (U.noiseEnergy D) hT
    U.drift_integrable (U.noiseEnergy_integrable D) U.continuous
    (fun r _ => driftResidual_decomposition Q U.state U.drift r)
  · simpa only [hzero, sub_zero] using particleBilinear_orthogonal Q N ℱ D
      (U.state 0) (driftResidual Q U.state U.drift 0) (driftResidual Q U.state U.drift T)
      U.noise U.martingale hT (U.noise_realizes 0 ⟨le_rfl, hT⟩)
      (U.noise_realizes T ⟨hT, le_rfl⟩) U.initial_adapted
  · intro r hr
    exact particleBilinear_orthogonal Q N ℱ D (U.drift r)
      (driftResidual Q U.state U.drift r) (driftResidual Q U.state U.drift T)
      U.noise U.martingale hr.2 (U.noise_realizes r (Ioc_subset_Icc_self hr))
      (U.noise_realizes T ⟨hT, le_rfl⟩) (U.drift_adapted r hr)
  · exact hIso T ⟨hT, le_rfl⟩

/-- Restriction preserves the actual paths and all original coefficients. -/
def ParticleIntegralTrajectory.restrict (U : ParticleIntegralTrajectory Q N M ν T ℱ)
    {R : ℝ} (hR : R ∈ Icc 0 T) : ParticleIntegralTrajectory Q N M ν R ℱ where
  state := U.state
  drift := U.drift
  diffusion := U.diffusion
  noise := U.noise
  continuous := U.continuous.mono (Icc_subset_Icc le_rfl hR.2)
  drift_integrable := U.drift_integrable.mono_set' (by
    rw [uIoc_of_le hR.1, uIoc_of_le (hR.1.trans hR.2)]
    exact Ioc_subset_Ioc_right hR.2)
  diffusion_timeL2 := fun ij => (U.diffusion_timeL2 ij).mono_measure
    (Measure.restrict_mono (by
      rw [uIoc_of_le hR.1, uIoc_of_le (hR.1.trans hR.2)]
      exact Ioc_subset_Ioc_right hR.2) le_rfl)
  drift_realizes := fun r hr => U.drift_realizes r ⟨hr.1, hr.2.trans hR.2⟩
  diffusion_realizes := fun r hr => U.diffusion_realizes r ⟨hr.1, hr.2.trans hR.2⟩
  drift_measurable := fun r hr => U.drift_measurable r ⟨hr.1, hr.2.trans hR.2⟩
  diffusion_measurable := U.diffusion_measurable
  martingale := U.martingale
  noise_realizes := fun r hr => U.noise_realizes r ⟨hr.1, hr.2.trans hR.2⟩
  initial_adapted := U.initial_adapted
  drift_adapted := fun r hr => U.drift_adapted r ⟨hr.1, hr.2.trans hR.2⟩

/-- The optimizer fluctuation is measurable from the original paired drift:
its empirical-reference term is the first drift coordinate on the diagonal. -/
theorem ParticleIntegralTrajectory.residual_measurable
    (U : ParticleIntegralTrajectory Q N M ν T ℱ) (D : TwistedGeometry S Z)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    Measurable (particlePopulationResidual M D N (ν t) t) := by
  have hdiag : Measurable (fun p : ParticlePair N S Z => (p.2, p.2)) :=
    measurable_snd.prodMk measurable_snd
  have hfirst : Measurable (fun p : ParticlePair N S Z => p.1.1) :=
    measurable_fst.comp measurable_fst
  have hsecond : Measurable (fun p : ParticlePair N S Z => p.2.1) :=
    measurable_fst.comp measurable_snd
  have he : Measurable (fun p : ParticlePair N S Z => M.particleField N t p.2.1 p.2.2) :=
    hfirst.comp ((U.drift_measurable t ht).comp hdiag)
  have hp : Measurable (fun p : ParticlePair N S Z => M.optimizerField t p.2.1 (ν t)) :=
    hsecond.comp (U.drift_measurable t ht)
  have hi : Continuous (fun p : S × S => ⟪p.1, D.optimizerWeight p.2⟫_ℝ) := by fun_prop
  exact hi.measurable.comp ((hfirst.sub hsecond).prodMk (he.sub hp))

/-- The raw time work is dissipative up to the actual iid reference gradient
fluctuation. Source A3, the true iid reference marginal and finite-sample
variance derive this estimate; it is not an energy-dissipation premise. -/
theorem ParticleIntegralTrajectory.forcing_dissipation
    (U : ParticleIntegralTrajectory Q N M ν T ℱ) (D : TwistedGeometry S Z)
    (hN : 0 < N) (ρ : ℝ) (hmono : TwistedJointMonotonicity M D ρ)
    (LΨ : ℝ≥0) (V : ℝ) (hV : 0 ≤ V) (sbar : S)
    (t : ℝ) (ht : t ∈ Icc 0 T) [IsProbabilityMeasure (ν t)]
    (hF : MemLp (fun z => M.observation (M.parameter sbar) (M.position z)) 2 (ν t))
    (hCloud : (U.law t).map (fun p => p.2.2) = Measure.pi (fun _ : Fin N => ν t))
    (hbar : ∀ᵐ p ∂U.law t, p.2.1 = sbar)
    (hΨ : ∀ s g g', ‖M.optimizer t s g - M.optimizer t s g'‖ ≤ (LΨ : ℝ) * ‖g - g'‖)
    (hVariance : (∫ z, ‖M.observation (M.parameter sbar) (M.position z) -
      M.meanGradient (ν t) sbar‖ ^ 2 ∂ν t) ≤ V) :
    2 * particleBilinear Q N D (U.state t) (U.drift t) + U.noiseEnergy D t ≤
      -2 * ρ * expectedParticleEnergy D N U.law t +
      2 * ((LΨ : ℝ) * Real.sqrt D.upper * Real.sqrt (V / (N : ℝ))) *
        Real.sqrt (expectedParticleEnergy D N U.law t) := by
  have hq := U.quadratic_integrable D t
  obtain ⟨hir, hres⟩ := expectedParticlePopulationResidual_le M D N hN (ν t) sbar hF
    (U.law t) hCloud hbar hq t LΨ hΨ (U.residual_measurable D t ht).aestronglyMeasurable
  have hsum : Integrable (fun p : ParticlePair N S Z =>
      particleCouplingWork M D N t p.1.1 p.2.1 p.1.2 p.2.2 +
        particlePopulationResidual M D N (ν t) t p) (U.law t) := by
    have hi := (U.generator_integrable D t ht).const_mul (1 / 2 : ℝ)
    convert hi using 1
    ext p
    rw [particleCopyGenerator_quadratic]
    dsimp only [particlePopulationResidual]
    ring
  have hiw : Integrable (fun p : ParticlePair N S Z =>
      particleCouplingWork M D N t p.1.1 p.2.1 p.1.2 p.2.2) (U.law t) := by
    convert hsum.sub hir using 1
    ext p
    exact (add_sub_cancel_right _ _).symm
  have hwork := integral_mono hiw (hq.const_mul (-ρ))
    (fun p : ParticlePair N S Z => by
      simpa only [particleQuadraticBilinear_diag] using
        particleCouplingWork_le M D ρ hmono N hN t ht.1 p.1.1 p.2.1 p.1.2 p.2.2)
  rw [integral_const_mul] at hwork
  have hvar := Real.sqrt_le_sqrt
    (div_le_div_of_nonneg_right hVariance (Nat.cast_nonneg N : (0 : ℝ) ≤ N))
  have hvar' := mul_le_mul_of_nonneg_left hvar
    (by positivity : 0 ≤ (LΨ : ℝ) * Real.sqrt D.upper *
      Real.sqrt (expectedParticleEnergy D N U.law t))
  change _ ≤ ((LΨ : ℝ) * Real.sqrt D.upper) *
    Real.sqrt (expectedParticleEnergy D N U.law t) * _ at hres
  have hgen : (∫ p, particleCopyGenerator M N (ν t) t
      (fun p => particleQuadraticBilinear D N p p) p ∂U.law t) =
      2 * ((∫ p, particleCouplingWork M D N t p.1.1 p.2.1 p.1.2 p.2.2 ∂U.law t) +
        (∫ p, particlePopulationResidual M D N (ν t) t p ∂U.law t)) := by
    simp_rw [particleCopyGenerator_quadratic]
    rw [integral_const_mul]
    change 2 * (∫ p, particleCouplingWork M D N t p.1.1 p.2.1 p.1.2 p.2.2 +
      particlePopulationResidual M D N (ν t) t p ∂U.law t) = _
    rw [integral_add hiw hir]
  rw [U.work_generator_integral D t ht, hgen]
  dsimp only [expectedParticleEnergy] at *
  nlinarith

/-- Finite-particle interaction energy for the actual integral dynamics.
All forcing, measurability and energy identities are derived. The iid law
belongs only to the reference cloud; interacting particles may depend on
each other and on the shared random optimizer. -/
theorem ParticleIntegralTrajectory.forced_energy_bound
    (U : ParticleIntegralTrajectory Q N M ν T ℱ) (D : TwistedGeometry S Z)
    (hT : 0 ≤ T) (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M D ρ) (LΨ : ℝ≥0) (V : ℝ) (hV : 0 ≤ V)
    (sbar : ℝ → S)
    (hν : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (ν r))
    (hF : ∀ r ∈ Icc 0 T,
      MemLp (fun z => M.observation (M.parameter (sbar r)) (M.position z)) 2 (ν r))
    (hCloud : ∀ r ∈ Icc 0 T,
      (U.law r).map (fun p => p.2.2) = Measure.pi (fun _ : Fin N => ν r))
    (hbar : ∀ r ∈ Icc 0 T, ∀ᵐ p ∂U.law r, p.2.1 = sbar r)
    (hΨ : ∀ r ∈ Icc 0 T, ∀ s g g',
      ‖M.optimizer r s g - M.optimizer r s g'‖ ≤ (LΨ : ℝ) * ‖g - g'‖)
    (hVariance : ∀ r ∈ Icc 0 T,
      (∫ z, ‖M.observation (M.parameter (sbar r)) (M.position z) -
        M.meanGradient (ν r) (sbar r)‖ ^ 2 ∂ν r) ≤ V)
    (hSync : ∀ᵐ ω ∂Q, (U.state 0 ω).1 = (U.state 0 ω).2)
    (hIso : U.SynchronousIsometry D) :
    Real.sqrt (expectedParticleEnergy D N U.law T) ≤
      ((LΨ : ℝ) * Real.sqrt D.upper * Real.sqrt (V / (N : ℝ))) / ρ *
        (1 - Real.exp (-ρ * T)) := by
  apply IntegralForcedEnergy.forced_energy_bound
    (expectedParticleEnergy D N U.law)
    (fun r => 2 * particleBilinear Q N D (U.state r) (U.drift r) + U.noiseEnergy D r)
    hT hρ (by positivity)
  · apply IntervalIntegrable.add _ (U.noiseEnergy_integrable D)
    exact (bilinear_continuous_integrable (particleBilinear Q N D) U.state U.drift
      (by simpa [uIcc_of_le hT] using U.continuous) U.drift_integrable).const_mul 2
  · intro r hr
    exact (U.restrict hr).energy_integral D hr.1 (fun s hs => hIso s ⟨hs.1, hs.2.trans hr.2⟩)
  · intro r _
    exact integral_nonneg (particleQuadratic_nonneg D N)
  · rw [U.energy_eq, particleBilinear_integral]
    apply integral_eq_zero_of_ae
    filter_upwards [hSync] with ω hω
    simp [particleQuadraticBilinear_apply, hω]
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr' := Ioc_subset_Icc_self hr
    letI := hν r hr'
    exact U.forcing_dissipation D hN ρ hmono LΨ V hV (sbar r) r hr'
      (hF r hr') (hCloud r hr') (hbar r hr') (hΨ r hr') (hVariance r hr')

/-- Source finite-particle empirical interaction bound for actual integral
trajectories, with no pointwise time regularity or quadratic test-domain
premise. The empirical W₂ statistic's measurability is derived. -/
theorem ParticleIntegralTrajectory.finite_particle_interaction_bound
    (U : ParticleIntegralTrajectory Q N M ν T ℱ) (D : TwistedGeometry S Z)
    (hT : 0 ≤ T) (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M D ρ) (LΨ : ℝ≥0) (V : ℝ) (hV : 0 ≤ V)
    (sbar : ℝ → S)
    (hν : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (ν r))
    (hF : ∀ r ∈ Icc 0 T,
      MemLp (fun z => M.observation (M.parameter (sbar r)) (M.position z)) 2 (ν r))
    (hCloud : ∀ r ∈ Icc 0 T,
      (U.law r).map (fun p => p.2.2) = Measure.pi (fun _ : Fin N => ν r))
    (hbar : ∀ r ∈ Icc 0 T, ∀ᵐ p ∂U.law r, p.2.1 = sbar r)
    (hΨ : ∀ r ∈ Icc 0 T, ∀ s g g',
      ‖M.optimizer r s g - M.optimizer r s g'‖ ≤ (LΨ : ℝ) * ‖g - g'‖)
    (hVariance : ∀ r ∈ Icc 0 T,
      (∫ z, ‖M.observation (M.parameter (sbar r)) (M.position z) -
        M.meanGradient (ν r) (sbar r)‖ ^ 2 ∂ν r) ≤ V)
    (hSync : ∀ᵐ ω ∂Q, (U.state 0 ω).1 = (U.state 0 ω).2)
    (hIso : U.SynchronousIsometry D) :
    Real.sqrt (∫ p, particleEmpiricalDistanceSq N p ∂U.law T) ≤
      ((LΨ : ℝ) / ρ) * Real.sqrt (D.conditionNumber * V / (N : ℝ)) *
        (1 - Real.exp (-ρ * T)) := by
  have hE := U.forced_energy_bound D hT hN ρ hρ hmono LΨ V hV sbar
    hν hF hCloud hbar hΨ hVariance hSync hIso
  have hm := particle_empirical_rms_le_energy D N hN (U.law T)
    (U.quadratic_integrable D T)
    (EmpiricalTransportMeasurable.particleEmpiricalDistanceSq_aestronglyMeasurable N hN (U.law T))
  have he := div_le_div_of_nonneg_right hE (Real.sqrt_nonneg D.lower)
  have hκ : 0 ≤ D.conditionNumber := le_trans (by norm_num : (0 : ℝ) ≤ 1) D.conditionNumber_ge_one
  have hs : Real.sqrt (D.conditionNumber * V / (N : ℝ)) =
      (Real.sqrt D.upper / Real.sqrt D.lower) * Real.sqrt (V / (N : ℝ)) := by
    rw [show D.conditionNumber * V / (N : ℝ) = D.conditionNumber * (V / (N : ℝ)) by ring,
      Real.sqrt_mul hκ, D.sqrt_conditionNumber]
  apply hm.trans (he.trans_eq ?_)
  rw [hs]
  ring

end PBGSO.IntegralParticleBound
