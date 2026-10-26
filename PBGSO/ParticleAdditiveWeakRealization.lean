import PBGSO.AdditiveWeakRealization
import PBGSO.ParticleProcess
import PBGSO.ParticleMethodLp
import PBGSO.IndependentCopies
import PBGSO.GlobalIntegral

/-! # Actual additive particle/copy integral trajectories and their quadratic generator
The optimiser is a random coordinate of the interacting L² state. The reference
cloud is packed from actual same-input sampler copies. Shared additive input
cancels in the difference equation, yielding the quadratic weak equation for
the source's complete particle/copy generator, without a marginal Itô claim.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators RealInnerProductSpace InnerProductSpace Topology
namespace PBGSO

section Packing
variable {Ω Z : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  (Q : Measure Ω) (N : ℕ)

/-- Pack finitely many L² variables on the same sample space into their actual
coordinate array. Their dependence is retained. -/
def packLp : (Fin N → Lp Z 2 Q) →L[ℝ] Lp (Fin N → Z) 2 Q :=
  ∑ i : Fin N, ((ContinuousLinearMap.single ℝ (fun _ : Fin N ↦ Z) i).compLpL 2 Q).comp
    (ContinuousLinearMap.proj i)

theorem packLp_coe (U : Fin N → Lp Z 2 Q) :
    packLp (Z := Z) Q N U =ᵐ[Q] fun ω i ↦ U i ω := by
  classical
  have hs := Lp.coeFn_finsetSum Finset.univ (fun i : Fin N ↦
    (ContinuousLinearMap.single ℝ (fun _ : Fin N ↦ Z) i).compLp (U i))
  have hi : ∀ᵐ ω ∂Q, ∀ i : Fin N,
      ((ContinuousLinearMap.single ℝ (fun _ : Fin N ↦ Z) i).compLp (U i)) ω =
        (ContinuousLinearMap.single ℝ (fun _ : Fin N ↦ Z) i) (U i ω) := by
    exact (ae_all_iff.mpr fun i ↦ (ContinuousLinearMap.single ℝ (fun _ : Fin N ↦ Z) i).coeFn_compLp (U i))
  filter_upwards [hs, hi] with ω hs hi
  have hdef : (packLp (Z := Z) Q N) U = ∑ i : Fin N, (ContinuousLinearMap.single ℝ (fun _ : Fin N ↦ Z) i).compLp (U i) := by
    simp only [packLp, sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
    rfl
  rw [hdef]
  rw [hs]
  funext j
  simp only [Finset.sum_apply]
  simp_rw [hi]
  simp

@[simp] theorem packLp_proj (U : Fin N → Lp Z 2 Q) (i : Fin N) :
    ((ContinuousLinearMap.proj i : (Fin N → Z) →L[ℝ] Z).compLpL 2 Q)
      (packLp (Z := Z) Q N U) = U i := by
  apply Lp.ext
  filter_upwards [(ContinuousLinearMap.proj i : (Fin N → Z) →L[ℝ] Z).coeFn_compLpL
    (packLp (Z := Z) Q N U), packLp_coe Q N U] with ω hp hu
  rw [hp, hu]
  rfl

end Packing

section Geometry
variable {Ω A Z : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (N : ℕ)

/-- Optimiser projection of the full random particle state. -/
def particleOptimizerLp : Lp (A × (Fin N → Z)) 2 Q →L[ℝ] Lp A 2 Q :=
  (ContinuousLinearMap.fst ℝ A (Fin N → Z)).compLpL 2 Q

/-- One sampler coordinate of the full random particle state. -/
def particleSamplerLp (i : Fin N) : Lp (A × (Fin N → Z)) 2 Q →L[ℝ] Lp Z 2 Q :=
  ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ A (Fin N → Z))).compLpL 2 Q

/-- The actual weighted bilinear average on random full particle states. -/
def particleLpBilinear (D : TwistedGeometry A Z) :
    Lp (A × (Fin N → Z)) 2 Q →L[ℝ] Lp (A × (Fin N → Z)) 2 Q →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (particleOptimizerLp (A := A) (Z := Z) Q N)
    ((D.optimizerWeight.compLpL 2 Q).comp (particleOptimizerLp (A := A) (Z := Z) Q N)) +
  (N : ℝ)⁻¹ • ∑ i : Fin N, (innerSL ℝ).bilinearComp (particleSamplerLp (A := A) (Z := Z) Q N i)
    ((D.samplerWeight.compLpL 2 Q).comp (particleSamplerLp (A := A) (Z := Z) Q N i))

theorem particleLpBilinear_integral (D : TwistedGeometry A Z)
    (U V : Lp (A × (Fin N → Z)) 2 Q) :
    particleLpBilinear Q N D U V = ∫ ω,
      ⟪(U ω).1, D.optimizerWeight (V ω).1⟫_ℝ +
        (N : ℝ)⁻¹ * ∑ i : Fin N, ⟪(U ω).2 i, D.samplerWeight ((V ω).2 i)⟫_ℝ ∂Q := by
  have hA := lp_weighted_pairing_integrable Q D.optimizerWeight
    (particleOptimizerLp (A := A) (Z := Z) Q N U) (particleOptimizerLp (A := A) (Z := Z) Q N V)
  have hZ (i : Fin N) := lp_weighted_pairing_integrable Q D.samplerWeight
    (particleSamplerLp (A := A) (Z := Z) Q N i U) (particleSamplerLp (A := A) (Z := Z) Q N i V)
  simp only [particleLpBilinear, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul]
  change ⟪particleOptimizerLp (A := A) (Z := Z) Q N U, D.optimizerWeight.compLpL 2 Q (particleOptimizerLp (A := A) (Z := Z) Q N V)⟫_ℝ +
    (N : ℝ)⁻¹ * ∑ i, ⟪particleSamplerLp (A := A) (Z := Z) Q N i U,
      D.samplerWeight.compLpL 2 Q (particleSamplerLp (A := A) (Z := Z) Q N i V)⟫_ℝ = _
  simp_rw [lp_weighted_pairing_eq_integral]
  rw [← integral_finset_sum _ (fun i _ ↦ hZ i), ← integral_const_mul,
    ← integral_add hA ((integrable_finset_sum _ (fun i _ ↦ hZ i)).const_mul _)]
  apply integral_congr_ae
  have hi (i : Fin N) : ∀ᵐ ω ∂Q,
      (particleSamplerLp (A := A) (Z := Z) Q N i U) ω = (U ω).2 i ∧
      (particleSamplerLp (A := A) (Z := Z) Q N i V) ω = (V ω).2 i := by
    filter_upwards [((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ A (Fin N → Z))).coeFn_compLpL U,
      ((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ A (Fin N → Z))).coeFn_compLpL V] with ω hu hv
    exact ⟨hu, hv⟩
  filter_upwards [(ContinuousLinearMap.fst ℝ A (Fin N → Z)).coeFn_compLpL U,
    (ContinuousLinearMap.fst ℝ A (Fin N → Z)).coeFn_compLpL V,
    ae_all_iff.mpr hi] with ω hu hv hz
  simp only [particleOptimizerLp] at hu hv ⊢
  rw [hu, hv]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [(hz i).1, (hz i).2]

/-- Every displayed optimiser/sampler weighted work is genuinely integrable
for arbitrary full L² states, including dependent coordinates. -/
theorem particleLpWork_integrable (D : TwistedGeometry A Z)
    (U V : Lp (A × (Fin N → Z)) 2 Q) :
    Integrable (fun ω ↦ ⟪(U ω).1, D.optimizerWeight (V ω).1⟫_ℝ +
      (N : ℝ)⁻¹ * ∑ i : Fin N, ⟪(U ω).2 i, D.samplerWeight ((V ω).2 i)⟫_ℝ) Q := by
  have hA := lp_weighted_pairing_integrable Q D.optimizerWeight
    (particleOptimizerLp (A := A) (Z := Z) Q N U) (particleOptimizerLp (A := A) (Z := Z) Q N V)
  have hZ (i : Fin N) := lp_weighted_pairing_integrable Q D.samplerWeight
    (particleSamplerLp (A := A) (Z := Z) Q N i U) (particleSamplerLp (A := A) (Z := Z) Q N i V)
  apply (hA.add ((integrable_finsetSum Finset.univ (fun i _ ↦ hZ i)).const_mul (N : ℝ)⁻¹)).congr
  have hi (i : Fin N) : ∀ᵐ ω ∂Q,
      (particleSamplerLp (A := A) (Z := Z) Q N i U) ω = (U ω).2 i ∧
      (particleSamplerLp (A := A) (Z := Z) Q N i V) ω = (V ω).2 i := by
    filter_upwards [((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ A (Fin N → Z))).coeFn_compLpL U,
      ((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ A (Fin N → Z))).coeFn_compLpL V] with ω hu hv
    exact ⟨hu, hv⟩
  filter_upwards [(ContinuousLinearMap.fst ℝ A (Fin N → Z)).coeFn_compLpL U,
    (ContinuousLinearMap.fst ℝ A (Fin N → Z)).coeFn_compLpL V,
    ae_all_iff.mpr hi] with ω hu hv hz
  change ⟪(particleOptimizerLp (A := A) (Z := Z) Q N U) ω,
    D.optimizerWeight ((particleOptimizerLp (A := A) (Z := Z) Q N V) ω)⟫_ℝ + _ = _
  simp only [particleOptimizerLp] at hu hv ⊢
  rw [hu, hv]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [(hz i).1, (hz i).2]

/-- Actual joint law of interacting and reference full states. -/
def particlePairLaw (U V : Lp (A × (Fin N → Z)) 2 Q) :
    Measure (ParticlePair N A Z) := Q.map (fun ω ↦ (U ω, V ω))

theorem particlePairWork_integrable (D : TwistedGeometry A Z)
    (U V F G : Lp (A × (Fin N → Z)) 2 Q) :
    Integrable (fun ω ↦ particleQuadraticBilinear D N (U ω, V ω) (F ω, G ω)) Q := by
  apply (particleLpWork_integrable Q N D (U - V) (F - G)).congr
  filter_upwards [Lp.coeFn_sub U V, Lp.coeFn_sub F G] with ω huv hfg
  rw [huv, hfg, particleQuadraticBilinear_apply]
  rfl

theorem particlePairWork_integral (D : TwistedGeometry A Z)
    (U V F G : Lp (A × (Fin N → Z)) 2 Q) :
    (∫ ω, particleQuadraticBilinear D N (U ω, V ω) (F ω, G ω) ∂Q) =
      particleLpBilinear Q N D (U - V) (F - G) := by
  rw [particleLpBilinear_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub U V, Lp.coeFn_sub F G] with ω huv hfg
  rw [huv, hfg, particleQuadraticBilinear_apply]
  rfl

theorem particlePairLaw_energy_integral (D : TwistedGeometry A Z)
    (U V : Lp (A × (Fin N → Z)) 2 Q) :
    (∫ p, particleQuadraticBilinear D N p p ∂particlePairLaw Q N U V) =
      particleLpBilinear Q N D (U - V) (U - V) := by
  rw [particlePairLaw, integral_map
    ((Lp.aestronglyMeasurable U).aemeasurable.prodMk (Lp.aestronglyMeasurable V).aemeasurable)]
  · exact particlePairWork_integral Q N D U V U V
  · exact (by fun_prop : Continuous (fun p : ParticlePair N A Z ↦ particleQuadraticBilinear D N p p)).aestronglyMeasurable


/-- A deterministic optimiser coordinate of the actual reference variable
remains deterministic under the true joint law. -/
theorem particlePairLaw_reference_optimizer (U V : Lp (A × (Fin N → Z)) 2 Q)
    (a : A) (hV : ∀ᵐ ω ∂Q, (V ω).1 = a) :
    ∀ᵐ p ∂particlePairLaw Q N U V, p.2.1 = a := by
  apply (ae_map_iff
    ((Lp.aestronglyMeasurable U).aemeasurable.prodMk (Lp.aestronglyMeasurable V).aemeasurable)
    (isClosed_eq continuous_snd.fst continuous_const).measurableSet).mpr
  exact hV

/-- The source's actual reference-cloud marginal is the packed cloud law. -/
theorem particlePairLaw_reference_cloud (U V : Lp (A × (Fin N → Z)) 2 Q) :
    (particlePairLaw Q N U V).map (fun p ↦ p.2.2) = Q.map (fun ω ↦ (V ω).2) := by
  rw [particlePairLaw, Measure.map_map (by fun_prop : Measurable (fun p : ParticlePair N A Z ↦ p.2.2))
    ((Lp.stronglyMeasurable U).measurable.prodMk (Lp.stronglyMeasurable V).measurable)]
  rfl

/-- Equality of the actual initial L² states gives the true zero quadratic
initial error, rather than requiring the scalar energy equation. -/
theorem particlePairLaw_zero_energy (D : TwistedGeometry A Z)
    (Y W : ℝ → Lp (A × (Fin N → Z)) 2 Q) (hzero : Y 0 = W 0) :
    expectedParticleEnergy D N (fun t ↦ particlePairLaw Q N (Y t) (W t)) 0 = 0 := by
  rw [expectedParticleEnergy, particlePairLaw_energy_integral, hzero, sub_self,
    map_zero]


theorem particleLpBilinear_symmetric (D : TwistedGeometry A Z)
    (U V : Lp (A × (Fin N → Z)) 2 Q) :
    particleLpBilinear Q N D U V = particleLpBilinear Q N D V U := by
  rw [particleLpBilinear_integral, particleLpBilinear_integral]
  apply integral_congr_ae
  apply ae_of_all
  intro ω
  dsimp only
  congr 1
  · exact (D.optimizer_symmetric _ _).trans (real_inner_comm _ _)
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact (D.sampler_symmetric _ _).trans (real_inner_comm _ _)

end Geometry
section IndependentReference
variable {Ω A Z : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (N : ℕ)

/-- Lift one deterministic optimiser and one actual L² sampler trajectory to
an independent full reference cloud on the finite product of complete seeds. -/
def independentReferenceCLM : (A × Lp Z 2 Q) →L[ℝ]
    Lp (A × (Fin N → Z)) 2 (IndependentCopies.seeds (J := Fin N) Q) :=
  ((ContinuousLinearMap.inl ℝ A (Fin N → Z)).compLpL 2 (IndependentCopies.seeds Q)).comp
    ((Lp.constL 2 (IndependentCopies.seeds Q) ℝ).comp (ContinuousLinearMap.fst ℝ A (Lp Z 2 Q))) +
  ((ContinuousLinearMap.inr ℝ A (Fin N → Z)).compLpL 2 (IndependentCopies.seeds Q)).comp
    ((packLp (Z := Z) (IndependentCopies.seeds Q) N).comp
      (ContinuousLinearMap.pi fun i : Fin N ↦
        (lpPullbackCLM (measurePreserving_eval (fun _ : Fin N ↦ Q) i)).comp
          (ContinuousLinearMap.snd ℝ A (Lp Z 2 Q))))

theorem independentReferenceCLM_apply (y : A × Lp Z 2 Q) :
    independentReferenceCLM (A := A) (Z := Z) Q N y = Methods.pairLp (IndependentCopies.seeds Q)
      (Lp.const 2 (IndependentCopies.seeds Q) y.1)
      (packLp (Z := Z) (IndependentCopies.seeds Q) N
        (fun i ↦ IndependentCopies.copyLp Q y.2 i)) := by
  simp only [independentReferenceCLM, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.pi_apply]
  rfl

theorem independentReferenceCLM_coe (y : A × Lp Z 2 Q) :
    independentReferenceCLM (A := A) (Z := Z) Q N y =ᵐ[IndependentCopies.seeds Q]
      fun ω ↦ (y.1, fun i ↦ y.2 (ω i)) := by
  rw [independentReferenceCLM_apply]
  have hi : ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q, ∀ i : Fin N,
      IndependentCopies.copyLp Q y.2 i ω = y.2 (ω i) :=
    ae_all_iff.mpr fun i ↦ IndependentCopies.copyLp_coe Q y.2 i
  filter_upwards [Methods.pairLp_coe (IndependentCopies.seeds Q)
    (Lp.const 2 (IndependentCopies.seeds Q) y.1)
    (packLp (Z := Z) (IndependentCopies.seeds Q) N (fun i ↦ IndependentCopies.copyLp Q y.2 i)),
    Lp.coeFn_const 2 (IndependentCopies.seeds (J := Fin N) Q) y.1,
    packLp_coe (IndependentCopies.seeds Q) N (fun i ↦ IndependentCopies.copyLp Q y.2 i), hi]
    with ω hp ha hz hi
  rw [hp, ha, hz]
  exact Prod.ext rfl (funext hi)

/-- The independent reference optimiser is the given deterministic state. -/
theorem independentReference_optimizer_coe (y : A × Lp Z 2 Q) :
    ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q,
      (independentReferenceCLM (A := A) (Z := Z) Q N y ω).1 = y.1 :=
  (independentReferenceCLM_coe Q N y).mono fun _ h ↦ congrArg Prod.fst h

variable [BorelSpace Z] [SecondCountableTopology Z]
/-- The fixed-time reference cloud is truly iid, by the actual product seed
construction and the proved coordinate identity. -/
theorem independentReference_cloud_law (y : A × Lp Z 2 Q) :
    (IndependentCopies.seeds (J := Fin N) Q).map
      (fun ω ↦ (independentReferenceCLM (A := A) (Z := Z) Q N y ω).2) =
        Measure.pi (fun _ : Fin N ↦ Q.map y.2) := by
  rw [Measure.map_congr ((independentReferenceCLM_coe Q N y).mono
    (fun _ h ↦ congrArg Prod.snd h))]
  exact IndependentCopies.cloud_law Q y.2 (Lp.stronglyMeasurable y.2).measurable

end IndependentReference

section Forward
variable {Ω A G Z X I : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype I]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (N : ℕ)

/-- For constant diffusion, the full source quadratic generator is exactly
twice the displayed drift pairing. Synchronous columns cancel pointwise. -/
theorem particleCopyGenerator_additive (L : LipschitzDynamics A Z G)
    (M : Model A G Z X I) (H : AdditiveModelCompatibility L M)
    (D : TwistedGeometry A Z) (ν : Measure Z) (t : ℝ) (p : ParticlePair N A Z) :
    particleCopyGenerator M N ν t (fun q ↦ particleQuadraticBilinear D N q q) p =
      2 * particleQuadraticBilinear D N p (particleCopyDrift M N ν t p) := by
  rw [particleCopyGenerator, (quadratic_hasFDerivAt _ p).fderiv]
  simp only [add_apply, ContinuousLinearMap.flip_apply, quadratic_second_fderiv,
    particleQuadraticBilinear_symmetric]
  have hz (ij : Fin N × I) : particleQuadraticBilinear D N
      (particleCopyDiffusion M N p ij) (particleCopyDiffusion M N p ij) = 0 := by
    rw [particleCopyDiffusion_quadratic, H.diffusion_constant p.1.1 p.2.1
      (p.1.2 ij.1) (p.2.2 ij.1) ij.2, sub_self]
    simp [TwistedGeometry.samplerSq]
  simp only [hz, add_zero, Finset.sum_const_zero, mul_zero]
  ring

/-- Shared-input integral equations imply the complete source particle/copy
quadratic weak equation. The drift identification is pointwise and is
discharged below for the actual empirical field and independent-copy lift. -/
theorem particle_integral_pair_weak
    (L : LipschitzDynamics A Z G) (M : Model A G Z X I)
    (H : AdditiveModelCompatibility L M) (D : TwistedGeometry A Z)
    (ν : ℝ → Measure Z)
    (Y W FY FW B : ℝ → Lp (A × (Fin N → Z)) 2 Q)
    (hFY : Continuous FY) (hFW : Continuous FW)
    (hY : ∀ t, 0 ≤ t → Y t - Y 0 = (∫ r in 0..t, FY r) + B t)
    (hW : ∀ t, 0 ≤ t → W t - W 0 = (∫ r in 0..t, FW r) + B t)
    (hsource : ∀ t, 0 ≤ t → Continuous (particleCopyDrift M N (ν t) t))
    (hfield : ∀ t, 0 ≤ t → ∀ᵐ ω ∂Q,
      (FY t ω, FW t ω) = particleCopyDrift M N (ν t) t (Y t ω, W t ω)) :
    IsParticleCopyWeakSolution M N ν {fun p ↦ particleQuadraticBilinear D N p p}
      (fun t ↦ particlePairLaw Q N (Y t) (W t)) := by
  have hmeas (t : ℝ) : AEMeasurable (fun ω ↦ (Y t ω, W t ω)) Q :=
    (Lp.aestronglyMeasurable (Y t)).aemeasurable.prodMk (Lp.aestronglyMeasurable (W t)).aemeasurable
  have htest (t : ℝ) : Integrable (fun p ↦ particleQuadraticBilinear D N p p)
      (particlePairLaw Q N (Y t) (W t)) := by
    apply (integrable_map_measure
      (by fun_prop : Continuous (fun p : ParticlePair N A Z ↦ particleQuadraticBilinear D N p p)).aestronglyMeasurable
      (hmeas t)).mpr
    exact particlePairWork_integrable Q N D (Y t) (W t) (Y t) (W t)
  have hgen (t : ℝ) (ht : 0 ≤ t) :
      (fun ω ↦ particleCopyGenerator M N (ν t) t
        (fun p ↦ particleQuadraticBilinear D N p p) (Y t ω, W t ω)) =ᵐ[Q]
      (fun ω ↦ 2 * particleQuadraticBilinear D N (Y t ω, W t ω) (FY t ω, FW t ω)) := by
    filter_upwards [hfield t ht] with ω hω
    rw [particleCopyGenerator_additive N L M H, ← hω]
  have hcgen (t : ℝ) (ht : 0 ≤ t) : AEStronglyMeasurable
      (particleCopyGenerator M N (ν t) t (fun p ↦ particleQuadraticBilinear D N p p))
      (particlePairLaw Q N (Y t) (W t)) := by
    change AEStronglyMeasurable (fun p ↦ particleCopyGenerator M N (ν t) t
      (fun p ↦ particleQuadraticBilinear D N p p) p) _
    simp_rw [particleCopyGenerator_additive N L M H]
    exact (continuous_const.mul ((particleQuadraticBilinear D N).continuous.clm_apply (hsource t ht))).aestronglyMeasurable
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t _
    exact (Measure.isProbabilityMeasure_map_iff (hmeas t)).mpr inferInstance
  · intro φ hφ t _
    have he : φ = fun p ↦ particleQuadraticBilinear D N p p := Set.mem_singleton_iff.mp hφ
    subst φ
    exact htest t
  · intro φ hφ t ht
    have he : φ = fun p ↦ particleQuadraticBilinear D N p p := Set.mem_singleton_iff.mp hφ
    subst φ
    apply (integrable_map_measure (hcgen t ht) (hmeas t)).mpr
    exact ((particlePairWork_integrable Q N D (Y t) (W t) (FY t) (FW t)).const_mul 2).congr (hgen t ht).symm
  · intro φ hφ t ht
    have he : φ = fun p ↦ particleQuadraticBilinear D N p p := Set.mem_singleton_iff.mp hφ
    subst φ
    let f := fun r ↦ FY r - FW r
    have hfc : Continuous f := hFY.sub hFW
    have heq (r : ℝ) (hr : 0 ≤ r) : Y r - W r = Y 0 - W 0 + ∫ u in 0..r, f u := by
      rw [intervalIntegral.integral_sub (hFY.intervalIntegrable 0 r) (hFW.intervalIntegrable 0 r)]
      have hy := hY r hr
      have hw := hW r hr
      rw [sub_eq_iff_eq_add] at hy hw
      rw [hy, hw]
      module
    have hd := intervalIntegral.integral_hasDerivAt_right (a := 0) (b := t)
      (hfc.intervalIntegrable 0 t) (hfc.stronglyMeasurableAtFilter volume (𝓝 t)) hfc.continuousAt
    have hdiff := (hd.const_add (Y 0 - W 0)).hasDerivWithinAt.congr heq (heq t ht)
    have hquad := (quadratic_hasFDerivAt (particleLpBilinear Q N D) (Y t - W t)).comp_hasDerivWithinAt t hdiff
    have hv : (∫ p, particleCopyGenerator M N (ν t) t
        (fun p ↦ particleQuadraticBilinear D N p p) p ∂particlePairLaw Q N (Y t) (W t)) =
        2 * particleLpBilinear Q N D (Y t - W t) (FY t - FW t) := by
      rw [particlePairLaw, integral_map (hmeas t) (hcgen t ht), integral_congr_ae (hgen t ht),
        integral_const_mul, particlePairWork_integral]
    rw [hv]
    have heall (r : ℝ) := particlePairLaw_energy_integral Q N D (Y r) (W r)
    convert hquad.congr (fun r _ ↦ heall r) (heall t) using 1 <;>
      simp only [add_apply, ContinuousLinearMap.flip_apply, particleLpBilinear_symmetric, two_mul, f] <;> rfl

end Forward
section ActualFields
variable {Ω A G Z X I : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype I]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (N : ℕ)
  (L : LipschitzDynamics A Z G) (M : Model A G Z X I)
  (H : AdditiveModelCompatibility L M)
include H

/-- Primitive implementation identities give the actual source empirical
particle field, including its shared random optimiser. -/
theorem additive_particle_field (t : ℝ) (ht : 0 ≤ t) (p : A × (Fin N → Z)) :
    (M.particleField N t p.1 p.2, fun i ↦ M.drift (M.parameter p.1) (p.2 i)) =
      L.particleField N p := by
  simp only [Model.particleField, Model.particleGradient, H.observation, H.response t ht,
    H.sampler, LipschitzDynamics.particleField, LipschitzDynamics.averageObservation]

theorem particleCopyDrift_actual (U : Lp Z 2 Q) (t : ℝ) (ht : 0 ≤ t)
    (p : ParticlePair N A Z) :
    particleCopyDrift M N (Q.map U) t p =
      (L.particleField N p.1,
        ((L.field Q (p.2.1, U)).1, (L.particleField N p.2).2)) := by
  rw [particleCopyDrift]
  rw [additive_particle_field N L M H t ht]
  simp only [Model.optimizerField, model_meanGradient_eq_expectedObservation Q L M H,
    H.response t ht, H.sampler, LipschitzDynamics.field, LipschitzDynamics.particleField]

/-- Continuity of the true source paired drift is derived from primitive
Lipschitz maps and an actual L² population law. -/
theorem particleCopyDrift_actual_continuous (hN : 0 < N) (U : Lp Z 2 Q)
    (t : ℝ) (ht : 0 ≤ t) : Continuous (particleCopyDrift M N (Q.map U) t) := by
  have he : particleCopyDrift M N (Q.map U) t = fun p : ParticlePair N A Z ↦
      (L.particleField N p.1,
        ((L.field Q (p.2.1, U)).1, (L.particleField N p.2).2)) :=
    funext fun p ↦ particleCopyDrift_actual Q N L M H U t ht p
  rw [he]
  have hp := (L.particleField_lipschitz N hN).continuous
  have hm := (L.field_lipschitz Q).continuous
  exact (hp.comp continuous_fst).prodMk
    ((continuous_fst.comp (hm.comp (continuous_snd.fst.prodMk continuous_const))).prodMk
      (continuous_snd.comp (hp.comp continuous_snd)))

/-- The lifted full empirical drift and the actual independent reference
drift match the source paired field almost everywhere. -/
theorem independent_particle_copy_field_coe (hN : 0 < N)
    (y : A × Lp Z 2 Q)
    (U : Lp (A × (Fin N → Z)) 2 (IndependentCopies.seeds (J := Fin N) Q))
    (t : ℝ) (ht : 0 ≤ t) :
    ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q,
      ((ULA.lpDrift (IndependentCopies.seeds Q) (L.particleField N)
        (L.particleField_lipschitz N hN) U) ω,
       (independentReferenceCLM (A := A) (Z := Z) Q N (L.field Q y)) ω) =
        particleCopyDrift M N (Q.map y.2) t
          (U ω, (independentReferenceCLM (A := A) (Z := Z) Q N y) ω) := by
  have hs : ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q, ∀ i : Fin N,
      (L.field Q y).2 (ω i) = L.sampler y.1 (y.2 (ω i)) := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : Fin N ↦ Q) i).quasiMeasurePreserving.ae_eq_comp
      (liftMap_coe Q (L.sampler y.1) (L.sampler_state y.1) y.2)
  filter_upwards [ULA.lpDrift_coe (IndependentCopies.seeds Q) (L.particleField N)
    (L.particleField_lipschitz N hN) U,
    independentReferenceCLM_coe Q N y,
    independentReferenceCLM_coe Q N (L.field Q y), hs] with ω hu hw hf hs
  rw [hu, hw, hf, particleCopyDrift_actual Q N L M H y.2 t ht]
  congr 1
  congr 1
  exact funext hs

/-- The actual complete independent-copy reference integral equation is a
continuous linear image of the constructed one-copy mean-field equation. -/
theorem independentReference_integral
    {Ybar : ℝ → A × Lp Z 2 Q} {B : ℝ → Lp Z 2 Q}
    (HY : IsGlobalAdditiveIntegralSolution Q L Ybar B) (t : ℝ) (ht : 0 ≤ t) :
    independentReferenceCLM (A := A) (Z := Z) Q N (Ybar t) -
      independentReferenceCLM (A := A) (Z := Z) Q N (Ybar 0) =
      (∫ r in 0..t, independentReferenceCLM (A := A) (Z := Z) Q N (L.field Q (Ybar r))) +
        independentReferenceCLM (A := A) (Z := Z) Q N (0, B t) := by
  let C := independentReferenceCLM (A := A) (Z := Z) Q N
  have hi : IntervalIntegrable (fun r ↦ L.field Q (Ybar r)) volume 0 t :=
    ((L.field_lipschitz Q).continuous.comp HY.continuous).intervalIntegrable 0 t
  have he := congrArg C (HY.equation t ht)
  rw [map_sub, map_add, ← C.intervalIntegral_comp_comm hi] at he
  exact he

/-- The common reference input has exactly zero optimiser coordinate. -/
theorem independentReference_input_optimizer_zero (B : Lp Z 2 Q) :
    ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q,
      (independentReferenceCLM (A := A) (Z := Z) Q N (0, B) ω).1 = 0 :=
  independentReference_optimizer_coe Q N (0, B)

/-- Primitive globally Lipschitz maps and an actual one-copy integral
trajectory construct the interacting trajectory, its synchronous independent
copies, and their true source quadratic forward equation. No particle weak
solution, output-law compatibility or energy derivative is a premise. -/
theorem exists_additive_particle_copy_weak (hN : 0 < N)
    (D : TwistedGeometry A Z)
    (Ybar : ℝ → A × Lp Z 2 Q) (B : ℝ → Lp Z 2 Q)
    (HY : IsGlobalAdditiveIntegralSolution Q L Ybar B)
    (hB : Continuous B) (hB0 : B 0 = 0) :
    ∃ Y : ℝ → Lp (A × (Fin N → Z)) 2 (IndependentCopies.seeds (J := Fin N) Q),
      Continuous Y ∧ Y 0 = independentReferenceCLM (A := A) (Z := Z) Q N (Ybar 0) ∧
      (∀ t, 0 ≤ t → Y t - Y 0 =
        (∫ r in 0..t, ULA.lpDrift (IndependentCopies.seeds Q) (L.particleField N)
          (L.particleField_lipschitz N hN) (Y r)) +
        independentReferenceCLM (A := A) (Z := Z) Q N (0, B t)) ∧
      IsParticleCopyWeakSolution M N (fun t ↦ Q.map (Ybar t).2)
        {fun p ↦ particleQuadraticBilinear D N p p}
        (fun t ↦ particlePairLaw (IndependentCopies.seeds Q) N (Y t)
          (independentReferenceCLM (A := A) (Z := Z) Q N (Ybar t))) := by
  let QN := IndependentCopies.seeds (J := Fin N) Q
  let C := independentReferenceCLM (A := A) (Z := Z) Q N
  let f := ULA.lpDrift QN (L.particleField N) (L.particleField_lipschitz N hN)
  have hf : LipschitzWith L.fieldLip f := ULA.lpDrift_lipschitz QN _ _
  have hinput : Continuous (fun t ↦ C (0, B t)) :=
    C.continuous.comp (continuous_const.prodMk hB)
  have hinput0 : C (0, B 0) = 0 := by rw [hB0]; exact C.map_zero
  obtain ⟨Y, hcont, hzero, heq⟩ := exists_global_integral_solution f L.fieldLip hf
    (C (Ybar 0)) (fun t ↦ C (0, B t)) hinput hinput0
  have hYe (t : ℝ) (ht : 0 ≤ t) : Y t - Y 0 =
      (∫ r in 0..t, f (Y r)) + C (0, B t) := by rw [hzero]; exact heq t ht
  refine ⟨Y, hcont, hzero, hYe, ?_⟩
  apply particle_integral_pair_weak QN N L M H D (fun t ↦ Q.map (Ybar t).2)
    Y (fun t ↦ C (Ybar t)) (fun t ↦ f (Y t))
    (fun t ↦ C (L.field Q (Ybar t))) (fun t ↦ C (0, B t))
  · exact hf.continuous.comp hcont
  · exact C.continuous.comp ((L.field_lipschitz Q).continuous.comp HY.continuous)
  · exact hYe
  · exact independentReference_integral Q N L M H HY
  · exact fun t ht ↦ particleCopyDrift_actual_continuous Q N L M H hN (Ybar t).2 t ht
  · exact fun t ht ↦ independent_particle_copy_field_coe Q N L M H hN (Ybar t) (Y t) t ht

end ActualFields


section ActualApproximation
variable {Ω A G Z X I : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype I]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (N : ℕ)
  (L : LipschitzDynamics A Z G) (M : Model A G Z X I)
  (H : AdditiveModelCompatibility L M)
include H

/-- All structural hypotheses of the source finite-particle parameter bound
are derived for the constructed additive particle dynamics. The uniform
observation variance is the remaining explicit statistical assumption. -/
theorem exists_additive_particle_approximation (hN : 0 < N)
    (D : TwistedGeometry A Z)
    (Ybar : ℝ → A × Lp Z 2 Q) (B : ℝ → Lp Z 2 Q)
    (HY : IsGlobalAdditiveIntegralSolution Q L Ybar B)
    (hB : Continuous B) (hB0 : B 0 = 0) (V : ℝ)
    (hVariance : ∀ r, 0 ≤ r →
      (∫ z, ‖M.observation (M.parameter (Ybar r).1) (M.position z) -
        M.meanGradient (Q.map (Ybar r).2) (Ybar r).1‖ ^ 2 ∂Q.map (Ybar r).2) ≤ V) :
    ∃ Y : ℝ → Lp (A × (Fin N → Z)) 2 (IndependentCopies.seeds (J := Fin N) Q),
      Continuous Y ∧ Y 0 = independentReferenceCLM (A := A) (Z := Z) Q N (Ybar 0) ∧
      (∀ t, 0 ≤ t → Y t - Y 0 =
        (∫ r in 0..t, ULA.lpDrift (IndependentCopies.seeds Q) (L.particleField N)
          (L.particleField_lipschitz N hN) (Y r)) +
        independentReferenceCLM (A := A) (Z := Z) Q N (0, B t)) ∧
      ∃ P : ParticleParameterApproximation M D N (fun t ↦ Q.map (Ybar t).2)
          (fun t ↦ (Ybar t).1) L.responseLip V,
        P.jointLaw = fun t ↦ particlePairLaw (IndependentCopies.seeds Q) N (Y t)
          (independentReferenceCLM (A := A) (Z := Z) Q N (Ybar t)) := by
  let QN := IndependentCopies.seeds (J := Fin N) Q
  let C := independentReferenceCLM (A := A) (Z := Z) Q N
  obtain ⟨Y, hc, hi, he, hw⟩ := exists_additive_particle_copy_weak Q N L M H hN D Ybar B HY hB hB0
  let Γ := fun t ↦ particlePairLaw QN N (Y t) (C (Ybar t))
  have hCloud (r : ℝ) : (Γ r).map (fun p ↦ p.2.2) =
      Measure.pi (fun _ : Fin N ↦ Q.map (Ybar r).2) := by
    rw [particlePairLaw_reference_cloud]
    exact independentReference_cloud_law Q N (Ybar r)
  have hbar (r : ℝ) : ∀ᵐ p ∂Γ r, p.2.1 = (Ybar r).1 :=
    particlePairLaw_reference_optimizer QN N (Y r) (C (Ybar r)) (Ybar r).1
      (independentReference_optimizer_coe Q N (Ybar r))
  have hF (r : ℝ) : MemLp
      (fun z ↦ M.observation (M.parameter (Ybar r).1) (M.position z)) 2 (Q.map (Ybar r).2) := by
    simp_rw [H.observation]
    apply (memLp_map_measure_iff (L.observation_state (Ybar r).1).continuous.aestronglyMeasurable
      (Lp.aestronglyMeasurable (Ybar r).2).aemeasurable).mpr
    exact ProximalLangevin.memLp_lipschitz_observable Q (L.observation_state (Ybar r).1)
      (Lp.memLp (Ybar r).2)
  have hΨ (r : ℝ) (hr : 0 ≤ r) (s : A) (g g' : G) :
      ‖M.optimizer r s g - M.optimizer r s g'‖ ≤ (L.responseLip : ℝ) * ‖g - g'‖ := by
    rw [H.response r hr, H.response r hr]
    simpa only [Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] using
      L.response_lipschitz.norm_sub_le (s, g) (s, g')
  have hR (r : ℝ) (hr : 0 ≤ r) :
      AEStronglyMeasurable (particlePopulationResidual M D N (Q.map (Ybar r).2) r) (Γ r) := by
    letI : IsProbabilityMeasure (Q.map (Ybar r).2) :=
      (Measure.isProbabilityMeasure_map_iff (Lp.aestronglyMeasurable (Ybar r).2).aemeasurable).mpr inferInstance
    exact particlePopulationResidual_aestronglyMeasurable M D N (Q.map (Ybar r).2)
      (Ybar r).1 (hF r) (Γ r) (hCloud r) (hbar r) r L.responseLip (hΨ r hr (Ybar r).1)
  refine ⟨Y, hc, hi, he, ?_⟩
  refine ⟨{
    jointLaw := Γ
    tests := {fun p ↦ particleQuadraticBilinear D N p p}
    solution := hw
    quadratic_test := Set.mem_singleton _
    observation_second_moment := fun r _ ↦ hF r
    reference_cloud := fun r _ ↦ hCloud r
    reference_optimizer := fun r _ ↦ hbar r
    response := hΨ
    observation_variance := hVariance
    residual_measurable := hR
    zero_initial_error := particlePairLaw_zero_energy QN N D Y (fun t ↦ C (Ybar t)) hi
  }, rfl⟩

end ActualApproximation
end PBGSO
