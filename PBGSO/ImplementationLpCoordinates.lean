import PBGSO.ImplementationCoordinates
import PBGSO.ParticleAdditiveWeakRealization

/-! # Actual L² implementation coordinates
Continuous-linear state coordinates split into genuine same-space L²
optimizer and cloud variables. Pointwise force and projection identities
transport the actual integral dynamics to their implementation coordinates;
no equality of output laws is assumed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped NNReal ENNReal
namespace PBGSO.ImplementationDynamics
open Methods

section Split
variable {Ω A C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  (Q : Measure Ω)

/-- Split a full L² kinetic phase into actual optimiser/cloud coordinates. -/
def phaseSplitLp : Lp ((A × C) × (A × C)) 2 Q →L[ℝ]
    ((Lp A 2 Q × Lp C 2 Q) × (Lp A 2 Q × Lp C 2 Q)) :=
  ((((ContinuousLinearMap.fst ℝ A C).comp (ContinuousLinearMap.fst ℝ (A × C) (A × C))).compLpL 2 Q).prod
    (((ContinuousLinearMap.snd ℝ A C).comp (ContinuousLinearMap.fst ℝ (A × C) (A × C))).compLpL 2 Q)).prod
  ((((ContinuousLinearMap.fst ℝ A C).comp (ContinuousLinearMap.snd ℝ (A × C) (A × C))).compLpL 2 Q).prod
    (((ContinuousLinearMap.snd ℝ A C).comp (ContinuousLinearMap.snd ℝ (A × C) (A × C))).compLpL 2 Q))

theorem phaseSplitLp_coe (U : Lp ((A × C) × (A × C)) 2 Q) :
    ∀ᵐ ω ∂Q, phaseValue Q (phaseSplitLp (A := A) (C := C) Q U) ω = U ω := by
  filter_upwards [((ContinuousLinearMap.fst ℝ A C).comp
      (ContinuousLinearMap.fst ℝ (A × C) (A × C))).coeFn_compLpL U,
    ((ContinuousLinearMap.snd ℝ A C).comp
      (ContinuousLinearMap.fst ℝ (A × C) (A × C))).coeFn_compLpL U,
    ((ContinuousLinearMap.fst ℝ A C).comp
      (ContinuousLinearMap.snd ℝ (A × C) (A × C))).coeFn_compLpL U,
    ((ContinuousLinearMap.snd ℝ A C).comp
      (ContinuousLinearMap.snd ℝ (A × C) (A × C))).coeFn_compLpL U] with ω h1 h2 h3 h4
  exact Prod.ext (Prod.ext h1 h2) (Prod.ext h3 h4)

/-- Split a full L² higher-order state into actual optimiser,x,u,v variables. -/
def holSplitLp : Lp (HOLState A C) 2 Q →L[ℝ] HOLState (Lp A 2 Q) (Lp C 2 Q) :=
  ((ContinuousLinearMap.fst ℝ A (C × C × C)).compLpL 2 Q).prod
    ((((ContinuousLinearMap.fst ℝ C (C × C)).comp (ContinuousLinearMap.snd ℝ A (C × C × C))).compLpL 2 Q).prod
      ((((ContinuousLinearMap.fst ℝ C C).comp (ContinuousLinearMap.snd ℝ C (C × C))).comp
        (ContinuousLinearMap.snd ℝ A (C × C × C))).compLpL 2 Q |>.prod
       ((((ContinuousLinearMap.snd ℝ C C).comp (ContinuousLinearMap.snd ℝ C (C × C))).comp
        (ContinuousLinearMap.snd ℝ A (C × C × C))).compLpL 2 Q)))

theorem holSplitLp_coe (U : Lp (HOLState A C) 2 Q) :
    ∀ᵐ ω ∂Q, holValue Q (holSplitLp (A := A) (C := C) Q U) ω = U ω := by
  filter_upwards [(ContinuousLinearMap.fst ℝ A (C × C × C)).coeFn_compLpL U,
    ((ContinuousLinearMap.fst ℝ C (C × C)).comp
      (ContinuousLinearMap.snd ℝ A (C × C × C))).coeFn_compLpL U,
    (((ContinuousLinearMap.fst ℝ C C).comp (ContinuousLinearMap.snd ℝ C (C × C))).comp
      (ContinuousLinearMap.snd ℝ A (C × C × C))).coeFn_compLpL U,
    (((ContinuousLinearMap.snd ℝ C C).comp (ContinuousLinearMap.snd ℝ C (C × C))).comp
      (ContinuousLinearMap.snd ℝ A (C × C × C))).coeFn_compLpL U] with ω h1 h2 h3 h4
  exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))

/-- Equality of the actual four phase coordinates implies L² phase equality. -/
theorem phase_eq_of_ae
    (z w : ((Lp A 2 Q × Lp C 2 Q) × (Lp A 2 Q × Lp C 2 Q)))
    (h : ∀ᵐ ω ∂Q, phaseValue Q z ω = phaseValue Q w ω) : z = w := by
  apply Prod.ext
  · apply Prod.ext
    · exact Lp.ext (h.mono fun _ hω ↦ congrArg (fun q ↦ q.1.1) hω)
    · exact Lp.ext (h.mono fun _ hω ↦ congrArg (fun q ↦ q.1.2) hω)
  · apply Prod.ext
    · exact Lp.ext (h.mono fun _ hω ↦ congrArg (fun q ↦ q.2.1) hω)
    · exact Lp.ext (h.mono fun _ hω ↦ congrArg (fun q ↦ q.2.2) hω)

/-- Equality of actual optimiser,x,u,v variables implies L² HOL equality. -/
theorem hol_eq_of_ae (z w : HOLState (Lp A 2 Q) (Lp C 2 Q))
    (h : ∀ᵐ ω ∂Q, holValue Q z ω = holValue Q w ω) : z = w := by
  apply Prod.ext
  · exact Lp.ext (h.mono fun _ hω ↦ congrArg (fun q ↦ q.1) hω)
  · apply Prod.ext
    · exact Lp.ext (h.mono fun _ hω ↦ congrArg (fun q ↦ q.2.1) hω)
    · apply Prod.ext
      · exact Lp.ext (h.mono fun _ hω ↦ congrArg (fun q ↦ q.2.2.1) hω)
      · exact Lp.ext (h.mono fun _ hω ↦ congrArg (fun q ↦ q.2.2.2) hω)

end Split
section Encoded
variable {Ω A X C : Type*} {N : ℕ} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  (Q : Measure Ω) (D : ParticleForceData A X C N)

/-- Include the implementation's explicit cloud encoding in the actual
invertible momentum state coordinates. -/
def momentumEncodedStateEquiv : ((A × C) × (A × C)) ≃L[ℝ]
    (HypocoercivePhase A × (Fin N → HypocoercivePhase X)) :=
  (((ContinuousLinearEquiv.refl ℝ A).prodCongr D.cloud).prodCongr
    ((ContinuousLinearEquiv.refl ℝ A).prodCongr D.cloud)).trans (momentumStateEquiv N)

@[simp] theorem momentumEncodedStateEquiv_symm_apply
    (z : HypocoercivePhase A × (Fin N → HypocoercivePhase X)) :
    (momentumEncodedStateEquiv D).symm z =
      ((z.1.snd, D.cloud.symm (fun i ↦ (z.2 i).snd)),
       (z.1.fst, D.cloud.symm (fun i ↦ (z.2 i).fst))) := rfl

/-- Actual encoded HOL state equivalence, with complete sampler auxiliaries. -/
def higherOrderEncodedStateEquiv : HOLState A C ≃L[ℝ]
    (A × (Fin N → HigherOrderSampler X)) :=
  ((ContinuousLinearEquiv.refl ℝ A).prodCongr
    (D.cloud.prodCongr (D.cloud.prodCongr D.cloud))).trans (higherOrderStateEquiv N)

@[simp] theorem higherOrderEncodedStateEquiv_symm_apply
    (z : A × (Fin N → HigherOrderSampler X)) :
    (higherOrderEncodedStateEquiv D).symm z =
      (z.1, D.cloud.symm (fun i ↦ (z.2 i).fst),
        D.cloud.symm (fun i ↦ (z.2 i).snd.fst), D.cloud.symm (fun i ↦ (z.2 i).snd.snd)) := rfl

/-- Actual continuous-linear kinetic implementation coordinates of a full
random optimiser/particle state. -/
def momentumUnpackLp : Lp (HypocoercivePhase A × (Fin N → HypocoercivePhase X)) 2 Q →L[ℝ]
    ((Lp A 2 Q × Lp C 2 Q) × (Lp A 2 Q × Lp C 2 Q)) :=
  (phaseSplitLp (A := A) (C := C) Q).comp
    ((momentumEncodedStateEquiv D).symm.toContinuousLinearMap.compLpL 2 Q)

theorem momentumUnpackLp_coe
    (U : Lp (HypocoercivePhase A × (Fin N → HypocoercivePhase X)) 2 Q) :
    ∀ᵐ ω ∂Q, phaseValue Q (momentumUnpackLp Q D U) ω =
      (momentumEncodedStateEquiv D).symm (U ω) := by
  filter_upwards [phaseSplitLp_coe Q ((momentumEncodedStateEquiv D).symm.toContinuousLinearMap.compLpL 2 Q U),
    (momentumEncodedStateEquiv D).symm.toContinuousLinearMap.coeFn_compLpL U] with ω h1 h2
  exact h1.trans h2

/-- Actual continuous-linear HOL implementation coordinates of a full
random optimiser/particle state. -/
def higherOrderUnpackLp : Lp (A × (Fin N → HigherOrderSampler X)) 2 Q →L[ℝ]
    HOLState (Lp A 2 Q) (Lp C 2 Q) :=
  (holSplitLp (A := A) (C := C) Q).comp
    ((higherOrderEncodedStateEquiv D).symm.toContinuousLinearMap.compLpL 2 Q)

theorem higherOrderUnpackLp_coe
    (U : Lp (A × (Fin N → HigherOrderSampler X)) 2 Q) :
    ∀ᵐ ω ∂Q, holValue Q (higherOrderUnpackLp Q D U) ω =
      (higherOrderEncodedStateEquiv D).symm (U ω) := by
  filter_upwards [holSplitLp_coe Q ((higherOrderEncodedStateEquiv D).symm.toContinuousLinearMap.compLpL 2 Q U),
    (higherOrderEncodedStateEquiv D).symm.toContinuousLinearMap.coeFn_compLpL U] with ω h1 h2
  exact h1.trans h2

/-- The encoded kinetic raw drift is exactly the actual empirical model
field, obtained by inverse continuous-linear state coordinates. -/
theorem momentumEncoded_drift (γ : ℝ)
    (z : HypocoercivePhase A × (Fin N → HypocoercivePhase X)) :
    (momentumEncodedStateEquiv D).symm
      ((momentumDynamics D.F D.G D.parameterLip D.samplerLip
        D.parameter_bound D.sampler_bound γ).particleField N z) =
      (-coupledForce (fun a x ↦ D.meanForce (a, x)) (fun a x ↦ D.samplerForce (a, x))
        ((momentumEncodedStateEquiv D).symm z).2 -
          γ • ((momentumEncodedStateEquiv D).symm z).1,
        ((momentumEncodedStateEquiv D).symm z).1) := by
  apply Prod.ext
  · apply Prod.ext
    · simp [momentumEncodedStateEquiv_symm_apply, momentumDynamics,
        LipschitzDynamics.particleField, LipschitzDynamics.averageObservation,
        coupledForce, ParticleForceData.meanForce, particleMeanForce]
    · apply D.cloud.injective
      simp only [momentumEncodedStateEquiv_symm_apply, momentumDynamics,
        LipschitzDynamics.particleField, coupledForce, ParticleForceData.samplerForce,
        particleSamplerForce, Prod.snd_sub, Prod.snd_neg, Prod.snd_smul,
        map_sub, map_neg, map_smul, ContinuousLinearEquiv.apply_symm_apply]
      funext i
      simp [particleSamplerForce]
  · rfl

/-- The encoded raw HOL drift is the actual complete empirical model field. -/
theorem higherOrderEncoded_drift (α γ : ℝ)
    (z : A × (Fin N → HigherOrderSampler X)) :
    (higherOrderEncodedStateEquiv D).symm
      ((higherOrderDynamics D.F D.G D.parameterLip D.samplerLip
        D.parameter_bound D.sampler_bound α γ).particleField N z) =
      holDrift (fun a x ↦ D.meanForce (a, x)) (fun a x ↦ D.samplerForce (a, x)) α γ
        ((higherOrderEncodedStateEquiv D).symm z) := by
  apply Prod.ext
  · simp [higherOrderEncodedStateEquiv_symm_apply, higherOrderDynamics,
      LipschitzDynamics.particleField, LipschitzDynamics.averageObservation,
      holDrift, ParticleForceData.meanForce, particleMeanForce]
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply D.cloud.injective
        simp only [higherOrderEncodedStateEquiv_symm_apply, higherOrderDynamics,
          LipschitzDynamics.particleField, higherOrderSamplerField, holDrift,
          ParticleForceData.samplerForce, particleSamplerForce, map_add, map_neg,
          map_smul, ContinuousLinearEquiv.apply_symm_apply]
        funext i
        rfl
      · apply D.cloud.injective
        simp only [higherOrderEncodedStateEquiv_symm_apply, higherOrderDynamics,
          LipschitzDynamics.particleField, higherOrderSamplerField, holDrift,
          map_sub, map_neg, map_smul, ContinuousLinearEquiv.apply_symm_apply]
        funext i
        rfl


section LpDrift
variable [IsProbabilityMeasure Q]

private theorem jointValue_neg (z : Lp A 2 Q × Lp C 2 Q) :
    ∀ᵐ ω ∂Q, jointValue Q (-z) ω = -jointValue Q z ω := by
  filter_upwards [Lp.coeFn_neg z.1, Lp.coeFn_neg z.2] with ω h1 h2
  exact Prod.ext h1 h2

/-- Actual shared L² kinetic drift has its exact raw force meaning. -/
theorem momentumLpDrift_coe (γ : ℝ)
    (z : ((Lp A 2 Q × Lp C 2 Q) × (Lp A 2 Q × Lp C 2 Q))) :
    ∀ᵐ ω ∂Q,
      phaseValue Q (-coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) z.2 - γ • z.1, z.1) ω =
      (-coupledForce (fun a x ↦ D.meanForce (a, x)) (fun a x ↦ D.samplerForce (a, x))
        (phaseValue Q z ω).2 - γ • (phaseValue Q z ω).1, (phaseValue Q z ω).1) := by
  filter_upwards [jointValue_sub Q (-(coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) z.2))
      (γ • z.1), jointValue_neg Q (coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) z.2),
    D.coupledForceLp_coe Q z.2, jointValue_smul Q γ z.1] with ω hs hn hf hγ
  change (jointValue Q (-coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) z.2 - γ • z.1) ω,
    jointValue Q z.1 ω) = _
  rw [hs, hn, hf, hγ]
  rfl

/-- The complete actual L² HOL drift equals the raw empirical implementation
at almost every sample; all auxiliary arithmetic is verified. -/
theorem higherOrderLpDrift_coe (α γ : ℝ) (z : HOLState (Lp A 2 Q) (Lp C 2 Q)) :
    ∀ᵐ ω ∂Q,
      holValue Q (holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ z) ω =
      holDrift (fun a x ↦ D.meanForce (a, x)) (fun a x ↦ D.samplerForce (a, x)) α γ
        (holValue Q z ω) := by
  filter_upwards [D.meanForceLp_coe Q z.1 z.2.1, D.samplerForceLp_coe_cloud Q z.1 z.2.1,
    Lp.coeFn_neg (D.meanForceLp Q z.1 z.2.1),
    Lp.coeFn_add (-(D.samplerForceLp Q z.1 z.2.1)) (γ • z.2.2.2),
    Lp.coeFn_neg (D.samplerForceLp Q z.1 z.2.1), Lp.coeFn_smul γ z.2.2.2,
    Lp.coeFn_sub ((-γ) • z.2.2.1) (α • z.2.2.2),
    Lp.coeFn_smul (-γ) z.2.2.1, Lp.coeFn_smul α z.2.2.2] with ω hf hg hn ha hng hγ hs hγu hαv
  change ( (-(D.meanForceLp Q z.1 z.2.1)) ω, z.2.2.1 ω,
    (-(D.samplerForceLp Q z.1 z.2.1) + γ • z.2.2.2) ω,
    ((-γ) • z.2.2.1 - α • z.2.2.2) ω) = _
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply] at hn ha hng hγ hs hγu hαv
  rw [hn, ha, hng, hγ, hs, hγu, hαv, hf, hg]
  rfl

/-- Primitive regularity data for the actual encoded kinetic forces. -/
abbrev momentumForceDynamics (γ : ℝ) := momentumDynamics D.F D.G D.parameterLip D.samplerLip
  D.parameter_bound D.sampler_bound γ

/-- Primitive regularity data for the actual encoded higher-order forces. -/
abbrev higherOrderForceDynamics (α γ : ℝ) := higherOrderDynamics D.F D.G D.parameterLip D.samplerLip
  D.parameter_bound D.sampler_bound α γ

/-- The actual L² empirical model field becomes precisely the kinetic
implementation drift under the proved coordinate map. -/
theorem momentumUnpackLp_drift (γ : ℝ)
    (U : Lp (HypocoercivePhase A × (Fin N → HypocoercivePhase X)) 2 Q) :
    momentumUnpackLp Q D (ULA.lpDrift Q ((momentumForceDynamics D γ).particleField N)
      ((momentumForceDynamics D γ).particleField_lipschitz N D.nonempty) U) =
      (-coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) (momentumUnpackLp Q D U).2 -
        γ • (momentumUnpackLp Q D U).1, (momentumUnpackLp Q D U).1) := by
  apply phase_eq_of_ae
  filter_upwards [momentumUnpackLp_coe Q D (ULA.lpDrift Q ((momentumForceDynamics D γ).particleField N)
      ((momentumForceDynamics D γ).particleField_lipschitz N D.nonempty) U),
    ULA.lpDrift_coe Q ((momentumForceDynamics D γ).particleField N)
      ((momentumForceDynamics D γ).particleField_lipschitz N D.nonempty) U,
    momentumUnpackLp_coe Q D U, momentumLpDrift_coe Q D γ (momentumUnpackLp Q D U)]
    with ω h1 h2 h3 h4
  rw [h1, h2, h4, h3]
  exact momentumEncoded_drift D γ (U ω)

/-- The actual L² empirical model field becomes precisely the HOL drift
under the proved complete-state coordinate map. -/
theorem higherOrderUnpackLp_drift (α γ : ℝ)
    (U : Lp (A × (Fin N → HigherOrderSampler X)) 2 Q) :
    higherOrderUnpackLp Q D (ULA.lpDrift Q ((higherOrderForceDynamics D α γ).particleField N)
      ((higherOrderForceDynamics D α γ).particleField_lipschitz N D.nonempty) U) =
      holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ (higherOrderUnpackLp Q D U) := by
  apply hol_eq_of_ae
  filter_upwards [higherOrderUnpackLp_coe Q D (ULA.lpDrift Q ((higherOrderForceDynamics D α γ).particleField N)
      ((higherOrderForceDynamics D α γ).particleField_lipschitz N D.nonempty) U),
    ULA.lpDrift_coe Q ((higherOrderForceDynamics D α γ).particleField N)
      ((higherOrderForceDynamics D α γ).particleField_lipschitz N D.nonempty) U,
    higherOrderUnpackLp_coe Q D U, higherOrderLpDrift_coe Q D α γ (higherOrderUnpackLp Q D U)]
    with ω h1 h2 h3 h4
  rw [h1, h2, h4, h3]
  exact higherOrderEncoded_drift D α γ (U ω)


section Parameter
variable {I : Type*} [Fintype I]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

/-- The unpacked kinetic optimiser-position variable is the actual model
parameter lift of the shared random optimiser, not only equal in law. -/
theorem momentumUnpackLp_parameter (γ : ℝ) (σ : I → HypocoercivePhase X)
    (U : Lp (HypocoercivePhase A × (Fin N → HypocoercivePhase X)) 2 Q) :
    (momentumUnpackLp Q D U).2.1 =
      liftMap Q (heavyBallModel γ D.F D.G σ).parameter
        (momentum_parameter_lipschitz D.F D.G γ σ)
        (particleOptimizerLp (A := HypocoercivePhase A) (Z := HypocoercivePhase X) Q N U) := by
  apply Lp.ext
  filter_upwards [momentumUnpackLp_coe Q D U,
    liftMap_coe Q (heavyBallModel γ D.F D.G σ).parameter
      (momentum_parameter_lipschitz D.F D.G γ σ)
      (particleOptimizerLp (A := HypocoercivePhase A) (Z := HypocoercivePhase X) Q N U),
    (ContinuousLinearMap.fst ℝ (HypocoercivePhase A) (Fin N → HypocoercivePhase X)).coeFn_compLpL U]
    with ω hu hp ho
  have hu' := congrArg (fun z ↦ z.2.1) hu
  change (momentumUnpackLp Q D U).2.1 ω = (U ω).1.fst at hu'
  rw [hp]
  change _ = WithLp.fst ((particleOptimizerLp (A := HypocoercivePhase A)
    (Z := HypocoercivePhase X) Q N U) ω)
  change ((particleOptimizerLp (A := HypocoercivePhase A) (Z := HypocoercivePhase X) Q N U) ω) =
    (U ω).1 at ho
  rw [ho]
  exact hu'

/-- The unpacked HOL optimiser coordinate is exactly the actual shared
random optimiser parameter, before passing to its law. -/
theorem higherOrderUnpackLp_parameter (α γ : ℝ) (σ : I → X)
    (U : Lp (A × (Fin N → HigherOrderSampler X)) 2 Q) :
    (higherOrderUnpackLp Q D U).1 =
      liftMap Q (higherOrderModel D.F D.G α γ σ).parameter
        (higherOrder_parameter_lipschitz D.F D.G α γ σ)
        (particleOptimizerLp (A := A) (Z := HigherOrderSampler X) Q N U) := by
  apply Lp.ext
  filter_upwards [higherOrderUnpackLp_coe Q D U,
    liftMap_coe Q (higherOrderModel D.F D.G α γ σ).parameter
      (higherOrder_parameter_lipschitz D.F D.G α γ σ)
      (particleOptimizerLp (A := A) (Z := HigherOrderSampler X) Q N U),
    (ContinuousLinearMap.fst ℝ A (Fin N → HigherOrderSampler X)).coeFn_compLpL U]
    with ω hu hp ho
  have hu' := congrArg Prod.fst hu
  change (higherOrderUnpackLp Q D U).1 ω = (U ω).1 at hu'
  rw [hp]
  change _ = (particleOptimizerLp (A := A) (Z := HigherOrderSampler X) Q N U) ω
  exact hu'.trans ho.symm

end Parameter

section Integral
variable [CompleteSpace C]

/-- Actual global empirical-model integral equations transport to the
original kinetic implementation integral equation. -/
theorem momentumUnpackLp_integral (γ : ℝ)
    (Y B : ℝ → Lp (HypocoercivePhase A × (Fin N → HypocoercivePhase X)) 2 Q)
    (hY : Continuous Y)
    (heq : ∀ t, 0 ≤ t → Y t - Y 0 =
      (∫ r in 0..t, ULA.lpDrift Q ((momentumForceDynamics D γ).particleField N)
        ((momentumForceDynamics D γ).particleField_lipschitz N D.nonempty) (Y r)) + B t)
    (t : ℝ) (ht : 0 ≤ t) :
    momentumUnpackLp Q D (Y t) - momentumUnpackLp Q D (Y 0) =
      (∫ r in 0..t,
        (-coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) (momentumUnpackLp Q D (Y r)).2 -
          γ • (momentumUnpackLp Q D (Y r)).1, (momentumUnpackLp Q D (Y r)).1)) +
      momentumUnpackLp Q D (B t) := by
  let T := momentumUnpackLp Q D
  have hi : IntervalIntegrable (fun r ↦ ULA.lpDrift Q ((momentumForceDynamics D γ).particleField N)
      ((momentumForceDynamics D γ).particleField_lipschitz N D.nonempty) (Y r)) volume 0 t :=
    ((ULA.lpDrift_lipschitz Q _ _).continuous.comp hY).intervalIntegrable 0 t
  have h := congrArg T (heq t ht)
  rw [map_sub, map_add, ← T.intervalIntegral_comp_comm hi] at h
  simpa only [T, momentumUnpackLp_drift] using h

/-- Actual global empirical-model integral equations transport to the
original HOL implementation integral equation, including all auxiliaries. -/
theorem higherOrderUnpackLp_integral (α γ : ℝ)
    (Y B : ℝ → Lp (A × (Fin N → HigherOrderSampler X)) 2 Q) (hY : Continuous Y)
    (heq : ∀ t, 0 ≤ t → Y t - Y 0 =
      (∫ r in 0..t, ULA.lpDrift Q ((higherOrderForceDynamics D α γ).particleField N)
        ((higherOrderForceDynamics D α γ).particleField_lipschitz N D.nonempty) (Y r)) + B t)
    (t : ℝ) (ht : 0 ≤ t) :
    higherOrderUnpackLp Q D (Y t) - higherOrderUnpackLp Q D (Y 0) =
      (∫ r in 0..t, holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ
        (higherOrderUnpackLp Q D (Y r))) + higherOrderUnpackLp Q D (B t) := by
  let T := higherOrderUnpackLp Q D
  have hi : IntervalIntegrable (fun r ↦ ULA.lpDrift Q ((higherOrderForceDynamics D α γ).particleField N)
      ((higherOrderForceDynamics D α γ).particleField_lipschitz N D.nonempty) (Y r)) volume 0 t :=
    ((ULA.lpDrift_lipschitz Q _ _).continuous.comp hY).intervalIntegrable 0 t
  have h := congrArg T (heq t ht)
  rw [map_sub, map_add, ← T.intervalIntegral_comp_comm hi] at h
  simpa only [T, higherOrderUnpackLp_drift] using h

end Integral

end LpDrift

end Encoded

end PBGSO.ImplementationDynamics
