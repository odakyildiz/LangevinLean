import PBGSO.ImplementationLpCoordinates
import PBGSO.ConstructedItoParticle

/-! # Invertible L² method coordinates
The split optimiser and cloud random variables are joined on their actual
shared sample space. Both inverse identities are proved almost everywhere;
no law or coordinate-identification assumption is introduced.
-/
noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory
open scoped NNReal ENNReal
namespace PBGSO.ImplementationDynamics
open Methods

section SplitJoin
variable {Ω A C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  (Q : Measure Ω)

/-- Join two actual L² coordinates continuously and linearly. -/
def pairJoinLp : (Lp A 2 Q × Lp C 2 Q) →L[ℝ] Lp (A × C) 2 Q :=
  ((ContinuousLinearMap.inl ℝ A C).compLpL 2 Q).comp
    (ContinuousLinearMap.fst ℝ (Lp A 2 Q) (Lp C 2 Q)) +
  ((ContinuousLinearMap.inr ℝ A C).compLpL 2 Q).comp
    (ContinuousLinearMap.snd ℝ (Lp A 2 Q) (Lp C 2 Q))

theorem pairJoinLp_coe (z : Lp A 2 Q × Lp C 2 Q) :
    pairJoinLp Q z =ᵐ[Q] fun ω => (z.1 ω,z.2 ω) :=
  pairLp_coe Q z.1 z.2

/-- Join the four kinetic implementation coordinates. -/
def phaseJoinLp : ((Lp A 2 Q × Lp C 2 Q) × (Lp A 2 Q × Lp C 2 Q)) →L[ℝ]
    Lp ((A × C) × (A × C)) 2 Q :=
  (pairJoinLp (A := A × C) (C := A × C) Q).comp
    ((pairJoinLp (A := A) (C := C) Q).prodMap (pairJoinLp (A := A) (C := C) Q))

theorem phaseJoinLp_coe
    (z : (Lp A 2 Q × Lp C 2 Q) × (Lp A 2 Q × Lp C 2 Q)) :
    phaseJoinLp Q z =ᵐ[Q] phaseValue Q z := by
  filter_upwards [pairJoinLp_coe Q (pairJoinLp Q z.1,pairJoinLp Q z.2),
    pairJoinLp_coe Q z.1,pairJoinLp_coe Q z.2] with ω h h1 h2
  exact h.trans (Prod.ext h1 h2)

@[simp] theorem phaseSplit_join
    (z : (Lp A 2 Q × Lp C 2 Q) × (Lp A 2 Q × Lp C 2 Q)) :
    phaseSplitLp Q (phaseJoinLp Q z)=z := by
  apply phase_eq_of_ae
  filter_upwards [phaseSplitLp_coe Q (phaseJoinLp Q z),phaseJoinLp_coe Q z] with ω h1 h2
  exact h1.trans h2

@[simp] theorem phaseJoin_split (z : Lp ((A × C) × (A × C)) 2 Q) :
    phaseJoinLp Q (phaseSplitLp Q z)=z := by
  apply Lp.ext
  filter_upwards [phaseJoinLp_coe Q (phaseSplitLp Q z),phaseSplitLp_coe Q z] with ω h1 h2
  exact h1.trans h2

/-- Join all four actual HOL implementation coordinates. -/
def holJoinLp : HOLState (Lp A 2 Q) (Lp C 2 Q) →L[ℝ] Lp (HOLState A C) 2 Q :=
  (pairJoinLp (A := A) (C := C × C × C) Q).comp
    ((ContinuousLinearMap.id ℝ (Lp A 2 Q)).prodMap
      ((pairJoinLp (A := C) (C := C × C) Q).comp
        ((ContinuousLinearMap.id ℝ (Lp C 2 Q)).prodMap
          (pairJoinLp (A := C) (C := C) Q))))

theorem holJoinLp_coe (z : HOLState (Lp A 2 Q) (Lp C 2 Q)) :
    holJoinLp Q z =ᵐ[Q] holValue Q z := by
  filter_upwards [pairJoinLp_coe Q
      (z.1,pairJoinLp Q (z.2.1,pairJoinLp Q z.2.2)),
    pairJoinLp_coe Q (z.2.1,pairJoinLp Q z.2.2),pairJoinLp_coe Q z.2.2] with ω h h1 h2
  exact h.trans (Prod.ext rfl (h1.trans (Prod.ext rfl h2)))

@[simp] theorem holSplit_join (z : HOLState (Lp A 2 Q) (Lp C 2 Q)) :
    holSplitLp Q (holJoinLp Q z)=z := by
  apply hol_eq_of_ae
  filter_upwards [holSplitLp_coe Q (holJoinLp Q z),holJoinLp_coe Q z] with ω h1 h2
  exact h1.trans h2

@[simp] theorem holJoin_split (z : Lp (HOLState A C) 2 Q) :
    holJoinLp Q (holSplitLp Q z)=z := by
  apply Lp.ext
  filter_upwards [holJoinLp_coe Q (holSplitLp Q z),holSplitLp_coe Q z] with ω h1 h2
  exact h1.trans h2

end SplitJoin

section MapLp
variable {Ω E F : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (Q : Measure Ω)

/-- A continuous linear coordinate equivalence acts on the actual L² space. -/
def mapLpEquiv (e : E ≃L[ℝ] F) : Lp E 2 Q ≃L[ℝ] Lp F 2 Q where
  toFun := e.toContinuousLinearMap.compLpL 2 Q
  invFun := e.symm.toContinuousLinearMap.compLpL 2 Q
  left_inv := by
    intro x
    apply Lp.ext
    filter_upwards [e.symm.toContinuousLinearMap.coeFn_compLpL
      (e.toContinuousLinearMap.compLpL 2 Q x),e.toContinuousLinearMap.coeFn_compLpL x]
      with ω h1 h2
    exact h1.trans (by rw [h2]; exact e.symm_apply_apply _)
  right_inv := by
    intro x
    apply Lp.ext
    filter_upwards [e.toContinuousLinearMap.coeFn_compLpL
      (e.symm.toContinuousLinearMap.compLpL 2 Q x),e.symm.toContinuousLinearMap.coeFn_compLpL x]
      with ω h1 h2
    exact h1.trans (by rw [h2]; exact e.apply_symm_apply _)
  map_add' := (e.toContinuousLinearMap.compLpL 2 Q).map_add
  map_smul' := (e.toContinuousLinearMap.compLpL 2 Q).map_smul
  continuous_toFun := (e.toContinuousLinearMap.compLpL 2 Q).continuous
  continuous_invFun := (e.symm.toContinuousLinearMap.compLpL 2 Q).continuous

end MapLp
section Packed
variable {Ω A C X : Type*} {N : ℕ} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  (Q : Measure Ω)
  (D : ParticleForceData A X C N)

/-- Join and reencode the actual kinetic random state. -/
def momentumPackLp : ((Lp A 2 Q × Lp C 2 Q) × (Lp A 2 Q × Lp C 2 Q)) →L[ℝ]
    Lp (HypocoercivePhase A × (Fin N → HypocoercivePhase X)) 2 Q :=
  ((momentumEncodedStateEquiv D).toContinuousLinearMap.compLpL 2 Q).comp
    (phaseJoinLp Q)

theorem momentumPackLp_coe
    (z : (Lp A 2 Q × Lp C 2 Q) × (Lp A 2 Q × Lp C 2 Q)) :
    momentumPackLp Q D z =ᵐ[Q] fun ω => momentumEncodedStateEquiv D (phaseValue Q z ω) := by
  filter_upwards [(momentumEncodedStateEquiv D).toContinuousLinearMap.coeFn_compLpL
      (phaseJoinLp Q z),phaseJoinLp_coe Q z] with ω h h1
  exact h.trans (congrArg (momentumEncodedStateEquiv D) h1)

@[simp] theorem momentumUnpack_pack
    (z : (Lp A 2 Q × Lp C 2 Q) × (Lp A 2 Q × Lp C 2 Q)) :
    momentumUnpackLp Q D (momentumPackLp Q D z)=z := by
  apply phase_eq_of_ae
  filter_upwards [momentumUnpackLp_coe Q D (momentumPackLp Q D z),
    momentumPackLp_coe Q D z] with ω h h1
  rw [h,h1]
  exact (momentumEncodedStateEquiv D).symm_apply_apply _

@[simp] theorem momentumPack_unpack
    (z : Lp (HypocoercivePhase A × (Fin N → HypocoercivePhase X)) 2 Q) :
    momentumPackLp Q D (momentumUnpackLp Q D z)=z := by
  apply Lp.ext
  filter_upwards [momentumPackLp_coe Q D (momentumUnpackLp Q D z),
    momentumUnpackLp_coe Q D z] with ω h h1
  rw [h,h1]
  exact (momentumEncodedStateEquiv D).apply_symm_apply _

/-- Join and reencode the actual higher-order random state. -/
def higherOrderPackLp : HOLState (Lp A 2 Q) (Lp C 2 Q) →L[ℝ]
    Lp (A × (Fin N → HigherOrderSampler X)) 2 Q :=
  ((higherOrderEncodedStateEquiv D).toContinuousLinearMap.compLpL 2 Q).comp
    (holJoinLp Q)

theorem higherOrderPackLp_coe (z : HOLState (Lp A 2 Q) (Lp C 2 Q)) :
    higherOrderPackLp Q D z =ᵐ[Q] fun ω => higherOrderEncodedStateEquiv D (holValue Q z ω) := by
  filter_upwards [(higherOrderEncodedStateEquiv D).toContinuousLinearMap.coeFn_compLpL
      (holJoinLp Q z),holJoinLp_coe Q z] with ω h h1
  exact h.trans (congrArg (higherOrderEncodedStateEquiv D) h1)

@[simp] theorem higherOrderUnpack_pack (z : HOLState (Lp A 2 Q) (Lp C 2 Q)) :
    higherOrderUnpackLp Q D (higherOrderPackLp Q D z)=z := by
  apply hol_eq_of_ae
  filter_upwards [higherOrderUnpackLp_coe Q D (higherOrderPackLp Q D z),
    higherOrderPackLp_coe Q D z] with ω h h1
  rw [h,h1]
  exact (higherOrderEncodedStateEquiv D).symm_apply_apply _

@[simp] theorem higherOrderPack_unpack
    (z : Lp (A × (Fin N → HigherOrderSampler X)) 2 Q) :
    higherOrderPackLp Q D (higherOrderUnpackLp Q D z)=z := by
  apply Lp.ext
  filter_upwards [higherOrderPackLp_coe Q D (higherOrderUnpackLp Q D z),
    higherOrderUnpackLp_coe Q D z] with ω h h1
  rw [h,h1]
  exact (higherOrderEncodedStateEquiv D).apply_symm_apply _

/-- The kinetic implementation coordinates are an actual L² equivalence. -/
def momentumSourceLpEquiv :
    ((Lp A 2 Q × Lp C 2 Q) × (Lp A 2 Q × Lp C 2 Q)) ≃L[ℝ]
      Lp (HypocoercivePhase A × (Fin N → HypocoercivePhase X)) 2 Q where
  toFun := momentumPackLp Q D
  invFun := momentumUnpackLp Q D
  left_inv := momentumUnpack_pack Q D
  right_inv := momentumPack_unpack Q D
  map_add' := (momentumPackLp Q D).map_add
  map_smul' := (momentumPackLp Q D).map_smul
  continuous_toFun := (momentumPackLp Q D).continuous
  continuous_invFun := (momentumUnpackLp Q D).continuous

/-- The HOL implementation coordinates are an actual L² equivalence. -/
def higherOrderSourceLpEquiv :
    HOLState (Lp A 2 Q) (Lp C 2 Q) ≃L[ℝ]
      Lp (A × (Fin N → HigherOrderSampler X)) 2 Q where
  toFun := higherOrderPackLp Q D
  invFun := higherOrderUnpackLp Q D
  left_inv := higherOrderUnpack_pack Q D
  right_inv := higherOrderPack_unpack Q D
  map_add' := (higherOrderPackLp Q D).map_add
  map_smul' := (higherOrderPackLp Q D).map_smul
  continuous_toFun := (higherOrderPackLp Q D).continuous
  continuous_invFun := (higherOrderUnpackLp Q D).continuous

/-- Complete physical Hilbert coordinates for the original kinetic method. -/
def momentumPhysicalLpEquiv :
    ((Lp A 2 Q × Lp C 2 Q) × (Lp A 2 Q × Lp C 2 Q)) ≃L[ℝ]
      Lp (ConstructedItoParticle.OneHilbert N (HypocoercivePhase A) (HypocoercivePhase X)) 2 Q :=
  (momentumSourceLpEquiv Q D).trans
    (mapLpEquiv Q (ConstructedItoParticle.oneEquiv N).symm)

/-- Complete physical Hilbert coordinates for the original HOL method. -/
def higherOrderPhysicalLpEquiv :
    HOLState (Lp A 2 Q) (Lp C 2 Q) ≃L[ℝ]
      Lp (ConstructedItoParticle.OneHilbert N A (HigherOrderSampler X)) 2 Q :=
  (higherOrderSourceLpEquiv Q D).trans
    (mapLpEquiv Q (ConstructedItoParticle.oneEquiv N).symm)

variable [IsProbabilityMeasure Q]

/-- The inverse coordinate map transports the literal kinetic drift. -/
theorem momentumPackLp_drift (γ : ℝ)
    (z : (Lp A 2 Q × Lp C 2 Q) × (Lp A 2 Q × Lp C 2 Q)) :
    momentumPackLp Q D
      (-coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) z.2-γ • z.1,z.1) =
      ULA.lpDrift Q ((momentumForceDynamics D γ).particleField N)
        ((momentumForceDynamics D γ).particleField_lipschitz N D.nonempty)
        (momentumPackLp Q D z) := by
  have he := congrArg (momentumPackLp Q D)
    (momentumUnpackLp_drift Q D γ (momentumPackLp Q D z))
  simpa only [momentumPack_unpack,momentumUnpack_pack] using he.symm

/-- The inverse coordinate map transports the literal HOL drift. -/
theorem higherOrderPackLp_drift (α γ : ℝ) (z : HOLState (Lp A 2 Q) (Lp C 2 Q)) :
    higherOrderPackLp Q D (holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ z) =
      ULA.lpDrift Q ((higherOrderForceDynamics D α γ).particleField N)
        ((higherOrderForceDynamics D α γ).particleField_lipschitz N D.nonempty)
        (higherOrderPackLp Q D z) := by
  have he := congrArg (higherOrderPackLp Q D)
    (higherOrderUnpackLp_drift Q D α γ (higherOrderPackLp Q D z))
  simpa only [higherOrderPack_unpack,higherOrderUnpack_pack] using he.symm

end Packed

end PBGSO.ImplementationDynamics
