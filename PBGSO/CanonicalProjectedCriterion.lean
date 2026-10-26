import PBGSO.GeneralizedSpectrum
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Canonical block-matrix instance of the source projected criterion

The position and auxiliary coordinates are literal Euclidean blocks. The
source's positive definite metric matrices act on those actual coordinates;
their coercivity is derived spectrally. The block `K=diag(c I,Daux)` is
constructed and proved positive definite, rather than supplied as a rate
certificate or an abstract quadratic-form identity.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator BigOperators
namespace PBGSO.CanonicalProjected
open GeneralizedSpectrum

section MatrixMetric
variable {n m : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [Fintype m] [DecidableEq m] [Nonempty m]

/-- Actual multiplication by a real matrix on Euclidean space. -/
def matrixAction (A : Matrix n n ℝ) : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n :=
  (Matrix.toEuclideanLin A).toContinuousLinearMap

omit [Nonempty n] in
theorem matrixAction_inner (A : Matrix n n ℝ) (x y : EuclideanSpace ℝ n) :
    ⟪x, matrixAction A y⟫_ℝ = (fun i => x i) ⬝ᵥ (A *ᵥ (fun i => y i)) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (A *ᵥ (fun i => y i)) ⬝ᵥ (fun i => x i) = _
  exact dotProduct_comm _ _

omit [DecidableEq n] [Nonempty n] in
theorem euclidean_dot_self (x : EuclideanSpace ℝ n) :
    (fun i => x i) ⬝ᵥ (fun i => x i) = ‖x‖ ^ 2 := by
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using
    (real_inner_self_eq_norm_sq x)

theorem matrixAction_lower {A : Matrix n n ℝ} (hA : A.PosDef) (x : EuclideanSpace ℝ n) :
    minimumEigenvalue hA.isHermitian * ‖x‖ ^ 2 ≤ ⟪x, matrixAction A x⟫_ℝ := by
  rw [matrixAction_inner, ← euclidean_dot_self]
  exact minimumEigenvalue_quadratic hA.isHermitian _

theorem matrixAction_upper (A : Matrix n n ℝ) (x : EuclideanSpace ℝ n) :
    ⟪x, matrixAction A x⟫_ℝ ≤ ‖matrixAction A‖ * ‖x‖ ^ 2 := by
  calc
    _ ≤ ‖x‖ * ‖matrixAction A x‖ := real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖matrixAction A‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left ((matrixAction A).le_opNorm x) (norm_nonneg x)
    _ = _ := by ring

/-- SPD source matrices give a genuine twisted geometry. The lower bound
uses the actual spectral minima; an operator-norm upper bound suffices. -/
def matrixGeometry (A : Matrix n n ℝ) (B : Matrix m m ℝ)
    (hA : A.PosDef) (hB : B.PosDef) :
    TwistedGeometry (EuclideanSpace ℝ n) (EuclideanSpace ℝ m) where
  optimizerWeight := matrixAction A
  samplerWeight := matrixAction B
  lower := min (minimumEigenvalue hA.isHermitian) (minimumEigenvalue hB.isHermitian)
  upper := min (minimumEigenvalue hA.isHermitian) (minimumEigenvalue hB.isHermitian) +
    ‖matrixAction A‖ + ‖matrixAction B‖
  lower_pos := lt_min (minimumEigenvalue_pos hA) (minimumEigenvalue_pos hB)
  lower_le_upper := by linarith [norm_nonneg (matrixAction A), norm_nonneg (matrixAction B)]
  optimizer_symmetric := by
    intro x y
    exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.isHermitian x y).symm
  sampler_symmetric := by
    intro x y
    exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB.isHermitian x y).symm
  optimizer_lower := fun x =>
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg ‖x‖)).trans (matrixAction_lower hA x)
  sampler_lower := fun x =>
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg ‖x‖)).trans (matrixAction_lower hB x)
  optimizer_upper := by
    intro x
    have hp := lt_min (minimumEigenvalue_pos hA) (minimumEigenvalue_pos hB)
    have hc : ‖matrixAction A‖ ≤
        min (minimumEigenvalue hA.isHermitian) (minimumEigenvalue hB.isHermitian) +
          ‖matrixAction A‖ + ‖matrixAction B‖ := by linarith [norm_nonneg (matrixAction B)]
    exact (matrixAction_upper A x).trans (mul_le_mul_of_nonneg_right hc (sq_nonneg ‖x‖))
  sampler_upper := by
    intro x
    have hp := lt_min (minimumEigenvalue_pos hA) (minimumEigenvalue_pos hB)
    have hc : ‖matrixAction B‖ ≤
        min (minimumEigenvalue hA.isHermitian) (minimumEigenvalue hB.isHermitian) +
          ‖matrixAction A‖ + ‖matrixAction B‖ := by linarith [norm_nonneg (matrixAction A)]
    exact (matrixAction_upper B x).trans (mul_le_mul_of_nonneg_right hc (sq_nonneg ‖x‖))

end MatrixMetric

section Transport
variable {S Z E F : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

@[simp] theorem inner_isometry_symm_right (e : S ≃ₗᵢ[ℝ] E) (x : S) (y : E) :
    ⟪x, e.symm y⟫_ℝ = ⟪e x, y⟫_ℝ := by
  simpa only [e.apply_symm_apply] using (e.inner_map_map x (e.symm y)).symm

@[simp] theorem inner_isometry_symm_left (e : S ≃ₗᵢ[ℝ] E) (x : S) (y : E) :
    ⟪e.symm y, x⟫_ℝ = ⟪y, e x⟫_ℝ := by
  calc
    _ = ⟪x, e.symm y⟫_ℝ := real_inner_comm _ _
    _ = ⟪e x, y⟫_ℝ := inner_isometry_symm_right e x y
    _ = _ := real_inner_comm _ _

/-- Transport a certified metric through actual isometric coordinates. -/
def transportGeometry (D : TwistedGeometry E F)
    (e : S ≃ₗᵢ[ℝ] E) (f : Z ≃ₗᵢ[ℝ] F) : TwistedGeometry S Z where
  optimizerWeight := e.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    D.optimizerWeight ∘L e.toContinuousLinearEquiv.toContinuousLinearMap
  samplerWeight := f.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    D.samplerWeight ∘L f.toContinuousLinearEquiv.toContinuousLinearMap
  lower := D.lower
  upper := D.upper
  lower_pos := D.lower_pos
  lower_le_upper := D.lower_le_upper
  optimizer_symmetric := by
    intro x y
    simpa using D.optimizer_symmetric (e x) (e y)
  sampler_symmetric := by
    intro x y
    simpa using D.sampler_symmetric (f x) (f y)
  optimizer_lower := by
    intro x
    simpa using D.optimizer_lower (e x)
  optimizer_upper := by
    intro x
    simpa using D.optimizer_upper (e x)
  sampler_lower := by
    intro x
    simpa using D.sampler_lower (f x)
  sampler_upper := by
    intro x
    simpa using D.sampler_upper (f x)

end Transport

section Blocks
variable {a u : Type*} [Fintype a] [DecidableEq a] [Fintype u] [DecidableEq u]

abbrev BlockSpace (a u : Type*) := WithLp 2 (EuclideanSpace ℝ a × EuclideanSpace ℝ u)

/-- The literal Euclidean coordinate splitting is an isometry. -/
def blockCoordinateIsometry : BlockSpace a u ≃ₗᵢ[ℝ] EuclideanSpace ℝ (a ⊕ u) :=
  (PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2 (fun _ : a ⊕ u => ℝ)).symm

/-- Raw coordinate form of the canonical isometry. -/
def blockCoordinates : BlockSpace a u →L[ℝ] ((a ⊕ u) → ℝ) :=
  (WithLp.linearEquiv 2 ℝ ((a ⊕ u) → ℝ)).toLinearMap.toContinuousLinearMap ∘L
    blockCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem blockCoordinates_apply (z : BlockSpace a u) :
    blockCoordinates z = Sum.elim (fun i => z.fst i) (fun j => z.snd j) := rfl

/-- The source block `diag(c I,Daux)`. -/
def blockK (c : ℝ) (A : Matrix u u ℝ) : Matrix (a ⊕ u) (a ⊕ u) ℝ :=
  Matrix.fromBlocks (c • (1 : Matrix a a ℝ)) 0 0 A

theorem blockK_quadratic (c : ℝ) (A : Matrix u u ℝ) (q : a → ℝ) (p : u → ℝ) :
    Sum.elim q p ⬝ᵥ (blockK c A *ᵥ Sum.elim q p) =
      c * (q ⬝ᵥ q) + p ⬝ᵥ (A *ᵥ p) := by
  simp [blockK, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- The source `c>0` and auxiliary SPD matrix imply that the constructed
block matrix is itself strictly positive definite. -/
theorem blockK_posDef (c : ℝ) (hc : 0 < c) (A : Matrix u u ℝ) (hA : A.PosDef) :
    (blockK (a := a) c A).PosDef := by
  have hI : (c • (1 : Matrix a a ℝ)).PosDef := Matrix.PosDef.one.smul hc
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (hI.isHermitian.fromBlocks (by simp) hA.isHermitian)
  intro z hz
  change 0 < star z ⬝ᵥ (blockK (a := a) c A *ᵥ z)
  have heq : z = Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr) := by ext (i | j) <;> rfl
  rw [star_trivial, heq, blockK_quadratic]
  by_cases hp : (z ∘ Sum.inr) = 0
  · have hq : (z ∘ Sum.inl) ≠ 0 := by
      intro hq
      apply hz
      rw [heq, hp, hq]
      ext (i | j) <;> rfl
    have hpos := (Matrix.PosDef.one : (1 : Matrix a a ℝ).PosDef).dotProduct_mulVec_pos hq
    simpa only [star_trivial, Matrix.one_mulVec, hp, Matrix.mulVec_zero, dotProduct_zero,
      add_zero] using mul_pos hc hpos
  · have hq := (Matrix.PosSemidef.one : (1 : Matrix a a ℝ).PosSemidef).dotProduct_mulVec_nonneg
      (z ∘ Sum.inl)
    have hpos := hA.dotProduct_mulVec_pos hp
    simp only [star_trivial, Matrix.one_mulVec] at hq hpos
    exact add_pos_of_nonneg_of_pos (mul_nonneg hc.le hq) hpos

/-- The constructed K matrix has exactly the projected-plus-auxiliary
quadratic form in the literal source coordinates. -/
theorem blockK_coordinate_form (c : ℝ) (A : Matrix u u ℝ) (z : BlockSpace a u) :
    blockCoordinates z ⬝ᵥ (blockK c A *ᵥ blockCoordinates z) =
      c * ‖z.fst‖ ^ 2 + ⟪z.snd, matrixAction A z.snd⟫_ℝ := by
  rw [blockCoordinates_apply, blockK_quadratic, euclidean_dot_self, matrixAction_inner]

end Blocks

section Canonical
variable {a u x v I : Type*}
  [Fintype a] [DecidableEq a] [Nonempty a] [Fintype u] [DecidableEq u]
  [Fintype x] [DecidableEq x] [Nonempty x] [Fintype v] [DecidableEq v] [Fintype I]

/-- The source's two given SPD metric matrices acting on the literal
position/auxiliary blocks. All norm comparisons are derived. -/
def canonicalGeometry (DOpt : Matrix (a ⊕ u) (a ⊕ u) ℝ)
    (DSam : Matrix (x ⊕ v) (x ⊕ v) ℝ) (hDOpt : DOpt.PosDef) (hDSam : DSam.PosDef) :
    TwistedGeometry (BlockSpace a u) (BlockSpace x v) :=
  transportGeometry (matrixGeometry DOpt DSam hDOpt hDSam)
    blockCoordinateIsometry blockCoordinateIsometry

theorem canonicalGeometry_optimizer_form (DOpt : Matrix (a ⊕ u) (a ⊕ u) ℝ)
    (DSam : Matrix (x ⊕ v) (x ⊕ v) ℝ) (hDOpt : DOpt.PosDef) (hDSam : DSam.PosDef)
    (s : BlockSpace a u) :
    (canonicalGeometry DOpt DSam hDOpt hDSam).optimizerSq s =
      blockCoordinates s ⬝ᵥ (DOpt *ᵥ blockCoordinates s) := by
  change ⟪s, blockCoordinateIsometry.symm
    (matrixAction DOpt (blockCoordinateIsometry s))⟫_ℝ = _
  rw [inner_isometry_symm_right, matrixAction_inner]
  rfl

theorem canonicalGeometry_sampler_form (DOpt : Matrix (a ⊕ u) (a ⊕ u) ℝ)
    (DSam : Matrix (x ⊕ v) (x ⊕ v) ℝ) (hDOpt : DOpt.PosDef) (hDSam : DSam.PosDef)
    (z : BlockSpace x v) :
    (canonicalGeometry DOpt DSam hDOpt hDSam).samplerSq z =
      blockCoordinates z ⬝ᵥ (DSam *ᵥ blockCoordinates z) := by
  change ⟪z, blockCoordinateIsometry.symm
    (matrixAction DSam (blockCoordinateIsometry z))⟫_ℝ = _
  rw [inner_isometry_symm_right, matrixAction_inner]
  rfl

/-- Canonical source projections with the actual auxiliary matrix actions.
The optimiser response and sampler drift of M remain arbitrary. -/
def canonicalData
    (M : Model (BlockSpace a u) (EuclideanSpace ℝ a) (BlockSpace x v) (EuclideanSpace ℝ x) I)
    (hparameter : M.parameter = WithLp.fst) (hposition : M.position = WithLp.fst)
    (H : EuclideanSpace ℝ a → EuclideanSpace ℝ x → EuclideanSpace ℝ x)
    (Dm : Matrix u u ℝ) (Dv : Matrix v v ℝ) :
    ProjectedData (U := EuclideanSpace ℝ u) (V := EuclideanSpace ℝ v) M where
  parameterProjection := WithLp.fstL 2 ℝ (EuclideanSpace ℝ a) (EuclideanSpace ℝ u)
  positionProjection := WithLp.fstL 2 ℝ (EuclideanSpace ℝ x) (EuclideanSpace ℝ v)
  optimizerAuxiliary := WithLp.sndL 2 ℝ (EuclideanSpace ℝ a) (EuclideanSpace ℝ u)
  samplerAuxiliary := WithLp.sndL 2 ℝ (EuclideanSpace ℝ x) (EuclideanSpace ℝ v)
  parameter_eq := hparameter
  position_eq := hposition
  force := H
  optimizerAuxWeight := matrixAction Dm
  samplerAuxWeight := matrixAction Dv

/-- The full canonical source projected-field corollary at its exact
generalized spectral rate. The K matrices, their SPD proofs, the twisted
geometry and every coordinate identity are constructed from the primitive
source matrices. U4/U5, constant diffusion and finite coupling expressions
remain the explicit substantive source hypotheses. Auxiliary dimensions
may be zero; parameter and position dimensions are nonempty. -/
theorem canonical_projected_source_criterion
    (M : Model (BlockSpace a u) (EuclideanSpace ℝ a) (BlockSpace x v) (EuclideanSpace ℝ x) I)
    (hparameter : M.parameter = WithLp.fst) (hposition : M.position = WithLp.fst)
    (H : EuclideanSpace ℝ a → EuclideanSpace ℝ x → EuclideanSpace ℝ x)
    (DOpt : Matrix (a ⊕ u) (a ⊕ u) ℝ) (DSam : Matrix (x ⊕ v) (x ⊕ v) ℝ)
    (Dm : Matrix u u ℝ) (Dv : Matrix v v ℝ)
    (hDOpt : DOpt.PosDef) (hDSam : DSam.PosDef) (hDm : Dm.PosDef) (hDv : Dv.PosDef)
    (β r AOpt ASam : ℝ) (hβ : 0 ≤ β) (hc : 0 < β * r - AOpt - ASam)
    (hmono : (canonicalData M hparameter hposition H Dm Dv).StrongMonotonicity r)
    (haux : ProjectedAuxiliaryDissipation M (canonicalGeometry DOpt DSam hDOpt hDSam)
      (canonicalData M hparameter hposition H Dm Dv) β AOpt ASam)
    (σ : I → BlockSpace x v) (hσ : ∀ θ z, M.diffusion θ z = σ)
    (hInt : ∀ s s' ν ν' Λ,
      ProjectedAdmissibleCoupling M (canonicalGeometry DOpt DSam hDOpt hDSam) s s' ν ν' Λ →
      (canonicalData M hparameter hposition H Dm Dv).Integrability s s' Λ) :
    let ρ := min
      (generalizedMinimum hDOpt (blockK_posDef (a := a) _ hc Dm hDm))
      (generalizedMinimum hDSam (blockK_posDef (a := x) _ hc Dv hDv))
    0 < ρ ∧ TwistedJointMonotonicity M (canonicalGeometry DOpt DSam hDOpt hDSam) ρ := by
  apply projected_twistedJointMonotonicity_spectral M
    (canonicalGeometry DOpt DSam hDOpt hDSam) (canonicalData M hparameter hposition H Dm Dv)
    β r AOpt ASam hβ hmono haux σ hσ hInt DOpt (blockK _ Dm) DSam (blockK _ Dv)
    hDOpt (blockK_posDef _ hc Dm hDm) hDSam (blockK_posDef _ hc Dv hDv)
    blockCoordinates blockCoordinates
  · exact canonicalGeometry_optimizer_form DOpt DSam hDOpt hDSam
  · exact canonicalGeometry_sampler_form DOpt DSam hDOpt hDSam
  · intro d
    simpa only [canonicalData, ProjectedData.optimizerAuxSq, WithLp.fstL_apply,
      WithLp.sndL_apply] using blockK_coordinate_form (β * r - AOpt - ASam) Dm d
  · intro zz
    simpa only [canonicalData, ProjectedData.samplerAuxSq, WithLp.fstL_apply,
      WithLp.sndL_apply] using blockK_coordinate_form (β * r - AOpt - ASam) Dv (zz.1 - zz.2)

end Canonical

end PBGSO.CanonicalProjected
