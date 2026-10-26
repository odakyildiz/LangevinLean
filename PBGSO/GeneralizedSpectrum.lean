import PBGSO.ProjectedCriteria
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Generalized spectral lower bounds for positive definite matrices

The minimum is taken over the actual finite spectrum of the whitened
matrix `D^(-1/2) K D^(-1/2)`. Positive definiteness and the quadratic
comparison are derived from the primitive SPD hypotheses.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator BigOperators
namespace PBGSO.GeneralizedSpectrum

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The smallest actual eigenvalue of a finite real symmetric matrix.
Nonempty coordinates are explicit because the empty spectrum has no minimum. -/
def minimumEigenvalue {A : Matrix n n ℝ} (hA : A.IsHermitian) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty hA.eigenvalues

theorem minimumEigenvalue_le {A : Matrix n n ℝ} (hA : A.IsHermitian) (i : n) :
    minimumEigenvalue hA ≤ hA.eigenvalues i :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem minimumEigenvalue_pos {A : Matrix n n ℝ} (hA : A.PosDef) :
    0 < minimumEigenvalue hA.isHermitian := by
  apply (Finset.lt_inf'_iff _).mpr
  intro i hi
  exact hA.eigenvalues_pos i

/-- The minimum is attained by an actual eigenvalue. -/
theorem minimumEigenvalue_attained {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    ∃ i, minimumEigenvalue hA = hA.eigenvalues i := by
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset n))
    Finset.univ_nonempty hA.eigenvalues
  exact ⟨i, he⟩

/-- This definition is precisely the least point of the real matrix
spectrum, not merely an arbitrary certified eigenvalue lower bound. -/
theorem minimumEigenvalue_isLeast_spectrum {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    IsLeast (spectrum ℝ A) (minimumEigenvalue hA) := by
  constructor
  · obtain ⟨i, hi⟩ := minimumEigenvalue_attained hA
    rw [hi]
    exact hA.eigenvalues_mem_spectrum_real i
  · intro r hr
    rw [hA.spectrum_real_eq_range_eigenvalues] at hr
    obtain ⟨i, rfl⟩ := hr
    exact minimumEigenvalue_le hA i

/-- Spectral diagonalization proves that subtracting the minimum eigenvalue
times the identity leaves a positive semidefinite matrix. -/
theorem minimumEigenvalue_sub_posSemidef {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (A - minimumEigenvalue hA • (1 : Matrix n n ℝ)).PosSemidef := by
  let U := (hA.eigenvectorUnitary : Matrix n n ℝ)
  have hdiag : (Matrix.diagonal (fun i => hA.eigenvalues i - minimumEigenvalue hA)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (fun i => sub_nonneg.mpr (minimumEigenvalue_le hA i))
  have hc := hdiag.mul_mul_conjTranspose_same U
  have hspec : A = U * Matrix.diagonal hA.eigenvalues * Uᴴ := by
    simpa only [U, Unitary.conjStarAlgAut_apply, Function.comp_def,
      RCLike.ofReal_real_eq_id, id_eq, Matrix.star_eq_conjTranspose] using
      hA.spectral_theorem
  have hU : U * Uᴴ = 1 := by
    simpa only [U, ← Matrix.star_eq_conjTranspose, Unitary.coe_star] using
      (Unitary.coe_mul_star_self hA.eigenvectorUnitary)
  have heq : U * Matrix.diagonal (fun i => hA.eigenvalues i - minimumEigenvalue hA) * Uᴴ =
      A - minimumEigenvalue hA • (1 : Matrix n n ℝ) := by
    rw [show Matrix.diagonal (fun i => hA.eigenvalues i - minimumEigenvalue hA) =
        Matrix.diagonal hA.eigenvalues - minimumEigenvalue hA • (1 : Matrix n n ℝ) by
      ext i j
      by_cases h : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, h]]
    rw [Matrix.mul_sub, Matrix.sub_mul, ← hspec]
    simp only [mul_smul_comm, smul_mul_assoc, Matrix.mul_one, hU]
  rwa [heq] at hc

/-- The spectral lower bound is an actual quadratic-form inequality. -/
theorem minimumEigenvalue_quadratic {A : Matrix n n ℝ} (hA : A.IsHermitian) (x : n → ℝ) :
    minimumEigenvalue hA * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
  have h := (minimumEigenvalue_sub_posSemidef hA).dotProduct_mulVec_nonneg x
  simpa only [Pi.star_apply, star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul, sub_nonneg] using h

/-- The matrix appearing in the source generalized-eigenvalue rate. -/
def whitened (D K : Matrix n n ℝ) : Matrix n n ℝ :=
  (CFC.sqrt D)⁻¹ * K * (CFC.sqrt D)⁻¹

theorem sqrt_posDef {D : Matrix n n ℝ} (hD : D.PosDef) : (CFC.sqrt D).PosDef :=
  (IsStrictlyPositive.sqrt D hD.isStrictlyPositive).posDef

/-- Whitening preserves strict positive definiteness because the actual
positive square root is invertible. -/
theorem whitened_posDef {D K : Matrix n n ℝ} (hD : D.PosDef) (hK : K.PosDef) :
    (whitened D K).PosDef := by
  have hW := (sqrt_posDef hD).inv
  have h := hK.conjTranspose_mul_mul_same (B := (CFC.sqrt D)⁻¹)
    (Matrix.mulVec_injective_of_isUnit hW.isUnit)
  simpa only [hW.isHermitian.eq, whitened] using h

/-- The exact source rate, the minimum generalized eigenvalue. -/
def generalizedMinimum {D K : Matrix n n ℝ} (hD : D.PosDef) (hK : K.PosDef) : ℝ :=
  minimumEigenvalue (whitened_posDef hD hK).isHermitian

theorem generalizedMinimum_pos {D K : Matrix n n ℝ} (hD : D.PosDef) (hK : K.PosDef) :
    0 < generalizedMinimum hD hK :=
  minimumEigenvalue_pos (whitened_posDef hD hK)

/-- Congruence by the actual positive square root converts the spectral
lower bound back to `K - rho D ≥ 0`. -/
theorem generalizedMinimum_sub_posSemidef {D K : Matrix n n ℝ}
    (hD : D.PosDef) (hK : K.PosDef) :
    (K - generalizedMinimum hD hK • D).PosSemidef := by
  let S := CFC.sqrt D
  have hS : S.PosDef := sqrt_posDef hD
  have hunit : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS.isUnit
  have hleft : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hunit
  have hright : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hunit
  have hsq : S * S = D := by
    simpa only [S, pow_two] using CFC.sq_sqrt D hD.posSemidef.nonneg
  have hfirst : S * whitened D K * S = K := by
    calc
      S * whitened D K * S = (S * S⁻¹) * K * (S⁻¹ * S) := by
        dsimp [whitened, S]
        noncomm_ring
      _ = K := by rw [hleft, hright]; simp
  have hsecond : S * (generalizedMinimum hD hK • (1 : Matrix n n ℝ)) * S =
      generalizedMinimum hD hK • D := by
    rw [mul_smul_comm, smul_mul_assoc, Matrix.mul_one, hsq]
  have hp := (minimumEigenvalue_sub_posSemidef
    (whitened_posDef hD hK).isHermitian).conjTranspose_mul_mul_same S
  change (Sᴴ * (whitened D K - generalizedMinimum hD hK • (1 : Matrix n n ℝ)) * S).PosSemidef at hp
  rw [hS.isHermitian.eq, Matrix.mul_sub, Matrix.sub_mul, hfirst, hsecond] at hp
  exact hp

/-- The exact generalized minimum eigenvalue controls the primitive
quadratic forms, for every coordinate vector. -/
theorem generalizedMinimum_quadratic {D K : Matrix n n ℝ}
    (hD : D.PosDef) (hK : K.PosDef) (x : n → ℝ) :
    generalizedMinimum hD hK * (x ⬝ᵥ (D *ᵥ x)) ≤ x ⬝ᵥ (K *ᵥ x) := by
  have h := (generalizedMinimum_sub_posSemidef hD hK).dotProduct_mulVec_nonneg x
  simpa only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, sub_nonneg] using h

/-- The chosen inverse square root is exactly the square root of the
inverse matrix, matching the source's `D^{-1/2}` notation. -/
theorem whitened_eq_sqrt_inv {D : Matrix n n ℝ} (hD : D.PosDef) (K : Matrix n n ℝ) :
    whitened D K = CFC.sqrt D⁻¹ * K * CFC.sqrt D⁻¹ := by
  rw [whitened, hD.posSemidef.inv_sqrt]

end PBGSO.GeneralizedSpectrum

namespace PBGSO
open GeneralizedSpectrum MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace

section Projected
variable {S Θ Z X U V I n m : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [MeasurableSpace Z] [BorelSpace Z]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fintype I]
  [Fintype n] [DecidableEq n] [Nonempty n] [Fintype m] [DecidableEq m] [Nonempty m]

/-- The projected criterion at the exact source generalized-eigenvalue
rate. Matrix equalities identify the two metrics and the projected-plus-
auxiliary quadratic forms in explicit coordinates; they do not assume the
final lower comparison. The SPD inputs prove that comparison spectrally. -/
theorem projected_twistedJointMonotonicity_spectral
    (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    (C : ProjectedData (U := U) (V := V) M)
    (β r AOpt ASam : ℝ) (hβ : 0 ≤ β)
    (hmono : C.StrongMonotonicity r)
    (haux : ProjectedAuxiliaryDissipation M D C β AOpt ASam)
    (σ : I → Z) (hσ : ∀ θ z, M.diffusion θ z = σ)
    (hInt : ∀ s s' ν ν' Λ, ProjectedAdmissibleCoupling M D s s' ν ν' Λ →
      C.Integrability s s' Λ)
    (DOpt KOpt : Matrix n n ℝ) (DSam KSam : Matrix m m ℝ)
    (hDOpt : DOpt.PosDef) (hKOpt : KOpt.PosDef)
    (hDSam : DSam.PosDef) (hKSam : KSam.PosDef)
    (coordinateOpt : S →L[ℝ] (n → ℝ)) (coordinateSam : Z →L[ℝ] (m → ℝ))
    (hDOptForm : ∀ d, D.optimizerSq d =
      coordinateOpt d ⬝ᵥ (DOpt *ᵥ coordinateOpt d))
    (hDSamForm : ∀ d, D.samplerSq d =
      coordinateSam d ⬝ᵥ (DSam *ᵥ coordinateSam d))
    (hKOptForm : ∀ d, coordinateOpt d ⬝ᵥ (KOpt *ᵥ coordinateOpt d) =
      (β * r - AOpt - ASam) * ‖C.parameterProjection d‖ ^ 2 + C.optimizerAuxSq d)
    (hKSamForm : ∀ zz : Z × Z,
      coordinateSam (zz.1 - zz.2) ⬝ᵥ (KSam *ᵥ coordinateSam (zz.1 - zz.2)) =
      (β * r - AOpt - ASam) * ‖C.positionProjection (zz.1 - zz.2)‖ ^ 2 +
        C.samplerAuxSq zz) :
    let ρ := min (generalizedMinimum hDOpt hKOpt) (generalizedMinimum hDSam hKSam)
    0 < ρ ∧ TwistedJointMonotonicity M D ρ := by
  dsimp
  refine ⟨lt_min (generalizedMinimum_pos hDOpt hKOpt)
    (generalizedMinimum_pos hDSam hKSam), ?_⟩
  apply projected_twistedJointMonotonicity M D C β r AOpt ASam _ hβ hmono haux σ hσ hInt
  · intro d
    calc
      _ ≤ generalizedMinimum hDOpt hKOpt * D.optimizerSq d :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (D.optimizerSq_nonneg d)
      _ ≤ coordinateOpt d ⬝ᵥ (KOpt *ᵥ coordinateOpt d) := by
        rw [hDOptForm]
        exact generalizedMinimum_quadratic hDOpt hKOpt (coordinateOpt d)
      _ = _ := hKOptForm d
  · intro zz
    calc
      _ ≤ generalizedMinimum hDSam hKSam * D.samplerSq (zz.1 - zz.2) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (D.samplerSq_nonneg _)
      _ ≤ coordinateSam (zz.1 - zz.2) ⬝ᵥ (KSam *ᵥ coordinateSam (zz.1 - zz.2)) := by
        rw [hDSamForm]
        exact generalizedMinimum_quadratic hDSam hKSam (coordinateSam (zz.1 - zz.2))
      _ = _ := hKSamForm zz

end Projected
end PBGSO
