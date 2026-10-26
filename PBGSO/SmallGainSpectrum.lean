import PBGSO.SeparatedSchur
import Mathlib.Analysis.Matrix.PosDef

/-! # Exact spectral identification of the source small-gain matrix

The explicit scalar rate is identified with the minimum of the actual two
matrix eigenvalues in Mathlib's spectral theorem. Thus the determinant
criterion produces the manuscript's spectral rate, not just a lower bound.
-/
noncomputable section
open MeasureTheory
open scoped Matrix NNReal
namespace PBGSO

/-- The actual symmetric two-by-two small-gain matrix. -/
def smallGainMatrix (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a, -c / 2; -c / 2, b]

theorem smallGainMatrix_isHermitian (a b c : ℝ) : (smallGainMatrix a b c).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [smallGainMatrix, Matrix.conjTranspose_apply]

/-- The explicit smaller-root formula is the actual minimum eigenvalue,
independent of the arbitrary indexing of the orthonormal eigenbasis. -/
theorem smallGainMatrix_min_eigenvalue (a b c : ℝ) :
    min ((smallGainMatrix_isHermitian a b c).eigenvalues 0)
      ((smallGainMatrix_isHermitian a b c).eigenvalues 1) = smallGainSpectralRate a b c := by
  let H := smallGainMatrix_isHermitian a b c
  let eigs := H.eigenvalues
  have ht : a + b = eigs 0 + eigs 1 := by
    have h := H.trace_eq_sum_eigenvalues
    simpa [smallGainMatrix, Matrix.trace, Fin.sum_univ_two, eigs, H] using h
  have hd : a * b - c ^ 2 / 4 = eigs 0 * eigs 1 := by
    have h := H.det_eq_prod_eigenvalues
    simp [smallGainMatrix, Matrix.det_fin_two, Fin.prod_univ_two] at h
    change a * b - -c / 2 * (-c / 2) = eigs 0 * eigs 1 at h
    nlinarith only [h]
  have htsq : (a + b) ^ 2 = (eigs 0 + eigs 1) ^ 2 := congrArg (fun x => x ^ 2) ht
  have hs := Real.sq_sqrt (show 0 ≤ (a - b) ^ 2 + c ^ 2 by positivity)
  have hp := Real.sqrt_nonneg ((a - b) ^ 2 + c ^ 2)
  change min (eigs 0) (eigs 1) = _
  by_cases ho : eigs 0 ≤ eigs 1
  · have he : Real.sqrt ((a - b) ^ 2 + c ^ 2) = eigs 1 - eigs 0 := by
      apply (sq_eq_sq₀ hp (sub_nonneg.mpr ho)).mp
      nlinarith [htsq]
    rw [min_eq_left ho]
    dsimp only [smallGainSpectralRate]
    rw [he]
    linarith
  · have ho' : eigs 1 ≤ eigs 0 := (le_of_not_ge ho)
    have he : Real.sqrt ((a - b) ^ 2 + c ^ 2) = eigs 0 - eigs 1 := by
      apply (sq_eq_sq₀ hp (sub_nonneg.mpr ho')).mp
      nlinarith [htsq]
    rw [min_eq_right ho']
    dsimp only [smallGainSpectralRate]
    rw [he]
    linarith

/-- The three strict small-gain conditions imply actual matrix positive
definiteness, as well as a positive scalar lower-bound certificate. -/
theorem smallGainMatrix_posDef {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hdet : c ^ 2 < 4 * a * b) : (smallGainMatrix a b c).PosDef := by
  apply (smallGainMatrix_isHermitian a b c).posDef_iff_eigenvalues_pos.mpr
  have hp := smallGainSpectralRate_pos ha hb hdet
  rw [← smallGainMatrix_min_eigenvalue] at hp
  intro i
  fin_cases i
  · exact hp.trans_le (min_le_left _ _)
  · exact hp.trans_le (min_le_right _ _)

variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype I]

/-- The source's matrix H, with its actual metric condition number. -/
def separatedSmallGainMatrix (D : TwistedGeometry S Z) (rO rS : ℝ)
    (LΨ LF Lb Lσ : ℝ≥0) : Matrix (Fin 2) (Fin 2) ℝ :=
  smallGainMatrix
    (rO - D.conditionNumber * (Lσ : ℝ) ^ 2 / 2)
    (rS - D.conditionNumber * (Lσ : ℝ) ^ 2 / 2)
    (Real.sqrt D.conditionNumber * ((LΨ : ℝ) * (LF : ℝ) + (Lb : ℝ)))

theorem separatedSmallGainMatrix_isHermitian (D : TwistedGeometry S Z) (rO rS : ℝ)
    (LΨ LF Lb Lσ : ℝ≥0) :
    (separatedSmallGainMatrix D rO rS LΨ LF Lb Lσ).IsHermitian :=
  smallGainMatrix_isHermitian _ _ _

/-- The actual minimum of the two matrix eigenvalues, as in the source. -/
def separatedMinimumEigenvalue (D : TwistedGeometry S Z) (rO rS : ℝ)
    (LΨ LF Lb Lσ : ℝ≥0) : ℝ :=
  min ((separatedSmallGainMatrix_isHermitian D rO rS LΨ LF Lb Lσ).eigenvalues 0)
    ((separatedSmallGainMatrix_isHermitian D rO rS LΨ LF Lb Lσ).eigenvalues 1)

theorem separatedMinimumEigenvalue_eq_rate (D : TwistedGeometry S Z) (rO rS : ℝ)
    (LΨ LF Lb Lσ : ℝ≥0) :
    separatedMinimumEigenvalue D rO rS LΨ LF Lb Lσ =
      separatedSpectralRate D rO rS LΨ LF Lb Lσ :=
  smallGainMatrix_min_eigenvalue _ _ _

/-- Full source small-gain corollary: the three primitive scalar conditions
give positive-definite H and actual law-level joint monotonicity with rate
equal to the actual minimum matrix eigenvalue. -/
theorem separated_source_criterion (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    (rO rS : ℝ) (LΨ LF Lb Lσ : ℝ≥0)
    (H : SeparatedAssumptions M D rO rS LΨ LF Lb Lσ)
    (hO : 0 < 2 * rO - D.conditionNumber * (Lσ : ℝ) ^ 2)
    (hS : 0 < 2 * rS - D.conditionNumber * (Lσ : ℝ) ^ 2)
    (hdet : D.conditionNumber * ((LΨ : ℝ) * (LF : ℝ) + (Lb : ℝ)) ^ 2 <
      (2 * rO - D.conditionNumber * (Lσ : ℝ) ^ 2) *
        (2 * rS - D.conditionNumber * (Lσ : ℝ) ^ 2)) :
    (separatedSmallGainMatrix D rO rS LΨ LF Lb Lσ).PosDef ∧
      0 < separatedMinimumEigenvalue D rO rS LΨ LF Lb Lσ ∧
      TwistedJointMonotonicity M D (separatedMinimumEigenvalue D rO rS LΨ LF Lb Lσ) := by
  have hp : 0 < separatedMinimumEigenvalue D rO rS LΨ LF Lb Lσ := by
    rw [separatedMinimumEigenvalue_eq_rate]
    exact separatedSpectralRate_pos D rO rS LΨ LF Lb Lσ hO hS hdet
  refine ⟨?_, hp, ?_⟩
  · apply (separatedSmallGainMatrix_isHermitian D rO rS LΨ LF Lb Lσ).posDef_iff_eigenvalues_pos.mpr
    intro i
    fin_cases i
    · exact hp.trans_le (min_le_left _ _)
    · exact hp.trans_le (min_le_right _ _)
  · rw [separatedMinimumEigenvalue_eq_rate]
    exact separated_joint_monotonicity_spectral M D H

end PBGSO
