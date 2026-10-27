import UnadjustedLangevin.WeakForwardTaylor
import UnadjustedLangevin.GaussianProposalDensity
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Analysis.InnerProductSpace.Laplacian

set_option linter.style.header false

/-!
# Gaussian cancellation for the Dynkin approximation

These are exact identities for the first and second Taylor terms under the
actual standard Gaussian law. In particular the second-order term is the
Laplacian, with coefficient exactly one for Langevin noise `sqrt (2h)`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace AverageLMC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

/-- The true Gaussian covariance cancels all off-diagonal quadratic terms. -/
theorem integral_gaussian_inner_mul (u v : H) :
    (∫ z : H, inner ℝ u z * inner ℝ v z ∂stdGaussian H) = inner ℝ u v := by
  have hz : MemLp (id : H → H) 2 (stdGaussian H) :=
    IsGaussian.memLp_id (stdGaussian H) 2 (by norm_num)
  have hc := covarianceBilin_apply hz u v
  simp only [id_eq, integral_id_stdGaussian, sub_zero, covarianceBilin_stdGaussian,
    innerSL_apply_apply] at hc
  exact hc.symm

/-- The expectation of a continuous quadratic form is its basis trace. -/
theorem integral_gaussian_bilinear (B : H →L[ℝ] H →L[ℝ] ℝ) :
    (∫ z : H, B z z ∂stdGaussian H) =
      ∑ i : Fin (Module.finrank ℝ H),
        B (stdOrthonormalBasis ℝ H i) (stdOrthonormalBasis ℝ H i) := by
  let b := stdOrthonormalBasis ℝ H
  have hz : MemLp (id : H → H) 2 (stdGaussian H) :=
    IsGaussian.memLp_id (stdGaussian H) 2 (by norm_num)
  have hi (i j : Fin (Module.finrank ℝ H)) :
      Integrable (fun z : H ↦
        (inner ℝ (b i) z * inner ℝ (b j) z) * B (b i) (b j)) (stdGaussian H) :=
    (show MemLp (fun z : H ↦ inner ℝ (b i) z * inner ℝ (b j) z) 1
      (stdGaussian H) from (hz.const_inner (b i)).mul (hz.const_inner (b j)))
        |>.integrable le_rfl |>.mul_const _
  have he (z : H) : B z z =
      ∑ i, ∑ j, (inner ℝ (b i) z * inner ℝ (b j) z) * B (b i) (b j) := by
    calc
      _ = ∑ i, inner ℝ (b i) z * B (b i) z := by
        have hs := congrArg (fun w : H ↦ B w z) (b.sum_repr' z).symm
        simpa only [map_sum, sum_apply, map_smul, smul_apply,
          smul_eq_mul] using hs
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        have hs := congrArg (fun w : H ↦ B (b i) w) (b.sum_repr' z).symm
        simp only [map_sum, map_smul, smul_eq_mul] at hs
        rw [hs, Finset.mul_sum]
        simp only [mul_assoc]
  have hefun : (fun z : H ↦ B z z) =
      fun z ↦ ∑ i, ∑ j,
        (inner ℝ (b i) z * inner ℝ (b j) z) * B (b i) (b j) := funext he
  rw [hefun]
  rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hi i j))]
  congr 1
  ext i
  rw [integral_finsetSum _ (fun j _ ↦ hi i j)]
  simp_rw [integral_mul_const, integral_gaussian_inner_mul]
  simp [orthonormal_iff_ite.mp b.orthonormal, b]

/-- Exact expectation of the quadratic Taylor polynomial for a Gaussian
Euler increment. The final term is the deterministic drift's quadratic term. -/
theorem integral_gaussian_secondOrderExpansion
    (φ : H → ℝ) (x v : H) (h : ℝ) (hh : 0 ≤ h) :
    (∫ z : H, ULA.secondOrderExpansion φ x (h • v + Real.sqrt (2 * h) • z)
      ∂stdGaussian H) =
      φ x + h * (fderiv ℝ φ x v + Laplacian.laplacian φ x) +
        h ^ 2 / 2 * iteratedFDeriv ℝ 2 φ x (fun _ ↦ v) := by
  let D := fderiv ℝ φ x
  let B := fderiv ℝ (fderiv ℝ φ) x
  let s := Real.sqrt (2 * h)
  have hz : MemLp (id : H → H) 2 (stdGaussian H) :=
    IsGaussian.memLp_id (stdGaussian H) 2 (by norm_num)
  have hD : Integrable (fun z : H ↦ D z) (stdGaussian H) :=
    D.integrable_comp (hz.integrable (by norm_num))
  have hBv : Integrable (fun z : H ↦ B v z) (stdGaussian H) :=
    (B v).integrable_comp (hz.integrable (by norm_num))
  have hvB : Integrable (fun z : H ↦ B z v) (stdGaussian H) := by
    exact ((ContinuousLinearMap.apply ℝ ℝ v).comp B).integrable_comp
      (hz.integrable (by norm_num))
  have hBB : Integrable (fun z : H ↦ B z z) (stdGaussian H) := by
    have hquad : MemLp (fun z : H ↦ B z z) 1 (stdGaussian H) :=
      MemLp.of_bilin (fun a b : H ↦ B a b) ‖B‖₊ hz hz
        (by fun_prop) (ae_of_all _ (fun z ↦ by
          exact (B z).le_opNNNorm z |>.trans
            (mul_le_mul_of_nonneg_right (B.le_opNNNorm z) (by positivity))))
    exact hquad.integrable le_rfl
  have hpoly (z : H) :
      ULA.secondOrderExpansion φ x (h • v + s • z) =
        φ x + h * D v + s * D z +
          (h ^ 2 / 2 * B v v + (h * s / 2) * (B v z + B z v) + s ^ 2 / 2 * B z z) := by
    simp only [ULA.secondOrderExpansion, iteratedFDeriv_two_apply,
      map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, D, B]
    ring
  have hmeanD : (∫ z : H, D z ∂stdGaussian H) = 0 := integral_strongDual_stdGaussian D
  have hmeanBv : (∫ z : H, B v z ∂stdGaussian H) = 0 :=
    integral_strongDual_stdGaussian (B v)
  have hmeanvB : (∫ z : H, B z v ∂stdGaussian H) = 0 := by
    exact integral_strongDual_stdGaussian ((ContinuousLinearMap.apply ℝ ℝ v).comp B)
  have htrace : (∫ z : H, B z z ∂stdGaussian H) = Laplacian.laplacian φ x := by
    rw [integral_gaussian_bilinear]
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis φ
      (stdOrthonormalBasis ℝ H)]
    simp [B, iteratedFDeriv_two_apply]
  change (∫ z : H, ULA.secondOrderExpansion φ x (h • v + s • z)
      ∂stdGaussian H) = _
  simp_rw [hpoly]
  have hlin : Integrable (fun z : H ↦ φ x + h * D v + s * D z)
      (stdGaussian H) := (integrable_const (φ x + h * D v)).add (hD.const_mul s)
  have hquad1 : Integrable (fun z : H ↦
      h ^ 2 / 2 * B v v + (h * s / 2) * (B v z + B z v)) (stdGaussian H) :=
    (integrable_const (h ^ 2 / 2 * B v v)).add ((hBv.add hvB).const_mul (h * s / 2))
  have hi0 := integral_add hlin (hquad1.add (hBB.const_mul (s ^ 2 / 2)))
  have hi1 := integral_add (integrable_const (φ x + h * D v)) (hD.const_mul s)
  have hi2 := integral_add hquad1 (hBB.const_mul (s ^ 2 / 2))
  have hi3 := integral_add (integrable_const (h ^ 2 / 2 * B v v))
    ((hBv.add hvB).const_mul (h * s / 2))
  have hi4 := integral_add hBv hvB
  simp only [Pi.add_apply] at hi0 hi1 hi2 hi3 hi4
  rw [hi0, hi1, hi2, hi3]
  simp only [integral_const_mul]
  rw [hi4]
  simp only [integral_const, probReal_univ, one_smul,
      integral_const_mul, hmeanD, hmeanBv, hmeanvB, htrace,
      mul_zero, add_zero, zero_add]
  have hs : s ^ 2 = 2 * h := Real.sq_sqrt (by positivity)
  rw [hs, iteratedFDeriv_two_apply]
  dsimp [D, B]
  ring

end AverageLMC
