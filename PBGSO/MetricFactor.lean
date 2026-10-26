import PBGSO.PaperTheorems
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Constructing a genuine linear metric factor from positive weights -/
noncomputable section
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace InnerProductSpace BigOperators
namespace PBGSO.MetricFactor
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H]

/-- Every finite-dimensional symmetric nonnegative weight admits an actual
finite Euclidean factor. The factor and its squared-norm identity are proved
from a positive rank-one decomposition, rather than assumed. -/
theorem exists_factor (W : H →L[ℝ] H)
    (hsym : ∀ x y, ⟪x,W y⟫_ℝ = ⟪W x,y⟫_ℝ)
    (hpos : ∀ x, 0≤ ⟪x,W x⟫_ℝ) :
    ∃ m : ℕ, ∃ C : H →L[ℝ] EuclideanSpace ℝ (Fin m),
      ∀ x, ‖C x‖^2= ⟪x,W x⟫_ℝ := by
  classical
  have hp : W.IsPositive := (ContinuousLinearMap.isPositive_iff W).mpr
    ⟨fun x y => (hsym x y).symm,fun x => by rw [real_inner_comm]; exact hpos x⟩
  obtain ⟨m,u,hu⟩ := ContinuousLinearMap.isPositive_iff_eq_sum_rankOne.mp hp
  let C : H →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun i => innerSL ℝ (u i)))
  refine ⟨m,C,fun x => ?_⟩
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ i : Fin m, (⟪u i,x⟫_ℝ)^2)= ⟪x,W x⟫_ℝ
  rw [hu]
  simp only [sum_apply,inner_sum,InnerProductSpace.rankOne_apply,inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm x (u i)]
  ring

omit [FiniteDimensional ℝ H] in
/-- A positive lower quadratic bound gives coercivity of the constructed
factor in the original norm. -/
theorem coercivity {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (W : H →L[ℝ] H) (C : H →L[ℝ] K) (hC : ∀ x, ‖C x‖^2= ⟪x,W x⟫_ℝ)
    (m : ℝ) (hm : 0≤m) (hLower : ∀ x, m*‖x‖^2≤ ⟪x,W x⟫_ℝ) (x : H) :
    Real.sqrt m*‖x‖≤‖C x‖ := by
  apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
  rw [mul_pow,Real.sq_sqrt hm,hC]
  exact hLower x

omit [FiniteDimensional ℝ H] in
/-- The upper quadratic bound supplies a norm bound for the same actual
factor; no arbitrary matrix norm comparison is an input. -/
theorem upper_bound {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (W : H →L[ℝ] H) (C : H →L[ℝ] K) (hC : ∀ x, ‖C x‖^2= ⟪x,W x⟫_ℝ)
    (M : ℝ) (hM : 0≤M) (hUpper : ∀ x, ⟪x,W x⟫_ℝ ≤ M*‖x‖^2) (x : H) :
    ‖C x‖≤Real.sqrt M*‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt hM,hC]
  exact hUpper x

omit [FiniteDimensional ℝ H] in
/-- The constructed squared-norm factor preserves the entire weighted
pairing, by real polarization. -/
theorem pairing {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (W : H →L[ℝ] H) (C : H →L[ℝ] K)
    (hsym : ∀ x y, ⟪x,W y⟫_ℝ = ⟪W x,y⟫_ℝ)
    (hC : ∀ x, ‖C x‖^2 = ⟪x,W x⟫_ℝ) (x y : H) :
    ⟪C x,C y⟫_ℝ = ⟪x,W y⟫_ℝ := by
  have hxy := hC (x+y)
  rw [map_add,norm_add_sq_real] at hxy
  simp only [map_add,inner_add_left,inner_add_right] at hxy
  have hcross : ⟪y,W x⟫_ℝ = ⟪x,W y⟫_ℝ :=
    (real_inner_comm (W x) y).trans (hsym x y).symm
  rw [hC x,hC y,hcross] at hxy
  nlinarith

/-- Strictly positive primitive quadratic bounds construct both a genuine
metric factor and its original-norm comparisons. -/
theorem exists_coercive_factor (W : H →L[ℝ] H)
    (hsym : ∀ x y, ⟪x,W y⟫_ℝ = ⟪W x,y⟫_ℝ)
    (m M : ℝ) (hm : 0<m) (hM : 0≤M)
    (hLower : ∀ x, m*‖x‖^2≤⟪x,W x⟫_ℝ)
    (hUpper : ∀ x, ⟪x,W x⟫_ℝ ≤ M*‖x‖^2) :
    ∃ n : ℕ, ∃ C : H →L[ℝ] EuclideanSpace ℝ (Fin n),
      (∀ x, ‖C x‖^2 = ⟪x,W x⟫_ℝ) ∧
      (∀ x, Real.sqrt m*‖x‖≤‖C x‖) ∧
      (∀ x, ‖C x‖≤Real.sqrt M*‖x‖) := by
  obtain ⟨n,C,hC⟩ := exists_factor W hsym (fun x =>
    (mul_nonneg hm.le (sq_nonneg ‖x‖)).trans (hLower x))
  exact ⟨n,C,hC,coercivity W C hC m hm.le hLower,upper_bound W C hC M hM hUpper⟩
end PBGSO.MetricFactor
