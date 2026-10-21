import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

set_option linter.style.header false

/-! # Scaled particle geometry and exact IPLA coordinate updates

The joint potential assumptions imply all lifted convexity and smoothness
properties used by Dalalyan, with no extra geometric hypotheses.
-/

noncomputable section
open scoped BigOperators NNReal

namespace IPLA

/-- The scaled IPLA state: the common parameter followed by `N` particle blocks. -/
abbrev State (N dθ dx : ℕ) := EuclideanSpace ℝ (Fin dθ ⊕ (Fin N × Fin dx))
/-- A parameter-particle pair, with parameter block first. -/
abbrev Joint (dθ dx : ℕ) := EuclideanSpace ℝ (Fin dθ ⊕ Fin dx)

/-- IPLA has one common parameter and `N` latent vectors, in arbitrary,
independent parameter and latent dimensions. -/
@[simp] theorem finrank_state (N dθ dx : ℕ) :
    Module.finrank ℝ (State N dθ dx) = dθ + N * dx := by
  simp [State]

/-- The original joint potential has one parameter block and one latent block. -/
@[simp] theorem finrank_joint (dθ dx : ℕ) :
    Module.finrank ℝ (Joint dθ dx) = dθ + dx := by
  simp [Joint]

/-- Extract the scaled latent vector of particle `i`. -/
def block {N dθ dx : ℕ} (z : State N dθ dx) (i : Fin N) : EuclideanSpace ℝ (Fin dx) :=
  WithLp.toLp 2 (fun j ↦ z (Sum.inr (i, j)))

/-- Pair the common parameter with the unscaled `i`th particle. -/
def joint {N dθ dx : ℕ} (i : Fin N) (z : State N dθ dx) : Joint dθ dx :=
  WithLp.toLp 2 (Sum.elim (fun j ↦ z (Sum.inl j))
    (fun j ↦ Real.sqrt N * z (Sum.inr (i, j))))

@[simp] theorem joint_parameter {N dθ dx : ℕ} (i : Fin N) (z : State N dθ dx)
    (j : Fin dθ) : joint i z (Sum.inl j) = z (Sum.inl j) := rfl

@[simp] theorem joint_particle {N dθ dx : ℕ} (i : Fin N) (z : State N dθ dx)
    (j : Fin dx) : joint i z (Sum.inr j) = Real.sqrt N * z (Sum.inr (i, j)) := rfl

/-- The potential used by ULA after scaling the particles by `1 / sqrt N`. -/
def potential {N dθ dx : ℕ} (U : Joint dθ dx → ℝ) (z : State N dθ dx) : ℝ :=
  ∑ i : Fin N, U (joint i z)

@[simp] theorem joint_add {N dθ dx : ℕ} (i : Fin N) (x y : State N dθ dx) :
    joint i (x + y) = joint i x + joint i y := by
  ext j
  cases j <;> simp [joint, mul_add]

@[simp] theorem joint_smul {N dθ dx : ℕ} (i : Fin N) (a : ℝ) (x : State N dθ dx) :
    joint i (a • x) = a • joint i x := by
  ext j
  cases j <;> simp [joint, mul_left_comm]

@[simp] theorem joint_sub {N dθ dx : ℕ} (i : Fin N) (x y : State N dθ dx) :
    joint i (x - y) = joint i x - joint i y := by
  ext j
  cases j <;> simp [joint, mul_sub]

/-- Squared Euclidean norms of all replicated pairs sum to exactly `N` times
    the squared norm in scaled particle coordinates. -/
theorem joint_norm_sq_sum {N dθ dx : ℕ} (z : State N dθ dx) :
    ∑ i : Fin N, ‖joint i z‖ ^ 2 = (N : ℝ) * ‖z‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type,
    Fintype.sum_prod_type, joint_parameter, joint_particle, mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg N), Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-- Strong convexity of the original pair potential gives `N*m` strong
    convexity of the scaled particle potential, with no extra hypothesis. -/
theorem potential_strongConvex {N dθ dx : ℕ} {U : Joint dθ dx → ℝ} {m : ℝ}
    (hU : StrongConvexOn Set.univ m U) :
    StrongConvexOn Set.univ ((N : ℝ) * m) (@potential N dθ dx U) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i (_ : i ∈ Finset.univ) ↦
    hU.2 (Set.mem_univ (joint i x)) (Set.mem_univ (joint i y)) ha hb hab)
  simpa only [← joint_smul, ← joint_add, ← joint_sub, smul_eq_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, potential, joint_norm_sq_sum,
    mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hsum

/-- The linear joint-pair extraction map. -/
def jointCLM {N dθ dx : ℕ} (i : Fin N) : State N dθ dx →L[ℝ] Joint dθ dx :=
  LinearMap.toContinuousLinearMap
    { toFun := joint i
      map_add' := joint_add i
      map_smul' := joint_smul i }

@[simp] theorem jointCLM_apply {N dθ dx : ℕ} (i : Fin N) (z : State N dθ dx) :
    jointCLM i z = joint i z := rfl

/-- Differentiability survives the finite sum and the coordinate scaling. -/
theorem potential_differentiable {N dθ dx : ℕ} {U : Joint dθ dx → ℝ}
    (hU : Differentiable ℝ U) : Differentiable ℝ (@potential N dθ dx U) := by
  exact Differentiable.fun_sum fun i _ ↦ hU.comp (jointCLM i).differentiable

end IPLA

namespace IPLA

/-- Chain rule for the lifted potential, stated as an inner-product identity. -/
theorem inner_gradient_potential {N dθ dx : ℕ} {U : Joint dθ dx → ℝ}
    (hU : Differentiable ℝ U) (z w : State N dθ dx) :
    inner ℝ (gradient (@potential N dθ dx U) z) w =
      ∑ i : Fin N, inner ℝ (gradient U (joint i z)) (joint i w) := by
  rw [inner_gradient_left]
  have hd : HasFDerivAt (@potential N dθ dx U)
      (∑ i : Fin N, (fderiv ℝ U (joint i z)).comp (jointCLM i)) z :=
    HasFDerivAt.fun_sum (fun i _ ↦
      (hU (joint i z)).hasFDerivAt.comp z (jointCLM i).hasFDerivAt)
  rw [hd.fderiv]
  simp [inner_gradient_left]

/-- Cauchy--Schwarz in the replicated pair coordinates. -/
theorem sum_joint_norm_mul {N dθ dx : ℕ} (v w : State N dθ dx) :
    (∑ i : Fin N, ‖joint i v‖ * ‖joint i w‖) ≤
      (N : ℝ) * ‖v‖ * ‖w‖ := by
  have hs := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (f := fun i : Fin N ↦ ‖joint i v‖) (g := fun i : Fin N ↦ ‖joint i w‖)
  rw [joint_norm_sq_sum, joint_norm_sq_sum] at hs
  have hn : 0 ≤ (N : ℝ) * ‖v‖ * ‖w‖ := by positivity
  nlinarith

/-- Smoothness scales by `N`, exactly as strong convexity does. -/
theorem potential_gradient_lipschitz {N dθ dx : ℕ} {U : Joint dθ dx → ℝ} {L : ℝ≥0}
    (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U)) :
    LipschitzWith ((N : ℝ≥0) * L) (gradient (@potential N dθ dx U)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  have hi (w : State N dθ dx) :
      inner ℝ (gradient (@potential N dθ dx U) x - gradient (@potential N dθ dx U) y) w ≤
        (N : ℝ) * (L : ℝ) * ‖x - y‖ * ‖w‖ := by
    rw [inner_sub_left, inner_gradient_potential hU, inner_gradient_potential hU,
      ← Finset.sum_sub_distrib]
    calc
      ∑ i : Fin N, (inner ℝ (gradient U (joint i x)) (joint i w) -
          inner ℝ (gradient U (joint i y)) (joint i w))
          = ∑ i : Fin N, inner ℝ (gradient U (joint i x) - gradient U (joint i y))
              (joint i w) := by simp [inner_sub_left]
      _ ≤ ∑ i : Fin N, ((L : ℝ) * ‖joint i (x - y)‖) * ‖joint i w‖ := by
        apply Finset.sum_le_sum
        intro i _
        apply (real_inner_le_norm _ _).trans
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simpa only [joint_sub] using hLip.norm_sub_le (joint i x) (joint i y)
      _ = (L : ℝ) * ∑ i : Fin N, ‖joint i (x - y)‖ * ‖joint i w‖ := by
        simp [Finset.mul_sum, mul_assoc]
      _ ≤ (L : ℝ) * ((N : ℝ) * ‖x - y‖ * ‖w‖) :=
        mul_le_mul_of_nonneg_left (sum_joint_norm_mul (x - y) w) L.coe_nonneg
      _ = _ := by ring
  have h := hi (gradient (@potential N dθ dx U) x - gradient (@potential N dθ dx U) y)
  rw [real_inner_self_eq_norm_sq] at h
  simp only [NNReal.coe_mul, NNReal.coe_natCast]
  by_cases hz : ‖gradient (@potential N dθ dx U) x - gradient (@potential N dθ dx U) y‖ = 0
  · rw [hz]
    positivity
  · exact (mul_le_mul_iff_right₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))).mp
      (by simpa [pow_two, mul_comm] using h)

end IPLA

namespace IPLA

@[simp] theorem joint_single_parameter {N dθ dx : ℕ} (i : Fin N) (j : Fin dθ) :
    joint i (EuclideanSpace.single (Sum.inl j) 1 : State N dθ dx) =
      EuclideanSpace.single (Sum.inl j) 1 := by
  ext a
  cases a <;> simp [joint]

@[simp] theorem joint_single_particle {N dθ dx : ℕ} (i q : Fin N) (j : Fin dx) :
    joint q (EuclideanSpace.single (Sum.inr (i, j)) 1 : State N dθ dx) =
      if q = i then EuclideanSpace.single (Sum.inr j) (Real.sqrt N) else 0 := by
  ext a
  cases a <;> by_cases h : q = i <;> simp [joint, h]

/-- The common parameter derivative is the sum of the pair derivatives. -/
theorem gradient_potential_parameter {N dθ dx : ℕ} {U : Joint dθ dx → ℝ}
    (hU : Differentiable ℝ U) (z : State N dθ dx) (j : Fin dθ) :
    gradient (@potential N dθ dx U) z (Sum.inl j) =
      ∑ i : Fin N, gradient U (joint i z) (Sum.inl j) := by
  have h := inner_gradient_potential hU z (EuclideanSpace.single (Sum.inl j) 1)
  simpa only [joint_single_parameter, EuclideanSpace.inner_single_right,
    map_one, one_mul, conj_trivial] using h

/-- The scaled particle derivative is `sqrt N` times the pair derivative. -/
theorem gradient_potential_particle {N dθ dx : ℕ} {U : Joint dθ dx → ℝ}
    (hU : Differentiable ℝ U) (z : State N dθ dx) (i : Fin N) (j : Fin dx) :
    gradient (@potential N dθ dx U) z (Sum.inr (i, j)) =
      Real.sqrt N * gradient U (joint i z) (Sum.inr j) := by
  have h := inner_gradient_potential hU z (EuclideanSpace.single (Sum.inr (i, j)) 1)
  simp only [joint_single_particle, EuclideanSpace.inner_single_right,
    one_mul, conj_trivial] at h
  simpa only [apply_ite, inner_zero_right, EuclideanSpace.inner_single_right,
    conj_trivial, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] using h

end IPLA

namespace IPLA

/-- Project the scaled state to its common parameter vector. -/
def parameterCLM {N dθ dx : ℕ} : State N dθ dx →L[ℝ] EuclideanSpace ℝ (Fin dθ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z ↦ WithLp.toLp 2 (fun j ↦ z (Sum.inl j))
      map_add' := by intro x y; ext j; rfl
      map_smul' := by intro a x; ext j; rfl }

@[simp] theorem parameterCLM_apply {N dθ dx : ℕ} (z : State N dθ dx) (j : Fin dθ) :
    parameterCLM z j = z (Sum.inl j) := rfl

/-- Forgetting the particle coordinates is a contraction. -/
theorem norm_parameterCLM_apply_le {N dθ dx : ℕ} (z : State N dθ dx) :
    ‖parameterCLM z‖ ≤ ‖z‖ := by
  have hs : ‖parameterCLM z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, parameterCLM_apply,
      Fintype.sum_sum_type]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)
  nlinarith [norm_nonneg (parameterCLM z), norm_nonneg z]

/-- The parameter projection has operator norm at most one. -/
theorem norm_parameterCLM_le_one {N dθ dx : ℕ} :
    ‖(@parameterCLM N dθ dx)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound (@parameterCLM N dθ dx) (by norm_num)
    (fun z ↦ by simpa using norm_parameterCLM_apply_le z)

/-- One IPLA step represented in the scaled joint coordinates. -/
def scaledUpdate {N dθ dx : ℕ} (U : Joint dθ dx → ℝ) (h : ℝ)
    (z ξ : State N dθ dx) : State N dθ dx :=
  z - (h / N) • gradient (@potential N dθ dx U) z + Real.sqrt (2 * h / N) • ξ

/-- The common parameter update is exactly the average-gradient IPLA update. -/
theorem scaledUpdate_parameter {N dθ dx : ℕ} {U : Joint dθ dx → ℝ}
    (hU : Differentiable ℝ U) (h : ℝ) (z ξ : State N dθ dx) (j : Fin dθ) :
    scaledUpdate U h z ξ (Sum.inl j) = z (Sum.inl j) -
      (h / N) * (∑ i : Fin N, gradient U (joint i z) (Sum.inl j)) +
      Real.sqrt (2 * h / N) * ξ (Sum.inl j) := by
  simp [scaledUpdate, gradient_potential_parameter hU]

/-- Unscaling a particle coordinate gives its usual IPLA update, including
    the `sqrt (2*h)` noise coefficient. -/
theorem scaledUpdate_particle {N dθ dx : ℕ} {U : Joint dθ dx → ℝ}
    (hN : 0 < N) (hU : Differentiable ℝ U) (h : ℝ)
    (z ξ : State N dθ dx) (i : Fin N) (j : Fin dx) :
    Real.sqrt N * scaledUpdate U h z ξ (Sum.inr (i, j)) =
      Real.sqrt N * z (Sum.inr (i, j)) -
        h * gradient U (joint i z) (Sum.inr j) +
        Real.sqrt (2 * h) * ξ (Sum.inr (i, j)) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hn : Real.sqrt N * Real.sqrt (2 * h / N) = Real.sqrt (2 * h) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg N)]
    congr 1
    field_simp
  simp only [scaledUpdate, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
    smul_eq_mul, gradient_potential_particle hU]
  rw [mul_add, mul_sub]
  have hd : Real.sqrt N * (h / N * (Real.sqrt N *
      gradient U (joint i z) (Sum.inr j))) = h * gradient U (joint i z) (Sum.inr j) := by
    calc
      _ = (Real.sqrt N ^ 2) * (h / N) * gradient U (joint i z) (Sum.inr j) := by ring
      _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]; field_simp
  rw [hd, ← mul_assoc, hn]

end IPLA
