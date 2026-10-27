import IPLA.Geometry
import LatentDiffusion.Numerics
import UnadjustedLangevin.StrongConvexity
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

set_option linter.style.header false

/-! # Dataset-dependent scaled cloud geometry

Each coordinate may have a different potential. For IPLD take N here equal
to the paper's M times N, and assign the potential of each datum to its
particle coordinates. The average potential has precisely the original
strong-convexity and gradient-Lipschitz constants, independently of both counts.
-/

noncomputable section
open scoped BigOperators NNReal

namespace LatentDiffusion.Cloud

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
def potential {N dθ dx : ℕ} (U : Fin N → Joint dθ dx → ℝ) (z : State N dθ dx) : ℝ :=
  ∑ i : Fin N, U i (joint i z)

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
theorem potential_strongConvex {N dθ dx : ℕ} {U : Fin N → Joint dθ dx → ℝ} {m : ℝ}
    (hU : ∀ i, StrongConvexOn Set.univ m (U i)) :
    StrongConvexOn Set.univ ((N : ℝ) * m) (@potential N dθ dx U) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i (_ : i ∈ Finset.univ) ↦
    (hU i).2 (Set.mem_univ (joint i x)) (Set.mem_univ (joint i y)) ha hb hab)
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
theorem potential_differentiable {N dθ dx : ℕ} {U : Fin N → Joint dθ dx → ℝ}
    (hU : ∀ i, Differentiable ℝ (U i)) : Differentiable ℝ (@potential N dθ dx U) := by
  exact Differentiable.fun_sum fun i _ ↦ (hU i).comp (jointCLM i).differentiable

end LatentDiffusion.Cloud





namespace LatentDiffusion.Cloud

/-- Chain rule for the lifted potential, stated as an inner-product identity. -/
theorem inner_gradient_potential {N dθ dx : ℕ} {U : Fin N → Joint dθ dx → ℝ}
    (hU : ∀ i, Differentiable ℝ (U i)) (z w : State N dθ dx) :
    inner ℝ (gradient (@potential N dθ dx U) z) w =
      ∑ i : Fin N, inner ℝ (gradient (U i) (joint i z)) (joint i w) := by
  rw [inner_gradient_left]
  have hd : HasFDerivAt (@potential N dθ dx U)
      (∑ i : Fin N, (fderiv ℝ (U i) (joint i z)).comp (jointCLM i)) z :=
    HasFDerivAt.fun_sum (fun i _ ↦
      (hU i (joint i z)).hasFDerivAt.comp z (jointCLM i).hasFDerivAt)
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
theorem potential_gradient_lipschitz {N dθ dx : ℕ} {U : Fin N → Joint dθ dx → ℝ} {L : ℝ≥0}
    (hU : ∀ i, Differentiable ℝ (U i)) (hLip : ∀ i, LipschitzWith L (gradient (U i))) :
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
      ∑ i : Fin N, (inner ℝ (gradient (U i) (joint i x)) (joint i w) -
          inner ℝ (gradient (U i) (joint i y)) (joint i w))
          = ∑ i : Fin N, inner ℝ (gradient (U i) (joint i x) - gradient (U i) (joint i y))
              (joint i w) := by simp [inner_sub_left]
      _ ≤ ∑ i : Fin N, ((L : ℝ) * ‖joint i (x - y)‖) * ‖joint i w‖ := by
        apply Finset.sum_le_sum
        intro i _
        apply (real_inner_le_norm _ _).trans
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simpa only [joint_sub] using (hLip i).norm_sub_le (joint i x) (joint i y)
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

end LatentDiffusion.Cloud

namespace LatentDiffusion.Cloud

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
theorem gradient_potential_parameter {N dθ dx : ℕ} {U : Fin N → Joint dθ dx → ℝ}
    (hU : ∀ i, Differentiable ℝ (U i)) (z : State N dθ dx) (j : Fin dθ) :
    gradient (@potential N dθ dx U) z (Sum.inl j) =
      ∑ i : Fin N, gradient (U i) (joint i z) (Sum.inl j) := by
  have h := inner_gradient_potential hU z (EuclideanSpace.single (Sum.inl j) 1)
  simpa only [joint_single_parameter, EuclideanSpace.inner_single_right,
    map_one, one_mul, conj_trivial] using h

/-- The scaled particle derivative is `sqrt N` times the pair derivative. -/
theorem gradient_potential_particle {N dθ dx : ℕ} {U : Fin N → Joint dθ dx → ℝ}
    (hU : ∀ i, Differentiable ℝ (U i)) (z : State N dθ dx) (i : Fin N) (j : Fin dx) :
    gradient (@potential N dθ dx U) z (Sum.inr (i, j)) =
      Real.sqrt N * gradient (U i) (joint i z) (Sum.inr j) := by
  have h := inner_gradient_potential hU z (EuclideanSpace.single (Sum.inr (i, j)) 1)
  simp only [joint_single_particle, EuclideanSpace.inner_single_right,
    one_mul, conj_trivial] at h
  simpa only [apply_ite, inner_zero_right, EuclideanSpace.inner_single_right,
    conj_trivial, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] using h

end LatentDiffusion.Cloud


namespace LatentDiffusion.Cloud

/-- The actual positive drift force in particle-normalized coordinates.
Here `N` counts all datum-particle pairs, i.e. `M * N` in the paper. -/
def meanForce {N dθ dx : ℕ} (U : Fin N → Joint dθ dx → ℝ)
    (z : State N dθ dx) : State N dθ dx :=
  (N : ℝ)⁻¹ • gradient (potential U) z

/-- Averaging exactly cancels the replicated-pair scaling: the lifted drift
retains the original strong-monotonicity and Lipschitz constants. -/
theorem meanForce_regular {N dθ dx : ℕ} (hN : 0 < N)
    (U : Fin N → Joint dθ dx → ℝ) (m : ℝ) (L : ℝ≥0)
    (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn Set.univ m (U i))
    (hLip : ∀ i, LipschitzWith L (gradient (U i))) :
    LatentDiffusion.ForceRegularity (meanForce U) m L := by
  have hNp : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNp
  constructor
  · intro x y
    have hs := ULA.strong_gradient_monotone (potential_differentiable hdiff)
      (potential_strongConvex hsc) x y
    have hs' := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hNp.le)
    simpa only [meanForce, ← smul_sub, real_inner_smul_left,
      ← mul_assoc, inv_mul_cancel₀ hN0, one_mul] using hs'
  · intro x y
    have hl := (potential_gradient_lipschitz hdiff hLip).norm_sub_le x y
    have hl' := mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr hNp.le)
    simpa only [meanForce, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hNp.le), NNReal.coe_mul, NNReal.coe_natCast,
      ← mul_assoc, inv_mul_cancel₀ hN0, one_mul] using hl'

/-- Synchronous contraction of the actual full-batch IPLD Euler map with
heterogeneous observations. The step restriction is independent of both
the number of data and the number of particles. -/
theorem full_batch_contraction {N dθ dx : ℕ} (hN : 0 < N)
    (U : Fin N → Joint dθ dx → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn Set.univ m (U i))
    (hLip : ∀ i, LipschitzWith L (gradient (U i)))
    (hs : LatentDiffusion.StableStep m L h) (x y ξ : State N dθ dx) :
    ‖LatentDiffusion.eulerStep (meanForce U) h x ξ -
      LatentDiffusion.eulerStep (meanForce U) h y ξ‖ ≤
        (1 - m * h / 2) * ‖x - y‖ :=
  LatentDiffusion.euler_contraction _ m h L
    (meanForce_regular hN U m L hdiff hsc hLip) hs x y ξ

end LatentDiffusion.Cloud

namespace LatentDiffusion.Cloud

/-- Full-batch numerical update. The input has standard Gaussian particle
coordinates and zero parameter coordinates in the paper's implementation. -/
def fullBatchStep {N dθ dx : ℕ} (U : Fin N → Joint dθ dx → ℝ) (h : ℝ)
    (z ξ : State N dθ dx) : State N dθ dx :=
  LatentDiffusion.eulerStep (meanForce U) h z (Real.sqrt (2 * h / N) • ξ)

/-- The parameter update is exactly the empirical gradient average. -/
theorem fullBatchStep_parameter {N dθ dx : ℕ} (U : Fin N → Joint dθ dx → ℝ)
    (hdiff : ∀ i, Differentiable ℝ (U i)) (h : ℝ) (z ξ : State N dθ dx)
    (j : Fin dθ) (hξ : ξ (Sum.inl j) = 0) :
    fullBatchStep U h z ξ (Sum.inl j) = z (Sum.inl j) -
      (h / N) * ∑ i, gradient (U i) (joint i z) (Sum.inl j) := by
  simp [fullBatchStep, LatentDiffusion.eulerStep, meanForce,
    gradient_potential_parameter hdiff, hξ, div_eq_mul_inv, mul_assoc]

/-- The physical latent update has the manuscript's `sqrt (2h)` noise,
with an individual datum-particle force and no extra factor of `M` or `N`. -/
theorem fullBatchStep_particle {N dθ dx : ℕ} (hN : 0 < N)
    (U : Fin N → Joint dθ dx → ℝ) (hdiff : ∀ i, Differentiable ℝ (U i))
    (h : ℝ) (z ξ : State N dθ dx) (i : Fin N) (j : Fin dx) :
    Real.sqrt N * fullBatchStep U h z ξ (Sum.inr (i, j)) =
      Real.sqrt N * z (Sum.inr (i, j)) -
        h * gradient (U i) (joint i z) (Sum.inr j) +
        Real.sqrt (2 * h) * ξ (Sum.inr (i, j)) := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hn : Real.sqrt N * Real.sqrt (2 * h / N) = Real.sqrt (2 * h) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg N)]
    congr 1
    field_simp
  simp only [fullBatchStep, LatentDiffusion.eulerStep, meanForce,
    PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    gradient_potential_particle hdiff]
  rw [mul_add, mul_sub]
  have hd : Real.sqrt N * (h * ((N : ℝ)⁻¹ * (Real.sqrt N *
      gradient (U i) (joint i z) (Sum.inr j)))) =
        h * gradient (U i) (joint i z) (Sum.inr j) := by
    calc
      _ = (Real.sqrt N ^ 2) * (h / N) * gradient (U i) (joint i z) (Sum.inr j) := by ring
      _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]; field_simp
  rw [hd, ← mul_assoc, hn]

end LatentDiffusion.Cloud
