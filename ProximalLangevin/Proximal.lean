import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Abel

set_option linter.style.header false

/-!
# Proximity mappings and their variational characterization

The proximal point is defined by the actual quadratic minimization problem.
The existence theorem uses convexity, finite dimensionality, and a lower bound;
no regularity or optimality conclusions are stored as assumptions.
-/

open Set Metric
open scoped RealInnerProductSpace

namespace ProximalLangevin

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Objective minimized by the proximity mapping with parameter `lam`. -/
def proxObjective (f : E → ℝ) (lam : ℝ) (x p : E) : ℝ :=
  f p + ‖p - x‖ ^ 2 / (2 * lam)

/-- `p` solves the actual unconstrained proximity minimization problem at `x`. -/
def IsProxPoint (f : E → ℝ) (lam : ℝ) (x p : E) : Prop :=
  ∀ y, proxObjective f lam x p ≤ proxObjective f lam x y

/-- The global supporting-hyperplane characterization of a convex subgradient. -/
def IsSubgradient (f : E → ℝ) (p g : E) : Prop :=
  ∀ y, f p + ⟪g, y - p⟫ ≤ f y

/-- Subgradients are monotone. -/
theorem IsSubgradient.monotone {f : E → ℝ} {p q g h : E}
    (hp : IsSubgradient f p g) (hq : IsSubgradient f q h) :
    0 ≤ ⟪g - h, p - q⟫ := by
  have hpq := hp q
  have hqp := hq p
  rw [show q - p = -(p - q) by abel, inner_neg_right] at hpq
  simp only [inner_sub_left]
  linarith

/-- A residual subgradient is sufficient for proximal optimality. -/
theorem isProxPoint_of_subgradient {f : E → ℝ} {lam : ℝ} (hlam : 0 < lam)
    {x p : E} (hp : IsSubgradient f p (lam⁻¹ • (x - p))) :
    IsProxPoint f lam x p := by
  intro y
  have h := hp y
  simp only [real_inner_smul_left] at h
  have heq : ‖y - x‖ ^ 2 = ‖p - x‖ ^ 2 + 2 * ⟪p - x, y - p⟫ +
      ‖y - p‖ ^ 2 := by
    rw [show y - x = (p - x) + (y - p) by abel, norm_add_sq_real]
  have hi : ⟪x - p, y - p⟫ = -⟪p - x, y - p⟫ := by
    rw [show x - p = -(p - x) by abel, inner_neg_left]
  rw [hi] at h
  unfold proxObjective
  apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < 2 * lam)).mp
  have h' : lam * (f p - f y) ≤ ⟪p - x, y - p⟫ := by
    have := (mul_le_mul_of_nonneg_left h hlam.le)
    field_simp at this
    nlinarith
  field_simp
  nlinarith [sq_nonneg ‖y - p‖]

/-- Convex proximal minimizers satisfy the residual subgradient inequality. -/
theorem subgradient_of_isProxPoint {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    {lam : ℝ} (hlam : 0 < lam) {x p : E} (hp : IsProxPoint f lam x p) :
    IsSubgradient f p (lam⁻¹ • (x - p)) := by
  intro y
  simp only [real_inner_smul_left]
  apply le_of_forall_pos_le_add
  intro eps heps
  let t := min (1 : ℝ) (eps * (2 * lam) / (‖y - p‖ ^ 2 + 1))
  have ht : 0 < t := lt_min zero_lt_one (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have hteps : t * ‖y - p‖ ^ 2 ≤ eps * (2 * lam) := by
    have hbound : t * (‖y - p‖ ^ 2 + 1) ≤ eps * (2 * lam) :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    nlinarith [sq_nonneg ‖y - p‖]
  have hconv := hf.2 (mem_univ p) (mem_univ y) (sub_nonneg.mpr ht1) ht.le
    (show 1 - t + t = 1 by ring)
  have hmin := hp ((1 - t) • p + t • y)
  have heq : (1 - t) • p + t • y - x = (p - x) + t • (y - p) := by
    simp only [sub_smul, one_smul, smul_sub]
    abel
  unfold proxObjective at hmin
  rw [heq, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos ht, mul_pow] at hmin
  simp only [smul_eq_mul] at hconv
  have hi : ⟪x - p, y - p⟫ = -⟪p - x, y - p⟫ := by
    rw [show x - p = -(p - x) by abel, inner_neg_left]
  rw [hi]
  have hstep : f p - lam⁻¹ * ⟪p - x, y - p⟫ ≤
      f y + t * ‖y - p‖ ^ 2 / (2 * lam) := by
    have : t * (2 * lam * (f p - f y) - 2 * ⟪p - x, y - p⟫ -
        t * ‖y - p‖ ^ 2) ≤ 0 := by
      field_simp at hmin
      nlinarith
    have hcancel := nonpos_of_mul_nonpos_right this ht
    apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < 2 * lam)).mp
    field_simp
    nlinarith
  have herr : t * ‖y - p‖ ^ 2 / (2 * lam) ≤ eps :=
    (div_le_iff₀ (by positivity)).mpr hteps
  linarith

/-- Exact convex proximal optimality condition. -/
theorem isProxPoint_iff_subgradient {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    {lam : ℝ} (hlam : 0 < lam) {x p : E} :
    IsProxPoint f lam x p ↔ IsSubgradient f p (lam⁻¹ • (x - p)) :=
  ⟨subgradient_of_isProxPoint hf hlam, isProxPoint_of_subgradient hlam⟩

/-- Firm nonexpansiveness follows from convex proximal optimality. -/
theorem IsProxPoint.firm {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    {lam : ℝ} (hlam : 0 < lam) {x y p q : E}
    (hp : IsProxPoint f lam x p) (hq : IsProxPoint f lam y q) :
    ‖p - q‖ ^ 2 ≤ ⟪x - y, p - q⟫ := by
  have h := (subgradient_of_isProxPoint hf hlam hp).monotone
    (subgradient_of_isProxPoint hf hlam hq)
  rw [← smul_sub, real_inner_smul_left] at h
  have hh : 0 ≤ ⟪(x - p) - (y - q), p - q⟫ := by
    exact nonneg_of_mul_nonneg_right h (inv_pos.mpr hlam)
  have heq : (x - p) - (y - q) = (x - y) - (p - q) := by abel
  rw [heq, inner_sub_left, real_inner_self_eq_norm_sq] at hh
  linarith

/-- The proximal minimizer is unique. -/
theorem IsProxPoint.unique {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    {lam : ℝ} (hlam : 0 < lam) {x p q : E}
    (hp : IsProxPoint f lam x p) (hq : IsProxPoint f lam x q) : p = q := by
  have h := hp.firm hf hlam hq
  simp only [sub_self, inner_zero_left] at h
  have : ‖p - q‖ = 0 := by nlinarith [norm_nonneg (p - q)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- Proximal minimizers are nonexpansive in the input. -/
theorem IsProxPoint.nonexpansive {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    {lam : ℝ} (hlam : 0 < lam) {x y p q : E}
    (hp : IsProxPoint f lam x p) (hq : IsProxPoint f lam y q) :
    ‖p - q‖ ≤ ‖x - y‖ := by
  have h := hp.firm hf hlam hq
  have hc := real_inner_le_norm (x - y) (p - q)
  nlinarith [norm_nonneg (p - q), norm_nonneg (x - y)]

/-- The residual of the proximal mapping is also nonexpansive. -/
theorem IsProxPoint.residual_nonexpansive {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    {lam : ℝ} (hlam : 0 < lam) {x y p q : E}
    (hp : IsProxPoint f lam x p) (hq : IsProxPoint f lam y q) :
    ‖(x - p) - (y - q)‖ ≤ ‖x - y‖ := by
  have h := hp.firm hf hlam hq
  have heq : (x - p) - (y - q) = (x - y) - (p - q) := by abel
  rw [heq]
  have hs := norm_sub_sq_real (x - y) (p - q)
  nlinarith [norm_nonneg ((x - y) - (p - q)), norm_nonneg (x - y)]

/-- Existence of proximal minimizers for finite-valued convex potentials bounded below.
Finite-valued convex functions are automatically continuous in finite dimensions. -/
theorem exists_proxPoint [FiniteDimensional ℝ E] {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hb : ∃ b, ∀ z, b ≤ f z)
    {lam : ℝ} (hlam : 0 < lam) (x : E) : ∃ p, IsProxPoint f lam x p := by
  obtain ⟨b, hb⟩ := hb
  let R := Real.sqrt (2 * lam * (f x - b)) + 1
  have hxb : 0 ≤ f x - b := sub_nonneg.mpr (hb x)
  have hR : 0 < R := by dsimp [R]; positivity
  have hcont : Continuous (proxObjective f lam x) := by
    unfold proxObjective
    exact hf.locallyLipschitz.continuous.add
      (((continuous_id.sub continuous_const).norm.pow 2).div_const _)
  obtain ⟨p, hp, hmin⟩ := (isCompact_closedBall x R).exists_isMinOn
    ⟨x, mem_closedBall_self hR.le⟩ hcont.continuousOn
  refine ⟨p, fun y => ?_⟩
  by_cases hy : y ∈ closedBall x R
  · exact hmin hy
  have hpx : proxObjective f lam x p ≤ f x := by
    simpa [proxObjective] using hmin (mem_closedBall_self hR.le)
  apply hpx.trans
  have hyR : R < ‖y - x‖ := by
    simpa [mem_closedBall, dist_eq_norm_sub, not_le] using hy
  have hsqrt : (Real.sqrt (2 * lam * (f x - b))) ^ 2 = 2 * lam * (f x - b) :=
    Real.sq_sqrt (mul_nonneg (by positivity) hxb)
  have hsq : 2 * lam * (f x - b) ≤ ‖y - x‖ ^ 2 := by
    dsimp [R] at hyR
    nlinarith [Real.sqrt_nonneg (2 * lam * (f x - b))]
  have hquot : f x - b ≤ ‖y - x‖ ^ 2 / (2 * lam) :=
    (le_div_iff₀ (by positivity)).mpr (by nlinarith)
  unfold proxObjective
  linarith [hb y]

/-- Choice of a true proximal minimizer, with zero as a harmless value off the existence domain. -/
def prox (f : E → ℝ) (lam : ℝ) (x : E) : E := by
  classical
  exact if h : ∃ p, IsProxPoint f lam x p then Classical.choose h else 0

/-- On its mathematical domain, `prox` attains the quadratic minimum. -/
theorem prox_isProxPoint [FiniteDimensional ℝ E] {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hb : ∃ b, ∀ z, b ≤ f z)
    {lam : ℝ} (hlam : 0 < lam) (x : E) : IsProxPoint f lam x (prox f lam x) := by
  classical
  have h := exists_proxPoint hf hb hlam x
  simp only [prox, dite_eq_left h]
  exact Classical.choose_spec h

end

end ProximalLangevin
