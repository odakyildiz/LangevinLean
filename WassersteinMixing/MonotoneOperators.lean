import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Topology.Order.MonotoneConvergence

/-! # Strong limits of increasing bounded positive operators

This supplies the monotone convergence step in the direct semigroup Poisson
construction. The limit is an actual bounded operator, not a postulated solution.
-/
noncomputable section
set_option linter.style.header false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter
open scoped Topology InnerProductSpace

namespace WassersteinMixing
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H

/-- The quadratic estimate behind strong monotone convergence. -/
theorem positive_operator_square_le (A : H →L[ℂ] H) (c : ℝ)
    (hA : 0 ≤ A) (hupper : A ≤ c • (1 : H →L[ℂ] H)) (x : H) :
    ‖A x‖ ^ 2 ≤ c * inner ℝ (A x) x := by
  have hc : Commute (c • (1 : H →L[ℂ] H) - A) A := by
    exact (Commute.smul_left (Commute.one_left A) c).sub_left (Commute.refl A)
  have hp := (ContinuousLinearMap.nonneg_iff_isPositive.mp
    (Commute.mul_nonneg (sub_nonneg.mpr hupper) hA hc)).re_inner_nonneg_left x
  change 0 ≤ inner ℝ ((c • (1 : H →L[ℂ] H) - A) (A x)) x at hp
  simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left,
    real_inner_smul_left] at hp
  have hs := (ContinuousLinearMap.nonneg_iff_isPositive.mp hA).isSymmetric (A x) x
  change inner ℂ (A (A x)) x = inner ℂ (A x) (A x) at hs
  have heq : inner ℝ (A (A x)) x = ‖A x‖ ^ 2 := by
    change RCLike.re (inner ℂ (A (A x)) x) = _
    rw [hs, inner_self_eq_norm_sq]
  rw [heq] at hp
  linarith

/-- An increasing sequence of positive operators bounded by a scalar identity
has pointwise Cauchy orbits. -/
theorem monotone_operator_cauchy (A : ℕ → H →L[ℂ] H) (c : ℝ) (hc : 0 ≤ c)
    (hmono : Monotone A) (hpos : ∀ n, 0 ≤ A n)
    (hupper : ∀ n, A n ≤ c • (1 : H →L[ℂ] H)) (x : H) :
    CauchySeq (fun n ↦ A n x) := by
  let a : ℕ → ℝ := fun n ↦ inner ℝ (A n x) x
  have hqmono : Monotone a := by
    intro n m hnm
    have hp := (ContinuousLinearMap.le_def.mp (hmono hnm)).re_inner_nonneg_left x
    change 0 ≤ inner ℝ ((A m - A n) x) x at hp
    simpa only [a, sub_apply, inner_sub_left, sub_nonneg] using hp
  have hqbdd : BddAbove (Set.range a) := by
    refine ⟨c * ‖x‖ ^ 2, ?_⟩
    rintro _ ⟨n, rfl⟩
    have hp := (ContinuousLinearMap.le_def.mp (hupper n)).re_inner_nonneg_left x
    change 0 ≤ inner ℝ ((c • (1 : H →L[ℂ] H) - A n) x) x at hp
    simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left,
      real_inner_smul_left, real_inner_self_eq_norm_sq] at hp
    change a n ≤ c * ‖x‖ ^ 2
    linarith
  have hqcauchy := (tendsto_atTop_ciSup hqmono hqbdd).cauchySeq
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hδ : 0 < ε ^ 2 / (c + 1) := div_pos (sq_pos_of_pos hε) (by linarith)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hqcauchy _ hδ
  refine ⟨N, ?_⟩
  intro n hn m hm
  have hordered (i j : ℕ) (hi : N ≤ i) (hj : N ≤ j) (hij : i ≤ j) :
      dist (A i x) (A j x) < ε := by
    have hdpos : 0 ≤ A j - A i := sub_nonneg.mpr (hmono hij)
    have hdupper : A j - A i ≤ c • (1 : H →L[ℂ] H) := by
      exact (sub_le_self _ (hpos i)).trans (hupper j)
    have hsq := positive_operator_square_le (A j - A i) c hdpos hdupper x
    have hsmall := hN i hi j hj
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hqmono hij))] at hsmall
    simp only [sub_apply, inner_sub_left] at hsq
    change ‖A j x - A i x‖ ^ 2 ≤ c * (a j - a i) at hsq
    have hmul : c * (a j - a i) < ε ^ 2 := by
      have hle := mul_le_mul_of_nonneg_left hsmall.le hc
      have heq : c * (ε ^ 2 / (c + 1)) < ε ^ 2 := by
        rw [← mul_div_assoc, div_lt_iff₀ (by linarith : 0 < c + 1)]
        nlinarith [sq_pos_of_pos hε]
      exact hle.trans_lt heq
    rw [dist_comm, dist_eq_norm]
    nlinarith [norm_nonneg (A j x - A i x)]
  rcases le_total n m with hnm | hmn
  · exact hordered n m hn hm hnm
  · simpa only [dist_comm] using hordered m n hm hn hmn

/-- Existence of the bounded linear strong limit, with the same scalar norm
bound and pointwise convergence on every vector. -/
theorem exists_monotone_operator_limit (A : ℕ → H →L[ℂ] H) (c : ℝ) (hc : 0 ≤ c)
    (hmono : Monotone A) (hpos : ∀ n, 0 ≤ A n)
    (hupper : ∀ n, A n ≤ c • (1 : H →L[ℂ] H)) :
    ∃ G : H →L[ℂ] H, ‖G‖ ≤ c ∧
      ∀ x, Tendsto (fun n ↦ A n x) atTop (𝓝 (G x)) := by
  have hex (x : H) : ∃ y, Tendsto (fun n ↦ A n x) atTop (𝓝 y) :=
    cauchySeq_tendsto_of_complete (monotone_operator_cauchy A c hc hmono hpos hupper x)
  choose g hg using hex
  have hbound (x : H) : ‖g x‖ ≤ c * ‖x‖ := by
    apply le_of_tendsto (hg x).norm
    filter_upwards [] with n
    have hn : ‖A n‖ ≤ c :=
      (CStarAlgebra.norm_le_iff_le_algebraMap (A n) hc (hpos n)).mpr (by
        simpa only [Algebra.algebraMap_eq_smul_one] using hupper n)
    exact ((A n).le_opNorm x).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg x))
  let L : H →ₗ[ℂ] H :=
    { toFun := g
      map_add' := by
        intro x y
        apply tendsto_nhds_unique (hg (x + y))
        simpa only [map_add] using (hg x).add (hg y)
      map_smul' := by
        intro a x
        apply tendsto_nhds_unique (hg (a • x))
        simpa only [map_smul, RingHom.id_apply] using (hg x).const_smul a }
  refine ⟨L.mkContinuous c hbound, ?_, hg⟩
  exact L.mkContinuous_norm_le hc hbound

/-- Positivity and the scalar upper bound pass to the constructed strong limit. -/
theorem strong_limit_order (A : ℕ → H →L[ℂ] H) (G : H →L[ℂ] H) (c : ℝ)
    (hpos : ∀ n, 0 ≤ A n) (hupper : ∀ n, A n ≤ c • (1 : H →L[ℂ] H))
    (hlim : ∀ x, Tendsto (fun n ↦ A n x) atTop (𝓝 (G x))) :
    0 ≤ G ∧ G ≤ c • (1 : H →L[ℂ] H) := by
  have hsym : G.IsSymmetric := by
    intro x y
    have hs (n : ℕ) := (ContinuousLinearMap.nonneg_iff_isPositive.mp (hpos n)).isSymmetric x y
    change inner ℂ (G x) y = inner ℂ x (G y)
    apply tendsto_nhds_unique ((hlim x).inner tendsto_const_nhds)
    convert tendsto_const_nhds.inner (hlim y) using 1
    exact funext hs
  constructor
  · apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
    refine ⟨hsym, ?_⟩
    intro x
    change 0 ≤ inner ℝ (G x) x
    apply ge_of_tendsto ((hlim x).inner (𝕜 := ℝ) (tendsto_const_nhds (x := x)))
    filter_upwards [] with n
    exact (ContinuousLinearMap.nonneg_iff_isPositive.mp (hpos n)).re_inner_nonneg_left x
  · apply ContinuousLinearMap.le_def.mpr
    refine ⟨(IsSelfAdjoint.all c).smul (IsSelfAdjoint.one _)
      |>.sub hsym.isSelfAdjoint |>.isSymmetric, ?_⟩
    intro x
    change 0 ≤ inner ℝ ((c • (1 : H →L[ℂ] H) - G) x) x
    have ht := (tendsto_const_nhds (x := c • x) |>.sub (hlim x)).inner
      (𝕜 := ℝ) (tendsto_const_nhds (x := x))
    change 0 ≤ inner ℝ (c • x - G x) x
    apply ge_of_tendsto ht
    filter_upwards [] with n
    exact (ContinuousLinearMap.le_def.mp (hupper n)).re_inner_nonneg_left x

/-- A bounded self-adjoint operator that commutes with a nonnegative energy
operator contracts that energy by its squared norm bound. -/
theorem commuting_energy_bound (G B : H →L[ℂ] H) (h : ℝ) (hh : 0 ≤ h)
    (hG : IsSelfAdjoint G) (hnorm : ‖G‖ ≤ h) (hB : 0 ≤ B)
    (hcomm : Commute G B) (x : H) :
    inner ℝ (G x) (B (G x)) ≤ h ^ 2 * inner ℝ x (B x) := by
  have hs (u v : H) : inner ℝ (G u) v = inner ℝ u (G v) := by
    have hc := hG.isSymmetric u v
    change inner ℂ (G u) v = inner ℂ u (G v) at hc
    exact congrArg RCLike.re hc
  let Q : H →L[ℂ] H := h ^ 2 • (1 : H →L[ℂ] H) - G * G
  have hQ : 0 ≤ Q := by
    apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
    apply ContinuousLinearMap.isPositive_def'.mpr
    refine ⟨?_, ?_⟩
    · exact ((IsSelfAdjoint.all (h ^ 2)).smul (IsSelfAdjoint.one _)).sub
        (by simpa only [pow_two] using hG.pow 2)
    · intro y
      change 0 ≤ inner ℝ (Q y) y
      simp only [Q, sub_apply, smul_apply, one_apply_eq_self, mul_apply_eq_comp,
        inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
      rw [hs (G y) y, real_inner_self_eq_norm_sq]
      have hn := (G.le_opNorm y).trans
        (mul_le_mul_of_nonneg_right hnorm (norm_nonneg y))
      have hsq := mul_self_le_mul_self (norm_nonneg (G y)) hn
      nlinarith only [hsq]
  have hQB : Commute Q B :=
    ((Commute.one_left B).smul_left (h ^ 2)).sub_left (hcomm.mul_left hcomm)
  have hp := (ContinuousLinearMap.nonneg_iff_isPositive.mp
    (Commute.mul_nonneg hQ hB hQB)).re_inner_nonneg_left x
  change 0 ≤ inner ℝ (Q (B x)) x at hp
  simp only [Q, sub_apply, smul_apply, one_apply_eq_self, mul_apply_eq_comp,
    inner_sub_left, real_inner_smul_left] at hp
  rw [hs (G (B x)) x] at hp
  have heq : G (B x) = B (G x) :=
    congrArg (fun T : H →L[ℂ] H ↦ T x) hcomm.eq
  rw [heq] at hp
  nlinarith [real_inner_comm (B (G x)) (G x), real_inner_comm (B x) x]

end WassersteinMixing
