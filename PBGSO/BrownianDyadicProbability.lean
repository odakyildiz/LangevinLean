import PBGSO.BrownianFourthMoment
import PBGSO.DyadicInterpolationLimit

/-! # Actual Gaussian laws yield continuous dyadic polygon limits
A fourth-moment Markov estimate for the actual finite sum of adjacent
increments derives summable tail probabilities. Borel–Cantelli then supplies
one eventual grid bound and an actual continuous uniform polygon limit on
every fixed rescaled horizon, without any original path-continuity premise.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology
namespace PBGSO.BrownianDyadicProbability
open BrownianFourthMoment

def root : ℝ := Real.sqrt (Real.sqrt (Real.sqrt 2))
def radius (n : ℕ) : ℝ := (root⁻¹) ^ n

theorem root_gt_one : 1 < root := by
  have h1 : (1 : ℝ) < Real.sqrt (Real.sqrt 2) :=
    Real.lt_sqrt_of_sq_lt (by simpa using Real.one_lt_sqrt_two)
  exact Real.lt_sqrt_of_sq_lt (by simpa using h1)

theorem root_pos : 0 < root := lt_trans zero_lt_one root_gt_one

theorem root_four : root ^ 4 = Real.sqrt 2 := by
  rw [root, show (4 : ℕ) = 2 * 2 by decide, pow_mul,
    Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (Real.sqrt_nonneg _)]

theorem radius_pos (n : ℕ) : 0 < radius n := pow_pos (inv_pos.mpr root_pos) n

theorem radius_summable : Summable radius :=
  summable_geometric_of_lt_one (inv_nonneg.mpr root_pos.le) ((inv_lt_one₀ root_pos).mpr root_gt_one)

def uniformTime (T : ℝ≥0) (N k : ℕ) : ℝ≥0 := T * k / N

theorem uniformTime_dist (T : ℝ≥0) (N k : ℕ) :
    dist (uniformTime T N (k + 1) : ℝ) (uniformTime T N k : ℝ) = (T : ℝ) / N := by
  simp only [uniformTime, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_add, NNReal.coe_one, Nat.cast_add,
    Nat.cast_one, Real.dist_eq]
  rw [show (T : ℝ) * (k + 1) / N - T * k / N = T / N by ring]
  exact abs_of_nonneg (by positivity)

variable {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
  (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B Q)

def badGrid (T : ℝ≥0) (N : ℕ) (a : ℝ) : Set Ω :=
  {ω | ∃ k < N, a ≤ ‖B (uniformTime T N (k + 1)) ω - B (uniformTime T N k) ω‖}

include hB in
theorem grid_fourth_integral (T : ℝ≥0) (N : ℕ) :
    (∫ ω, ∑ k ∈ Finset.range N,
      ‖B (uniformTime T N (k + 1)) ω - B (uniformTime T N k) ω‖ ^ 4 ∂Q) =
      (N : ℝ) * (fourthConstant * ((T : ℝ) / N) ^ 2) := by
  rw [integral_finsetSum _ (fun k _ => increment_fourth_integrable Q B hB _ _)]
  simp_rw [increment_fourth_moment Q B hB, uniformTime_dist]
  simp

include hB in
theorem badGrid_real_le (T : ℝ≥0) (N : ℕ) (a : ℝ) (ha : 0 < a) :
    Q.real (badGrid B T N a) ≤
      ((N : ℝ) * (fourthConstant * ((T : ℝ) / N) ^ 2)) / a ^ 4 := by
  let V : Ω → ℝ := fun ω => ∑ k ∈ Finset.range N,
    ‖B (uniformTime T N (k + 1)) ω - B (uniformTime T N k) ω‖ ^ 4
  have hV : Integrable V Q := integrable_finsetSum _
    (fun k _ => increment_fourth_integrable Q B hB _ _)
  have hnonneg (ω : Ω) : 0 ≤ V ω := Finset.sum_nonneg (fun _ _ => by positivity)
  have hsub : badGrid B T N a ⊆ {ω | a ^ 4 ≤ V ω} := by
    rintro ω ⟨k, hk, he⟩
    have hp := pow_le_pow_left₀ ha.le he 4
    apply hp.trans
    change ‖B (uniformTime T N (k + 1)) ω - B (uniformTime T N k) ω‖ ^ 4 ≤
      ∑ j ∈ Finset.range N, ‖B (uniformTime T N (j + 1)) ω - B (uniformTime T N j) ω‖ ^ 4
    exact Finset.single_le_sum (f := fun j : ℕ =>
      ‖B (uniformTime T N (j + 1)) ω - B (uniformTime T N j) ω‖ ^ 4)
      (fun _ _ => by positivity) (Finset.mem_range.mpr hk)
  have hm := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hnonneg) hV (a ^ 4)
  have he : (∫ ω, V ω ∂Q) = (N : ℝ) * (fourthConstant * ((T : ℝ) / N) ^ 2) :=
    grid_fourth_integral Q B hB T N
  rw [he] at hm
  apply (le_div_iff₀ (pow_pos ha 4)).mpr
  calc
    Q.real (badGrid B T N a) * a ^ 4 = a ^ 4 * Q.real (badGrid B T N a) := mul_comm _ _
    _ ≤ a ^ 4 * Q.real {ω | a ^ 4 ≤ V ω} :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsub) (pow_nonneg ha.le 4)
    _ ≤ _ := hm

include hB in
theorem badGrid_le (T : ℝ≥0) (N : ℕ) (a : ℝ) (ha : 0 < a) :
    Q (badGrid B T N a) ≤
      ENNReal.ofReal (((N : ℝ) * (fourthConstant * ((T : ℝ) / N) ^ 2)) / a ^ 4) := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top Q _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (div_nonneg (mul_nonneg (Nat.cast_nonneg N)
    (mul_nonneg fourthConstant_nonneg (sq_nonneg _))) (pow_nonneg ha.le 4))]
  exact badGrid_real_le Q B hB T N a ha


def decay : ℝ := root ^ 4 / 2

theorem decay_nonneg : 0 ≤ decay := by unfold decay; positivity

theorem decay_lt_one : decay < 1 := by
  rw [decay, root_four]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

theorem grid_budget_geometric (T : ℝ≥0) (n : ℕ) :
    (((2 ^ n : ℕ) : ℝ) * (fourthConstant * ((T : ℝ) / (2 ^ n : ℕ)) ^ 2)) /
        radius n ^ 4 = fourthConstant * (T : ℝ) ^ 2 * decay ^ n := by
  have hp : ((root⁻¹) ^ n) ^ 4 = ((root ^ 4) ^ n)⁻¹ := by
    rw [← pow_mul, Nat.mul_comm n 4, pow_mul, inv_pow, inv_pow]
  simp only [radius, decay, Nat.cast_pow, Nat.cast_ofNat]
  rw [hp]
  simp only [div_eq_mul_inv, inv_inv]
  field_simp
  have hc : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = (fourthConstant * (T : ℝ) ^ 2 * (root ^ 4) ^ n) *
        ((1 / 2 : ℝ) ^ n * 2 ^ n) := by rw [hc]; ring
    _ = _ := by ring

include hB in
theorem badDyadic_summable (T : ℝ≥0) :
    (∑' n, Q (badGrid B T (2 ^ n) (radius n))) < ∞ := by
  have hbound (n : ℕ) : Q (badGrid B T (2 ^ n) (radius n)) ≤
      ENNReal.ofReal (fourthConstant * (T : ℝ) ^ 2 * decay ^ n) := by
    rw [← grid_budget_geometric]
    exact badGrid_le Q B hB T (2 ^ n) (radius n) (radius_pos n)
  have hs : Summable (fun n => fourthConstant * (T : ℝ) ^ 2 * decay ^ n) :=
    (summable_geometric_of_lt_one decay_nonneg decay_lt_one).mul_left _
  have hsum : (∑' n, ENNReal.ofReal (fourthConstant * (T : ℝ) ^ 2 * decay ^ n)) < ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg
      (mul_nonneg fourthConstant_nonneg (sq_nonneg _)) (pow_nonneg decay_nonneg n)) hs]
    exact ENNReal.ofReal_lt_top
  exact lt_of_le_of_lt (ENNReal.tsum_le_tsum hbound) hsum

include hB in
/-- The original Gaussian laws derive one full-measure event of eventual
uniform adjacent-dyadic increment bounds. -/
theorem ae_eventual_grid_bound (T : ℝ≥0) :
    ∀ᵐ ω ∂Q, ∀ᶠ n in atTop, ∀ k < 2 ^ n,
      ‖B (uniformTime T (2 ^ n) (k + 1)) ω - B (uniformTime T (2 ^ n) k) ω‖ ≤ radius n := by
  have hc := ae_eventually_notMem (badDyadic_summable Q B hB T).ne
  filter_upwards [hc] with ω hω
  filter_upwards [hω] with n hn
  intro k hk
  exact le_of_lt (lt_of_not_ge (fun h => hn ⟨k, hk, h⟩))

def scaled (T : ℝ≥0) (ω : Ω) (t : ℝ) : ℝ := B (T * t.toNNReal) ω

theorem scaled_sample (T : ℝ≥0) (ω : Ω) (N k : ℕ) :
    scaled B T ω ((k : ℝ) / N) = B (uniformTime T N k) ω := by
  have ht : T * ((k : ℝ) / N).toNNReal = uniformTime T N k := by
    apply NNReal.eq
    simp only [uniformTime, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast,
      Real.coe_toNNReal _ (div_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg N))]
    ring
  exact congrArg (fun τ => B τ ω) ht

theorem radius_succ_le (n : ℕ) : radius (n + 1) ≤ radius n := by
  rw [radius, pow_succ]
  exact mul_le_of_le_one_right (pow_nonneg (inv_nonneg.mpr root_pos.le) n)
    ((inv_le_one₀ root_pos).mpr root_gt_one.le)

include hB in
/-- Actual pre-Brownian laws construct an almost-sure continuous uniform
polygon limit on every fixed rescaled finite horizon. No path-continuity
hypothesis is used. -/
theorem ae_uniform_polygon_limit (T : ℝ≥0) :
    ∀ᵐ ω ∂Q, ∃ U : C(DyadicInterpolation.UnitWindow, ℝ),
      TendstoUniformly (fun n (t : DyadicInterpolation.UnitWindow) =>
        DyadicInterpolation.dyadicPolygon n (scaled B T ω) t) U atTop := by
  filter_upwards [ae_eventual_grid_bound Q B hB T] with ω hω
  have hstep : ∀ᶠ n in atTop, ∀ j < 2 ^ (n + 1),
      ‖scaled B T ω (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) -
        scaled B T ω ((j : ℝ) / (2 : ℝ) ^ (n + 1))‖ ≤ radius n := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp hω
    filter_upwards [eventually_ge_atTop N] with n hn
    intro j hj
    have hb := hN (n + 1) (by omega) j hj
    have he1 := scaled_sample B T ω (2 ^ (n + 1)) (j + 1)
    have he0 := scaled_sample B T ω (2 ^ (n + 1)) j
    simp only [Nat.cast_pow, Nat.cast_ofNat] at he1 he0
    rw [he1, he0]
    exact hb.trans (radius_succ_le n)
  obtain ⟨U, _, hU⟩ := DyadicInterpolation.exists_uniform_dyadic_limit
    (scaled B T ω) radius (fun n => (radius_pos n).le) radius_summable hstep
  exact ⟨U, hU⟩
end PBGSO.BrownianDyadicProbability
