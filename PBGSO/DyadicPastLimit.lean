import PBGSO.DyadicPastSamples
import PBGSO.DyadicInterpolationLimit

/-! # The continuous dyadic limit has an explicit past-only series
The raw candidate is defined without a convergence assumption. Actual
summable grid bounds prove convergence and identify its value with the
continuous polygon limit, simultaneously throughout the unit window.
-/
noncomputable section
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology BigOperators
namespace PBGSO.DyadicInterpolation
variable {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R] [CompleteSpace R]

def pastSample (n : ℕ) (F : ℝ → R) (t : ℝ) : R := F (leftTime (2 ^ n) t)

def pastCandidate (F : ℝ → R) (t : ℝ) : R :=
  pastSample 0 F t + ∑' n, (pastSample (n + 1) F t - pastSample n F t)

/-- Actual endpoint control identifies each polygon with its past-only
sample to within the actual adjacent-grid bound. -/
theorem dyadic_past_bound (n : ℕ) (F : ℝ → R) (t : ℝ) (ht : t ∈ Icc 0 1)
    (a : ℝ) (ha : 0 ≤ a)
    (hstep : ∀ j < 2 ^ n,
      ‖F (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) - F ((j : ℝ) / (2 : ℝ) ^ n)‖ ≤ a) :
    ‖dyadicPolygon n F t - pastSample n F t‖ ≤ a := by
  have h := polygon_past_bound (2 ^ n) (by positivity)
    (fun j => F ((j : ℝ) / (2 : ℝ) ^ n)) t ht a ha hstep
  simpa only [dyadicPolygon, sampledPolygon, pastSample, leftTime,
    Nat.cast_pow, Nat.cast_ofNat] using h

variable (F : ℝ → R) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
  (hsum : Summable a)
  (hstep : ∀ᶠ n in atTop, ∀ j < 2 ^ n,
    ‖F (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) - F ((j : ℝ) / (2 : ℝ) ^ n)‖ ≤ a n)

include hstep in
theorem eventual_steps : ∀ᶠ n in atTop,
    (∀ j < 2 ^ n,
      ‖F (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) - F ((j : ℝ) / (2 : ℝ) ^ n)‖ ≤ a n) ∧
    (∀ j < 2 ^ (n + 1),
      ‖F (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) -
        F ((j : ℝ) / (2 : ℝ) ^ (n + 1))‖ ≤ a (n + 1)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hstep
  filter_upwards [eventually_ge_atTop N] with n hn
  exact ⟨hN n hn, hN (n + 1) (by omega)⟩

include ha hsum hstep in
theorem past_differences_summable (t : ℝ) (ht : t ∈ Icc 0 1) :
    Summable (fun n => ‖pastSample (n + 1) F t - pastSample n F t‖) := by
  have hshift : Summable (fun n => a (n + 1)) := hsum.comp_injective Nat.succ_injective
  apply (hsum.add (hshift.mul_left 6)).of_norm_bounded_eventually_nat
  filter_upwards [eventual_steps F a hstep] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hp := dyadic_past_bound n F t ht (a n) (ha n) hn.1
  have hp' := dyadic_past_bound (n + 1) F t ht (a (n + 1)) (ha (n + 1)) hn.2
  have hd := dyadicPolygon_succ_bound n F (a (n + 1)) (ha (n + 1)) hn.2 t ht
  calc
    _ ≤ ‖pastSample (n + 1) F t - dyadicPolygon (n + 1) F t‖ +
        ‖dyadicPolygon (n + 1) F t - pastSample n F t‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖pastSample (n + 1) F t - dyadicPolygon (n + 1) F t‖ +
        (‖dyadicPolygon (n + 1) F t - dyadicPolygon n F t‖ +
          ‖dyadicPolygon n F t - pastSample n F t‖) :=
      add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub _ _ _)
    _ ≤ a (n + 1) + (5 * a (n + 1) + a n) := by
      rw [norm_sub_rev (pastSample (n + 1) F t)]
      exact add_le_add hp' (add_le_add hd hp)
    _ = a n + 6 * a (n + 1) := by ring

include ha hsum hstep in
theorem pastSample_tendsto_candidate (t : ℝ) (ht : t ∈ Icc 0 1) :
    Tendsto (fun n => pastSample n F t) atTop (𝓝 (pastCandidate F t)) := by
  have hs := (past_differences_summable F a ha hsum hstep t ht).of_norm
  have hc : Tendsto (fun _ : ℕ => pastSample 0 F t) atTop (𝓝 (pastSample 0 F t)) :=
    tendsto_const_nhds
  have hh := hc.add hs.hasSum.tendsto_sum_nat
  have he (n : ℕ) : pastSample 0 F t +
      ∑ k ∈ Finset.range n, (pastSample (k + 1) F t - pastSample k F t) = pastSample n F t := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ih]
      abel
  simpa only [he, pastCandidate] using hh

include ha hsum hstep in
theorem pastCandidate_eq_of_uniform_limit (U : C(UnitWindow, R))
    (hU : TendstoUniformly (fun n (t : UnitWindow) => dyadicPolygon n F t) U atTop)
    (t : UnitWindow) : pastCandidate F t = U t := by
  have hz : Tendsto (fun n => ‖pastSample n F t - dyadicPolygon n F t‖) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hsum.tendsto_atTop_zero
    filter_upwards [hstep] with n hn
    rw [norm_sub_rev]
    exact dyadic_past_bound n F t t.property (a n) (ha n) hn
  have hv : Tendsto (fun n => pastSample n F t - dyadicPolygon n F t) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hz
  have hp := hv.add (hU.tendsto_at t)
  have he : (fun n => (pastSample n F t - dyadicPolygon n F t) + dyadicPolygon n F t) =
      fun n => pastSample n F t := by funext n; abel
  rw [he, zero_add] at hp
  exact tendsto_nhds_unique (pastSample_tendsto_candidate F a ha hsum hstep t t.property) hp

include ha hsum hstep in
/-- Actual summable eventual dyadic increments give the past-only candidate
continuous sample paths; no measurable choice of the continuous polygon limit
enters the candidate's definition. -/
theorem pastCandidate_continuousOn : ContinuousOn (pastCandidate F) (Icc 0 1) := by
  have hshift : Summable (fun n => a (n + 1)) := hsum.comp_injective Nat.succ_injective
  have hnext := (eventual_steps F a hstep).mono (fun _ hn => hn.2)
  obtain ⟨U, _, hU⟩ := exists_uniform_dyadic_limit F (fun n => a (n + 1))
    (fun n => ha (n + 1)) hshift hnext
  apply continuousOn_iff_continuous_domRestrict.mpr
  have he : (fun t : UnitWindow => pastCandidate F t) = U := by
    funext t
    exact pastCandidate_eq_of_uniform_limit F a ha hsum hstep U hU t
  change Continuous (fun t : UnitWindow => pastCandidate F t)
  rw [he]
  exact U.continuous

end PBGSO.DyadicInterpolation
