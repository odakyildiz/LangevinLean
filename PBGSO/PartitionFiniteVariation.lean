import PBGSO.IntegralQuadraticEnergy
import PBGSO.TimeGridContinuity
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Pathwise finite-variation limits for actual energy partitions
The drift is only Bochner L¹ on each path. No L¹-time L² drift or
quadratic-variation conclusion is an assumption.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open MeasureTheory Set Filter
open scoped Topology NNReal
namespace PBGSO.PartitionFiniteVariation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem clm_intervalIntegrable (L : E →L[ℝ] ℝ) (b : ℝ → E) {a c : ℝ}
    (hb : IntervalIntegrable b volume a c) :
    IntervalIntegrable (fun r => L (b r)) volume a c := by
  rw [intervalIntegrable_iff] at hb ⊢
  exact L.integrable_comp hb

structure Partition (T : ℝ) where
  time : ℕ → ℝ
  count : ℕ
  monotone : Monotone time
  start : time 0 = 0
  finish : time count = T

variable {T : ℝ}

theorem Partition.nonneg (P : Partition T) : 0 ≤ T := by
  simpa only [P.start, P.finish] using P.monotone (Nat.zero_le P.count)

theorem Partition.mem (P : Partition T) (k : ℕ) (hk : k ≤ P.count) :
    P.time k ∈ Icc 0 T := by
  constructor
  · rw [← P.start]; exact P.monotone (Nat.zero_le _)
  · exact (P.monotone hk).trans_eq P.finish

theorem Partition.cell_integrable (P : Partition T) (b : ℝ → E)
    (hb : IntervalIntegrable b volume 0 T) (k : ℕ) (hk : k < P.count) :
    IntervalIntegrable b volume (P.time k) (P.time (k + 1)) := by
  apply hb.mono_set'
  rw [uIoc_of_le (P.monotone (Nat.le_succ k)), uIoc_of_le P.nonneg]
  exact Ioc_subset_Ioc (P.mem k hk.le).1 (P.mem (k + 1) (Nat.succ_le_of_lt hk)).2

theorem Partition.sum_integrals (P : Partition T) (b : ℝ → E)
    (hb : IntervalIntegrable b volume 0 T) :
    ∑ k ∈ Finset.range P.count, (∫ r in P.time k..P.time (k + 1), b r) =
      ∫ r in 0..T, b r := by
  simpa only [P.start, P.finish] using intervalIntegral.sum_integral_adjacent_intervals
    (fun k hk => P.cell_integrable b hb k hk)

/-- Total variation on the actual partition is bounded by the original
pathwise L¹ drift integral, including repeated partition times. -/
theorem Partition.variation_bound (P : Partition T) (b : ℝ → E)
    (hb : IntervalIntegrable b volume 0 T) :
    ∑ k ∈ Finset.range P.count, ‖∫ r in P.time k..P.time (k + 1), b r‖ ≤
      ∫ r in 0..T, ‖b r‖ := by
  calc
    _ ≤ ∑ k ∈ Finset.range P.count, (∫ r in P.time k..P.time (k + 1), ‖b r‖) := by
      apply Finset.sum_le_sum
      intro k hk
      exact intervalIntegral.norm_integral_le_integral_norm (P.monotone (Nat.le_succ k))
    _ = _ := P.sum_integrals (fun r => ‖b r‖) hb.norm

/-- A bilinear increment sum is controlled by one uniform increment bound
and the original total variation of the other path. -/
theorem Partition.bilinear_bound (P : Partition T) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (a : ℕ → E) (b : ℝ → E) (hb : IntervalIntegrable b volume 0 T)
    (ε : ℝ) (hε : 0 ≤ ε) (ha : ∀ k < P.count, ‖a k‖ ≤ ε) :
    ‖∑ k ∈ Finset.range P.count, B (a k) (∫ r in P.time k..P.time (k + 1), b r)‖ ≤
      (‖B‖ * ε) * ∫ r in 0..T, ‖b r‖ := by
  calc
    _ ≤ ∑ k ∈ Finset.range P.count,
        ‖B (a k) (∫ r in P.time k..P.time (k + 1), b r)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range P.count,
        (‖B‖ * ε) * ‖∫ r in P.time k..P.time (k + 1), b r‖ := by
      apply Finset.sum_le_sum
      intro k hk
      exact (B.le_opNorm₂ _ _).trans (by gcongr; exact ha k (Finset.mem_range.mp hk))
    _ = (‖B‖ * ε) * ∑ k ∈ Finset.range P.count,
        ‖∫ r in P.time k..P.time (k + 1), b r‖ := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (P.variation_bound b hb) (by positivity)

/-- Work error for an arbitrary monotone partition. Only continuity of the
state and pathwise L¹ drift are used; a time derivative is unnecessary. -/
theorem Partition.work_error_bound (P : Partition T)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (x b : ℝ → E)
    (hx : ContinuousOn x (Icc 0 T)) (hb : IntervalIntegrable b volume 0 T)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hosc : ∀ k < P.count, ∀ r ∈ Icc (P.time k) (P.time (k + 1)),
      ‖x (P.time k) - x r‖ ≤ ε) :
    ‖(∑ k ∈ Finset.range P.count,
        B (x (P.time k)) (∫ r in P.time k..P.time (k + 1), b r)) -
        ∫ r in 0..T, B (x r) (b r)‖ ≤
      (‖B‖ * ε) * ∫ r in 0..T, ‖b r‖ := by
  have hT : 0 ≤ T := P.nonneg
  have hwork := IntegralQuadraticEnergy.bilinear_continuous_integrable B x b
    (by simpa only [uIcc_of_le hT] using hx) hb
  have he : (∑ k ∈ Finset.range P.count,
      B (x (P.time k)) (∫ r in P.time k..P.time (k + 1), b r)) -
        ∫ r in 0..T, B (x r) (b r) =
      ∑ k ∈ Finset.range P.count, (∫ r in P.time k..P.time (k + 1),
        B (x (P.time k) - x r) (b r)) := by
    rw [← P.sum_integrals _ hwork, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hkb := P.cell_integrable b hb k (Finset.mem_range.mp hk)
    have hkw := P.cell_integrable _ hwork k (Finset.mem_range.mp hk)
    rw [← (B (x (P.time k))).intervalIntegral_comp_comm hkb,
      ← intervalIntegral.integral_sub (clm_intervalIntegrable (B (x (P.time k))) b hkb) hkw]
    apply intervalIntegral.integral_congr
    intro r hr
    simp only [map_sub, sub_apply]
  rw [he]
  calc
    _ ≤ ∑ k ∈ Finset.range P.count, ‖∫ r in P.time k..P.time (k + 1),
        B (x (P.time k) - x r) (b r)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range P.count,
        (‖B‖ * ε) * (∫ r in P.time k..P.time (k + 1), ‖b r‖) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn := Finset.mem_range.mp hk
      have hkb := P.cell_integrable b hb k hkn
      have hkw := P.cell_integrable _ hwork k hkn
      have hki : IntervalIntegrable (fun r => B (x (P.time k) - x r) (b r)) volume
          (P.time k) (P.time (k + 1)) := by
        simpa only [map_sub, sub_apply] using
          (clm_intervalIntegrable (B (x (P.time k))) b hkb).sub hkw
      calc
        _ ≤ ∫ r in P.time k..P.time (k + 1), ‖B (x (P.time k) - x r) (b r)‖ :=
          intervalIntegral.norm_integral_le_integral_norm (P.monotone (Nat.le_succ k))
        _ ≤ ∫ r in P.time k..P.time (k + 1), (‖B‖ * ε) * ‖b r‖ := by
          apply intervalIntegral.integral_mono_on (P.monotone (Nat.le_succ k)) hki.norm
            (hkb.norm.const_mul _)
          intro r hr
          exact (B.le_opNorm₂ _ _).trans (by gcongr; exact hosc k hkn r hr)
        _ = _ := intervalIntegral.integral_const_mul _ _
    _ = _ := by rw [← Finset.mul_sum, P.sum_integrals _ hb.norm]

/-- The actual uniform dyadic partition, not a supplied approximation. -/
def dyadic (T : ℝ≥0) (n : ℕ) : Partition (T : ℝ) where
  time k := ((GridIntegralCompletion.dyadicGrids T).time n k : ℝ)
  count := (GridIntegralCompletion.dyadicGrids T).count n
  monotone := fun i j hij => (GridIntegralCompletion.dyadicGrids T).monotone n hij
  start := by simp [GridIntegralCompletion.dyadicGrids]
  finish := by
    simp only [GridIntegralCompletion.dyadicGrids, NNReal.coe_mul, NNReal.coe_div,
      NNReal.coe_natCast, Nat.cast_pow, Nat.cast_ofNat, NNReal.coe_pow, NNReal.coe_ofNat]
    field_simp

theorem dyadic_mesh (T : ℝ≥0) (n k : ℕ) :
    (dyadic T n).time (k + 1) - (dyadic T n).time k = (T : ℝ) / 2 ^ n := by
  simp only [dyadic, GridIntegralCompletion.dyadicGrids, NNReal.coe_mul, NNReal.coe_div,
    NNReal.coe_pow, NNReal.coe_ofNat, NNReal.coe_natCast]
  push_cast
  ring

/-- Compact path continuity supplies a simultaneous bound for every point
of every fine dyadic cell, with no assumed modulus. -/
theorem eventual_cell_oscillation (T : ℝ≥0) (x : ℝ → E)
    (hx : ContinuousOn x (Icc 0 (T : ℝ))) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ k < (dyadic T n).count,
      ∀ r ∈ Icc ((dyadic T n).time k) ((dyadic T n).time (k + 1)),
        ‖x ((dyadic T n).time k) - x r‖ ≤ ε := by
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hx) ε hε
  have hm := (TimeGridContinuity.dyadic_mesh_tendsto T).eventually
    (gt_mem_nhds hδ)
  filter_upwards [hm] with n hn
  intro k hk r hr
  have hleft := (dyadic T n).mem k hk.le
  have hright := (dyadic T n).mem (k + 1) (Nat.succ_le_of_lt hk)
  have hrt : r ∈ Icc 0 (T : ℝ) := ⟨hleft.1.trans hr.1, hr.2.trans hright.2⟩
  have hdist : dist ((dyadic T n).time k) r < δ := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hr.1)]
    have he := dyadic_mesh T n k
    linarith [hr.2]
  exact le_of_lt (by simpa only [dist_eq_norm] using hd _ hleft _ hrt hdist)



/-- Error controls on every positive tolerance imply an actual limit. -/
theorem tendsto_of_error_control (u : ℕ → ℝ) (L C : ℝ) (hC : 0 ≤ C)
    (h : ∀ ε > 0, ∀ᶠ n in atTop, ‖u n - L‖ ≤ C * ε) :
    Tendsto u atTop (𝓝 L) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hd : 0 < ε / (C + 1) := div_pos hε (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h _ hd)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  apply (hN n hn).trans_lt
  have he : (C + 1) * (ε / (C + 1)) = ε := by field_simp
  nlinarith

/-- Left-state work sums converge to the actual pathwise drift work. -/
theorem work_tendsto (T : ℝ≥0) (B : E →L[ℝ] E →L[ℝ] ℝ) (x b : ℝ → E)
    (hx : ContinuousOn x (Icc 0 (T : ℝ)))
    (hb : IntervalIntegrable b volume 0 (T : ℝ)) :
    Tendsto (fun n => ∑ k ∈ Finset.range (dyadic T n).count,
      B (x ((dyadic T n).time k))
        (∫ r in (dyadic T n).time k..(dyadic T n).time (k + 1), b r)) atTop
      (𝓝 (∫ r in 0..(T : ℝ), B (x r) (b r))) := by
  have hC : 0 ≤ ∫ r in 0..(T : ℝ), ‖b r‖ :=
    intervalIntegral.integral_nonneg_of_forall T.coe_nonneg (fun _ => norm_nonneg _)
  apply tendsto_of_error_control _ _ (‖B‖ * ∫ r in 0..(T : ℝ), ‖b r‖) (by positivity)
  intro ε hε
  filter_upwards [eventual_cell_oscillation T x hx ε hε] with n hn
  exact ((dyadic T n).work_error_bound B x b hx hb ε hε.le hn).trans_eq (by ring)

/-- The indefinite primitive has the literal original drift increments. -/
theorem primitive_increment (b : ℝ → E) (hb : IntervalIntegrable b volume 0 T)
    (P : Partition T) (k : ℕ) (hk : k < P.count) :
    (∫ r in 0..P.time (k + 1), b r) - (∫ r in 0..P.time k, b r) =
      ∫ r in P.time k..P.time (k + 1), b r := by
  apply intervalIntegral.integral_interval_sub_left
  · apply hb.mono_set
    rw [uIcc_of_le P.nonneg,
      uIcc_of_le (P.mem (k + 1) (Nat.succ_le_of_lt hk)).1]
    exact Icc_subset_Icc le_rfl (P.mem (k + 1) (Nat.succ_le_of_lt hk)).2
  · apply hb.mono_set
    rw [uIcc_of_le P.nonneg, uIcc_of_le (P.mem k hk.le).1]
    exact Icc_subset_Icc le_rfl (P.mem k hk.le).2

/-- Quadratic finite-variation increments vanish on actual dyadic meshes.
No quadratic-variation theorem or time-L² drift is assumed. -/
theorem quadratic_variation_tendsto (T : ℝ≥0) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (b : ℝ → E) (hb : IntervalIntegrable b volume 0 (T : ℝ)) :
    Tendsto (fun n => ∑ k ∈ Finset.range (dyadic T n).count,
      B (∫ r in (dyadic T n).time k..(dyadic T n).time (k + 1), b r)
        (∫ r in (dyadic T n).time k..(dyadic T n).time (k + 1), b r)) atTop (𝓝 0) := by
  let V : ℝ → E := fun t => ∫ r in 0..t, b r
  have hc : ContinuousOn V (Icc 0 (T : ℝ)) := by
    simpa only [uIcc_of_le T.coe_nonneg] using
      (IntegralQuadraticEnergy.integral_absolutelyContinuous b hb).continuousOn
  have hC : 0 ≤ ∫ r in 0..(T : ℝ), ‖b r‖ :=
    intervalIntegral.integral_nonneg_of_forall T.coe_nonneg (fun _ => norm_nonneg _)
  apply tendsto_of_error_control _ _ (‖B‖ * ∫ r in 0..(T : ℝ), ‖b r‖) (by positivity)
  intro ε hε
  filter_upwards [eventual_cell_oscillation T V hc ε hε] with n hn
  simp only [sub_zero]
  apply ((dyadic T n).bilinear_bound B _ b hb ε hε.le ?_).trans_eq (by ring)
  intro k hk
  rw [← primitive_increment b hb (dyadic T n) k hk, norm_sub_rev]
  exact hn k hk _ ⟨(dyadic T n).monotone (Nat.le_succ _), le_rfl⟩

/-- Continuous paths have zero cross variation against an L¹ drift primitive.
This includes continuous martingale paths, without moment assumptions here. -/
theorem cross_variation_tendsto (T : ℝ≥0) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (b m : ℝ → E) (hb : IntervalIntegrable b volume 0 (T : ℝ))
    (hm : ContinuousOn m (Icc 0 (T : ℝ))) :
    Tendsto (fun n => ∑ k ∈ Finset.range (dyadic T n).count,
      B (∫ r in (dyadic T n).time k..(dyadic T n).time (k + 1), b r)
        (m ((dyadic T n).time (k + 1)) - m ((dyadic T n).time k))) atTop (𝓝 0) := by
  have hC : 0 ≤ ∫ r in 0..(T : ℝ), ‖b r‖ :=
    intervalIntegral.integral_nonneg_of_forall T.coe_nonneg (fun _ => norm_nonneg _)
  apply tendsto_of_error_control _ _ (‖B.flip‖ * ∫ r in 0..(T : ℝ), ‖b r‖) (by positivity)
  intro ε hε
  filter_upwards [eventual_cell_oscillation T m hm ε hε] with n hn
  simp only [sub_zero]
  apply ((dyadic T n).bilinear_bound B.flip _ b hb ε hε.le ?_).trans_eq (by ring)
  intro k hk
  rw [norm_sub_rev]
  exact hn k hk _ ⟨(dyadic T n).monotone (Nat.le_succ _), le_rfl⟩

end PBGSO.PartitionFiniteVariation
