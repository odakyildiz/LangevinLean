import PBGSO.PartitionFiniteVariation

/-! # Derived domination of finite-variation energy sums
All bounds refer to original pathwise drift integrals and actual state/noise
paths. They supply the bounds for dominated convergence after localization.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal
namespace PBGSO.PartitionFiniteVariation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {T : ℝ}

/-- Every actual drift increment is bounded by the original total variation. -/
theorem Partition.increment_le_variation (P : Partition T) (b : ℝ → E)
    (hb : IntervalIntegrable b volume 0 T) (k : ℕ) (hk : k < P.count) :
    ‖∫ r in P.time k..P.time (k + 1), b r‖ ≤ ∫ r in 0..T, ‖b r‖ := by
  apply le_trans _ (P.variation_bound b hb)
  exact Finset.single_le_sum (fun j _ => norm_nonneg
    (∫ r in P.time j..P.time (j + 1), b r)) (Finset.mem_range.mpr hk)

/-- The work sum is bounded by the original state radius times total variation. -/
theorem Partition.work_bound (P : Partition T) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (x b : ℝ → E) (hb : IntervalIntegrable b volume 0 T) (K : ℝ) (hK : 0 ≤ K)
    (hx : ∀ t ∈ Icc 0 T, ‖x t‖ ≤ K) :
    ‖∑ k ∈ Finset.range P.count,
      B (x (P.time k)) (∫ r in P.time k..P.time (k + 1), b r)‖ ≤
        (‖B‖ * K) * ∫ r in 0..T, ‖b r‖ :=
  P.bilinear_bound B _ b hb K hK (fun k hk => hx _ (P.mem k hk.le))

/-- Quadratic drift sums are bounded using only the original L¹ norm. -/
theorem Partition.quadratic_bound (P : Partition T) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (b : ℝ → E) (hb : IntervalIntegrable b volume 0 T) :
    ‖∑ k ∈ Finset.range P.count,
      B (∫ r in P.time k..P.time (k + 1), b r)
        (∫ r in P.time k..P.time (k + 1), b r)‖ ≤
      ‖B‖ * (∫ r in 0..T, ‖b r‖) ^ 2 := by
  have hC : 0 ≤ ∫ r in 0..T, ‖b r‖ :=
    intervalIntegral.integral_nonneg_of_forall P.nonneg (fun _ => norm_nonneg _)
  exact (P.bilinear_bound B _ b hb _ hC
    (fun k hk => P.increment_le_variation b hb k hk)).trans_eq (by ring)

/-- Cross sums are bounded by the continuous noise radius times total variation.
No stochastic property of the noise is needed for this deterministic bound. -/
theorem Partition.cross_bound (P : Partition T) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (b m : ℝ → E) (hb : IntervalIntegrable b volume 0 T) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ t ∈ Icc 0 T, ‖m t‖ ≤ K) :
    ‖∑ k ∈ Finset.range P.count,
      B (∫ r in P.time k..P.time (k + 1), b r)
        (m (P.time (k + 1)) - m (P.time k))‖ ≤
      (‖B.flip‖ * (2 * K)) * ∫ r in 0..T, ‖b r‖ := by
  apply P.bilinear_bound B.flip _ b hb (2 * K) (by positivity)
  intro k hk
  exact (norm_sub_le _ _).trans (by
    linarith [hm _ (P.mem (k + 1) (Nat.succ_le_of_lt hk)), hm _ (P.mem k hk.le)])

/-- The actual limiting drift work has the same pathwise domination. -/
theorem drift_work_bound (T : ℝ≥0) (B : E →L[ℝ] E →L[ℝ] ℝ) (x b : ℝ → E)
    (hx : ContinuousOn x (Icc 0 (T : ℝ)))
    (hb : IntervalIntegrable b volume 0 (T : ℝ)) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Icc 0 (T : ℝ), ‖x t‖ ≤ K) :
    ‖∫ r in 0..(T : ℝ), B (x r) (b r)‖ ≤
      (‖B‖ * K) * ∫ r in 0..(T : ℝ), ‖b r‖ := by
  exact le_of_tendsto' (work_tendsto T B x b hx hb).norm
    (fun n => (dyadic T n).work_bound B x b hb K hK hbound)

end PBGSO.PartitionFiniteVariation
