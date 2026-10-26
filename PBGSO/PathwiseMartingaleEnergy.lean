import PBGSO.ExpectedBilinearLimits

/-! # Expected quadratic energy with merely pathwise L¹ drift
The actual martingale and original pathwise primitive determine the energy.
Time L¹(L²) drift is not an assumption. A square-integrable path radius is
explicit, as supplied by bounded localization.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal RealInnerProductSpace InnerProductSpace
namespace PBGSO.PathwiseMartingaleEnergy
open QuadraticMartingale PartitionFiniteVariation ExpectedBilinearLimits
variable {Ω Z : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z] [MeasurableSpace Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (F : Filtration ℝ mΩ)
  (W : Z →L[ℝ] Z) (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)

/-- The original raw state, noise and drift-primitive realizations agree on
one event at all actual dyadic grid times. -/
theorem grid_realizations (T : ℝ≥0) (X V N : ℝ → Lp Z 2 Q)
    (x b m : ℝ → Ω → Z)
    (hX : ∀ t, x t =ᵐ[Q] X t)
    (hV : ∀ t ∈ Icc 0 (T : ℝ), (fun ω => ∫ r in 0..t, b r ω) =ᵐ[Q] V t)
    (hN : ∀ t, m t =ᵐ[Q] N t) :
    ∀ᵐ ω ∂Q, ∀ n, ∀ k ≤ (dyadic T n).count,
      x ((dyadic T n).time k) ω = X ((dyadic T n).time k) ω ∧
      (∫ r in 0..(dyadic T n).time k, b r ω) = V ((dyadic T n).time k) ω ∧
      m ((dyadic T n).time k) ω = N ((dyadic T n).time k) ω := by
  apply ae_all_iff.mpr
  intro n
  apply ae_all_iff.mpr
  intro k
  by_cases hk : k ≤ (dyadic T n).count
  · filter_upwards [hX ((dyadic T n).time k),
      hV _ ((dyadic T n).mem k hk), hN ((dyadic T n).time k)] with ω hx hv hn _
    exact ⟨hx, hv, hn⟩
  · exact ae_of_all _ (fun _ h => False.elim (hk h))

include hW

/-- Actual expected quadratic balance, derived from finite martingale
orthogonality and pathwise finite-variation limits. The bound is an explicit
localization radius, not a claimed consequence of point-time P₂ alone. -/
theorem quadratic_balance (T : ℝ≥0) (X V N : ℝ → Lp Z 2 Q)
    (x b m : ℝ → Ω → Z) (C : Ω → ℝ)
    (hmart : Martingale m F Q) (hN : ∀ t, m t =ᵐ[Q] N t)
    (hX : ∀ t, x t =ᵐ[Q] X t)
    (hV : ∀ t ∈ Icc 0 (T : ℝ), (fun ω => ∫ r in 0..t, b r ω) =ᵐ[Q] V t)
    (hN0 : N 0 = 0)
    (hdecomp : ∀ t ∈ Icc 0 (T : ℝ), X t = X 0 + V t + N t)
    (hadapt : ∀ t ∈ Icc 0 (T : ℝ), AEStronglyMeasurable[F t] (X t) Q)
    (hC : Integrable (fun ω => C ω ^ 2) Q)
    (hpaths : ∀ᵐ ω ∂Q, ContinuousOn (fun t => x t ω) (Icc 0 (T : ℝ)) ∧
      ContinuousOn (fun t => m t ω) (Icc 0 (T : ℝ)) ∧
      IntervalIntegrable (fun r => b r ω) volume 0 (T : ℝ) ∧ 0 ≤ C ω ∧
      (∀ t ∈ Icc 0 (T : ℝ), ‖x t ω‖ ≤ C ω ∧ ‖m t ω‖ ≤ C ω) ∧
      (∫ r in 0..(T : ℝ), ‖b r ω‖) ≤ C ω) :
    Integrable (fun ω => ∫ r in 0..(T : ℝ), ⟪x r ω, W (b r ω)⟫_ℝ) Q ∧
    weightedPairing Q W (X T) (X T) = weightedPairing Q W (X 0) (X 0) +
      2 * (∫ ω, (∫ r in 0..(T : ℝ), ⟪x r ω, W (b r ω)⟫_ℝ) ∂Q) +
      weightedPairing Q W (N T) (N T) := by
  let P := dyadic T
  let B := spatialPairing W
  let A (n k : ℕ) := X ((P n).time k)
  let D (n k : ℕ) := V ((P n).time (k + 1)) - V ((P n).time k)
  let E (n k : ℕ) := N ((P n).time (k + 1)) - N ((P n).time k)
  let work (n : ℕ) (ω : Ω) := ∑ k ∈ Finset.range (P n).count,
    B (x ((P n).time k) ω) (∫ r in (P n).time k..(P n).time (k + 1), b r ω)
  let q (n : ℕ) (ω : Ω) := ∑ k ∈ Finset.range (P n).count,
    B (∫ r in (P n).time k..(P n).time (k + 1), b r ω)
      (∫ r in (P n).time k..(P n).time (k + 1), b r ω)
  let cross (n : ℕ) (ω : Ω) := ∑ k ∈ Finset.range (P n).count,
    B (∫ r in (P n).time k..(P n).time (k + 1), b r ω)
      (m ((P n).time (k + 1)) ω - m ((P n).time k) ω)
  have hgrid := grid_realizations Q T X V N x b m hX hV hN
  have hraw (n : ℕ) : ∀ᵐ ω ∂Q,
      (∀ k < (P n).count, D n k ω = ∫ r in (P n).time k..(P n).time (k + 1), b r ω) ∧
      (∀ k < (P n).count, A n k ω = x ((P n).time k) ω) ∧
      (∀ k < (P n).count, E n k ω = m ((P n).time (k + 1)) ω - m ((P n).time k) ω) := by
    filter_upwards [hgrid, hpaths,
      ae_all_iff.mpr (fun k => Lp.coeFn_sub (V ((P n).time (k + 1))) (V ((P n).time k))),
      ae_all_iff.mpr (fun k => Lp.coeFn_sub (N ((P n).time (k + 1))) (N ((P n).time k)))]
      with ω hg hp hv hn
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      change (V ((P n).time (k + 1)) - V ((P n).time k)) ω = _
      rw [hv k, Pi.sub_apply, ← (hg n (k + 1) (Nat.succ_le_of_lt hk)).2.1,
        ← (hg n k hk.le).2.1]
      exact primitive_increment (fun r => b r ω) hp.2.2.1 (P n) k hk
    · intro k hk
      exact (hg n k hk.le).1.symm
    · intro k hk
      change (N ((P n).time (k + 1)) - N ((P n).time k)) ω = _
      rw [hn k, Pi.sub_apply, ← (hg n (k + 1) (Nat.succ_le_of_lt hk)).2.2,
        ← (hg n k hk.le).2.2]
  have heq (n : ℕ) : ∀ᵐ ω ∂Q,
      (∑ k ∈ Finset.range (P n).count, B (A n k ω) (D n k ω)) = work n ω ∧
      (∑ k ∈ Finset.range (P n).count, B (D n k ω) (D n k ω)) = q n ω ∧
      (∑ k ∈ Finset.range (P n).count, B (D n k ω) (E n k ω)) = cross n ω := by
    filter_upwards [hraw n] with ω hh
    refine ⟨Finset.sum_congr rfl (fun k hk => ?_),
      Finset.sum_congr rfl (fun k hk => ?_), Finset.sum_congr rfl (fun k hk => ?_)⟩
    · rw [hh.1 k (Finset.mem_range.mp hk), hh.2.1 k (Finset.mem_range.mp hk)]
    · rw [hh.1 k (Finset.mem_range.mp hk)]
    · rw [hh.1 k (Finset.mem_range.mp hk), hh.2.2 k (Finset.mem_range.mp hk)]
  have hwlim : ∀ᵐ ω ∂Q, Tendsto
      (fun n => ∑ k ∈ Finset.range (P n).count, B (A n k ω) (D n k ω)) atTop
        (𝓝 (∫ r in 0..(T : ℝ), B (x r ω) (b r ω))) := by
    filter_upwards [hpaths, ae_all_iff.mpr heq] with ω hp he
    exact (work_tendsto T B (fun r => x r ω) (fun r => b r ω) hp.1 hp.2.2.1).congr'
      (Eventually.of_forall (fun n => (he n).1.symm))
  have hqlim : ∀ᵐ ω ∂Q, Tendsto
      (fun n => ∑ k ∈ Finset.range (P n).count, B (D n k ω) (D n k ω)) atTop (𝓝 0) := by
    filter_upwards [hpaths, ae_all_iff.mpr heq] with ω hp he
    exact (quadratic_variation_tendsto T B (fun r => b r ω) hp.2.2.1).congr'
      (Eventually.of_forall (fun n => (he n).2.1.symm))
  have hclim : ∀ᵐ ω ∂Q, Tendsto
      (fun n => ∑ k ∈ Finset.range (P n).count, B (D n k ω) (E n k ω)) atTop (𝓝 0) := by
    filter_upwards [hpaths, ae_all_iff.mpr heq] with ω hp he
    exact (cross_variation_tendsto T B (fun r => b r ω) (fun r => m r ω)
      hp.2.2.1 hp.2.1).congr' (Eventually.of_forall (fun n => (he n).2.2.symm))
  have hwbound (n : ℕ) : ∀ᵐ ω ∂Q,
      ‖∑ k ∈ Finset.range (P n).count, B (A n k ω) (D n k ω)‖ ≤ ‖B‖ * C ω ^ 2 := by
    filter_upwards [hpaths, heq n] with ω hp he
    rw [he.1]
    apply ((P n).work_bound B _ _ hp.2.2.1 _ hp.2.2.2.1
      (fun t ht => (hp.2.2.2.2.1 t ht).1)).trans
    have hc := hp.2.2.2.2.2
    nlinarith [mul_le_mul_of_nonneg_left hc (mul_nonneg (norm_nonneg B) hp.2.2.2.1)]
  have hqbound (n : ℕ) : ∀ᵐ ω ∂Q,
      ‖∑ k ∈ Finset.range (P n).count, B (D n k ω) (D n k ω)‖ ≤ ‖B‖ * C ω ^ 2 := by
    filter_upwards [hpaths, heq n] with ω hp he
    rw [he.2.1]
    apply ((P n).quadratic_bound B _ hp.2.2.1).trans
    have hpos : 0 ≤ ∫ r in 0..(T : ℝ), ‖b r ω‖ :=
      intervalIntegral.integral_nonneg_of_forall T.coe_nonneg (fun _ => norm_nonneg _)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpos hp.2.2.2.2.2 2) (norm_nonneg B)
  have hcbound (n : ℕ) : ∀ᵐ ω ∂Q,
      ‖∑ k ∈ Finset.range (P n).count, B (D n k ω) (E n k ω)‖ ≤
        (2 * ‖B.flip‖) * C ω ^ 2 := by
    filter_upwards [hpaths, heq n] with ω hp he
    rw [he.2.2]
    apply ((P n).cross_bound B _ _ hp.2.2.1 _ hp.2.2.2.1
      (fun t ht => (hp.2.2.2.2.1 t ht).2)).trans
    have hc := hp.2.2.2.2.2
    nlinarith [mul_le_mul_of_nonneg_left hc
      (mul_nonneg (norm_nonneg B.flip) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hp.2.2.2.1))]
  obtain ⟨hwork, hw⟩ := pairSum_limit Q W A D (fun n => (P n).count) _ _
    (hC.const_mul ‖B‖) hwbound hwlim
  have hq := (pairSum_limit Q W D D (fun n => (P n).count) (fun _ => 0) _
    (hC.const_mul ‖B‖) hqbound hqlim).2
  have hc := (pairSum_limit Q W D E (fun n => (P n).count) (fun _ => 0) _
    (hC.const_mul (2 * ‖B.flip‖)) hcbound hclim).2
  refine ⟨hwork, ?_⟩
  have htotal := ((((tendsto_const_nhds (x := weightedPairing Q W (X 0) (X 0))).add (hw.const_mul 2)).add hq).add
    (hc.const_mul 2)).add_const (weightedPairing Q W (N T) (N T))
  have hevery (n : ℕ) : weightedPairing Q W (X 0) (X 0) +
      2 * (∑ k ∈ Finset.range (P n).count, weightedPairing Q W (A n k) (D n k)) +
      (∑ k ∈ Finset.range (P n).count, weightedPairing Q W (D n k) (D n k)) +
      2 * (∑ k ∈ Finset.range (P n).count, weightedPairing Q W (D n k) (E n k)) +
      weightedPairing Q W (N T) (N T) = weightedPairing Q W (X T) (X T) :=
    (PartitionQuadraticEnergy.finite_partition_identity Q F W hW X V N m hmart hN
      T (P n).time (P n).monotone (P n).count (P n).start (P n).finish hN0 hdecomp hadapt).symm
  have hh := tendsto_nhds_unique
    (htotal.congr (fun n => hevery n)) (tendsto_const_nhds (x := weightedPairing Q W (X T) (X T)))
  simpa only [integral_zero, add_zero, mul_zero, B, spatialPairing_apply] using hh.symm

end PBGSO.PathwiseMartingaleEnergy
