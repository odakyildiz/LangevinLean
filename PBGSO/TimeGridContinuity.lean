import PBGSO.GridIntegralCompletion
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Indicator

/-! # Literal dyadic step approximation of time integrands -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.TimeGridContinuity
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℝ R] [CompleteSpace R]

def rawGrid (τ : ℕ → ℝ≥0) (A : ℕ → R) (n : ℕ) (r : ℝ) : R :=
  ∑ k : Fin n, (Ioc (τ k : ℝ) (τ (k + 1))).indicator (fun _ => A k) r

/-- The actual time-L² grid is represented by the literal finite interval sum. -/
theorem grid_coe (τ : ℕ → ℝ≥0) (A : ℕ → R) (n : ℕ) :
    TimeGridEnergy.grid τ A n =ᵐ[volume] rawGrid τ A n := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun k : Fin n => TimeGridEnergy.column (τ k) (τ (k + 1)) (A k)),
    ae_all_iff.mpr (fun k : Fin n =>
      indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc) (hμs := by simp)
        (c := A k) (s := Ioc (τ k : ℝ) (τ (k + 1))))] with r hsum hc
  change (TimeGridEnergy.grid τ A n) r = rawGrid τ A n r
  rw [TimeGridEnergy.grid, hsum]
  simp only [Finset.sum_apply, rawGrid]
  exact Finset.sum_congr rfl fun k _ => hc k

/-- A finite monotone grid covers its full interval, including repeated knots. -/
theorem exists_interval (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (n : ℕ) (r : ℝ)
    (hr : r ∈ Ioc (τ 0 : ℝ) (τ n)) :
    ∃ k : Fin n, r ∈ Ioc (τ k : ℝ) (τ (k + 1)) := by
  induction n with
  | zero => exact False.elim ((not_lt_of_ge hr.2) hr.1)
  | succ n ih =>
    by_cases hn : r ≤ τ n
    · obtain ⟨k, hk⟩ := ih ⟨hr.1, hn⟩
      exact ⟨k.castSucc, hk⟩
    · exact ⟨Fin.last n, lt_of_not_ge hn, hr.2⟩

/-- The interval cells of a monotone grid are pairwise disjoint. -/
theorem interval_unique (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (i j : ℕ) (r : ℝ)
    (hi : r ∈ Ioc (τ i : ℝ) (τ (i + 1)))
    (hj : r ∈ Ioc (τ j : ℝ) (τ (j + 1))) : i = j := by
  by_contra hne
  obtain h | h := lt_or_gt_of_ne hne
  · have hh : (τ (i + 1) : ℝ) ≤ τ j := hτ (Nat.succ_le_of_lt h)
    exact (not_lt_of_ge (hi.2.trans hh)) hj.1
  · have hh : (τ (j + 1) : ℝ) ≤ τ i := hτ (Nat.succ_le_of_lt h)
    exact (not_lt_of_ge (hj.2.trans hh)) hi.1

/-- At a grid-cell point the raw sum has exactly its left-endpoint value. -/
theorem rawGrid_eq (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (A : ℕ → R) (n : ℕ)
    (k : Fin n) (r : ℝ) (hk : r ∈ Ioc (τ k : ℝ) (τ (k + 1))) :
    rawGrid τ A n r = A k := by
  classical
  unfold rawGrid
  rw [Finset.sum_eq_single k]
  · exact Set.indicator_of_mem hk _
  · intro j _ hj
    apply Set.indicator_of_notMem
    intro hm
    exact hj (Fin.ext (interval_unique τ hτ j k r hm hk))
  · simp

/-- Outside the full interval every actual grid cell contributes zero. -/
theorem rawGrid_zero_outside (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (A : ℕ → R) (n : ℕ)
    (r : ℝ) (hr : r ∉ Ioc (τ 0 : ℝ) (τ n)) : rawGrid τ A n r = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  apply Set.indicator_of_notMem
  intro hk
  apply hr
  exact ⟨lt_of_le_of_lt (show (τ 0 : ℝ) ≤ τ k from hτ (Nat.zero_le _)) hk.1,
    hk.2.trans (show (τ (k + 1) : ℝ) ≤ τ n from hτ (Nat.succ_le_of_lt k.isLt))⟩

/-- Dyadic mesh widths tend to zero on every fixed finite horizon. -/
theorem dyadic_mesh_tendsto (T : ℝ≥0) :
    Tendsto (fun n : ℕ => (T : ℝ) / (2 : ℝ) ^ n) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (T : ℝ)
  simpa [div_eq_mul_inv, inv_pow] using h

/-- Literal dyadic finite sums converge at every continuity point in the horizon. -/
theorem rawGrid_dyadic_tendsto (T : ℝ≥0) (u : ℝ → R) (r : ℝ)
    (hr : r ∈ Ioc 0 (T : ℝ)) (hu : ContinuousAt u r) :
    Tendsto (fun n => rawGrid ((GridIntegralCompletion.dyadicGrids T).time n)
      (fun k => u ((GridIntegralCompletion.dyadicGrids T).time n k))
      ((GridIntegralCompletion.dyadicGrids T).count n) r) atTop (𝓝 (u r)) := by
  let G := GridIntegralCompletion.dyadicGrids T
  have hzero (n : ℕ) : G.time n 0 = 0 := by simp [G, GridIntegralCompletion.dyadicGrids]
  have hend (n : ℕ) : G.time n (G.count n) = T := by
    simp only [G, GridIntegralCompletion.dyadicGrids, Nat.cast_pow, Nat.cast_ofNat]
    have hp : (2 : ℝ≥0) ^ n ≠ 0 := by positivity
    field_simp
  have hcell (n : ℕ) := exists_interval (G.time n) (G.monotone n) (G.count n) r
    (by simpa only [hzero, hend, NNReal.coe_zero] using hr)
  choose k hk using hcell
  have hdist (n : ℕ) : dist (G.time n (k n) : ℝ) r ≤ (T : ℝ) / 2 ^ n := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hk n).1.le)]
    have he : (G.time n ((k n : ℕ) + 1) : ℝ) =
        (G.time n (k n) : ℝ) + (T : ℝ) / 2 ^ n := by
      simp only [G, GridIntegralCompletion.dyadicGrids, NNReal.coe_mul, NNReal.coe_div,
        NNReal.coe_pow, NNReal.coe_ofNat, NNReal.coe_natCast]
      push_cast
      ring
    linarith [(hk n).2]
  have hleft : Tendsto (fun n => (G.time n (k n) : ℝ)) atTop (𝓝 r) :=
    Metric.tendsto_atTop.mpr fun ε hε => by
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (dyadic_mesh_tendsto T) ε hε
      refine ⟨N, fun n hn => (hdist n).trans_lt ?_⟩
      have hh := hN n hn
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ (T : ℝ) / 2 ^ n)] using hh
  have hout := hu.tendsto.comp hleft
  convert hout using 1
  funext n
  exact rawGrid_eq (G.time n) (G.monotone n) _ (G.count n) (k n) r (hk n)



/-- A bounded measurable time integrand on a finite horizon is genuinely in time-L². -/
theorem horizon_memLp (T : ℝ≥0) (u : ℝ → R)
    (hu : AEStronglyMeasurable u (volume : Measure ℝ)) (P : ℝ)
    (hP : ∀ r ∈ Icc 0 (T : ℝ), ‖u r‖ ≤ P) :
    MemLp ((Ioc 0 (T : ℝ)).indicator u) 2 (volume : Measure ℝ) := by
  rw [memLp_indicator_iff_restrict measurableSet_Ioc]
  apply MemLp.of_bound hu.restrict P
  exact ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => hP r ⟨hr.1.le, hr.2⟩

/-- The actual finite-horizon time-L² integrand. -/
def horizonLp (T : ℝ≥0) (u : ℝ → R)
    (hu : AEStronglyMeasurable u (volume : Measure ℝ)) (P : ℝ)
    (hP : ∀ r ∈ Icc 0 (T : ℝ), ‖u r‖ ≤ P) : Lp R 2 (volume : Measure ℝ) :=
  (horizon_memLp T u hu P hP).toLp ((Ioc 0 (T : ℝ)).indicator u)

/-- Actual dyadic sums remain bounded by the original integrand bound. -/
theorem rawGrid_dyadic_bound (T : ℝ≥0) (u : ℝ → R) (P : ℝ) (hP0 : 0 ≤ P)
    (hP : ∀ r ∈ Icc 0 (T : ℝ), ‖u r‖ ≤ P) (n : ℕ) (r : ℝ) :
    ‖rawGrid ((GridIntegralCompletion.dyadicGrids T).time n)
      (fun k => u ((GridIntegralCompletion.dyadicGrids T).time n k))
      ((GridIntegralCompletion.dyadicGrids T).count n) r‖ ≤
        (Ioc 0 (T : ℝ)).indicator (fun _ => P) r := by
  let G := GridIntegralCompletion.dyadicGrids T
  have hzero : G.time n 0 = 0 := by simp [G, GridIntegralCompletion.dyadicGrids]
  have hend : G.time n (G.count n) = T := by
    simp only [G, GridIntegralCompletion.dyadicGrids, Nat.cast_pow, Nat.cast_ofNat]
    have hp : (2 : ℝ≥0) ^ n ≠ 0 := by positivity
    field_simp
  by_cases hr : r ∈ Ioc 0 (T : ℝ)
  · obtain ⟨k, hk⟩ := exists_interval (G.time n) (G.monotone n) (G.count n) r
      (by simpa only [hzero, hend, NNReal.coe_zero] using hr)
    rw [rawGrid_eq (G.time n) (G.monotone n) _ (G.count n) k r hk,
      Set.indicator_of_mem hr]
    apply hP
    exact ⟨(G.time n k).coe_nonneg,
      show (G.time n k : ℝ) ≤ T from by
        rw [← hend]
        exact G.monotone n k.isLt.le⟩
  · rw [rawGrid_zero_outside (G.time n) (G.monotone n) _ (G.count n) r
      (by simpa only [hzero, hend, NNReal.coe_zero] using hr), norm_zero,
        Set.indicator_of_notMem hr]

/-- Literal dyadic time-step functions converge in genuine time-L² to every
bounded measurable integrand continuous almost everywhere on the horizon.
Deterministic interval masks are permitted because their endpoints are null. -/
theorem dyadic_grid_tendsto (T : ℝ≥0) (u : ℝ → R)
    (hu : AEStronglyMeasurable u (volume : Measure ℝ)) (P : ℝ) (hP0 : 0 ≤ P)
    (hP : ∀ r ∈ Icc 0 (T : ℝ), ‖u r‖ ≤ P)
    (hcont : ∀ᵐ r ∂(volume : Measure ℝ).restrict (Ioc 0 (T : ℝ)), ContinuousAt u r) :
    Tendsto (fun n => TimeGridEnergy.grid ((GridIntegralCompletion.dyadicGrids T).time n)
      (fun k => u ((GridIntegralCompletion.dyadicGrids T).time n k))
      ((GridIntegralCompletion.dyadicGrids T).count n)) atTop
      (𝓝 (horizonLp T u hu P hP)) := by
  let G := GridIntegralCompletion.dyadicGrids T
  let U := horizonLp T u hu P hP
  let S (n : ℕ) := TimeGridEnergy.grid (G.time n) (fun k => u (G.time n k)) (G.count n)
  have hU : U =ᵐ[volume] (Ioc 0 (T : ℝ)).indicator u := (horizon_memLp T u hu P hP).coeFn_toLp
  have hS (n : ℕ) := grid_coe (G.time n) (fun k => u (G.time n k)) (G.count n)
  have hcont' : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioc 0 (T : ℝ) → ContinuousAt u r :=
    (ae_restrict_iff' measurableSet_Ioc).mp hcont
  have hbound (n : ℕ) : ∀ᵐ r ∂(volume : Measure ℝ), ‖(S n - U) r‖ ^ 2 ≤
      (Ioc 0 (T : ℝ)).indicator (fun _ => (2 * P) ^ 2) r := by
    filter_upwards [hS n, hU, Lp.coeFn_sub (S n) U] with r hs hu hsub
    rw [hsub, Pi.sub_apply, hs, hu]
    by_cases hr : r ∈ Ioc 0 (T : ℝ)
    · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr]
      have hb := rawGrid_dyadic_bound T u P hP0 hP n r
      rw [Set.indicator_of_mem hr] at hb
      have he : ‖rawGrid (G.time n) (fun k => u (G.time n k)) (G.count n) r - u r‖ ≤ 2 * P :=
        (norm_sub_le _ _).trans (by linarith [hP r ⟨hr.1.le, hr.2⟩])
      exact pow_le_pow_left₀ (norm_nonneg _) he 2
    · have hb := rawGrid_dyadic_bound T u P hP0 hP n r
      rw [Set.indicator_of_notMem hr] at hb
      have hz : rawGrid (G.time n) (fun k => u (G.time n k)) (G.count n) r = 0 :=
        norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
      rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr, hz, sub_zero, norm_zero, zero_pow (by decide)]
  have hlim : ∀ᵐ r ∂(volume : Measure ℝ),
      Tendsto (fun n => ‖(S n - U) r‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [ae_all_iff.mpr hS, hU, hcont',
      ae_all_iff.mpr (fun n => Lp.coeFn_sub (S n) U)] with r hs hu hc hsub
    have ht : Tendsto (fun n => S n r) atTop (𝓝 (U r)) := by
      by_cases hr : r ∈ Ioc 0 (T : ℝ)
      · rw [hu, Set.indicator_of_mem hr]
        exact (rawGrid_dyadic_tendsto T u r hr (hc hr)).congr (fun n => (hs n).symm)
      · have hz (n : ℕ) : S n r = 0 := by
          have hb := rawGrid_dyadic_bound T u P hP0 hP n r
          rw [Set.indicator_of_notMem hr, ← hs n] at hb
          exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
        simp only [hu, Set.indicator_of_notMem hr, hz]
        exact tendsto_const_nhds
    have he := (ht.sub_const (U r)).norm.pow 2
    have he' : Tendsto (fun n => ‖S n r - U r‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
      simpa only [sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using he
    convert he' using 1
    funext n
    rw [hsub n]
    rfl
  have hDCT := tendsto_integral_of_dominated_convergence
    ((Ioc 0 (T : ℝ)).indicator (fun _ => (2 * P) ^ 2))
    (fun n => (Lp.aestronglyMeasurable (S n - U)).norm.pow 2)
    ((integrableOn_const (C := (2 * P) ^ 2) (s := Ioc 0 (T : ℝ))
      (μ := (volume : Measure ℝ)) (by simp)).integrable_indicator measurableSet_Ioc)
    (fun n => (hbound n).mono fun r hr => by rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]) hlim
  have hsq : Tendsto (fun n => ‖S n - U‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [ProximalLangevin.lp_norm_sq_eq_integral, Pi.pow_apply, integral_zero] using hDCT
  have hn := (Real.continuous_sqrt.tendsto 0).comp hsq
  have hn' : Tendsto (fun n => ‖S n - U‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn'



/-- A deterministic interval mask of a continuous integrand is continuous
almost everywhere; neither boundary value changes its actual time-L² class. -/
theorem continuous_mask_ae (u : ℝ → R) (hu : Continuous u) (s t : ℝ) :
    ∀ᵐ r ∂(volume : Measure ℝ), ContinuousAt ((Ioc s t).indicator u) r := by
  by_cases hst : s < t
  · have hfront : (volume : Measure ℝ) (frontier (Ioc s t)) = 0 := by
      rw [frontier_Ioc hst]
      exact (Set.toFinite _).measure_zero _
    filter_upwards [compl_mem_ae_iff.mpr hfront] with r hr
    exact hu.continuousOn.continuousAt_indicator hr
  · have he : Ioc s t = ∅ := Ioc_eq_empty hst
    simp only [he, Set.indicator_empty]
    exact ae_of_all _ fun _ => continuousAt_const

/-- Continuous integrands and all their deterministic interval cuts have
literal dyadic approximations in actual time-L². -/
theorem dyadic_masked_grid_tendsto (T : ℝ≥0) (u : ℝ → R) (hu : Continuous u)
    (s t P : ℝ) (hP0 : 0 ≤ P) (hP : ∀ r ∈ Icc 0 (T : ℝ), ‖u r‖ ≤ P) :
    let v := (Ioc s t).indicator u
    let hvm : AEStronglyMeasurable v (volume : Measure ℝ) :=
      hu.aestronglyMeasurable.indicator measurableSet_Ioc
    let hvP : ∀ r ∈ Icc 0 (T : ℝ), ‖v r‖ ≤ P := fun r hr => by
      exact le_trans (norm_indicator_le_norm_self u r) (hP r hr)
    Tendsto (fun n => TimeGridEnergy.grid ((GridIntegralCompletion.dyadicGrids T).time n)
      (fun k => v ((GridIntegralCompletion.dyadicGrids T).time n k))
      ((GridIntegralCompletion.dyadicGrids T).count n)) atTop
      (𝓝 (horizonLp T v hvm P hvP)) := by
  dsimp only
  apply dyadic_grid_tendsto T _ _ P hP0
  exact ae_restrict_of_ae (continuous_mask_ae u hu s t)

/-- Continuity supplies the required finite-horizon radius from compactness. -/
theorem exists_horizon_bound (T : ℝ≥0) (u : ℝ → R) (hu : Continuous u) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ r ∈ Icc 0 (T : ℝ), ‖u r‖ ≤ P := by
  obtain ⟨P, hP⟩ := isCompact_Icc.exists_bound_of_continuousOn hu.continuousOn
  exact ⟨max 0 P, le_max_left _ _, fun r hr => (hP r hr).trans (le_max_right _ _)⟩

end PBGSO.TimeGridContinuity
