import PBGSO.PredictableIsometry

/-! Exact time-L² energy of finite left-step functions. -/
noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory Set
open scoped NNReal RealInnerProductSpace InnerProductSpace
namespace PBGSO.TimeGridEnergy
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℝ R] [CompleteSpace R]

def column (s t : ℝ) (a : R) : Lp R 2 (volume : Measure ℝ) :=
  indicatorConstLp 2 measurableSet_Ioc (by simp) a (s := Ioc s t)

def grid (τ : ℕ → ℝ≥0) (A : ℕ → R) (n : ℕ) : Lp R 2 (volume : Measure ℝ) :=
  ∑ k : Fin n, column (τ k) (τ (k + 1)) (A k)

theorem column_inner (s t u v : ℝ) (a b : R) :
    ⟪column s t a, column u v b⟫_ℝ =
      ((volume : Measure ℝ).real (Ioc s t ∩ Ioc u v)) * ⟪a, b⟫_ℝ := by
  simpa only [column, smul_eq_mul] using
    (L2.inner_indicatorConstLp_indicatorConstLp (𝕜 := ℝ) (μ := (volume : Measure ℝ))
      (s := Ioc s t) (t := Ioc u v) measurableSet_Ioc measurableSet_Ioc
      (by simp) (by simp) a b)

theorem grid_column_inner (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (A : ℕ → R)
    (i j : ℕ) :
    ⟪column (τ i) (τ (i + 1)) (A i), column (τ j) (τ (j + 1)) (A j)⟫_ℝ =
      if i = j then ((τ (i + 1) : ℝ) - τ i) * ‖A i‖ ^ 2 else 0 := by
  rw [column_inner]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, Set.inter_self, real_inner_self_eq_norm_sq]
    simp only [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal
      (sub_nonneg.mpr (show (τ i : ℝ) ≤ τ (i + 1) from hτ (Nat.le_succ i)))]
  · rw [ite_eq_right hij]
    have hd : Disjoint (Ioc (τ i : ℝ) (τ (i + 1))) (Ioc (τ j : ℝ) (τ (j + 1))) := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      obtain h | h := lt_or_gt_of_ne hij
      · have hh : (τ (i + 1) : ℝ) ≤ τ j := hτ (Nat.succ_le_of_lt h)
        exact (not_lt_of_ge (hx.2.trans hh)) hy.1
      · have hh : (τ (j + 1) : ℝ) ≤ τ i := hτ (Nat.succ_le_of_lt h)
        exact (not_lt_of_ge (hy.2.trans hh)) hx.1
    have he : Ioc (τ i : ℝ) (τ (i + 1)) ∩ Ioc (τ j : ℝ) (τ (j + 1)) = ∅ :=
      Set.disjoint_iff_inter_eq_empty.mp hd
    rw [he]
    simp

theorem grid_norm_sq (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (A : ℕ → R) (n : ℕ) :
    ‖grid τ A n‖ ^ 2 = ∑ k : Fin n, ((τ (k + 1) : ℝ) - τ k) * ‖A k‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [grid, sum_inner, inner_sum]
  simp_rw [grid_column_inner τ hτ A]
  simp only [Fin.val_inj]
  simp




theorem column_sub (s t : ℝ) (a b : R) :
    column s t (a - b) = column s t a - column s t b :=
  indicatorConstLp_sub.symm

theorem grid_sub (τ : ℕ → ℝ≥0) (A C : ℕ → R) (n : ℕ) :
    grid τ (A - C) n = grid τ A n - grid τ C n := by
  simp only [grid, Pi.sub_apply, column_sub, Finset.sum_sub_distrib]

theorem column_split (s u t : ℝ) (hsu : s ≤ u) (hut : u ≤ t) (a : R) :
    column s u a + column u t a = column s t a := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (column s u a) (column u t a),
    indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc) (hμs := by simp) (c := a)
      (s := Ioc s u),
    indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc) (hμs := by simp) (c := a)
      (s := Ioc u t),
    indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc) (hμs := by simp) (c := a)
      (s := Ioc s t)] with r hadd h1 h2 h3
  rw [hadd]
  change column s u a r + column u t a r = column s t a r
  change column s u a r = _ at h1
  change column u t a r = _ at h2
  change column s t a r = _ at h3
  rw [h1, h2, h3]
  by_cases hrs : r ≤ s
  · have hru : r ≤ u := hrs.trans hsu
    simp [Set.indicator, Set.mem_Ioc, not_lt.mpr hrs, not_lt.mpr hru]
  · have hsr : s < r := lt_of_not_ge hrs
    by_cases hru : r ≤ u
    · have hrt : r ≤ t := hru.trans hut
      simp [Set.indicator, Set.mem_Ioc, hsr, hru, hrt, not_lt.mpr hru]
    · have hur : u < r := lt_of_not_ge hru
      simp [Set.indicator, Set.mem_Ioc, hsr, hur, hru]

theorem grid_succ (τ : ℕ → ℝ≥0) (A : ℕ → R) (n : ℕ) :
    grid τ A (n + 1) = grid τ A n + column (τ n) (τ (n + 1)) (A n) := by
  simp only [grid, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

theorem grid_zero (τ : ℕ → ℝ≥0) (A : ℕ → R) : grid τ A 0 = 0 := by simp [grid]

theorem constant_block_sum (υ : ℕ → ℝ≥0) (hυ : Monotone υ) (a d : ℕ) (z : R) :
    (∑ j ∈ Finset.range d, column (υ (a + j)) (υ (a + j + 1)) z) =
      column (υ a) (υ (a + d)) z := by
  induction d with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]
    apply Lp.ext
    filter_upwards [Lp.coeFn_zero (E := R) (μ := (volume : Measure ℝ)) (p := 2),
      indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc)
      (hμs := by simp) (c := z) (s := Ioc (υ a : ℝ) (υ a))] with r hz hr
    rw [hz]
    simpa only [Set.Ioc_self, Set.indicator_empty, Pi.zero_apply, column] using hr.symm
  | succ d ih =>
    rw [Finset.sum_range_succ, ih]
    exact column_split _ _ _ (hυ (Nat.le_add_right a d)) (hυ (Nat.le_succ _)) z

/-- Refining a time-step function preserves the actual time-L² element. -/
theorem grid_refine_mul (τ υ : ℕ → ℝ≥0) (hυmono : Monotone υ)
    (d : ℕ) (hd : 0 < d) (hυ : ∀ k, υ (d * k) = τ k) (A : ℕ → R) (n : ℕ) :
    grid υ (fun k => A (k / d)) (d * n) = grid τ A n := by
  have h1 (m : ℕ) : grid υ (fun k => A (k / d)) m =
      ∑ j ∈ Finset.range m, column (υ j) (υ (j + 1)) (A (j / d)) :=
    Fin.sum_univ_eq_sum_range (fun j => column (υ j) (υ (j + 1)) (A (j / d))) m
  have h2 (m : ℕ) : grid τ A m =
      ∑ j ∈ Finset.range m, column (τ j) (τ (j + 1)) (A j) :=
    Fin.sum_univ_eq_sum_range (fun j => column (τ j) (τ (j + 1)) (A j)) m
  rw [h1, h2]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    have he : (∑ j ∈ Finset.range d,
        column (υ (d * n + j)) (υ (d * n + j + 1)) (A ((d * n + j) / d))) =
        ∑ j ∈ Finset.range d,
          column (υ (d * n + j)) (υ (d * n + j + 1)) (A n) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Nat.mul_add_div hd, Nat.div_eq_of_lt (Finset.mem_range.mp hj), add_zero]
    rw [he, constant_block_sum υ hυmono]
    rw [show d * n + d = d * (n + 1) by ring, hυ n, hυ (n + 1)]

end PBGSO.TimeGridEnergy
