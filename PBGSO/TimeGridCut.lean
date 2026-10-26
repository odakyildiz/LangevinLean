import PBGSO.TimeGridContinuity

/-! # Splitting actual time grids at one deterministic cut -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped NNReal ENNReal
namespace PBGSO.TimeGridCut

/-- Insert the cut, clamped inside each original cell. -/
def splitTime (τ : ℕ → ℝ≥0) (t : ℝ≥0) (j : ℕ) : ℝ≥0 :=
  if j % 2 = 0 then τ (j / 2) else max (τ (j / 2)) (min t (τ (j / 2 + 1)))

@[simp] theorem splitTime_even (τ : ℕ → ℝ≥0) (t : ℝ≥0) (k : ℕ) :
    splitTime τ t (2 * k) = τ k := by simp [splitTime]

@[simp] theorem splitTime_odd (τ : ℕ → ℝ≥0) (t : ℝ≥0) (k : ℕ) :
    splitTime τ t (2 * k + 1) = max (τ k) (min t (τ (k + 1))) := by
  simp [splitTime, Nat.add_div]

/-- Every inserted midpoint lies between its two original endpoints. -/
theorem midpoint_bounds (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (t : ℝ≥0) (k : ℕ) :
    τ k ≤ max (τ k) (min t (τ (k + 1))) ∧
      max (τ k) (min t (τ (k + 1))) ≤ τ (k + 1) :=
  ⟨le_max_left _ _, max_le (hτ (Nat.le_succ k)) (min_le_right _ _)⟩

/-- The split grid is an actual monotone refinement, including empty subcells. -/
theorem splitTime_monotone (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (t : ℝ≥0) :
    Monotone (splitTime τ t) := by
  apply monotone_nat_of_le_succ
  intro j
  by_cases hj : j % 2 = 0
  · obtain ⟨k, hk⟩ : ∃ k, j = 2 * k := ⟨j / 2, by omega⟩
    subst j
    simpa only [splitTime_even, splitTime_odd] using (midpoint_bounds τ hτ t k).1
  · obtain ⟨k, hk⟩ : ∃ k, j = 2 * k + 1 := ⟨j / 2, by omega⟩
    subst j
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega, splitTime_odd, splitTime_even]
    exact (midpoint_bounds τ hτ t k).2

variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℝ R] [CompleteSpace R]

/-- Keep each original coefficient before the cut, and put zero after it. -/
def splitValues (A : ℕ → R) (j : ℕ) : R := if j % 2 = 0 then A (j / 2) else 0

@[simp] theorem splitValues_even (A : ℕ → R) (k : ℕ) : splitValues A (2 * k) = A k := by
  simp [splitValues]

@[simp] theorem splitValues_odd (A : ℕ → R) (k : ℕ) : splitValues A (2 * k + 1) = 0 := by
  simp [splitValues, Nat.add_div]

/-- Literal interval restriction in actual time-L². -/
def cut (U : Lp R 2 (volume : Measure ℝ)) (s t : ℝ) : Lp R 2 (volume : Measure ℝ) :=
  ((Lp.memLp U).indicator measurableSet_Ioc).toLp ((Ioc s t).indicator U)

theorem cut_coe (U : Lp R 2 (volume : Measure ℝ)) (s t : ℝ) :
    cut U s t =ᵐ[volume] (Ioc s t).indicator U :=
  ((Lp.memLp U).indicator measurableSet_Ioc).coeFn_toLp

theorem cut_zero (s t : ℝ) : cut (0 : Lp R 2 (volume : Measure ℝ)) s t = 0 := by
  apply Lp.ext
  filter_upwards [cut_coe (0 : Lp R 2 (volume : Measure ℝ)) s t,
    Lp.coeFn_zero R 2 (volume : Measure ℝ)] with r hc hz
  rw [hc]
  by_cases hr : r ∈ Ioc s t
  · rw [Set.indicator_of_mem hr, hz]
  · rw [Set.indicator_of_notMem hr, hz]
    rfl

theorem cut_add (U V : Lp R 2 (volume : Measure ℝ)) (s t : ℝ) :
    cut (U + V) s t = cut U s t + cut V s t := by
  apply Lp.ext
  filter_upwards [cut_coe (U + V) s t, cut_coe U s t, cut_coe V s t,
    Lp.coeFn_add (cut U s t) (cut V s t), Lp.coeFn_add U V] with r hsum hU hV ha hUV
  rw [ha, hsum]
  simp only [Pi.add_apply]
  rw [hU, hV]
  by_cases hr : r ∈ Ioc s t
  · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr, Set.indicator_of_mem hr, hUV]
    rfl
  · simp only [Set.indicator_of_notMem hr, zero_add]

theorem column_zero (a b : ℝ) : TimeGridEnergy.column a b (0 : R) = 0 := by
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (μ := (volume : Measure ℝ)) (p := 2)
    (hs := measurableSet_Ioc) (hμs := by simp) (c := (0 : R)) (s := Ioc a b),
    Lp.coeFn_zero R 2 (volume : Measure ℝ)] with r hc hz
  change (TimeGridEnergy.column a b (0 : R)) r = _ at hc
  rw [hc, hz]
  simp

/-- Clamping a cell endpoint describes its actual interval intersection. -/
theorem cell_intersection (a b t : ℝ≥0) :
    Ioc 0 (t : ℝ) ∩ Ioc (a : ℝ) (b : ℝ) = Ioc (a : ℝ) (max a (min t b) : ℝ≥0) := by
  ext r
  simp only [Set.mem_inter_iff, Set.mem_Ioc, NNReal.coe_max, NNReal.coe_min]
  constructor
  · rintro ⟨⟨_, hrt⟩, hra, hrb⟩
    exact ⟨hra, (le_min hrt hrb).trans (le_max_right _ _)⟩
  · rintro ⟨hra, hrm⟩
    have hm : r ≤ min (t : ℝ) b := (le_max_iff.mp hrm).resolve_left (not_le.mpr hra)
    exact ⟨⟨lt_of_le_of_lt a.coe_nonneg hra, hm.trans (min_le_left _ _)⟩,
      hra, hm.trans (min_le_right _ _)⟩

/-- The first split cell is exactly the cut of the original time-L² column. -/
theorem cut_column (a b t : ℝ≥0) (z : R) :
    cut (TimeGridEnergy.column a b z) 0 t = TimeGridEnergy.column a (max a (min t b)) z := by
  apply Lp.ext
  filter_upwards [cut_coe (TimeGridEnergy.column a b z) 0 t,
    indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc) (hμs := by simp)
      (c := z) (s := Ioc (a : ℝ) b),
    indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc) (hμs := by simp)
      (c := z) (s := Ioc (a : ℝ) (max a (min t b) : ℝ≥0))] with r hc hcol hmid
  change (TimeGridEnergy.column (a : ℝ) (b : ℝ) z) r = _ at hcol
  change (TimeGridEnergy.column (a : ℝ) (max a (min t b) : ℝ≥0) z) r = _ at hmid
  simp only [NNReal.coe_max, NNReal.coe_min] at hmid
  rw [hc, hmid]
  have he := congrArg (fun s : Set ℝ => s.indicator (fun _ => z) r) (cell_intersection a b t)
  rw [← Set.indicator_indicator] at he
  simp only [NNReal.coe_max, NNReal.coe_min] at he
  by_cases hr : r ∈ Ioc 0 (t : ℝ)
  · rw [Set.indicator_of_mem hr, hcol]
    simpa only [Set.indicator_of_mem hr] using he
  · rw [Set.indicator_of_notMem hr]
    simpa only [Set.indicator_of_notMem hr] using he

/-- The actual split-grid coefficient embedding is exactly a literal time cut.
This includes repeated knots and cuts outside the original horizon. -/
theorem split_grid_eq_cut (τ : ℕ → ℝ≥0) (A : ℕ → R) (t : ℝ≥0) (n : ℕ) :
    TimeGridEnergy.grid (splitTime τ t) (splitValues A) (2 * n) =
      cut (TimeGridEnergy.grid τ A n) 0 t := by
  induction n with
  | zero => simp [TimeGridEnergy.grid_zero, cut_zero]
  | succ n ih =>
    rw [Nat.mul_succ, show 2 * n + 2 = (2 * n + 1) + 1 by omega,
      TimeGridEnergy.grid_succ, TimeGridEnergy.grid_succ,
      splitValues_odd, splitValues_even, splitTime_odd, splitTime_even,
      show 2 * n + 1 + 1 = 2 * (n + 1) by omega, splitTime_even]
    rw [column_zero, add_zero, ih, TimeGridEnergy.grid_succ, cut_add, cut_column]
    simp only [NNReal.coe_max, NNReal.coe_min]

end PBGSO.TimeGridCut
