import PBGSO.StoppingSteps

/-! # Actual bounded stopping times approximated from above on dyadic grids -/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology
namespace PBGSO.FilteredBrownian
variable {Ω I : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

/-- The final actual dyadic knot is precisely the horizon, including T=0. -/
theorem dyadic_time_last (T : ℝ≥0) (m : ℕ) :
    (dyadicGrids T).time m ((dyadicGrids T).count m) = T := by
  simp only [GridIntegralCompletion.dyadicGrids, Nat.cast_pow, Nat.cast_ofNat]
  have hp : (2 : ℝ≥0) ^ m ≠ 0 := by positivity
  field_simp

/-- The deterministic adjacent-mesh identity used in the stopping ceiling estimate. -/
theorem dyadic_time_succ (T : ℝ≥0) (m k : ℕ) :
    ((dyadicGrids T).time m (k + 1) : ℝ) =
      ((dyadicGrids T).time m k : ℝ) + (T : ℝ) / (2 : ℝ) ^ m := by
  simp only [GridIntegralCompletion.dyadicGrids, Nat.cast_add, Nat.cast_one,
    NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_natCast, NNReal.coe_ofNat]
  ring

/-- The first actual dyadic knot not earlier than the supplied stopping time. -/
def dyadicStopIndex (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (m : ℕ) (ω : Ω) : ℕ :=
  Nat.find (show ∃ k, τ ω ≤ (dyadicGrids T).time m k from
    ⟨(dyadicGrids T).count m, by rw [dyadic_time_last]; exact hτ ω⟩)

theorem dyadicStopIndex_spec (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (m : ℕ) (ω : Ω) : τ ω ≤ (dyadicGrids T).time m (dyadicStopIndex T τ hτ m ω) :=
by
  unfold dyadicStopIndex
  exact Nat.find_spec (p := fun k => τ ω ≤ (dyadicGrids T).time m k) _

theorem dyadicStopIndex_le_iff (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (m k : ℕ) (ω : Ω) :
    dyadicStopIndex T τ hτ m ω ≤ k ↔ τ ω ≤ (dyadicGrids T).time m k := by
  constructor
  · intro hk
    exact (dyadicStopIndex_spec T τ hτ m ω).trans ((dyadicGrids T).monotone m hk)
  · intro hk
    unfold dyadicStopIndex
    exact Nat.find_min' _ hk

/-- The dyadic ceiling has genuine stopping events in the original actual
Brownian filtration. No stopping-approximation property is supplied. -/
def dyadicStoppingIndex (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (hstop : ∀ t, MeasurableSet[D.filtration t] {ω | τ ω ≤ t}) (m : ℕ) :
    GridStoppingIndex Q D ((dyadicGrids T).time m) ((dyadicGrids T).count m) where
  index := dyadicStopIndex T τ hτ m
  bound ω := (dyadicStopIndex_le_iff T τ hτ m _ ω).mpr (by
    rw [dyadic_time_last]; exact hτ ω)
  stopping k := by
    have he : {ω | dyadicStopIndex T τ hτ m ω ≤ k} =
        {ω | τ ω ≤ (dyadicGrids T).time m k} := by
      ext ω
      exact dyadicStopIndex_le_iff T τ hτ m k ω
    rw [he]
    exact hstop _

/-- Actual random stopping knot, on the same source probability space. -/
def dyadicStop (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (m : ℕ) (ω : Ω) : ℝ≥0 :=
  (dyadicGrids T).time m (dyadicStopIndex T τ hτ m ω)

theorem dyadicStop_bounds (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (m : ℕ) (ω : Ω) : τ ω ≤ dyadicStop T τ hτ m ω ∧ dyadicStop T τ hτ m ω ≤ T := by
  refine ⟨dyadicStopIndex_spec T τ hτ m ω, ?_⟩
  calc
    dyadicStop T τ hτ m ω ≤ (dyadicGrids T).time m ((dyadicGrids T).count m) :=
      (dyadicGrids T).monotone m ((dyadicStopIndex_le_iff T τ hτ m _ ω).mpr (by
        rw [dyadic_time_last]; exact hτ ω))
    _ = T := dyadic_time_last T m

theorem dyadicStop_error (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (m : ℕ) (ω : Ω) :
    (dyadicStop T τ hτ m ω : ℝ) ≤ (τ ω : ℝ) + (T : ℝ) / (2 : ℝ) ^ m := by
  have hspec := dyadicStopIndex_spec T τ hτ m ω
  cases he : dyadicStopIndex T τ hτ m ω with
  | zero =>
    rw [dyadicStop, he]
    simp only [GridIntegralCompletion.dyadicGrids, Nat.cast_zero, zero_mul, NNReal.coe_zero]
    positivity
  | succ k =>
    have hprev : ¬ τ ω ≤ (dyadicGrids T).time m k := by
      intro hk
      have hi := (dyadicStopIndex_le_iff T τ hτ m k ω).mpr hk
      rw [he] at hi
      omega
    have hlt : ((dyadicGrids T).time m k : ℝ) < (τ ω : ℝ) := by
      exact_mod_cast lt_of_not_ge hprev
    rw [dyadicStop, he, dyadic_time_succ]
    exact add_le_add hlt.le le_rfl

/-- The derived finite stopping times converge to the original bounded
stopping time at every sample, in actual real time. -/
theorem dyadicStop_tendsto_real (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (ω : Ω) : Tendsto (fun m => (dyadicStop T τ hτ m ω : ℝ)) atTop (𝓝 (τ ω : ℝ)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    ((tendsto_order.mp (TimeGridContinuity.dyadic_mesh_tendsto T)).2 ε hε)
  refine ⟨M, fun m hm => ?_⟩
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast (dyadicStop_bounds T τ hτ m ω).1))]
  have he := dyadicStop_error T τ hτ m ω
  linarith [hM m hm]

theorem dyadicStop_tendsto (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (ω : Ω) : Tendsto (fun m => dyadicStop T τ hτ m ω) atTop (𝓝 (τ ω)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp (dyadicStop_tendsto_real T τ hτ ω) ε hε
  exact ⟨M, fun m hm => hM m hm⟩

/-- The stopping indicators stabilize pointwise, including atoms at the
stopping boundary because the approximation is always from above. -/
theorem dyadicStop_indicator_eventually (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (r : ℝ) (ω : Ω) :
    ∀ᶠ m in atTop, (r ≤ (dyadicStop T τ hτ m ω : ℝ) ↔ r ≤ (τ ω : ℝ)) := by
  by_cases hr : r ≤ (τ ω : ℝ)
  · exact Eventually.of_forall (fun m => iff_of_true
      (hr.trans (by exact_mod_cast (dyadicStop_bounds T τ hτ m ω).1)) hr)
  · have he := (tendsto_order.mp (dyadicStop_tendsto_real T τ hτ ω)).2 r (lt_of_not_ge hr)
    exact he.mono (fun m hm => iff_of_false (not_le_of_gt hm) hr)

end PBGSO.FilteredBrownian
