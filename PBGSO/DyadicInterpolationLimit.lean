import PBGSO.DyadicInterpolation
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Continuous limits of the actual dyadic polygons
Summable eventual adjacent-increment bounds imply convergence in the actual
Banach space of continuous functions on the unit interval.
-/
noncomputable section
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology
namespace PBGSO.DyadicInterpolation
variable {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R] [CompleteSpace R]

abbrev UnitWindow := Icc (0 : ℝ) 1

def dyadicMap (n : ℕ) (F : ℝ → R) : C(UnitWindow, R) :=
  ⟨fun t => dyadicPolygon n F t, (dyadicPolygon_continuous n F).comp continuous_subtype_val⟩

theorem dyadicMap_succ_bound (n : ℕ) (F : ℝ → R) (a : ℝ) (ha : 0 ≤ a)
    (hstep : ∀ j < 2 ^ (n + 1),
      ‖F (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) -
        F ((j : ℝ) / (2 : ℝ) ^ (n + 1))‖ ≤ a) :
    dist (dyadicMap n F) (dyadicMap (n + 1) F) ≤ 5 * a := by
  rw [dist_comm, dist_eq_norm]
  apply (ContinuousMap.norm_le (dyadicMap (n + 1) F - dyadicMap n F) (by positivity)).mpr
  intro t
  exact dyadicPolygon_succ_bound n F a ha hstep t t.property

/-- No continuity of the original curve is assumed: eventual fine-grid
increment bounds with summable deterministic thresholds construct a continuous
uniform polygon limit. -/
theorem exists_dyadicMap_limit (F : ℝ → R) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hsum : Summable a)
    (hstep : ∀ᶠ n in atTop, ∀ j < 2 ^ (n + 1),
      ‖F (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) -
        F ((j : ℝ) / (2 : ℝ) ^ (n + 1))‖ ≤ a n) :
    ∃ U : C(UnitWindow, R), Tendsto (fun n => dyadicMap n F) atTop (𝓝 U) := by
  have hd : Summable (fun n => dist (dyadicMap n F) (dyadicMap (n + 1) F)) := by
    apply (hsum.mul_left 5).of_norm_bounded_eventually_nat
    filter_upwards [hstep] with n hn
    rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg]
    exact dyadicMap_succ_bound n F (a n) (ha n) hn
  exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hd)

/-- Convergence in the actual compact continuous-function space is uniform
on every point of the unit window. -/
theorem dyadicMap_tendsto_uniformly (F : ℝ → R) (U : C(UnitWindow, R))
    (hU : Tendsto (fun n => dyadicMap n F) atTop (𝓝 U)) :
    TendstoUniformly (fun n (t : UnitWindow) => dyadicPolygon n F t) U atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have he := hU.eventually (Metric.ball_mem_nhds U hε)
  filter_upwards [he] with n hn t
  have hc : dist U (dyadicMap n F) < ε := by
    simpa only [Metric.mem_ball, dist_comm] using hn
  exact (ContinuousMap.dist_apply_le_dist (f := U) (g := dyadicMap n F) t).trans_lt hc

/-- Summable eventual grid-increment bounds construct a literal continuous
uniform limit of all actual dyadic polygons. -/
theorem exists_uniform_dyadic_limit (F : ℝ → R) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hsum : Summable a)
    (hstep : ∀ᶠ n in atTop, ∀ j < 2 ^ (n + 1),
      ‖F (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) -
        F ((j : ℝ) / (2 : ℝ) ^ (n + 1))‖ ≤ a n) :
    ∃ U : C(UnitWindow, R),
      Tendsto (fun n => dyadicMap n F) atTop (𝓝 U) ∧
      TendstoUniformly (fun n (t : UnitWindow) => dyadicPolygon n F t) U atTop := by
  obtain ⟨U, hU⟩ := exists_dyadicMap_limit F a ha hsum hstep
  exact ⟨U, hU, dyadicMap_tendsto_uniformly F U hU⟩

end PBGSO.DyadicInterpolation
