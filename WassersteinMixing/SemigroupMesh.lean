import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! # Common fine meshes for continuous-time Markov composition

Two nonnegative target times use integer counts on the same vanishing mesh.
Each rounded elapsed time converges to its target, and the sum of the two
counts converges to the sum of the targets without changing the mesh.
-/

noncomputable section
open Filter
open scoped Topology

namespace WassersteinMixing

/-- The number of complete steps before a requested nonnegative time. -/
def meshCount (step time : ℝ) : ℕ := ⌊time / step⌋₊

theorem meshCount_elapsed_le (step time : ℝ) (hs : 0 < step) (ht : 0 ≤ time) :
    (meshCount step time : ℝ) * step ≤ time := by
  apply (le_div_iff₀ hs).mp
  exact Nat.floor_le (div_nonneg ht hs.le)

theorem meshCount_remainder_lt (step time : ℝ) (hs : 0 < step) :
    time - (meshCount step time : ℝ) * step < step := by
  have hf := Nat.lt_floor_add_one (time / step)
  have hm := (div_lt_iff₀ hs).mp hf
  unfold meshCount
  nlinarith

/-- Rounded elapsed times converge on every positive mesh tending to zero. -/
theorem meshCount_elapsed_tendsto {I : Type*} {l : Filter I}
    (step : I → ℝ) (hs : ∀ i, 0 < step i) (hlim : Tendsto step l (𝓝 0))
    (time : ℝ) (ht : 0 ≤ time) :
    Tendsto (fun i ↦ (meshCount (step i) time : ℝ) * step i) l (𝓝 time) := by
  have hr : Tendsto (fun i ↦ time - (meshCount (step i) time : ℝ) * step i) l (𝓝 0) := by
    apply squeeze_zero (fun i ↦ sub_nonneg.mpr (meshCount_elapsed_le _ _ (hs i) ht))
      (fun i ↦ (meshCount_remainder_lt _ _ (hs i)).le) hlim
  have hc : Tendsto (fun _ : I ↦ time) l (𝓝 time) := tendsto_const_nhds
  simpa only [sub_sub_cancel, sub_zero] using hc.sub hr

theorem meshCount_sum_elapsed_le (step s t : ℝ) (hs : 0 < step)
    (hs0 : 0 ≤ s) (ht0 : 0 ≤ t) :
    ((meshCount step s + meshCount step t : ℕ) : ℝ) * step ≤ s + t := by
  push_cast
  nlinarith [meshCount_elapsed_le step s hs hs0, meshCount_elapsed_le step t hs ht0]

/-- The sum of two rounded step counts has the correct limiting total time.
This is the exact discrete algebra used for the limiting semigroup law. -/
theorem meshCount_sum_elapsed_tendsto {I : Type*} {l : Filter I}
    (step : I → ℝ) (hs : ∀ i, 0 < step i) (hlim : Tendsto step l (𝓝 0))
    (s t : ℝ) (hs0 : 0 ≤ s) (ht0 : 0 ≤ t) :
    Tendsto (fun i ↦ ((meshCount (step i) s + meshCount (step i) t : ℕ) : ℝ) * step i)
      l (𝓝 (s + t)) := by
  have h := (meshCount_elapsed_tendsto step hs hlim s hs0).add
    (meshCount_elapsed_tendsto step hs hlim t ht0)
  convert h using 1
  ext i
  push_cast
  ring

end WassersteinMixing
