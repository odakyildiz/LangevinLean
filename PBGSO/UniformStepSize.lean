import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! # An explicit positive step range for time-uniform error absorption

The `b+1` denominator keeps the bound strictly positive when the computed
local-growth coefficient is zero. All quantities depend only on primitive
model constants, the dissipativity rate and the quadratic metric.
-/
noncomputable section
namespace PBGSO.UniformStep

/-- A conservative, strictly positive computable upper step size. -/
def maximumStep (ρ b : ℝ) : ℝ :=
  min 1 (min (1 / ρ) ((ρ / (4 * (b + 1))) ^ 2))

theorem maximumStep_pos (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 ≤ b) :
    0 < maximumStep ρ b := by
  unfold maximumStep
  apply lt_min (by norm_num)
  exact lt_min (by positivity) (sq_pos_of_pos (by positivity))

/-- The positive maximum step discharges every scalar small-step condition
in the time-uniform comparison theorem. No final error budget is assumed. -/
theorem admissible (ρ b h : ℝ) (hρ : 0 < ρ) (hb : 0 ≤ b)
    (_hh : 0 < h) (hhmax : h ≤ maximumStep ρ b) :
    h ≤ 1 ∧ ρ * h ≤ 1 ∧ b * Real.sqrt h ≤ ρ / 4 := by
  have hunit : h ≤ 1 := hhmax.trans (min_le_left _ _)
  have hrest : h ≤ min (1 / ρ) ((ρ / (4 * (b + 1))) ^ 2) :=
    hhmax.trans (min_le_right _ _)
  have hρstep : ρ * h ≤ 1 := by
    have hr := (le_div_iff₀ hρ).mp (hrest.trans (min_le_left _ _))
    simpa [mul_comm] using hr
  have hden : 0 < 4 * (b + 1) := by positivity
  have hquot : 0 ≤ ρ / (4 * (b + 1)) := div_nonneg hρ.le hden.le
  have hsqrt : Real.sqrt h ≤ ρ / (4 * (b + 1)) :=
    Real.sqrt_le_iff.mpr ⟨hquot, hrest.trans (min_le_right _ _)⟩
  refine ⟨hunit, hρstep, ?_⟩
  calc
    _ ≤ b * (ρ / (4 * (b + 1))) := mul_le_mul_of_nonneg_left hsqrt hb
    _ ≤ (b + 1) * (ρ / (4 * (b + 1))) :=
      mul_le_mul_of_nonneg_right (by linarith) hquot
    _ = ρ / 4 := by field_simp

end PBGSO.UniformStep
