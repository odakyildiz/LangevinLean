import UnadjustedLangevin.Coupling
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.style.header false
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace LatentDiffusion.RegularMetricFlow

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- A regular optimal-transport realization to a fixed target. Minimality is
over genuine measure couplings, not a distance or convergence bound. In a
characteristic-flow application the anchor is T_t(Y_t), where T_t is a regular
optimal transport map from the current law to the fixed target. -/
structure OptimalAnchor (Y : Lp E 2 P) (target : Measure E) where
  value : Lp E 2 P
  law : P.map value = target
  minimal : ∀ c : ULA.Coupling (P.map Y) target,
    ENNReal.ofReal ‖Y - value‖ ≤ ULA.couplingCost c.joint

def distanceTo (Y : ℝ → Lp E 2 P) (target : Measure E) (t : ℝ) : ℝ :=
  ULA.wasserstein2Real (P.map (Y t)) target

theorem OptimalAnchor.distance_eq {Y : Lp E 2 P} {target : Measure E}
    (D : OptimalAnchor P Y target) :
    ULA.wasserstein2Real (P.map Y) target = ‖Y - D.value‖ := by
  have upper := ULA.wasserstein2_le_Lp_cost P Y D.value
  rw [D.law] at upper
  have lower : ENNReal.ofReal ‖Y - D.value‖ ≤ ULA.wasserstein2 (P.map Y) target := by
    exact le_iInf D.minimal
  have heq := le_antisymm upper lower
  exact (congrArg ENNReal.toReal heq).trans (ENNReal.toReal_ofReal (norm_nonneg _))

/-- Gluing the actual characteristic variables to an optimal target anchor
proves the distance comparison. No Wasserstein triangle bound is assumed. -/
theorem distance_increment_le (Y : ℝ → Lp E 2 P) (target : Measure E)
    (anchor : ∀ t, OptimalAnchor P (Y t) target) (s t : ℝ) :
    distanceTo P Y target s - distanceTo P Y target t ≤ ‖Y s - Y t‖ := by
  have upper := ULA.wasserstein2_le_Lp_cost_real P (Y s) (anchor t).value
  rw [(anchor t).law] at upper
  have tri : ‖Y s - (anchor t).value‖ ≤ ‖Y s - Y t‖ + ‖Y t - (anchor t).value‖ := by
    calc
      _ = ‖(Y s - Y t) + (Y t - (anchor t).value)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have heq := (anchor t).distance_eq
  change distanceTo P Y target t = _ at heq
  change distanceTo P Y target s ≤ _ at upper
  linarith

theorem distance_abs_increment_le (Y : ℝ → Lp E 2 P) (target : Measure E)
    (anchor : ∀ t, OptimalAnchor P (Y t) target) (s t : ℝ) :
    |distanceTo P Y target s - distanceTo P Y target t| ≤ ‖Y s - Y t‖ := by
  refine abs_le.mpr ⟨?_, distance_increment_le P Y target anchor s t⟩
  have h := distance_increment_le P Y target anchor t s
  rw [norm_sub_rev] at h
  linarith

/-- Corrected source metric-speed lemma, in the stronger upper-Dini form.
The ordinary distance derivative need not exist at a crossing time. -/
theorem distance_right_slope (Y : ℝ → Lp E 2 P) (target : Measure E)
    (anchor : ∀ t, OptimalAnchor P (Y t) target) (t : ℝ) (v : Lp E 2 P)
    (hY : HasDerivWithinAt Y v (Ici t) t) (r : ℝ) (hr : ‖v‖ < r) :
    ∀ᶠ s in 𝓝[>] t, slope (distanceTo P Y target) t s < r := by
  have h := (hY.mono Ioi_subset_Ici_self).limsup_norm_slope_le hr
  filter_upwards [h, self_mem_nhdsWithin] with s hs hst
  have hinc := distance_increment_le P Y target anchor s t
  rw [slope_def_field]
  have hpos : 0 < s - t := sub_pos.mpr hst
  simp only [Real.norm_eq_abs, abs_of_pos hpos] at hs
  have hscaled := mul_le_mul_of_nonneg_left hinc (inv_nonneg.mpr hpos.le)
  simpa only [Real.norm_eq_abs, abs_of_pos hpos, div_eq_inv_mul] using hscaled.trans_lt hs

/-- Integrating the characteristic velocity gives the source's integrated
metric-speed control for actual probability laws. -/
theorem distance_integral_bound (Y v : ℝ → Lp E 2 P) (target : Measure E)
    (anchor : ∀ t, OptimalAnchor P (Y t) target) (s t : ℝ) (hst : s ≤ t)
    (hY : ∀ u ∈ uIcc s t, HasDerivAt Y (v u) u)
    (hv : IntervalIntegrable v volume s t) :
    |distanceTo P Y target t - distanceTo P Y target s| ≤ ∫ u in s..t, ‖v u‖ := by
  apply (distance_abs_increment_le P Y target anchor t s).trans
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hY hv]
  exact intervalIntegral.norm_integral_le_integral_norm hst

end LatentDiffusion.RegularMetricFlow
