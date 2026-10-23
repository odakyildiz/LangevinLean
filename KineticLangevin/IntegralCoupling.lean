import KineticLangevin.Dynamics
import Mathlib.Analysis.ODE.Gronwall

/-! # Noise cancellation and uniqueness for actual integral solutions

Two additive-noise integral solutions driven by the same input have a
differentiable difference.  The proof cancels the noise in the integral
equations and applies the fundamental theorem of calculus.  This justifies
the deterministic coupling equation; it is not an extra process assumption.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace KineticLangevin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Shared additive noise cancels in the integral equation itself. -/
theorem integral_difference_identity
    (g : E → E) (L : ℝ≥0) (hg : LipschitzWith L g)
    (Y Z B : ℝ → E) (hY : Continuous Y) (hZ : Continuous Z) (T : ℝ)
    (heY : ∀ t ∈ Icc 0 T, Y t - Y 0 = -(∫ s in 0..t, g (Y s)) + B t)
    (heZ : ∀ t ∈ Icc 0 T, Z t - Z 0 = -(∫ s in 0..t, g (Z s)) + B t)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    Y t - Z t = Y 0 - Z 0 - ∫ s in 0..t, g (Y s) - g (Z s) := by
  have hiY : IntervalIntegrable (fun s ↦ g (Y s)) volume 0 t :=
    (hg.continuous.comp hY).intervalIntegrable _ _
  have hiZ : IntervalIntegrable (fun s ↦ g (Z s)) volume 0 t :=
    (hg.continuous.comp hZ).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hiY hiZ]
  have hy := heY t ht
  have hz := heZ t ht
  rw [sub_eq_iff_eq_add] at hy hz
  rw [hy, hz]
  abel

/-- The actual noise-cancelled difference satisfies the drift ODE, including
the initial endpoint in the right-derivative sense needed by Grönwall. -/
theorem integral_difference_hasDerivWithinAt
    (g : E → E) (L : ℝ≥0) (hg : LipschitzWith L g)
    (Y Z B : ℝ → E) (hY : Continuous Y) (hZ : Continuous Z) (T : ℝ)
    (heY : ∀ t ∈ Icc 0 T, Y t - Y 0 = -(∫ s in 0..t, g (Y s)) + B t)
    (heZ : ∀ t ∈ Icc 0 T, Z t - Z 0 = -(∫ s in 0..t, g (Z s)) + B t)
    (t : ℝ) (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt (fun r ↦ Y r - Z r) (-(g (Y t) - g (Z t))) (Ici t) t := by
  have hforce : Continuous (fun s ↦ g (Y s) - g (Z s)) :=
    (hg.continuous.comp hY).sub (hg.continuous.comp hZ)
  have hd := intervalIntegral.integral_hasDerivAt_right (a := 0) (b := t)
    (hforce.intervalIntegrable 0 t) (hforce.stronglyMeasurableAtFilter volume (𝓝 t))
    hforce.continuousAt
  have hmem : Icc 0 T ∈ 𝓝[Ici t] t := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds ht.2)] with r hr hrT
    exact ⟨ht.1.trans hr, hrT⟩
  have he : (fun r ↦ Y r - Z r) =ᶠ[𝓝[Ici t] t]
      (fun r ↦ Y 0 - Z 0 - ∫ s in 0..r, g (Y s) - g (Z s)) := by
    filter_upwards [hmem] with r hr
    exact integral_difference_identity g L hg Y Z B hY hZ T heY heZ r hr
  exact (hd.const_sub (Y 0 - Z 0)).hasDerivWithinAt.congr_of_eventuallyEq he
    (integral_difference_identity g L hg Y Z B hY hZ T heY heZ t ⟨ht.1, ht.2.le⟩)

/-- A globally Lipschitz drift makes the constructed finite-horizon integral
solution unique for every shared continuous additive input. -/
theorem integral_solution_unique
    (g : E → E) (L : ℝ≥0) (hg : LipschitzWith L g)
    (Y Z B : ℝ → E) (hY : Continuous Y) (hZ : Continuous Z) (T : ℝ)
    (heY : ∀ t ∈ Icc 0 T, Y t - Y 0 = -(∫ s in 0..t, g (Y s)) + B t)
    (heZ : ∀ t ∈ Icc 0 T, Z t - Z 0 = -(∫ s in 0..t, g (Z s)) + B t)
    (hinitial : Y 0 = Z 0) (t : ℝ) (ht : t ∈ Icc 0 T) : Y t = Z t := by
  have hd := integral_difference_hasDerivWithinAt g L hg Y Z B hY hZ T heY heZ
  have hgrowth : ∀ r ∈ Ico 0 T,
      ‖-(g (Y r) - g (Z r))‖ ≤ (L : ℝ) * ‖Y r - Z r‖ + 0 := by
    intro r hr
    simpa only [norm_neg, add_zero] using hg.norm_sub_le (Y r) (Z r)
  have hb := norm_le_gronwallBound_of_norm_deriv_right_le
    (hY.sub hZ).continuousOn hd (show ‖Y 0 - Z 0‖ ≤ (0 : ℝ) by simp [hinitial])
    hgrowth t ht
  rw [gronwallBound_ε0_δ0] at hb
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))

end KineticLangevin
