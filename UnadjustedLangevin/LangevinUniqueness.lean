import UnadjustedLangevin.LangevinIntegral
import Mathlib.Analysis.ODE.Gronwall

set_option linter.style.header false

/-!
# Uniqueness and initial-state stability of the additive Langevin equation

Common additive noise cancels between two integral solutions. Their difference
is therefore differentiable even when the noise is only continuous. Grönwall
bounds its norm and proves uniqueness on every finite horizon, without a
small-time condition. Together with `LangevinIntegral.lean` this establishes
existence and uniqueness in the Banach space, including the actual `L²` drift.
No stationary-law or Gibbs-invariance assertion is made.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace ULA

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- Two continuous solutions with the same additive input depend at most
exponentially on their initial values. Noise derivatives and a small-time
restriction are unnecessary. -/
theorem langevin_integral_stability
    (g : H → H) (L : ℝ≥0) (hLip : LipschitzWith L g)
    (x y : H) (B Y Z : ℝ → H) (hY : Continuous Y) (hZ : Continuous Z)
    (h : ℝ) (hh : 0 ≤ h)
    (hYe : ∀ t ∈ Icc 0 h, Y t - x = -(∫ s in 0..t, g (Y s)) + B t)
    (hZe : ∀ t ∈ Icc 0 h, Z t - y = -(∫ s in 0..t, g (Z s)) + B t) :
    ∀ t ∈ Icc 0 h, ‖Y t - Z t‖ ≤ ‖x - y‖ * Real.exp ((L : ℝ) * t) := by
  let D : ℝ → H := fun t ↦ Y t - Z t
  let F : ℝ → H := fun t ↦ (x - y) -
    ((∫ s in 0..t, g (Y s)) - ∫ s in 0..t, g (Z s))
  have hD : ∀ t ∈ Icc 0 h, D t = F t := by
    intro t ht
    have hy := hYe t ht
    have hz := hZe t ht
    dsimp [D, F]
    rw [sub_eq_iff_eq_add] at hy hz
    rw [hy, hz]
    abel
  have hcY : Continuous (fun s ↦ g (Y s)) := hLip.continuous.comp hY
  have hcZ : Continuous (fun s ↦ g (Z s)) := hLip.continuous.comp hZ
  have hderiv : ∀ t ∈ Ico 0 h,
      HasDerivWithinAt D (-(g (Y t) - g (Z t))) (Ici t) t := by
    intro t ht
    have hiY := intervalIntegral.integral_hasDerivAt_right
      (hcY.intervalIntegrable 0 t) (hcY.stronglyMeasurableAtFilter volume (𝓝 t)) hcY.continuousAt
    have hiZ := intervalIntegral.integral_hasDerivAt_right
      (hcZ.intervalIntegrable 0 t) (hcZ.stronglyMeasurableAtFilter volume (𝓝 t)) hcZ.continuousAt
    have hf : HasDerivAt F (-(g (Y t) - g (Z t))) t := by
      convert (hasDerivAt_const t (x - y)).sub (hiY.sub hiZ) using 1
      simp
    have hevent : D =ᶠ[𝓝[Ici t] t] F := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds ht.2)] with s hst hsh
      exact hD s ⟨ht.1.trans hst, hsh.le⟩
    exact hf.hasDerivWithinAt.congr_of_eventuallyEq hevent (hD t ⟨ht.1, ht.2.le⟩)
  have hD0 : D 0 = x - y := by
    simpa only [F, intervalIntegral.integral_same, sub_self, sub_zero] using
      hD 0 ⟨le_rfl, hh⟩
  have hb (t : ℝ) (_ht : t ∈ Ico 0 h) :
      ‖-(g (Y t) - g (Z t))‖ ≤ (L : ℝ) * ‖D t‖ + 0 := by
    simpa only [norm_neg, D, add_zero] using hLip.norm_sub_le (Y t) (Z t)
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := D) (f' := fun t ↦ -(g (Y t) - g (Z t)))
    (δ := ‖x - y‖) (K := (L : ℝ)) (ε := 0)
    (hY.sub hZ).continuousOn hderiv (by rw [hD0]) hb
  intro t ht
  simpa only [D, gronwallBound_ε0, sub_zero] using hg t ht

/-- A continuous solution with a fixed initial state and additive input is
unique on the entire finite interval. -/
theorem langevin_integral_unique
    (g : H → H) (L : ℝ≥0) (hLip : LipschitzWith L g)
    (x : H) (B Y Z : ℝ → H) (hY : Continuous Y) (hZ : Continuous Z)
    (h : ℝ) (hh : 0 ≤ h)
    (hYe : ∀ t ∈ Icc 0 h, Y t - x = -(∫ s in 0..t, g (Y s)) + B t)
    (hZe : ∀ t ∈ Icc 0 h, Z t - x = -(∫ s in 0..t, g (Z s)) + B t) :
    EqOn Y Z (Icc 0 h) := by
  intro t ht
  have hb := langevin_integral_stability g L hLip x x B Y Z hY hZ h hh hYe hZe t ht
  simpa only [sub_self, norm_zero, zero_mul, norm_le_zero_iff, sub_eq_zero] using hb

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Initial-state stability for the actual square-integrable gradient drift. -/
theorem lp_langevin_integral_stability
    (U : K → ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (initial₁ initial₂ : Lp K 2 P) (B Y Z : ℝ → Lp K 2 P)
    (hY : Continuous Y) (hZ : Continuous Z) (h : ℝ) (hh : 0 ≤ h)
    (hYe : ∀ t ∈ Icc 0 h, Y t - initial₁ =
      -(∫ s in 0..t, lpDrift P (gradient U) hLip (Y s)) + B t)
    (hZe : ∀ t ∈ Icc 0 h, Z t - initial₂ =
      -(∫ s in 0..t, lpDrift P (gradient U) hLip (Z s)) + B t) :
    ∀ t ∈ Icc 0 h,
      ‖Y t - Z t‖ ≤ ‖initial₁ - initial₂‖ * Real.exp ((L : ℝ) * t) :=
  langevin_integral_stability (lpDrift P (gradient U) hLip) L
    (lpDrift_lipschitz P (gradient U) hLip) initial₁ initial₂ B Y Z hY hZ h hh hYe hZe

/-- Uniqueness of the actual `L²` Langevin integral solution with common initial
state and noise, on any finite nonnegative time interval. -/
theorem lp_langevin_integral_unique
    (U : K → ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (initial : Lp K 2 P) (B Y Z : ℝ → Lp K 2 P)
    (hY : Continuous Y) (hZ : Continuous Z) (h : ℝ) (hh : 0 ≤ h)
    (hYe : ∀ t ∈ Icc 0 h, Y t - initial =
      -(∫ s in 0..t, lpDrift P (gradient U) hLip (Y s)) + B t)
    (hZe : ∀ t ∈ Icc 0 h, Z t - initial =
      -(∫ s in 0..t, lpDrift P (gradient U) hLip (Z s)) + B t) :
    EqOn Y Z (Icc 0 h) :=
  langevin_integral_unique (lpDrift P (gradient U) hLip) L
    (lpDrift_lipschitz P (gradient U) hLip) initial B Y Z hY hZ h hh hYe hZe

end ULA
