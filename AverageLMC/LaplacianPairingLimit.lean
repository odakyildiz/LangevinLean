import AverageLMC.LaplacianWeightClipping
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.style.header false

/-!
# Passing compact gradient approximations to the coupling cross term

The compact test identities are paired before taking the approximation
limit. Stationarity supplies one generator error norm uniformly in time.
Consequently no continuity premise on the unbounded generator path is needed.
Radial clipping then removes boundedness of the initial coupling error.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace AverageLMC

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Uniform generator approximation in the stationary `L²` norm is enough to
pass compact Dynkin identities to the desired gradient pairing bound. -/
theorem pairing_bound_of_compact_dynkin_approximations
    (Ψ X Y : H) (Xn Yn : ℕ → H) (Gn : ℕ → ℝ → H)
    (T R : ℝ) (hT : 0 ≤ T) (hR : 0 ≤ R) (err : ℕ → ℝ)
    (herr : ∀ n, 0 ≤ err n) (herrlim : Tendsto err atTop (𝓝 0))
    (hX : Tendsto Xn atTop (𝓝 X)) (hY : Tendsto Yn atTop (𝓝 Y))
    (hgen : ∀ n t, t ∈ Icc 0 T → ‖Gn n t‖ ≤ R + err n)
    (hidentity : ∀ n, inner ℝ Ψ (Xn n - Yn n) =
      ∫ t in 0..T, inner ℝ Ψ (Gn n t)) :
    inner ℝ Ψ (X - Y) ≤ T * ‖Ψ‖ * R := by
  have hbound (n : ℕ) : inner ℝ Ψ (Xn n - Yn n) ≤ T * ‖Ψ‖ * (R + err n) := by
    rw [hidentity n]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := T) (C := ‖Ψ‖ * (R + err n))
      (f := fun t ↦ inner ℝ Ψ (Gn n t)) (fun t ht ↦ ?_)
    · have hab : (∫ t in 0..T, inner ℝ Ψ (Gn n t)) ≤
          ‖∫ t in 0..T, inner ℝ Ψ (Gn n t)‖ := by
        simpa only [Real.norm_eq_abs] using le_abs_self (∫ t in 0..T, inner ℝ Ψ (Gn n t))
      exact hab.trans (by simpa only [sub_zero, abs_of_nonneg hT, mul_comm,
        mul_assoc, mul_left_comm] using hb)
    · rw [uIoc_of_le hT] at ht
      exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
        (mul_le_mul_of_nonneg_left (hgen n t ⟨ht.1.le, ht.2⟩) (norm_nonneg _))
  have hleft : Tendsto (fun n ↦ inner ℝ Ψ (Xn n - Yn n)) atTop
      (𝓝 (inner ℝ Ψ (X - Y))) := tendsto_const_nhds.inner (hX.sub hY)
  have hright : Tendsto (fun n ↦ T * ‖Ψ‖ * (R + err n)) atTop
      (𝓝 (T * ‖Ψ‖ * R)) := by
    simpa only [add_zero] using (tendsto_const_nhds.add herrlim).const_mul (T * ‖Ψ‖)
  exact le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hbound)

end Hilbert

section Lp

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- Bounds proved for every bounded radial clipping of the initial vector
pass to the original arbitrary square-integrable initial vector, with its
original norm and no dimension loss. -/
theorem pairing_bound_of_clipped_weights
    (Ψ D : Lp H 2 P) (T R : ℝ) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hclip : ∀ n, inner ℝ (lpClippedWeight P Ψ n) D ≤
      T * ‖lpClippedWeight P Ψ n‖ * R) :
    inner ℝ Ψ D ≤ T * ‖Ψ‖ * R := by
  apply le_of_tendsto (lpClippedWeight_inner_tendsto P Ψ D)
  exact Eventually.of_forall (fun n ↦ (hclip n).trans (by
    have hn := lpClippedWeight_norm_le P Ψ n
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn hT) hR))

end Lp
end AverageLMC
