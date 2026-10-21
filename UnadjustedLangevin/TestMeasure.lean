import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

set_option linter.style.header false

/-! # Smooth compactly supported tests determine finite measures

This supplies the measure-theoretic last step of a weak forward-equation
argument. It does not assume densities with respect to Lebesgue measure:
both measures have Radon–Nikodym densities with respect to their sum.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal

namespace ULA

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

/-- Equality on all smooth compactly supported real tests implies equality
of finite Borel measures. No absolute-continuity assumption is needed. -/
theorem measure_eq_of_integral_contDiff_eq
    (μ ν : Measure H) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ φ : H → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, φ x ∂μ) = ∫ x, φ x ∂ν) : μ = ν := by
  let ξ := μ + ν
  have hμ : μ ≪ ξ := (Measure.AbsolutelyContinuous.refl μ).add_right ν
  have hν : ν ≪ ξ := (Measure.AbsolutelyContinuous.refl ν).add_right' μ
  have hd : (fun x ↦ (μ.rnDeriv ξ x).toReal) =ᵐ[ξ]
      (fun x ↦ (ν.rnDeriv ξ x).toReal) := by
    apply ae_eq_of_integral_contDiff_smul_eq
      (Measure.integrable_toReal_rnDeriv (μ := μ) (ν := ξ)).locallyIntegrable
      (Measure.integrable_toReal_rnDeriv (μ := ν) (ν := ξ)).locallyIntegrable
    intro φ hφ hc
    simpa only [smul_eq_mul, mul_comm] using
      (integral_toReal_rnDeriv_mul (f := φ) hμ).trans
        ((h φ hφ hc).trans (integral_toReal_rnDeriv_mul (f := φ) hν).symm)
  have hd' : μ.rnDeriv ξ =ᵐ[ξ] ν.rnDeriv ξ := by
    filter_upwards [hd, Measure.rnDeriv_lt_top μ ξ,
      Measure.rnDeriv_lt_top ν ξ] with x hx hμx hνx
    exact (ENNReal.toReal_eq_toReal_iff' hμx.ne hνx.ne).mp hx
  calc
    μ = ξ.withDensity (μ.rnDeriv ξ) := (Measure.withDensity_rnDeriv_eq μ ξ hμ).symm
    _ = ξ.withDensity (ν.rnDeriv ξ) := withDensity_congr_ae hd'
    _ = ν := Measure.withDensity_rnDeriv_eq ν ξ hν

/-- The `C²` compact tests used by the Langevin generator also determine
finite Borel measures. -/
theorem measure_eq_of_integral_contDiff_two_eq
    (μ ν : Measure H) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ φ : H → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      (∫ x, φ x ∂μ) = ∫ x, φ x ∂ν) : μ = ν := by
  apply measure_eq_of_integral_contDiff_eq μ ν
  intro φ hφ hc
  exact h φ (hφ.of_le (by simp)) hc

end ULA
