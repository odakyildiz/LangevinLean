import AverageLMC.SquaredTransport

set_option linter.style.header false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AverageLMC

/-- A finite-distance squared estimate with positive contraction extends to
every initialization in extended nonnegative transport. No moment hypothesis
is needed when the initial distance is infinite. -/
theorem squared_transport_extended {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (μ π μ' π' : Measure E) (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (houtput : ULA.wasserstein2 μ π ≠ ⊤ → ULA.wasserstein2 μ' π' ≠ ⊤)
    (hbound : ULA.wasserstein2 μ π ≠ ⊤ →
      ULA.wasserstein2Real μ' π' ^ 2 ≤ a * ULA.wasserstein2Real μ π ^ 2 + b) :
    ULA.wasserstein2 μ' π' ^ 2 ≤
      ENNReal.ofReal a * ULA.wasserstein2 μ π ^ 2 + ENNReal.ofReal b := by
  by_cases hi : ULA.wasserstein2 μ π = ⊤
  · simp [hi, ENNReal.ofReal_pos.mpr ha |>.ne']
  · have h := ENNReal.ofReal_le_ofReal (hbound hi)
    rw [ENNReal.ofReal_add (mul_nonneg ha.le (sq_nonneg _)) hb,
      ENNReal.ofReal_mul ha.le] at h
    simpa only [ULA.wasserstein2Real, pow_two,
      ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (houtput hi), ENNReal.ofReal_toReal hi] using h

end AverageLMC
