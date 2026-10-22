import UnadjustedLangevin.InitialCoupling
import UnadjustedLangevin.MarkovLaw

set_option linter.style.header false

/-! # Passing a squared coupling estimate to quadratic transport

The infimum is taken over all finite-cost couplings. No optimal coupling or
assumed transport recurrence is used.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ProximalLangevin

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]

/-- A uniform squared estimate for actual finite-cost couplings passes to the
square of the genuine Wasserstein distance. -/
theorem wasserstein2_sq_bound_of_finite_couplings
    (μ ν μ' ν' : Measure E) (q c : ℝ) (hq : 0 ≤ q) (_hc : 0 ≤ c)
    (hfinite : ULA.wasserstein2 μ ν ≠ ⊤)
    (hfamily : ∀ p : ULA.Coupling μ ν, ULA.couplingCost p.joint ≠ ⊤ →
      ULA.wasserstein2Real μ' ν' ^ 2 ≤ q * (ULA.couplingCost p.joint).toReal ^ 2 + c) :
    ULA.wasserstein2Real μ' ν' ^ 2 ≤ q * ULA.wasserstein2Real μ ν ^ 2 + c := by
  obtain ⟨p₀, hp₀⟩ := ULA.exists_finiteCost_coupling μ ν hfinite
  by_cases hq0 : q = 0
  · simpa only [hq0, zero_mul, zero_add] using hfamily p₀ (ne_of_lt hp₀)
  have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
  by_cases hbase : ULA.wasserstein2Real μ' ν' ^ 2 ≤ c
  · exact hbase.trans (by nlinarith [sq_nonneg (ULA.wasserstein2Real μ ν)])
  have hnum : 0 < ULA.wasserstein2Real μ' ν' ^ 2 - c := by linarith
  let r := Real.sqrt ((ULA.wasserstein2Real μ' ν' ^ 2 - c) / q)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = (ULA.wasserstein2Real μ' ν' ^ 2 - c) / q :=
    Real.sq_sqrt (div_nonneg hnum.le hq)
  have hrq : q * r ^ 2 = ULA.wasserstein2Real μ' ν' ^ 2 - c := by
    rw [hr2]
    field_simp
  have hlower : ENNReal.ofReal r ≤ ULA.wasserstein2 μ ν := by
    apply le_iInf
    intro p
    by_cases hp : ULA.couplingCost p.joint = ⊤
    · simp only [hp, le_top]
    have hh := hfamily p hp
    have hcost : r ≤ (ULA.couplingCost p.joint).toReal := by
      have hs : r ^ 2 ≤ (ULA.couplingCost p.joint).toReal ^ 2 := by
        apply (mul_le_mul_iff_of_pos_left hqpos).mp
        linarith
      exact (sq_le_sq₀ hr ENNReal.toReal_nonneg).mp hs
    exact (ENNReal.ofReal_le_ofReal hcost).trans_eq (ENNReal.ofReal_toReal hp)
  have hreal : r ≤ ULA.wasserstein2Real μ ν := by
    have hh := ENNReal.toReal_mono hfinite hlower
    simpa only [ENNReal.toReal_ofReal hr, ULA.wasserstein2Real] using hh
  have hs := (sq_le_sq₀ hr (show 0 ≤ ULA.wasserstein2Real μ ν from ENNReal.toReal_nonneg)).mpr hreal
  have hh := mul_le_mul_of_nonneg_left hs hq
  linarith

end ProximalLangevin
