import UnadjustedLangevin.Coupling

/-!
# Taking the infimum over initial couplings

An affine transport estimate that holds for every initial coupling passes to
the Wasserstein distance itself. No optimal coupling or attainment theorem is
required. The premise still explicitly requests the estimate for every
initial coupling; constructing a reference process for those couplings is a
separate probabilistic obligation.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace ULA

variable {H : Type*} [NormedAddCommGroup H] [MeasurableSpace H]

/-- An estimate uniform over all initial couplings passes to their infimum.
The finite coefficient permits multiplication to commute with the infimum,
including coefficient zero. -/
theorem wasserstein2_affine_bound_of_all_couplings
    (μ ν μ' ν' : Measure H) (a : ℝ≥0) (b : ℝ≥0∞)
    (hnonempty : Nonempty (Coupling μ ν))
    (hfamily : ∀ c : Coupling μ ν,
      wasserstein2 μ' ν' ≤ (a : ℝ≥0∞) * couplingCost c.joint + b) :
    wasserstein2 μ' ν' ≤ (a : ℝ≥0∞) * wasserstein2 μ ν + b := by
  let : Nonempty (Coupling μ ν) := hnonempty
  unfold wasserstein2
  rw [ENNReal.mul_iInf (fun h ↦ (ENNReal.coe_ne_top h).elim), ENNReal.iInf_add]
  exact le_iInf hfamily

/-- Finiteness of the transport infimum supplies at least one finite-cost
coupling, without asserting that any coupling attains the infimum. -/
theorem exists_finiteCost_coupling (μ ν : Measure H)
    (hfinite : wasserstein2 μ ν ≠ ⊤) :
    ∃ c : Coupling μ ν, couplingCost c.joint < ⊤ := by
  have hlt : wasserstein2 μ ν < ⊤ := lt_top_iff_ne_top.mpr hfinite
  exact iInf_lt_iff.mp hlt

/-- The real-valued transport endpoint, with finite initial distance.
The output distance is also finite, because the affine upper bound is finite. -/
theorem wasserstein2_affine_bound_real_of_all_couplings
    (μ ν μ' ν' : Measure H) (a b : ℝ≥0)
    (hfinite : wasserstein2 μ ν ≠ ⊤)
    (hfamily : ∀ c : Coupling μ ν,
      wasserstein2 μ' ν' ≤ (a : ℝ≥0∞) * couplingCost c.joint + (b : ℝ≥0∞)) :
    wasserstein2Real μ' ν' ≤ (a : ℝ) * wasserstein2Real μ ν + (b : ℝ) := by
  obtain ⟨c, _⟩ := exists_finiteCost_coupling μ ν hfinite
  have hb := wasserstein2_affine_bound_of_all_couplings μ ν μ' ν' a b ⟨c⟩ hfamily
  have hprod : (a : ℝ≥0∞) * wasserstein2 μ ν ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hfinite
  have hsum : (a : ℝ≥0∞) * wasserstein2 μ ν + (b : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hprod, ENNReal.coe_ne_top⟩
  have hr := ENNReal.toReal_mono hsum hb
  simpa only [wasserstein2Real, ENNReal.toReal_add hprod ENNReal.coe_ne_top,
    ENNReal.toReal_mul, ENNReal.coe_toReal] using hr

/-- Real estimates for every finite-cost initial coupling suffice. This form
can be applied directly to finite-moment synchronous-coupling theorems.
Finiteness of the output is explicit so that `toReal` cannot hide infinity. -/
theorem wasserstein2_affine_bound_real_of_finite_couplings
    (μ ν μ' ν' : Measure H) (a b : ℝ≥0)
    (hfinite : wasserstein2 μ ν ≠ ⊤) (houtputfinite : wasserstein2 μ' ν' ≠ ⊤)
    (hfamily : ∀ c : Coupling μ ν, couplingCost c.joint ≠ ⊤ →
      wasserstein2Real μ' ν' ≤ (a : ℝ) * (couplingCost c.joint).toReal + (b : ℝ)) :
    wasserstein2Real μ' ν' ≤ (a : ℝ) * wasserstein2Real μ ν + (b : ℝ) := by
  have hlift (c : Coupling μ ν) (hc : couplingCost c.joint ≠ ⊤) :
      wasserstein2 μ' ν' ≤ (a : ℝ≥0∞) * couplingCost c.joint + (b : ℝ≥0∞) := by
    have h := ENNReal.ofReal_le_ofReal (hfamily c hc)
    simpa only [wasserstein2Real, ENNReal.ofReal_toReal houtputfinite,
      ENNReal.ofReal_add (mul_nonneg a.coe_nonneg ENNReal.toReal_nonneg) b.coe_nonneg,
      ENNReal.ofReal_mul a.coe_nonneg, ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_toReal hc] using h
  apply wasserstein2_affine_bound_real_of_all_couplings μ ν μ' ν' a b hfinite
  intro c
  by_cases hc : couplingCost c.joint ≠ ⊤
  · exact hlift c hc
  · have hctop : couplingCost c.joint = ⊤ := not_ne_iff.mp hc
    by_cases ha : a = 0
    · obtain ⟨c₀, hc₀⟩ := exists_finiteCost_coupling μ ν hfinite
      have hb := hlift c₀ (ne_of_lt hc₀)
      simpa only [ha, ENNReal.coe_zero, zero_mul, zero_add] using hb
    · have hane : (a : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha
      simp only [hctop, ENNReal.mul_top hane, top_add, le_top]

end ULA
