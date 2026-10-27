import AverageLMC.GaussianCanonical
import AverageLMC.Smoothing

set_option linter.style.header false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace AverageLMC
open ULA ULA.Hilbert

/-- A zero LMC step retains its exact input law. -/
@[simp] theorem ulaLawStep_zero {p : ℕ} (f : State p → ℝ) (μ : Measure (State p)) :
    ulaLawStep f 0 μ = μ := by
  simp [ulaLawStep, malaProposal, Measure.map_fst_prod]

/-- Theorem 1, claim 1, with the exact average coordinate smoothness,
for the actual Gaussian transition. Finite transport is precisely the finite
second-moment interpretation required by the displayed real inequality. -/
theorem lmc_one_step {p : ℕ} (hp : 0 < p) (f : State p → ℝ)
    (m h : ℝ) (L : ℝ≥0) (hm : 0 < m) (hh : 0 ≤ h)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith L (gradient f))
    (μ : Measure (State p)) [IsProbabilityMeasure μ]
    (hfinite : wasserstein2 μ (gibbsMeasure f) ≠ ⊤) :
    wasserstein2Real (ulaLawStep f h μ) (gibbsMeasure f) ^ 2 ≤
      (1 - m * h) / (1 + m * h) * wasserstein2Real μ (gibbsMeasure f) ^ 2 +
      ((averageSmoothness f + m) * h ^ 2 * p) / (1 + m * h) +
      h ^ 2 * (h * (L : ℝ) - 1) / (1 + m * h) *
        (∫ x, ‖gradient f x‖ ^ 2 ∂μ) := by
  rcases eq_or_lt_of_le hh with rfl | hhpos
  · simp
  have hd : 0 < 1 + m * h := by positivity
  have hsm (x : State p) (s : ℝ) (hs : 0 ≤ s) :
      (∫ z, f (x + Real.sqrt (2 * s) • z) - f x ∂stdGaussian (State p)) ≤
        averageSmoothness f * (Fintype.card (Fin p) : ℝ) * s := by
    simpa using integral_stdGaussian_smoothing hp f L hf hLip x s hs
  obtain ⟨c₀, hc₀⟩ := exists_finiteCost_coupling μ (gibbsMeasure f) hfinite
  have houtput := (lmc_coupling_step f m h (averageSmoothness f) L hm hhpos hf hsc hLip
    hsm μ c₀ (ne_of_lt hc₀)).1
  have hb := wasserstein2_sq_bound_of_finite_couplings μ (gibbsMeasure f)
    (ulaLawStep f h μ) (gibbsMeasure f) ((1 - m * h) / (1 + m * h))
    (((averageSmoothness f + m) * h ^ 2 * p +
      h ^ 2 * (h * (L : ℝ) - 1) * (∫ x, ‖gradient f x‖ ^ 2 ∂μ)) / (1 + m * h))
    hfinite houtput (fun c hc ↦ by
      have hs := (lmc_coupling_step f m h (averageSmoothness f) L hm hhpos hf hsc hLip
        hsm μ c hc).2
      rw [Fintype.card_fin] at hs
      apply (mul_le_mul_iff_of_pos_left hd).mp
      convert hs using 1 <;> field_simp <;> ring)
  convert hb using 1 <;> field_simp <;> ring

end AverageLMC
