import AverageLMC.LaplacianEulerLimit

set_option linter.style.header false

/-!
# Passing Gaussian Euler weak consistency to Dynkin's identity

The weak residual is the sum of the proved one-step Gaussian Taylor
remainders. This file supplies the deterministic limit argument, using the
actual integral solution's matching-noise Euler approximations. It does not
postulate a one-step Wasserstein error or a convergence recurrence.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology

namespace AverageLMC

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- An arbitrarily small first-order weak remainder, plus a square-root mesh
remainder, forces the scalar Euler residual to converge to zero. -/
theorem weakEuler_residual_tendsto_zero
    (r : ℕ → ℝ) (T C : ℝ) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hres : ∀ ε > 0, ∃ K : ℝ, 0 ≤ K ∧ ∃ N : ℕ, ∀ n ≥ N,
      |r n| ≤ C * (ε + K * Real.sqrt (T / ((n + 1 : ℕ) : ℝ)))) :
    Tendsto r atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε / (2 * (C + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  have hscale : η * (2 * (C + 1)) = ε := div_mul_cancel₀ ε (by positivity)
  obtain ⟨K, _hK, N₀, hN₀⟩ := hres η hη
  have hmesh : Tendsto (fun n : ℕ ↦ T / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_const_div_atTop_nhds_zero_nat T)
  have hroot : Tendsto (fun n : ℕ ↦ K * Real.sqrt (T / ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero, mul_zero] using
      ((Real.continuous_sqrt.tendsto 0).comp hmesh).const_mul K
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hroot.eventually (gt_mem_nhds hη))
  refine ⟨max N₀ N₁, fun n hn ↦ ?_⟩
  have hbound := hN₀ n ((le_max_left _ _).trans hn)
  have htail := hN₁ n ((le_max_right _ _).trans hn)
  rw [Real.dist_eq, sub_zero]
  nlinarith

/-- The actual additive integral equation, the proved uniform mesh limits,
and vanishing summed weak residuals give the exact weighted Dynkin identity.
`test` and `generator` are observations on the Banach state, ordinarily
weighted expectations on `L²`; their uniform continuity is proved separately
from bounded compact scalar tests. -/
theorem weighted_dynkin_of_weak_euler_consistency
    (g : H → H) (L : ℝ≥0) (hLip : LipschitzWith L g)
    (x : H) (B Y : ℝ → H) (hB0 : B 0 = 0) (hY : Continuous Y)
    (T : ℝ) (hT : 0 ≤ T)
    (hYe : ∀ t ∈ Icc 0 T, Y t - x = -(∫ s in 0..t, g (Y s)) + B t)
    (test generator : H → ℝ) (htest : UniformContinuous test)
    (hgenerator : UniformContinuous generator)
    (C : ℝ) (hC : 0 ≤ C)
    (hres : ∀ ε > 0, ∃ K : ℝ, 0 ≤ K ∧ ∃ N : ℕ, ∀ n ≥ N,
      |test (ULA.additiveEulerChain g (T / ((n + 1 : ℕ) : ℝ)) x B (n + 1)) -
        test x - ∑ k ∈ Finset.range (n + 1), (T / ((n + 1 : ℕ) : ℝ)) *
          generator (ULA.additiveEulerChain g (T / ((n + 1 : ℕ) : ℝ)) x B k)| ≤
        C * (ε + K * Real.sqrt (T / ((n + 1 : ℕ) : ℝ)))) :
    test (Y T) - test x = ∫ t in 0..T, generator (Y t) := by
  let r : ℕ → ℝ := fun n ↦
    test (ULA.additiveEulerChain g (T / ((n + 1 : ℕ) : ℝ)) x B (n + 1)) -
      test x - ∑ k ∈ Finset.range (n + 1), (T / ((n + 1 : ℕ) : ℝ)) *
        generator (ULA.additiveEulerChain g (T / ((n + 1 : ℕ) : ℝ)) x B k)
  have hzero : Tendsto r atTop (𝓝 0) := weakEuler_residual_tendsto_zero r T C hT hC hres
  have hendpoint := (htest.continuous.tendsto (Y T)).comp
    (ULA.additiveEulerChain_tendsto g L hLip x B Y hB0 hY T hT hYe)
  have hsum := additiveEulerChain_test_sum_tendsto g L hLip x B Y hB0 hY T hT hYe
    generator hgenerator
  have hlimit : Tendsto r atTop
      (𝓝 (test (Y T) - test x - ∫ t in 0..T, generator (Y t))) := by
    simpa only [r, smul_eq_mul, Function.comp_def] using (hendpoint.sub_const (test x)).sub hsum
  have he := tendsto_nhds_unique hlimit hzero
  exact sub_eq_zero.mp he

end AverageLMC
