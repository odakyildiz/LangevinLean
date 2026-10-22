import IPLA.LSI.Theorem
import IPLA.LSI.Marginal
import UnadjustedLangevin.LSI.UnconditionalTheorem

set_option linter.style.header false

/-! # IPLA entropy from the lifted target's LSI and finite initial KL

The actual IPLA laws are the proved lifted ULA laws. The shared unconditional
entropy theorem supplies every interpolation and moment estimate. The only
functional inequality assumed here is for the actual lifted Gibbs target;
no tensorization from a single pair model is asserted.
-/

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace IPLA.LSI

/-- Finite joint KL and its full-state bound for the actual Gaussian IPLA
laws, with no regular interpolation data or compatibility premise. -/
theorem particle_kl_bound_of_finite_kl
    {N dθ dx : ℕ} (hN : 0 < N) (U : Joint dθ dx → ℝ)
    (β γ : ℝ) (L : ℝ≥0) (μ : Measure (State N dθ dx)) [IsProbabilityMeasure μ]
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hβ : 0 < β) (hγ : 0 < γ)
    (hsmall : γ ≤ β / (4 * (N : ℝ) * (L : ℝ) ^ 2))
    (hLSI : ULA.LSI.IsLogSobolev (@gibbsTarget N dθ dx U) β)
    (hKL : InformationTheory.klDiv μ (gibbsTarget U) ≠ ⊤) (k : ℕ) :
    InformationTheory.klDiv (particleLaws U γ μ k) (gibbsTarget U) ≠ ⊤ ∧
      (InformationTheory.klDiv (particleLaws U γ μ k) (gibbsTarget U)).toReal ≤
        Real.exp (-β * γ * k / N) *
          (InformationTheory.klDiv μ (gibbsTarget U)).toReal +
            8 * γ * N * (dθ + N * dx : ℕ) * (L : ℝ) ^ 2 / β := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 < L := by
    by_contra h
    have hz : L = 0 := le_antisymm (le_of_not_gt h) zero_le
    simp only [hz, NNReal.coe_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, div_zero] at hsmall
    linarith
  have hs : γ / (N : ℝ) ≤ β / (4 * ((N : ℝ) * (L : ℝ)) ^ 2) :=
    (lifted_lsi_step_iff N hN β (L : ℝ) γ hL).mpr hsmall
  have hscaled : γ / (N : ℝ) ≤ β / (4 * (((N : ℝ≥0) * L : ℝ≥0) : ℝ) ^ 2) := by
    simpa only [NNReal.coe_mul, NNReal.coe_natCast] using hs
  obtain ⟨hfinite, hb⟩ := ULA.LSI.ula_kl_bound (@potential N dθ dx U) β (γ / N)
    ((N : ℝ≥0) * L) μ hβ (div_pos hγ hn) (potential_differentiable hdiff)
    (potential_gradient_lipschitz hdiff hLip) hLSI hscaled hKL k
  refine ⟨hfinite, ?_⟩
  change (InformationTheory.klDiv (particleLaws U γ μ k) (gibbsTarget U)).toReal ≤ _ at hb
  simpa only [NNReal.coe_mul, NNReal.coe_natCast, finrank_state,
    lifted_entropy_rate_eq, lifted_entropy_bias_eq N hN] using! hb

/-- Per-particle entropy from the actual lifted-target LSI and finite initial
joint entropy. Output finiteness is retained before real normalization. -/
theorem particle_kl_bound_normalized_of_finite_kl
    {N dθ dx : ℕ} (hN : 0 < N) (U : Joint dθ dx → ℝ)
    (β γ : ℝ) (L : ℝ≥0) (μ : Measure (State N dθ dx)) [IsProbabilityMeasure μ]
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hβ : 0 < β) (hγ : 0 < γ)
    (hsmall : γ ≤ β / (4 * (N : ℝ) * (L : ℝ) ^ 2))
    (hLSI : ULA.LSI.IsLogSobolev (@gibbsTarget N dθ dx U) β)
    (hKL : InformationTheory.klDiv μ (gibbsTarget U) ≠ ⊤) (k : ℕ) :
    InformationTheory.klDiv (particleLaws U γ μ k) (gibbsTarget U) ≠ ⊤ ∧
      (InformationTheory.klDiv (particleLaws U γ μ k) (gibbsTarget U)).toReal / N ≤
        Real.exp (-β * γ * k / N) *
          ((InformationTheory.klDiv μ (gibbsTarget U)).toReal / N) +
            8 * γ * (dθ + N * dx : ℕ) * (L : ℝ) ^ 2 / β := by
  obtain ⟨hfinite, hb⟩ := particle_kl_bound_of_finite_kl hN U β γ L μ
    hdiff hLip hβ hγ hsmall hLSI hKL k
  exact ⟨hfinite, normalize_entropy_bound N hN β γ (L : ℝ) (dθ + N * dx : ℕ)
    _ _ _ hb⟩

/-- Under an LSI constant `N * α` for the actual lifted target, the intensive
dimension is `dx + dθ / N` and the decay rate is independent of `N`. -/
theorem particle_kl_bound_linear_lsi_of_finite_kl
    {N dθ dx : ℕ} (hN : 0 < N) (U : Joint dθ dx → ℝ)
    (α γ : ℝ) (L : ℝ≥0) (μ : Measure (State N dθ dx)) [IsProbabilityMeasure μ]
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hα : 0 < α) (hγ : 0 < γ)
    (hsmall : γ ≤ α / (4 * (L : ℝ) ^ 2))
    (hLSI : ULA.LSI.IsLogSobolev (@gibbsTarget N dθ dx U) ((N : ℝ) * α))
    (hKL : InformationTheory.klDiv μ (gibbsTarget U) ≠ ⊤) (k : ℕ) :
    InformationTheory.klDiv (particleLaws U γ μ k) (gibbsTarget U) ≠ ⊤ ∧
      (InformationTheory.klDiv (particleLaws U γ μ k) (gibbsTarget U)).toReal / N ≤
        Real.exp (-α * γ * k) *
          ((InformationTheory.klDiv μ (gibbsTarget U)).toReal / N) +
            (8 * γ * (L : ℝ) ^ 2 / α) * ((dx : ℝ) + (dθ : ℝ) / N) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hL := ULA.LSI.positive_smoothness_of_step α γ L hγ hsmall
  have hs := (linear_lsi_step_iff N hN α (L : ℝ) γ hL).mpr hsmall
  obtain ⟨hfinite, hb⟩ := particle_kl_bound_normalized_of_finite_kl hN U ((N : ℝ) * α)
    γ L μ hdiff hLip (mul_pos hn hα) hγ hs hLSI hKL k
  refine ⟨hfinite, ?_⟩
  simpa only [linear_entropy_rate_eq N hN,
    linear_normalized_entropy_bias_eq N dθ dx hN] using hb

/-- The parameter marginal has finite KL and inherits the unnormalized
full-state bound by data processing. The initial entropy is joint entropy. -/
theorem parameter_kl_bound_of_finite_kl
    {N dθ dx : ℕ} (hN : 0 < N) (U : Joint dθ dx → ℝ)
    (β γ : ℝ) (L : ℝ≥0) (μ : Measure (State N dθ dx)) [IsProbabilityMeasure μ]
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hβ : 0 < β) (hγ : 0 < γ)
    (hsmall : γ ≤ β / (4 * (N : ℝ) * (L : ℝ) ^ 2))
    (hLSI : ULA.LSI.IsLogSobolev (@gibbsTarget N dθ dx U) β)
    (hKL : InformationTheory.klDiv μ (gibbsTarget U) ≠ ⊤) (k : ℕ) :
    InformationTheory.klDiv ((particleLaws U γ μ k).map parameterCLM)
      (@parameterTarget N dθ dx U) ≠ ⊤ ∧
      (InformationTheory.klDiv ((particleLaws U γ μ k).map parameterCLM)
        (@parameterTarget N dθ dx U)).toReal ≤
        Real.exp (-β * γ * k / N) *
          (InformationTheory.klDiv μ (gibbsTarget U)).toReal +
            8 * γ * N * (dθ + N * dx : ℕ) * (L : ℝ) ^ 2 / β := by
  have : IsProbabilityMeasure (particleLaws U γ μ k) :=
    particleLaws_isProbability U γ μ L hdiff hLip k
  have : IsProbabilityMeasure (@gibbsTarget N dθ dx U) := hLSI.1
  obtain ⟨hfinite, hb⟩ := particle_kl_bound_of_finite_kl hN U β γ L μ
    hdiff hLip hβ hγ hsmall hLSI hKL k
  exact ⟨parameter_kl_ne_top_of_gibbs_joint U (particleLaws U γ μ k) hfinite,
    parameter_kl_bound_of_gibbs_joint_bound U (particleLaws U γ μ k) hfinite _ hb⟩

end IPLA.LSI
