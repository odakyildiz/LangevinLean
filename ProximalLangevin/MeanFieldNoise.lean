import UnadjustedLangevin.ProductBrownian
import UnadjustedLangevin.CanonicalBrownian

set_option linter.style.header false

/-!
# Actual parameter Brownian noise on the iid particle-copy space

The finite-product comparison uses the first copy of a supplied Brownian
source for the common parameter noise. Its `N⁻¹/²` size and finite-horizon
bound are derived from the source laws, rather than assumed error estimates.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace ProximalLangevin

section Source
variable {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    {N dθ : ℕ} (hN : 0 < N)
    (W : Fin dθ → ℝ≥0 → Ω → ℝ) (hW : ∀ j, IsPreBrownianReal (W j) Q)

include hW

/-- Each coordinate of the common parameter source has the actual Brownian
law after pullback to the finite iid product. -/
theorem empiricalParameter_preBrownian (j : Fin dθ) :
    IsPreBrownianReal (fun s (ω : Fin N → Ω) => W j s (ω ⟨0, hN⟩))
      (Measure.pi (fun _ : Fin N => Q)) :=
  ULA.Hilbert.preBrownian_comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin N => Q) ⟨0, hN⟩) (W j) (hW j)

/-- The actual parameter Brownian input, with the particle scaling. -/
def empiricalParameterNoise (t : ℝ) :
    Lp (EuclideanSpace ℝ (Fin dθ)) 2 (Measure.pi (fun _ : Fin N => Q)) :=
  (Real.sqrt (N : ℝ))⁻¹ •
    ULA.brownianLangevinNoise (Measure.pi (fun _ : Fin N => Q))
      (fun j s (ω : Fin N → Ω) => W j s (ω ⟨0, hN⟩))
      (empiricalParameter_preBrownian Q hN W hW) 0 t

theorem empiricalParameterNoise_continuous :
    Continuous (empiricalParameterNoise Q hN W hW) := by
  change Continuous (fun t : ℝ => (Real.sqrt (N : ℝ))⁻¹ •
    ULA.brownianLangevinNoise (Measure.pi (fun _ : Fin N => Q))
      (fun j s (ω : Fin N → Ω) => W j s (ω ⟨0, hN⟩))
      (empiricalParameter_preBrownian Q hN W hW) 0 t)
  exact (continuous_const : Continuous (fun _ : ℝ => (Real.sqrt (N : ℝ))⁻¹)).smul
    (ULA.brownianLangevinNoise_continuous (Measure.pi (fun _ : Fin N => Q))
    (fun j s (ω : Fin N → Ω) => W j s (ω ⟨0, hN⟩))
    (empiricalParameter_preBrownian Q hN W hW) 0)

@[simp] theorem empiricalParameterNoise_zero :
    empiricalParameterNoise Q hN W hW 0 = 0 := by
  simp only [empiricalParameterNoise, ULA.brownianLangevinNoise_zero, smul_zero]

/-- The exact Brownian second-moment scale of the actual parameter input. -/
theorem empiricalParameterNoise_norm (t : ℝ) (ht : 0 ≤ t) :
    ‖empiricalParameterNoise Q hN W hW t‖ =
      Real.sqrt (2 * (dθ : ℝ)) * Real.sqrt t / Real.sqrt (N : ℝ) := by
  rw [empiricalParameterNoise, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), ULA.brownianLangevinNoise_norm _ _ _ 0 t le_rfl ht]
  simp only [Fintype.card_fin]
  ring

/-- A finite-horizon bound with an explicit coefficient independent of `N`. -/
theorem empiricalParameterNoise_bound (T t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖empiricalParameterNoise Q hN W hW t‖ ≤
      (Real.sqrt (2 * (dθ : ℝ)) * Real.sqrt T) / Real.sqrt (N : ℝ) := by
  rw [empiricalParameterNoise_norm Q hN W hW t ht.1]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt ht.2) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

end Source

/-- A concrete source exists: the Brownian coordinates are the already
constructed independent Gaussian time-indicator processes. -/
theorem canonical_empiricalParameterNoise_bound (N dθ : ℕ) (hN : 0 < N)
    (T t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖empiricalParameterNoise (ULA.CanonicalBrownian.vectorProbability (Fin dθ)) hN
      ULA.CanonicalBrownian.coordinate ULA.CanonicalBrownian.coordinate_isPreBrownian t‖ ≤
      (Real.sqrt (2 * (dθ : ℝ)) * Real.sqrt T) / Real.sqrt (N : ℝ) :=
  empiricalParameterNoise_bound _ hN _ _ T t ht

end ProximalLangevin
