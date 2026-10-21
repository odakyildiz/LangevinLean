import IPLA.Model
import UnadjustedLangevin.Degenerate

set_option linter.style.header false

/-! # Zero-dimensional parameter and particle spaces

The Euclidean space indexed by the empty type is a singleton. Its quadratic
transport distance and every parameter error are zero. These elementary facts
permit the public theorem to include dimension zero without extra analytic
assumptions.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace IPLA

/-- There is no parameter error when the parameter dimension is zero. This
holds for every latent dimension and every measure. -/
theorem parameterRMS_zero_dimension {N dx : ℕ} (ν : Measure (State N 0 dx))
    (θStar : EuclideanSpace ℝ (Fin 0)) :
    Real.sqrt (∫ z, ‖parameterCLM z - θStar‖ ^ 2 ∂ν) = 0 := by
  have h : (fun z : State N 0 dx ↦ ‖parameterCLM z - θStar‖ ^ 2) = fun _ ↦ (0 : ℝ) := by
    funext z
    rw [Subsingleton.elim (parameterCLM z) θStar, sub_self, norm_zero, zero_pow two_ne_zero]
  rw [h]
  simp

/-- The complete displayed error bound in the zero-dimensional state. No
regularity of a potential, noise law, or initialization is needed here. -/
theorem zero_dimensions_bound {N : ℕ}
    (μ π ν : Measure (State N 0 0)) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (m γ : ℝ) (L : ℝ≥0) (θStar : EuclideanSpace ℝ (Fin 0)) (k : ℕ) :
    Real.sqrt (∫ z, ‖parameterCLM z - θStar‖ ^ 2 ∂ν) ≤
      Real.sqrt (2 * (0 : ℝ) / ((N : ℝ) * m)) +
        (1 - m * γ) ^ k * ULA.wasserstein2Real μ π +
        (33 / 20 : ℝ) * ((L : ℝ) / m) *
          Real.sqrt ((0 : ℝ) + (0 : ℝ) / (N : ℝ)) * Real.sqrt γ := by
  simp [parameterRMS_zero_dimension, ULA.wasserstein2Real_eq_zero_of_subsingleton]

end IPLA
