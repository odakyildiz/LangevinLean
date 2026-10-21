import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.LinearAlgebra.Pi

set_option linter.style.header false

/-!
# Gaussian processes from Gaussian linear maps into L²

A linear map into real L² whose every output has a Gaussian law produces a
Gaussian process along any family of vectors. A finite-dimensional linear
projection is an actual finite linear combination; its chosen L² representative
equals the corresponding scalar random variable almost everywhere.

Only linearity is needed on the source space. In particular this applies to
the Gaussian isometry on a real Hilbert space without extra hypotheses.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ULA

variable {Ω H ι Time : Type*} [MeasurableSpace Ω]
  [AddCommMonoid H] [Module ℝ H] (P : Measure Ω)

/-- Finite collections of outputs of a Gaussian linear map are jointly
Gaussian, for the actual random-variable representatives of those outputs. -/
theorem hasGaussianLaw_pi_of_linearMap_Lp [Finite ι]
    (T : H →ₗ[ℝ] Lp ℝ 2 P) (hT : ∀ x, HasGaussianLaw (T x) P) (f : ι → H) :
    HasGaussianLaw (fun ω (i : ι) ↦ T (f i) ω) P := by
  classical
  letI := Fintype.ofFinite ι
  have hmeas : AEMeasurable (fun ω (i : ι) ↦ T (f i) ω) P :=
    aemeasurable_pi_iff.mpr fun i ↦ (Lp.aestronglyMeasurable (T (f i))).aemeasurable
  refine ⟨hmeas, isGaussian_of_isGaussian_map fun L ↦ ?_⟩
  let c : ι → ℝ := fun i ↦ L (fun j ↦ if i = j then 1 else 0)
  have hL (x : ι → ℝ) : L x = ∑ i, c i * x i := by
    change L.toLinearMap x = _
    rw [LinearMap.pi_apply_eq_sum_univ L.toLinearMap x]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm (x i) (c i)
  have hsum : T (∑ i, c i • f i) = ∑ i, c i • T (f i) := by
    simp only [map_sum, map_smul]
  have hprojection : T (∑ i, c i • f i) =ᵐ[P]
      fun ω ↦ L (fun i ↦ T (f i) ω) := by
    rw [hsum]
    have hscalar : ∀ᵐ ω ∂P, ∀ i, (c i • T (f i)) ω = c i * T (f i) ω :=
      ae_all_iff.mpr fun i ↦ Lp.coeFn_smul (c i) (T (f i))
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦ c i • T (f i)),
      hscalar] with ω hcoe hsmul
    rw [hcoe, hL]
    exact Finset.sum_congr rfl fun i _ ↦ hsmul i
  have hprojectedGaussian := (hT (∑ i, c i • f i)).congr hprojection
  rw [AEMeasurable.map_map_of_aemeasurable L.continuous.measurable.aemeasurable hmeas]
  exact hprojectedGaussian.isGaussian_map

/-- Any indexed family of vectors, mapped through a Gaussian linear map into
L², gives a Gaussian process. No continuity or countability of the index set
or of the vector family is required for its finite-dimensional laws. -/
theorem isGaussianProcess_of_linearMap_Lp
    (T : H →ₗ[ℝ] Lp ℝ 2 P) (hT : ∀ x, HasGaussianLaw (T x) P) (f : Time → H) :
    IsGaussianProcess (fun t ω ↦ T (f t) ω) P where
  hasGaussianLaw I := hasGaussianLaw_pi_of_linearMap_Lp P T hT (fun i : I ↦ f i)

end ULA
