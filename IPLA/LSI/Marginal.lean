import IPLA.Model
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Tactic.Positivity

set_option linter.style.header false

/-!
# Parameter-marginal KL from the joint IPLA law

Projection to the common parameter is measurable, so actual KL divergence
decreases under that projection. Finite joint KL supplies finite marginal KL
before any `ENNReal.toReal` conversion. The target here is the pushforward of
the actual lifted Gibbs measure; no marginal-density representation or
strong-convexity assumption is needed for this measure-theoretic step.

The inequality concerns full joint KL. A bound on joint KL divided by the
particle count gives a parameter-KL bound multiplied by that count. This file
does not assert concentration at a mode or marginal-likelihood maximizer.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace IPLA.LSI

variable {N dθ dx : ℕ}

/-- The parameter target is the actual lifted Gibbs law projected to its
parameter coordinates. Probability normalization remains an explicit premise. -/
def parameterTarget (U : Joint dθ dx → ℝ) : Measure (EuclideanSpace ℝ (Fin dθ)) :=
  (@gibbsTarget N dθ dx U).map parameterCLM

/-- Projecting a probability-valued state law preserves probability mass. -/
theorem parameterLaw_isProbability (μ : Measure (State N dθ dx))
    [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (μ.map parameterCLM) := by
  constructor
  rw [Measure.map_apply parameterCLM.continuous.measurable MeasurableSet.univ,
    Set.preimage_univ, measure_univ]

/-- The Gibbs parameter target is normalized whenever the actual joint target
is normalized. No concentration or convexity hypothesis is introduced. -/
theorem parameterTarget_isProbability (U : Joint dθ dx → ℝ)
    [IsProbabilityMeasure (@gibbsTarget N dθ dx U)] :
    IsProbabilityMeasure (@parameterTarget N dθ dx U) :=
  parameterLaw_isProbability _

/-- Extended-valued data processing for the common parameter projection. -/
theorem parameter_kl_le_joint (μ ν : Measure (State N dθ dx))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    InformationTheory.klDiv (μ.map parameterCLM) (ν.map parameterCLM) ≤
      InformationTheory.klDiv μ ν :=
  InformationTheory.klDiv_map_le μ ν parameterCLM.continuous.measurable

/-- Finite joint KL implies finite parameter KL. -/
theorem parameter_kl_ne_top_of_joint (μ ν : Measure (State N dθ dx))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hKL : InformationTheory.klDiv μ ν ≠ ⊤) :
    InformationTheory.klDiv (μ.map parameterCLM) (ν.map parameterCLM) ≠ ⊤ :=
  ne_top_of_le_ne_top hKL (parameter_kl_le_joint μ ν)

/-- The real data-processing inequality, with finiteness of both divergences
established before taking their `toReal` values. -/
theorem parameter_klReal_le_joint (μ ν : Measure (State N dθ dx))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hKL : InformationTheory.klDiv μ ν ≠ ⊤) :
    (InformationTheory.klDiv (μ.map parameterCLM) (ν.map parameterCLM)).toReal ≤
      (InformationTheory.klDiv μ ν).toReal :=
  (ENNReal.toReal_le_toReal (parameter_kl_ne_top_of_joint μ ν hKL) hKL).mpr
    (parameter_kl_le_joint μ ν)

/-- Any finite real bound on full joint KL is also a parameter-marginal bound. -/
theorem parameter_kl_bound_of_joint_bound (μ ν : Measure (State N dθ dx))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hKL : InformationTheory.klDiv μ ν ≠ ⊤) (B : ℝ)
    (hbound : (InformationTheory.klDiv μ ν).toReal ≤ B) :
    (InformationTheory.klDiv (μ.map parameterCLM) (ν.map parameterCLM)).toReal ≤ B :=
  (parameter_klReal_le_joint μ ν hKL).trans hbound

/-- A per-particle joint entropy bound controls unscaled parameter KL after
multiplication by the particle count. -/
theorem parameter_kl_bound_of_per_particle_bound (hN : 0 < N)
    (μ ν : Measure (State N dθ dx))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hKL : InformationTheory.klDiv μ ν ≠ ⊤) (B : ℝ)
    (hbound : (InformationTheory.klDiv μ ν).toReal / (N : ℝ) ≤ B) :
    (InformationTheory.klDiv (μ.map parameterCLM) (ν.map parameterCLM)).toReal ≤
      (N : ℝ) * B := by
  apply parameter_kl_bound_of_joint_bound μ ν hKL
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  simpa only [mul_comm] using (div_le_iff₀ hNreal).mp hbound

/-- Extended KL data processing with the actual Gibbs parameter target. -/
theorem parameter_kl_le_gibbs_joint (U : Joint dθ dx → ℝ)
    (μ : Measure (State N dθ dx)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure (@gibbsTarget N dθ dx U)] :
    InformationTheory.klDiv (μ.map parameterCLM) (@parameterTarget N dθ dx U) ≤
      InformationTheory.klDiv μ (gibbsTarget U) :=
  parameter_kl_le_joint μ (gibbsTarget U)

/-- Finite actual Gibbs-relative joint KL gives finite parameter KL. -/
theorem parameter_kl_ne_top_of_gibbs_joint (U : Joint dθ dx → ℝ)
    (μ : Measure (State N dθ dx)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure (@gibbsTarget N dθ dx U)]
    (hKL : InformationTheory.klDiv μ (gibbsTarget U) ≠ ⊤) :
    InformationTheory.klDiv (μ.map parameterCLM) (@parameterTarget N dθ dx U) ≠ ⊤ :=
  parameter_kl_ne_top_of_joint μ (gibbsTarget U) hKL

/-- A joint KL estimate transfers to the actual Gibbs parameter marginal,
without constructing a formula for its marginal density. -/
theorem parameter_kl_bound_of_gibbs_joint_bound (U : Joint dθ dx → ℝ)
    (μ : Measure (State N dθ dx)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure (@gibbsTarget N dθ dx U)]
    (hKL : InformationTheory.klDiv μ (gibbsTarget U) ≠ ⊤) (B : ℝ)
    (hbound : (InformationTheory.klDiv μ (gibbsTarget U)).toReal ≤ B) :
    (InformationTheory.klDiv (μ.map parameterCLM) (@parameterTarget N dθ dx U)).toReal ≤ B :=
  parameter_kl_bound_of_joint_bound μ (gibbsTarget U) hKL B hbound

end IPLA.LSI
