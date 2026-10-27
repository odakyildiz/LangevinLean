import LatentDiffusion.SourceAssumptions
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# The literal time-zero solution assumption has an obstruction

An arbitrary finite-second-moment initial law includes a Dirac measure. Such a
law cannot have a density relative to a reference measure that assigns zero mass
to the corresponding singleton. This argument needs no PDE or positivity
assumption. In particular it applies to Lebesgue measure in positive dimension.
-/

noncomputable section
open MeasureTheory Set

namespace LatentDiffusion.SourceObstruction

variable {P Z : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-- The source's universal solution regularity is impossible whenever the
reference measure has even one null singleton. The initial law is an actual
finite-second-moment Dirac probability measure. -/
theorem not_solutionRegularity_of_null_singleton {M : ℕ} (hM : 0 < M)
    (ν : Measure Z) (z₀ : Z) (hν : ν {z₀} = 0) (p₀ : P)
    (flowEquation : (ℝ → P) → (Fin M → ℝ → ProbabilityMeasure Z) → Prop) :
    ¬ SourceAssumptions.SolutionRegularity ν flowEquation := by
  intro h
  let μ₀ : Fin M → ProbabilityMeasure Z := fun _ ↦ (Measure.dirac z₀).toProbabilityMeasure
  have hmem : ∀ i, MemLp (fun z : Z ↦ z) 2 (μ₀ i : Measure Z) := by
    intro i
    change MemLp (fun z : Z ↦ z) 2 (Measure.dirac z₀)
    exact (memLp_congr_ae (ae_eq_dirac (fun z : Z ↦ z))).mpr
      (memLp_const (μ := Measure.dirac z₀) (p := 2) z₀)
  obtain ⟨S⟩ := h p₀ μ₀ hmem
  let i : Fin M := ⟨0, hM⟩
  have hinit : (S.law i 0 : Measure Z) = Measure.dirac z₀ := by
    rw [S.initial_law i]
    rfl
  have hd : Measure.dirac z₀ =
      ν.withDensity (fun z ↦ ENNReal.ofReal (S.density i 0 z)) := by
    rw [← hinit]
    exact S.density_realizes i 0 le_rfl
  have hac : Measure.dirac z₀ ≪ ν := by
    rw [hd]
    exact withDensity_absolutelyContinuous _ _
  have hz := hac hν
  simp at hz

/-- Atomless reference measures, including positive-dimensional Lebesgue
measures, therefore rule out the literal source premise. -/
theorem not_solutionRegularity_of_noAtoms {M : ℕ} (hM : 0 < M)
    (ν : Measure Z) [NullSingletonClass ν] (p₀ : P)
    (flowEquation : (ℝ → P) → (Fin M → ℝ → ProbabilityMeasure Z) → Prop) :
    ¬ SourceAssumptions.SolutionRegularity ν flowEquation :=
  not_solutionRegularity_of_null_singleton hM ν 0 (measure_singleton 0) p₀ flowEquation

end LatentDiffusion.SourceObstruction
