import UnadjustedLangevin.Coupling
import Mathlib.MeasureTheory.Measure.Prod

set_option linter.style.header false

/-! # Quadratic transport on singleton spaces

A product coupling proves that any two probability measures on a singleton
have zero Wasserstein distance. This shared result includes the zero-dimensional
Euclidean case.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace ULA

variable {H : Type*} [NormedAddCommGroup H] [MeasurableSpace H] [Subsingleton H]

/-- Every coupling on a singleton has quadratic cost zero. -/
theorem couplingCost_eq_zero_of_subsingleton (ν : Measure (H × H)) :
    couplingCost ν = 0 := by
  have h : (fun p : H × H ↦ p.1 - p.2) = fun _ ↦ (0 : H) := by
    funext p
    exact sub_eq_zero.mpr (Subsingleton.elim _ _)
  simp [couplingCost, h]

/-- Probability measures on a singleton have Wasserstein distance zero, as
witnessed by their product coupling. -/
theorem wasserstein2_eq_zero_of_subsingleton (μ π : Measure H)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure π] :
    wasserstein2 μ π = 0 := by
  let c : Coupling μ π :=
    { joint := μ.prod π
      fst := by simp
      snd := by simp }
  refine le_antisymm ?_ (by simp)
  simpa only [couplingCost_eq_zero_of_subsingleton] using
    wasserstein2_le_couplingCost c

/-- The corresponding real-valued Wasserstein distance is also zero. -/
theorem wasserstein2Real_eq_zero_of_subsingleton (μ π : Measure H)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure π] :
    wasserstein2Real μ π = 0 := by
  simp [wasserstein2Real, wasserstein2_eq_zero_of_subsingleton]

end ULA

