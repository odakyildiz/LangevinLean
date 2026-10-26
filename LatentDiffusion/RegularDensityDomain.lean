import LatentDiffusion.RegularVariational
import UnadjustedLangevin.Coupling

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-! # Complete regular domains with the actual normalized transport metric

The chart's metric is explicitly the source normalized Euclidean/Wasserstein
metric of its actual probability laws. Ordinary pointwise density continuity
and local integrable energy envelopes then prove continuity and lower
semicontinuity of the actual averaged density energy. Completeness is a
property required of the chosen regular domain, never attributed to all
smooth densities.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace LatentDiffusion.RegularDensityDomain

variable {X A Z : Type*} [MetricSpace X]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] {M : ℕ}

/-- An actual regular source-state domain. The identification of its metric
with parameter error plus probability-law Wasserstein distances is part of the
domain specification. It contains no continuity or minimizing-limit assertion
about the energy integral. -/
structure ProductDensityChart (X A Z : Type*) [MetricSpace X]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
    [MeasurableSpace Z] [BorelSpace Z] (M : ℕ) (U : Fin M → A → Z → ℝ) where
  parameter : X → A
  chart : Fin M → RegularVariational.DominatedDensityChart X Z volume
  law : X → Fin M → ProbabilityMeasure Z
  finite_second_moment : ∀ x i, MemLp (fun z : Z ↦ z) 2 (law x i : Measure Z)
  density_law : ∀ x i, (law x i : Measure Z) =
    volume.withDensity (fun z ↦ ENNReal.ofReal ((chart i).density x z))
  positive : ∀ x i z, 0 < (chart i).density x z
  potential_eq : ∀ x i z, (chart i).potential x z = U i (parameter x) z
  metric_eq : ∀ x y, dist x y ^ 2 = ‖parameter x-parameter y‖ ^ 2 +
    (M : ℝ)⁻¹ * ∑ i, ULA.wasserstein2Real (law x i : Measure Z) (law y i : Measure Z) ^ 2

variable {U : Fin M → A → Z → ℝ} (D : ProductDensityChart X A Z M U)

/-- The source energy, using actual base densities and the given potentials. -/
def ProductDensityChart.energy (x : X) : ℝ :=
  (M : ℝ)⁻¹ * ∑ i, SourceCalculus.densityFreeEnergy volume
    ((D.chart i).density x) (U i (D.parameter x))

theorem ProductDensityChart.energy_eq_average_chart (x : X) :
    D.energy x = (M : ℝ)⁻¹ * ∑ i, (D.chart i).energy x := by
  unfold energy RegularVariational.DominatedDensityChart.energy
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  funext z
  exact (D.potential_eq x i z).symm

/-- Pointwise density continuity and the local integrable envelopes prove
continuity of the actual normalized source energy in its transport metric. -/
theorem ProductDensityChart.continuous_energy : Continuous D.energy := by
  have h : Continuous (fun x ↦ (M : ℝ)⁻¹ * ∑ i, (D.chart i).energy x) :=
    continuous_const.mul (continuous_finsetSum Finset.univ
      (fun i _ ↦ (D.chart i).continuous_energy))
  apply h.congr
  intro x
  exact (D.energy_eq_average_chart x).symm

theorem ProductDensityChart.lowerSemicontinuous_energy : LowerSemicontinuous D.energy :=
  D.continuous_energy.lowerSemicontinuous

/-- A Cauchy minimizing sequence for the actual normalized density energy
converges to an admissible minimizer in the complete regular transport domain. -/
theorem ProductDensityChart.cauchy_minimizer [CompleteSpace X]
    (Fstar : ℝ) (hstar : ∀ x, Fstar ≤ D.energy x) (x : ℕ → X)
    (hCauchy : CauchySeq x) (hvalue : Tendsto (fun n ↦ D.energy (x n)) atTop (𝓝 Fstar)) :
    ∃ xstar, Tendsto x atTop (𝓝 xstar) ∧ D.energy xstar = Fstar ∧
      ∀ y, D.energy xstar ≤ D.energy y :=
  SourceResults.cauchy_minimizing_sequence D.energy Fstar D.lowerSemicontinuous_energy
    hstar x hCauchy hvalue

end LatentDiffusion.RegularDensityDomain
