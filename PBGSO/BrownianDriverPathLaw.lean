import PBGSO.ProcessPathIndependence
import PBGSO.InitialPathIndependence
import PBGSO.DriverInitialIndependence

/-! # Actual initial/Wiener-path maps for every primitive Brownian Driver
Whole path independence follows from finite-grid Driver consequences. The
continuous modification and actual initial/path law map preserve the original
Brownian evaluations at each deterministic time, without a Gaussian-seed
inverse or supplied whole-noise/product-law hypothesis.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.FilteredBrownian
variable {Ω I A : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup A] [MeasurableSpace A] [BorelSpace A]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

/-- Initialization in the original time-zero past is independent of the
whole vector Brownian path, derived from actual finite-time independence. -/
theorem Driver.initial_paths_independent (X : Ω → A) (hX : Measurable X)
    (hXA : AEStronglyMeasurable[D.filtration 0] X Q) :
    IndepFun X (fun ω i t => D.process i t ω) Q := by
  have ht := ProcessPathIndependence.initial_independent_of_finite Q
    (fun t ω i => D.process i t ω) X
    (fun t => measurable_pi_iff.mpr (fun i =>
      ((D.adapted i t).mono (D.filtration.le t)).measurable)) hX
    (fun J => Driver.initial_finite_paths_independent_ae Q D X hXA J)
  have hi := ht.comp measurable_id
    (ProcessPathIndependence.transpose ℝ≥0 I ℝ).measurable
  change IndepFun X (fun ω i t => D.process i t ω) Q at hi
  exact hi

/-- The original initial variable and actual continuous Brownian path.
The continuous modification is used on the original Driver filtration. -/
def Driver.initialPathMap (X : Ω → A) (ω : Ω) : A × (I → C(ℝ≥0,ℝ)) :=
  (X ω, BrownianPathSpace.vectorPathMap Q (continuousDriver Q D).process ω)

theorem Driver.initialPathMap_measurable (X : Ω → A) (hX : Measurable X) :
    Measurable (D.initialPathMap Q X) :=
  hX.prodMk (BrownianPathSpace.vectorPathMap_measurable Q (continuousDriver Q D).process
    (fun i t => (((continuousDriver Q D).adapted i t).mono
      ((continuousDriver Q D).filtration.le t)).measurable))

/-- The target law is exactly original-initial-law × actual product Wiener
law, derived for every primitive Driver from its original time-zero past.
No whole-coordinate/path independence or output-law conclusion is supplied. -/
theorem Driver.initialPathMap_measurePreserving (X : Ω → A) (hX : Measurable X)
    (hXA : AEStronglyMeasurable[D.filtration 0] X Q) :
    MeasurePreserving (D.initialPathMap Q X) Q
      ((Q.map X).prod (Measure.pi (fun _ : I => BrownianPathSpace.wiener))) :=
  BrownianPathSpace.initial_path_measurePreserving Q (continuousDriver Q D).process X
    (continuousDriver_brownian Q D)
    (fun i t => (((continuousDriver Q D).adapted i t).mono
      ((continuousDriver Q D).filtration.le t)).measurable) hX
    (Driver.paths_independent Q (continuousDriver Q D))
    (Driver.initial_paths_independent Q (continuousDriver Q D) X hX hXA)

@[simp] theorem Driver.initialPathMap_initial (X : Ω → A) (ω : Ω) :
    (D.initialPathMap Q X ω).1 = X ω := rfl

/-- Every deterministic path evaluation realizes the ORIGINAL Driver's
Brownian variable. A simultaneous equality to arbitrary raw pre-Brownian
representatives is deliberately not asserted. -/
theorem Driver.initialPathMap_evaluation (X : Ω → A) (i : I) (t : ℝ≥0) :
    (fun ω => (D.initialPathMap Q X ω).2 i t) =ᵐ[Q] D.process i t := by
  have hm := BrownianPathSpace.vectorPathMap_ae Q (continuousDriver Q D).process
    (continuousDriver_continuous Q D)
  have he : (fun ω => (D.initialPathMap Q X ω).2 i t) =ᵐ[Q]
      (continuousDriver Q D).process i t := by
    filter_upwards [hm] with ω hω
    exact hω i t
  exact he.trans (continuousDriver_process_ae Q D i t)

end PBGSO.FilteredBrownian
