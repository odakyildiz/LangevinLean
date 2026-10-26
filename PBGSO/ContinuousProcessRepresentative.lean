import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-! # Joint representatives of processes with almost surely continuous paths
A single measurable null-set correction preserves the entire original path
on one full-measure event. Time-point measurability and actual path continuity
then derive joint strong measurability; no jointly measurable version is an
input.
-/
noncomputable section
open MeasureTheory Set TopologicalSpace
namespace PBGSO.ContinuousProcessRepresentative
variable {Ω T Z : Type*} [MeasurableSpace Ω]
  [TopologicalSpace T] [MetrizableSpace T] [MeasurableSpace T]
  [SecondCountableTopology T] [OpensMeasurableSpace T]
  [NormedAddCommGroup Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

/-- An actual joint representative with every path continuous, and one
probability-one event on which all original time values are preserved. -/
theorem exists_joint (Q : Measure Ω) (X : T → Ω → Z)
    (hX : ∀ t, StronglyMeasurable (X t))
    (hc : ∀ᵐ ω ∂Q, Continuous (fun t => X t ω)) :
    ∃ g : T → Ω → Z, StronglyMeasurable (Function.uncurry g) ∧
      (∀ ω, Continuous (fun t => g t ω)) ∧
      ∀ᵐ ω ∂Q, ∀ t, g t ω = X t ω := by
  classical
  obtain ⟨B, hsub, hBm, hB0⟩ := exists_measurable_superset_of_null (ae_iff.mp hc)
  let g : T → Ω → Z := fun t ω => if ω ∈ B then 0 else X t ω
  have hcont (ω : Ω) : Continuous (fun t => g t ω) := by
    by_cases hω : ω ∈ B
    · simpa only [g, hω, ite_true] using (continuous_const : Continuous (fun _ : T => (0 : Z)))
    · have hgood : Continuous (fun t => X t ω) := by
        by_contra hbad
        exact hω (hsub hbad)
      simpa only [g, hω, ite_false] using hgood
  have hmeas (t : T) : StronglyMeasurable (g t) := by
    change StronglyMeasurable (B.piecewise (fun _ => (0 : Z)) (X t))
    exact stronglyMeasurable_const.piecewise hBm (hX t)
  refine ⟨g, stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hcont hmeas, hcont, ?_⟩
  filter_upwards [compl_mem_ae_iff.mpr hB0] with ω hω t
  change ω ∉ B at hω
  simp only [g, hω, ite_false]

/-- In a separable state space, ordinary fixed-time measurability suffices. -/
theorem exists_joint_of_measurable (Q : Measure Ω) (X : T → Ω → Z)
    (hX : ∀ t, Measurable (X t))
    (hc : ∀ᵐ ω ∂Q, Continuous (fun t => X t ω)) :
    ∃ g : T → Ω → Z, StronglyMeasurable (Function.uncurry g) ∧
      (∀ ω, Continuous (fun t => g t ω)) ∧
      ∀ᵐ ω ∂Q, ∀ t, g t ω = X t ω :=
  exists_joint Q X (fun t => (hX t).stronglyMeasurable) hc
end PBGSO.ContinuousProcessRepresentative
