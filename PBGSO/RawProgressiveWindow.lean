import PBGSO.PathwiseLocalEnergy
import PBGSO.DriverNullAugmentation

/-! # Raw real-time windows of actual progressively measurable processes -/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace PBGSO.RawProgressiveWindow
variable {Ω Z R : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup Z] [MeasurableSpace Z] [BorelSpace Z]
  [NormedAddCommGroup R] [MeasurableSpace R] [BorelSpace R]
  [SecondCountableTopology Z] [SecondCountableTopology R]

/-- Literal extension of a nonnegative-time process to real time. Negative
times are evaluated at zero and subsequently removed by the raw time mask. -/
def realExtension (u : ℝ≥0 → Ω → R) (r : ℝ) (ω : Ω) : R := u r.toNNReal ω

/-- Strong progressive measurability supplies the exact real-window raw
measurability used by first-hit energy localization. -/
theorem progressive_window (ℱ : Filtration ℝ≥0 mΩ) (u : ℝ≥0 → Ω → R)
    (hu : IsStronglyProgressive ℱ u) (t : ℝ≥0) :
    StronglyMeasurable[(inferInstance : MeasurableSpace ℝ).prod (ℱ t)]
      (fun p : ℝ × Ω => (Ioc 0 (t : ℝ)).indicator
        (fun r => realExtension u r p.2) p.1) := by
  let C : ℝ × Ω → (Iic t) × Ω := fun p => (⟨min p.1.toNNReal t, Set.mem_Iic.mpr (min_le_right _ _)⟩,p.2)
  have hC : @Measurable _ _ ((inferInstance : MeasurableSpace ℝ).prod (ℱ t))
      (Subtype.instMeasurableSpace.prod (ℱ t)) C := by
    apply Measurable.prodMk
    · exact ((measurable_fst.real_toNNReal).min measurable_const).subtype_mk
    · exact measurable_snd
  have hU := (hu t).comp_measurable hC
  have hmask := hU.indicator ((measurableSet_Ioc : MeasurableSet (Ioc 0 (t : ℝ))).preimage measurable_fst)
  have he : (fun p : ℝ × Ω => (Ioc 0 (t : ℝ)).indicator
      (fun r => realExtension u r p.2) p.1) =
      {p : ℝ × Ω | p.1 ∈ Ioc 0 (t : ℝ)}.indicator
        (fun p : ℝ × Ω => u (C p).1 (C p).2) := by
    funext p
    by_cases hp : p.1 ∈ Ioc 0 (t : ℝ)
    · have hm : p.1.toNNReal ≤ t := by
        simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hp.2
      simp only [Set.indicator,mem_setOf_eq,hp,ite_eq_left,realExtension,C,min_eq_left hm]
    · rw [Set.indicator_of_notMem hp,
        Set.indicator_of_notMem (show p ∉ {p : ℝ × Ω | p.1 ∈ Ioc 0 (t : ℝ)} from hp)]
  rw [he]
  exact hmask

/-- Measurable coefficients of an actual strongly progressive state remain
strongly progressive; no continuity of the coefficients is required. -/
theorem progressive_measurable_coefficient (ℱ : Filtration ℝ≥0 mΩ)
    (u : ℝ≥0 → Ω → Z) (hu : IsStronglyProgressive ℱ u)
    (g : Z → R) (hg : Measurable g) : IsStronglyProgressive ℱ (fun t ω => g (u t ω)) := by
  intro t
  exact (hg.comp (hu t).measurable).stronglyMeasurable

/-- For the actual null-augmented Brownian past, continuous adapted state
versions induce raw progressive measurable coefficients under merely Borel
g. This derives the path-energy window premise from primitive state data. -/
theorem continuous_adapted_coefficient_window (ℱ : Filtration ℝ≥0 mΩ)
    (u : ℝ≥0 → Ω → Z) (hu : StronglyAdapted ℱ u)
    (hcont : ∀ ω, Continuous (fun t => u t ω))
    (g : Z → R) (hg : Measurable g) (t : ℝ≥0) :
    StronglyMeasurable[(inferInstance : MeasurableSpace ℝ).prod (ℱ t)]
      (fun p : ℝ × Ω => (Ioc 0 (t : ℝ)).indicator
        (fun r => g (u r.toNNReal p.2)) p.1) :=
  progressive_window ℱ _
    (progressive_measurable_coefficient ℱ u (hu.isStronglyProgressive_of_continuous hcont) g hg) t

end PBGSO.RawProgressiveWindow
