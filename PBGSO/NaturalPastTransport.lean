import PBGSO.DriverNullAugmentation

/-! # Actual natural pasts after null modification
The ambient-measurable version of an a.e. past-measurable random variable
is measurable in the proved null augmentation of that same past. Consequently
natural filtrations of actual continuous path maps pull back to a valid
augmented Brownian past; no completeness assumption is required.
-/
noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal
namespace PBGSO.FilteredBrownian
variable {Ω Ω' E : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ω']
  [mE : MeasurableSpace E] (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- An actual ambient measurable null modification belongs to the actual
null-augmented past. -/
theorem measurable_nullAugmentation_of_ae (m : MeasurableSpace Ω)
    {f g : Ω → E} (hf : @Measurable Ω E mΩ mE f) (hg : @Measurable Ω E m inferInstance g)
    (he : f =ᵐ[Q] g) : @Measurable Ω E (nullAugmentation (mΩ := mΩ) Q m) inferInstance f := by
  intro s hs
  refine ⟨hf hs, g ⁻¹' s, hg hs, ?_⟩
  filter_upwards [he] with ω hω
  simp only [mem_preimage, hω]

section Normed
variable [NormedAddCommGroup E] [BorelSpace E]

/-- A raw a.e. adapted variable that is actually ambient measurable has an
actual past-measurable version already equal to the original raw variable. -/
theorem measurable_nullAugmentation_of_aestrong (m : MeasurableSpace Ω)
    {f : Ω → E} (hf : @Measurable Ω E mΩ mE f) (ha : AEStronglyMeasurable[m] f Q) :
    @Measurable Ω E (nullAugmentation (mΩ := mΩ) Q m) inferInstance f :=
  measurable_nullAugmentation_of_ae (mΩ := mΩ) (mE := mE) Q m hf ha.stronglyMeasurable_mk.measurable ha.ae_eq_mk

/-- The actual natural filtration of a path map pulls back to the proved
null-augmented original past. Only primitive a.e. adaptation is required. -/
theorem natural_comap_le_nullAugmented (ℱ : Filtration ℝ≥0 mΩ)
    (u : ℝ≥0 → Ω' → E) (hu : ∀ t, StronglyMeasurable (u t))
    {f : Ω → Ω'} (hf : Measurable f)
    (hA : ∀ t, AEStronglyMeasurable[ℱ t] (u t ∘ f) Q) (t : ℝ≥0) :
    MeasurableSpace.comap f (Filtration.natural u hu t) ≤ nullAugmentedFiltration Q ℱ t := by
  rw [Filtration.natural_eq_comap, MeasurableSpace.comap_comp]
  have h : @Measurable Ω (Iic t → E) (nullAugmentedFiltration Q ℱ t) inferInstance
      (fun ω r => u r (f ω)) := by
    apply (@measurable_pi_iff Ω (Iic t) (fun _ => E)
      (nullAugmentedFiltration Q ℱ t) (fun _ => mE) (fun ω r => u r (f ω))).mpr
    intro r
    exact measurable_nullAugmentation_of_aestrong (mΩ := mΩ) Q (ℱ t)
      ((hu r).measurable.comp hf) ((hA r).mono (ℱ.mono r.property))
  exact h.comap_le

end Normed
end PBGSO.FilteredBrownian
