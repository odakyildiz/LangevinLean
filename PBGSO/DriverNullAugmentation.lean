import PBGSO.FilteredIntegralModification

/-! # Actual ambient-null augmentation of a Brownian filtration
Every augmented event has an original past event equal almost surely.
Future Brownian independence is preserved by literal measure substitution.
The ambient space and probability measure are unchanged.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.FilteredBrownian
variable {Ω I : Type*} [mΩ : MeasurableSpace Ω]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- The actual measurable events equal a.e. to an event of the past algebra. -/
def nullAugmentation (m : MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' s := @MeasurableSet Ω mΩ s ∧ ∃ t, MeasurableSet[m] t ∧ s =ᵐ[Q] t
  measurableSet_empty := ⟨@MeasurableSet.empty Ω mΩ, ∅, @MeasurableSet.empty Ω m, EventuallyEq.rfl⟩
  measurableSet_compl := by
    rintro s ⟨hs,t,ht,he⟩
    exact ⟨hs.compl, tᶜ, ht.compl, he.compl⟩
  measurableSet_iUnion := by
    intro s hs
    choose hm t ht he using hs
    refine ⟨MeasurableSet.iUnion hm, ⋃ n, t n, MeasurableSet.iUnion ht, ?_⟩
    filter_upwards [ae_all_iff.mpr he] with ω hω
    simp only [mem_iUnion]
    exact propext (exists_congr (fun n => (hω n).to_iff))

theorem nullAugmentation_le (m : MeasurableSpace Ω) : nullAugmentation (mΩ := mΩ) Q m ≤ mΩ :=
  fun _ hs => hs.1

theorem le_nullAugmentation (m : MeasurableSpace Ω) (hm : m ≤ mΩ) :
    m ≤ nullAugmentation (mΩ := mΩ) Q m := fun s hs => ⟨hm s hs,s,hs,EventuallyEq.rfl⟩

theorem nullAugmentation_mono {m n : MeasurableSpace Ω} (h : m ≤ n) :
    nullAugmentation (mΩ := mΩ) Q m ≤ nullAugmentation (mΩ := mΩ) Q n := by
  rintro s ⟨hs,t,ht,he⟩
  exact ⟨hs,t,h t ht,he⟩

theorem measurableSet_nullAugmentation (m : MeasurableSpace Ω) (s : Set Ω)
    (hs : @MeasurableSet Ω mΩ s) (hnull : Q s = 0) : MeasurableSet[nullAugmentation (mΩ := mΩ) Q m] s := by
  refine ⟨hs, ∅, MeasurableSet.empty, ?_⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with ω hω
  simp [hω]

/-- Every null cover of the ambient probability space is present already at
initial time, while every event remains an actual ambient measurable set. -/
def nullAugmentedFiltration (ℱ : Filtration ℝ≥0 mΩ) : Filtration ℝ≥0 mΩ where
  seq t := nullAugmentation (mΩ := mΩ) Q (ℱ t)
  mono' _ _ h := nullAugmentation_mono Q (ℱ.mono h)
  le' _ := nullAugmentation_le Q _

theorem filtration_le_nullAugmented (ℱ : Filtration ℝ≥0 mΩ) (t : ℝ≥0) :
    ℱ t ≤ nullAugmentedFiltration Q ℱ t := le_nullAugmentation (mΩ := mΩ) Q _ (ℱ.le t)

/-- Adjoining ambient null events preserves actual independence. -/
theorem indep_nullAugmentation_right (m n : MeasurableSpace Ω)
    (hm : m ≤ mΩ) (hn : n ≤ mΩ) (h : Indep m n Q) :
    Indep m (nullAugmentation (mΩ := mΩ) Q n) Q := by
  apply (@indep_iff_forall_indepSet Ω m (nullAugmentation (mΩ := mΩ) Q n) mΩ Q).mpr
  intro s t hs ht
  change @MeasurableSet Ω mΩ t ∧ ∃ u, MeasurableSet[n] u ∧ t =ᵐ[Q] u at ht
  obtain ⟨ht, u, hu, htu⟩ := ht
  apply (@indepSet_iff_measure_inter_eq_mul Ω mΩ s t (hm s hs) ht Q inferInstance).mpr
  have he : s ∩ t =ᵐ[Q] s ∩ u := by
    filter_upwards [htu] with ω hω
    simp only [mem_inter_iff]
    exact propext (and_congr_right (fun _ => hω.to_iff))
  rw [measure_congr he, measure_congr htu]
  exact (h.indepSet_of_measurableSet hs hu).measure_inter_eq_mul

/-- The same Brownian coordinates on the same sample space with completed
past null events. Every Driver property is proved from the original one. -/
def nullAugmentedDriver (D : Driver (I := I) Q) : Driver (I := I) Q where
  process := D.process
  brownian := D.brownian
  filtration := nullAugmentedFiltration Q D.filtration
  adapted i t := (D.adapted i t).mono (filtration_le_nullAugmented Q D.filtration t)
  increment_coordinates := D.increment_coordinates
  future_independent s t hst := by
    apply indep_nullAugmentation_right Q _ _ _ (D.filtration.le s) (D.future_independent s t hst)
    apply Measurable.comap_le
    apply measurable_pi_lambda
    intro i
    exact ((D.adapted i t).measurable.mono (D.filtration.le t) le_rfl).sub
      ((D.adapted i s).measurable.mono (D.filtration.le s) le_rfl)

/-- A single measurable null cover gives an actually adapted, everywhere
continuous version after the proved null augmentation. It agrees with the
original process simultaneously at every time off that cover. -/
theorem exists_nullAugmented_continuous_version {Z : Type*}
    [NormedAddCommGroup Z]
    (ℱ : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → Z)
    (hX : StronglyAdapted ℱ X)
    (hcont : ∀ᵐ ω ∂Q, Continuous (fun t => X t ω)) :
    ∃ Y : ℝ≥0 → Ω → Z,
      StronglyAdapted (nullAugmentedFiltration Q ℱ) Y ∧
      (∀ ω, Continuous (fun t => Y t ω)) ∧
      (∀ᵐ ω ∂Q, ∀ t, Y t ω = X t ω) := by
  classical
  obtain ⟨B, hbad, hBm, hB0⟩ := exists_measurable_superset_of_null
    (show Q {ω | ¬ Continuous (fun t => X t ω)} = 0 from
      ae_iff.mp hcont)
  let Y : ℝ≥0 → Ω → Z := fun t ω => if ω ∈ B then 0 else X t ω
  refine ⟨Y, ?_, ?_, ?_⟩
  · intro t
    exact stronglyMeasurable_const.piecewise
      (measurableSet_nullAugmentation Q (ℱ t) B hBm hB0)
      ((hX t).mono (filtration_le_nullAugmented Q ℱ t))
  · intro ω
    by_cases hω : ω ∈ B
    · simpa only [Y, ite_eq_left hω] using (continuous_const : Continuous (fun _ : ℝ≥0 => (0 : Z)))
    · have hc : Continuous (fun t => X t ω) := by
        by_contra hn
        exact hω (hbad hn)
      simpa only [Y, ite_eq_right hω] using hc
  · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hB0] with ω hω
    intro t
    exact ite_eq_right hω

end PBGSO.FilteredBrownian
