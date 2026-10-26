import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

/-! # Countable spatial dependence of jointly measurable random fields

Every measurable set in a product algebra uses only countably many spatial
generators. A random field valued in a countably generated codomain therefore
is jointly measurable over a countably generated subalgebra of its original
sample space. No separability of the ambient probability measure is needed.
-/
noncomputable section
open MeasureTheory Set
namespace PBGSO.CountableProductDependence
variable {T Ω R : Type*} [mT : MeasurableSpace T] [mΩ : MeasurableSpace Ω]

private theorem prod_mono_right {m n : MeasurableSpace Ω} (h : m ≤ n) :
    mT.prod m ≤ mT.prod n :=
  sup_le_sup le_rfl (MeasurableSpace.comap_mono h)

/-- A product measurable event depends on a countable collection of
original spatial events. The dependence is exact, not only almost everywhere. -/
theorem measurableSet_countable_spatial_dependence {s : Set (T × Ω)}
    (hs : MeasurableSet s) :
    ∃ C : Set (Set Ω), C.Countable ∧ (∀ c ∈ C, MeasurableSet c) ∧
      @MeasurableSet (T × Ω) (mT.prod (MeasurableSpace.generateFrom C)) s := by
  rw [← generateFrom_prod] at hs
  induction s, hs using MeasurableSpace.generateFrom_induction with
  | hC s hs _ =>
    obtain ⟨a,ha,b,hb,rfl⟩ := hs
    exact ⟨{b}, countable_singleton _, by simpa using hb,
      @MeasurableSet.prod T Ω mT (MeasurableSpace.generateFrom {b}) a b ha
        (MeasurableSpace.measurableSet_generateFrom (by simp))⟩
  | empty => exact ⟨∅, countable_empty, by simp,
      @MeasurableSet.empty (T × Ω) (mT.prod (MeasurableSpace.generateFrom ∅))⟩
  | compl s hs ih =>
    obtain ⟨C,hC,hCm,hCs⟩ := ih
    exact ⟨C,hC,hCm,hCs.compl⟩
  | iUnion s hs ih =>
    choose C hC hCm hCs using ih
    refine ⟨⋃ n, C n, countable_iUnion hC, ?_, ?_⟩
    · intro c hc
      obtain ⟨n,hn⟩ := mem_iUnion.mp hc
      exact hCm n c hn
    · apply MeasurableSet.iUnion
      intro n
      exact prod_mono_right (MeasurableSpace.generateFrom_mono (subset_iUnion C n)) _ (hCs n)

variable [mR : MeasurableSpace R] [MeasurableSpace.CountablyGenerated R]

/-- A jointly measurable field has an actual countably generated spatial
subalgebra on which it is still jointly measurable. -/
theorem measurable_countable_spatial_dependence (f : T × Ω → R) (hf : Measurable f) :
    ∃ m : MeasurableSpace Ω, m ≤ mΩ ∧ @MeasurableSpace.CountablyGenerated Ω m ∧
      @Measurable (T × Ω) R (mT.prod m) mR f := by
  let B := MeasurableSpace.countableGeneratingSet R
  have hB : B.Countable := MeasurableSpace.countable_countableGeneratingSet (α := R)
  letI : Countable B := hB.to_subtype
  have h (s : B) : ∃ C : Set (Set Ω), C.Countable ∧ (∀ c ∈ C, MeasurableSet c) ∧
      @MeasurableSet (T × Ω) (mT.prod (MeasurableSpace.generateFrom C)) (f ⁻¹' s.val) :=
    measurableSet_countable_spatial_dependence (hf
      (MeasurableSpace.measurableSet_countableGeneratingSet s.property))
  choose C hC hCm hCs using h
  let A := ⋃ s : B, C s
  have hA : A.Countable := countable_iUnion hC
  have hAm : ∀ a ∈ A, MeasurableSet a := by
    intro a ha
    obtain ⟨s,hs⟩ := mem_iUnion.mp ha
    exact hCm s a hs
  have hCG : @MeasurableSpace.CountablyGenerated Ω (MeasurableSpace.generateFrom A) :=
    @MeasurableSpace.CountablyGenerated.mk Ω (MeasurableSpace.generateFrom A) ⟨A,hA,rfl⟩
  refine ⟨MeasurableSpace.generateFrom A, MeasurableSpace.generateFrom_le hAm, hCG, ?_⟩
  apply (@measurable_iff_comap_le (T × Ω) R (mT.prod (MeasurableSpace.generateFrom A)) mR f).mpr
  rw [← MeasurableSpace.generateFrom_countableGeneratingSet (α := R),
    MeasurableSpace.comap_generateFrom]
  apply MeasurableSpace.generateFrom_le
  rintro _ ⟨s,hs,rfl⟩
  exact prod_mono_right (MeasurableSpace.generateFrom_mono (subset_iUnion C (⟨s,hs⟩ : B))) _
    (hCs (⟨s,hs⟩ : B))

end PBGSO.CountableProductDependence
