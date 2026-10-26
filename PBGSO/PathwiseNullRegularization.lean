import PBGSO.DriverNullAugmentation

/-! # Genuine progressive local coefficient versions after null augmentation
One measurable initial-null event regularizes all time sections together.
No path integrability, adaptation or coefficient identity is changed a.s.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace PBGSO.FilteredBrownian
variable {Ω R : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- A raw progressive coefficient whose sample paths are locally time-L¹
almost surely admits a genuine progressive version with every path time-L¹.
The construction changes only one ambient measurable null event, which the
proved augmented Brownian filtration contains already at time zero. -/
theorem exists_nullAugmented_integrable_version (ℱ : Filtration ℝ≥0 mΩ)
    (T : ℝ≥0) (q : ℝ → Ω → R)
    (hq : StronglyMeasurable (Function.uncurry q))
    (hpast : ∀ t : ℝ≥0,
      StronglyMeasurable[(inferInstance : MeasurableSpace ℝ).prod (ℱ t)]
        (fun p : ℝ × Ω => (Ioc 0 (t : ℝ)).indicator (fun r => q r p.2) p.1))
    (hlocal : ∀ᵐ ω ∂Q, IntegrableOn (fun r => q r ω) (Ioc 0 (T : ℝ))) :
    ∃ q' : ℝ → Ω → R,
      StronglyMeasurable (Function.uncurry q') ∧
      (∀ t : ℝ≥0,
        StronglyMeasurable[(inferInstance : MeasurableSpace ℝ).prod
          (nullAugmentedFiltration Q ℱ t)]
          (fun p : ℝ × Ω => (Ioc 0 (t : ℝ)).indicator (fun r => q' r p.2) p.1)) ∧
      (∀ ω, IntegrableOn (fun r => q' r ω) (Ioc 0 (T : ℝ))) ∧
      (∀ᵐ ω ∂Q, ∀ r, q' r ω = q r ω) := by
  classical
  let P : Ω → Prop := fun ω => IntegrableOn (fun r => q r ω) (Ioc 0 (T : ℝ))
  have hP : ∀ᵐ ω ∂Q, P ω := hlocal
  have hP0 : Q {ω | ¬ P ω} = 0 := ae_iff.mp hP
  obtain ⟨B,hbad,hBm,hB0⟩ := exists_measurable_superset_of_null hP0
  let q' : ℝ → Ω → R := fun r ω => if ω ∈ B then 0 else q r ω
  refine ⟨q', ?_, ?_, ?_, ?_⟩
  · have hb : MeasurableSet {p : ℝ × Ω | p.2 ∈ B} := hBm.preimage measurable_snd
    have hz : StronglyMeasurable (fun _ : ℝ × Ω => (0 : R)) := stronglyMeasurable_const
    exact hz.piecewise hb hq
  · intro t
    have hprod : (inferInstance : MeasurableSpace ℝ).prod (ℱ t) ≤
        (inferInstance : MeasurableSpace ℝ).prod (nullAugmentedFiltration Q ℱ t) := by
      exact sup_le_sup le_rfl (MeasurableSpace.comap_mono (filtration_le_nullAugmented Q ℱ t))
    have hp := (hpast t).mono hprod
    have hb : MeasurableSet[(inferInstance : MeasurableSpace ℝ).prod
        (nullAugmentedFiltration Q ℱ t)] {p : ℝ × Ω | p.2 ∈ B} :=
      (measurableSet_nullAugmentation Q (ℱ t) B hBm hB0).preimage measurable_snd
    have hfun : (fun p : ℝ × Ω => (Ioc 0 (t : ℝ)).indicator (fun r => q' r p.2) p.1) =
        fun p : ℝ × Ω => if p.2 ∈ B then 0 else
          (Ioc 0 (t : ℝ)).indicator (fun r => q r p.2) p.1 := by
      funext p
      by_cases hB : p.2 ∈ B <;> by_cases ht : p.1 ∈ Ioc 0 (t : ℝ) <;> simp [q',hB,ht]
    rw [hfun]
    exact stronglyMeasurable_const.piecewise hb hp
  · intro ω
    by_cases hω : ω ∈ B
    · simpa only [q', ite_eq_left hω] using (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : R)) _)
    · have hi : IntegrableOn (fun r => q r ω) (Ioc 0 (T : ℝ)) := by
        by_contra hn
        exact hω (hbad hn)
      simpa only [q', ite_eq_right hω] using hi
  · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hB0] with ω hω
    exact fun r => ite_eq_right hω

end PBGSO.FilteredBrownian
