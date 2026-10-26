import PBGSO.DyadicStopping
import Mathlib.MeasureTheory.Function.FactorsThrough

/-! # Actual AE past-adaptation under bounded random stopping
Dyadic finite selections and a genuine measurable limit derive the stopped
adaptation without an all-path continuity or complete-filtration premise.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.FilteredBrownian
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

/-- Adapted original states with almost-sure continuous paths remain
AE-adapted after genuine bounded stopping, proved by actual finite random
selections in the current past algebra. -/
theorem stopped_raw_aestronglyAdapted (τ : Ω → ℝ≥0)
    (hstop : ∀ r, MeasurableSet[D.filtration r] {ω | τ ω ≤ r})
    (X : ℝ≥0 → Ω → Z)
    (hX : ∀ r, AEStronglyMeasurable[D.filtration r] (X r) Q)
    (hC : ∀ᵐ ω ∂Q, Continuous (fun r => X r ω)) (t : ℝ≥0) :
    AEStronglyMeasurable[D.filtration t] (fun ω => X (min t (τ ω)) ω) Q := by
  classical
  let ς : Ω → ℝ≥0 := fun ω => min t (τ ω)
  have hς : ∀ ω, ς ω ≤ t := fun ω => min_le_left _ _
  have hs : ∀ r, MeasurableSet[D.filtration r] {ω | ς ω ≤ r} := by
    intro r
    by_cases hr : t ≤ r
    · have he : {ω | ς ω ≤ r} = univ := Set.eq_univ_of_forall (fun ω => (hς ω).trans hr)
      rw [he]
      exact MeasurableSet.univ
    · have he : {ω | ς ω ≤ r} = {ω | τ ω ≤ r} := by
        ext ω
        simp only [ς,min_le_iff,hr,false_or,mem_setOf_eq]
      rw [he]
      exact hstop r
  let σ (m : ℕ) := dyadicStoppingIndex Q D t ς hς hs m
  have hj (m : ℕ) : Measurable[D.filtration t] (σ m).index := by
    apply measurable_of_Iic
    intro k
    change MeasurableSet[D.filtration t] {ω | (σ m).index ω ≤ k}
    by_cases hk : (dyadicGrids t).count m ≤ k
    · have he : {ω | (σ m).index ω ≤ k} = univ :=
        Set.eq_univ_of_forall (fun ω => ((σ m).bound ω).trans hk)
      rw [he]
      exact MeasurableSet.univ
    · have hkt : (dyadicGrids t).time m k ≤ t := by
        exact ((dyadicGrids t).monotone m (le_of_not_ge hk)).trans_eq (dyadic_time_last t m)
      exact D.filtration.mono hkt _ ((σ m).stopping k)
  let F (m k : ℕ) : Ω → Z := if hk : k ≤ (dyadicGrids t).count m then
    (hX ((dyadicGrids t).time m k)).mk (X ((dyadicGrids t).time m k)) else 0
  have hF (m k : ℕ) : StronglyMeasurable[D.filtration t] (F m k) := by
    by_cases hk : k ≤ (dyadicGrids t).count m
    · have hkt : (dyadicGrids t).time m k ≤ t := by
        exact ((dyadicGrids t).monotone m hk).trans_eq (dyadic_time_last t m)
      simpa only [F,dite_eq_left hk] using
        (hX ((dyadicGrids t).time m k)).stronglyMeasurable_mk.mono (D.filtration.mono hkt)
    · simpa only [F,dite_eq_right hk] using (stronglyMeasurable_zero : StronglyMeasurable[D.filtration t] (0 : Ω → Z))
  let G (m : ℕ) (ω : Ω) : Z := F m ((σ m).index ω) ω
  have hG (m : ℕ) : StronglyMeasurable[D.filtration t] (G m) := by
    have hm : @Measurable _ _ ((inferInstance : MeasurableSpace ℕ).prod (D.filtration t)) _
        (fun p : ℕ × Ω => F m p.1 p.2) :=
      measurable_from_prod_countable_right (fun k => (hF m k).measurable)
    exact (hm.comp ((hj m).prodMk measurable_id)).stronglyMeasurable
  have he (m : ℕ) : G m =ᵐ[Q] (fun ω => X (dyadicStop t ς hς m ω) ω) := by
    have hall : ∀ᵐ ω ∂Q, ∀ k : ℕ, X ((dyadicGrids t).time m k) ω =
        (hX ((dyadicGrids t).time m k)).mk (X ((dyadicGrids t).time m k)) ω :=
      ae_all_iff.mpr (fun k => (hX ((dyadicGrids t).time m k)).ae_eq_mk)
    filter_upwards [hall] with ω hω
    change F m ((σ m).index ω) ω = X ((dyadicGrids t).time m ((σ m).index ω)) ω
    simpa only [F,dite_eq_left ((σ m).bound ω)] using (hω ((σ m).index ω)).symm
  have hlim : ∀ᵐ ω ∂Q, Tendsto (fun m => G m ω) atTop (𝓝 (X (ς ω) ω)) := by
    filter_upwards [hC,ae_all_iff.mpr he] with ω hc heω
    have ht := (hc.tendsto (ς ω)).comp (dyadicStop_tendsto t ς hς ω)
    exact ht.congr' (Eventually.of_forall (fun m => (heω m).symm))
  have hsm : StronglyMeasurable[D.filtration t] (fun ω => limUnder atTop (fun m => G m ω)) :=
    @StronglyMeasurable.limUnder ℕ Ω Z (D.filtration t) _ _ atTop _ G _ _ hG
  refine ⟨fun ω => limUnder atTop (fun m => G m ω), hsm, ?_⟩
  filter_upwards [hlim] with ω hω
  exact hω.limUnder_eq.symm

end PBGSO.FilteredBrownian
