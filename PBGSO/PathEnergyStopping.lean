import PBGSO.StoppingSteps
import Mathlib.Topology.Order.IntermediateValue

/-! # Genuine stopping times from continuous monotone path energies -/
noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace PBGSO.PathEnergyStopping
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The actual first-hit set, restricted to the fixed finite horizon. -/
def hitSet (T : ℝ≥0) (A : ℝ≥0 → Ω → ℝ) (c : ℝ) (ω : Ω) : Set ℝ≥0 :=
  {t | t ≤ T ∧ c ≤ A t ω}

/-- First threshold hit, capped at T; empty hit sets stop at T. -/
def firstHit (T : ℝ≥0) (A : ℝ≥0 → Ω → ℝ) (c : ℝ) (ω : Ω) : ℝ≥0 := by
  classical
  exact if h : (hitSet T A c ω).Nonempty then sInf (hitSet T A c ω) else T

theorem hitSet_closed (T : ℝ≥0) (A : ℝ≥0 → Ω → ℝ) (c : ℝ) (ω : Ω)
    (hA : Continuous (fun t => A t ω)) : IsClosed (hitSet T A c ω) :=
  isClosed_Iic.inter (isClosed_Ici.preimage hA)

theorem firstHit_mem (T : ℝ≥0) (A : ℝ≥0 → Ω → ℝ) (c : ℝ) (ω : Ω)
    (hA : Continuous (fun t => A t ω)) (hne : (hitSet T A c ω).Nonempty) :
    firstHit T A c ω ∈ hitSet T A c ω := by
  classical
  rw [firstHit, dif_pos hne]
  exact (hitSet_closed T A c ω hA).csInf_mem hne (OrderBot.bddBelow _)

theorem firstHit_le_horizon (T : ℝ≥0) (A : ℝ≥0 → Ω → ℝ) (c : ℝ) (ω : Ω)
    (hA : Continuous (fun t => A t ω)) : firstHit T A c ω ≤ T := by
  classical
  by_cases hne : (hitSet T A c ω).Nonempty
  · exact (firstHit_mem T A c ω hA hne).1
  · simp only [firstHit, dif_neg hne, le_refl]

theorem firstHit_le_of_hit (T : ℝ≥0) (A : ℝ≥0 → Ω → ℝ) (c : ℝ) (ω : Ω)
    (hA : Continuous (fun t => A t ω)) (t : ℝ≥0) (ht : t ≤ T) (hc : c ≤ A t ω) :
    firstHit T A c ω ≤ t := by
  classical
  have hmem : t ∈ hitSet T A c ω := ⟨ht, hc⟩
  have hne := Set.nonempty_of_mem hmem
  rw [firstHit, dif_pos hne]
  exact csInf_le (OrderBot.bddBelow _) hmem

/-- The stopping event is a current-time energy event, with no use of
future information or a supplied stopping-time conclusion. -/
theorem firstHit_le_iff (T : ℝ≥0) (A : ℝ≥0 → Ω → ℝ) (c : ℝ) (ω : Ω)
    (hA : Continuous (fun t => A t ω)) (hmono : Monotone (fun t => A t ω)) (t : ℝ≥0) :
    firstHit T A c ω ≤ t ↔ T ≤ t ∨ c ≤ A t ω := by
  classical
  constructor
  · intro ht
    by_cases hT : T ≤ t
    · exact Or.inl hT
    · right
      have hne : (hitSet T A c ω).Nonempty := by
        by_contra hn
        simp only [firstHit, dif_neg hn] at ht
        exact hT ht
      exact (firstHit_mem T A c ω hA hne).2.trans (hmono ht)
  · rintro (hT | hc)
    · exact (firstHit_le_horizon T A c ω hA).trans hT
    · by_cases hT : T ≤ t
      · exact (firstHit_le_horizon T A c ω hA).trans hT
      · exact firstHit_le_of_hit T A c ω hA t (le_of_not_ge hT) hc

/-- Actual primitive stopping events follow from the actual adapted path
energy and the proved first-hit CDF identity. -/
theorem firstHit_stopping (ℱ : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (A : ℝ≥0 → Ω → ℝ) (c : ℝ)
    (hA : ∀ ω, Continuous (fun t => A t ω))
    (hmono : ∀ ω, Monotone (fun t => A t ω))
    (hadapted : ∀ t, Measurable[ℱ t] (A t)) :
    ∀ t, MeasurableSet[ℱ t] {ω | firstHit T A c ω ≤ t} := by
  intro t
  have he : {ω | firstHit T A c ω ≤ t} = {ω | T ≤ t ∨ c ≤ A t ω} := by
    ext ω
    exact firstHit_le_iff T A c ω (hA ω) (hmono ω) t
  rw [he]
  exact (MeasurableSet.const (T ≤ t)).union ((hadapted t) measurableSet_Ici)

/-- Continuity and genuine first-hit minimality prove the energy cap.
No bounded stopped-energy hypothesis is supplied. -/
theorem firstHit_energy_le (T : ℝ≥0) (A : ℝ≥0 → Ω → ℝ) (c : ℝ) (ω : Ω)
    (hA : Continuous (fun t => A t ω)) (hzero : A 0 ω ≤ c) :
    A (firstHit T A c ω) ω ≤ c := by
  by_contra hnot
  have hlt : c < A (firstHit T A c ω) ω := lt_of_not_ge hnot
  obtain ⟨u, hu, hAu⟩ := intermediate_value_Icc (show (0 : ℝ≥0) ≤ firstHit T A c ω from bot_le)
    hA.continuousOn ⟨hzero, hlt.le⟩
  have hmin := firstHit_le_of_hit T A c ω hA u
    (hu.2.trans (firstHit_le_horizon T A c ω hA)) (le_of_eq hAu.symm)
  have huEq : u = firstHit T A c ω := le_antisymm hu.2 hmin
  rw [huEq] at hAu
  linarith

/-- Increasing the localization threshold increases the actual stopping time. -/
theorem firstHit_mono_threshold (T : ℝ≥0) (A : ℝ≥0 → Ω → ℝ) (a b : ℝ) (hab : a ≤ b)
    (ω : Ω) (hA : Continuous (fun t => A t ω)) (hmono : Monotone (fun t => A t ω)) :
    firstHit T A a ω ≤ firstHit T A b ω := by
  have hb := (firstHit_le_iff T A b ω hA hmono (firstHit T A b ω)).mp le_rfl
  rcases hb with hT | hB
  · exact (firstHit_le_horizon T A a ω hA).trans hT
  · exact firstHit_le_of_hit T A a ω hA _ (firstHit_le_horizon T A b ω hA) (hab.trans hB)

theorem firstHit_eq_horizon_of_lt (T : ℝ≥0) (A : ℝ≥0 → Ω → ℝ) (c : ℝ) (ω : Ω)
    (hmono : Monotone (fun t => A t ω)) (hc : A T ω < c) : firstHit T A c ω = T := by
  classical
  have hne : ¬ (hitSet T A c ω).Nonempty := by
    rintro ⟨t, ht⟩
    exact (not_le_of_gt hc) (ht.2.trans (hmono ht.1))
  simp only [firstHit, dif_neg hne]

/-- Every finite path energy eventually lies below a natural threshold.
The actual localization stops are eventually exactly T on each sample. -/
theorem firstHit_nat_eventually_horizon (T : ℝ≥0) (A : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hmono : Monotone (fun t => A t ω)) :
    ∀ᶠ n : ℕ in atTop, firstHit T A n ω = T := by
  obtain ⟨N, hN⟩ := exists_nat_gt (A T ω)
  refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
  exact firstHit_eq_horizon_of_lt T A n ω hmono
    (lt_of_lt_of_le hN (by exact_mod_cast hn))

end PBGSO.PathEnergyStopping
