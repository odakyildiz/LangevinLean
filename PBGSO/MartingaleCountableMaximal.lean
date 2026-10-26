import PBGSO.MartingaleMaximalL2
import Mathlib.Data.Finset.Sort

/-! # Maximal bounds on arbitrary finite and countable observation sets
Finite times are sorted internally and a terminal time is appended. Increasing
unions then give the same bound for any countable family of earlier times.
-/
noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory Set Filter
open scoped NNReal ENNReal
namespace PBGSO.MartingaleMaximalL2
variable {Ω H ι : Type*} [mΩ : MeasurableSpace Ω] [LinearOrder ι]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (F : Filtration ι mΩ)
  (X : ι → Ω → H) (hX : Martingale X F Q)
  (h2 : ∀ t, MemLp (X t) 2 Q)

include hX h2

/-- Any finite observation set has its terminal L² maximal bound, without an
ordering premise on the input observations. -/
theorem maximal_finset (s : Finset ι) (T : ι) (hs : ∀ t ∈ s, t ≤ T) (a : ℝ≥0) :
    (a : ℝ≥0∞) * Q {ω | ∃ t ∈ s, (a : ℝ) ≤ ‖X t ω‖ ^ 2} ≤
      ENNReal.ofReal (∫ ω, ‖X T ω‖ ^ 2 ∂Q) := by
  classical
  let τ : ℕ → ι := fun n => if hn : n < s.card then s.orderEmbOfFin rfl ⟨n, hn⟩ else T
  have hτ : Monotone τ := by
    intro i j hij
    dsimp [τ]
    split_ifs with hi hj
    · exact (s.orderEmbOfFin rfl).monotone hij
    · exact hs _ (s.orderEmbOfFin_mem rfl _)
    · omega
    · rfl
  have hT : τ s.card = T := by simp [τ]
  have hd := maximal_grid Q hX h2 τ hτ a s.card
  rw [hT] at hd
  apply le_trans ?_ hd
  apply mul_le_mul_right
  apply measure_mono
  intro ω hω
  obtain ⟨t, ht, hta⟩ := hω
  have ht' : t ∈ Set.range (s.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact ht
  obtain ⟨j, hj⟩ := ht'
  change (a : ℝ) ≤ (Finset.range (s.card + 1)).sup' Finset.nonempty_range_add_one
    (fun k => ‖X (τ k) ω‖ ^ 2)
  apply hta.trans
  have he : τ j.val = t := by simp only [τ, dif_pos j.isLt, hj]
  rw [← he]
  exact Finset.le_sup' (fun k => ‖X (τ k) ω‖ ^ 2) (by simp only [Finset.mem_range]; omega)

/-- A countable family of observations is controlled by the same actual
terminal second moment, without a time-continuity assumption. -/
theorem maximal_countable (τ : ℕ → ι) (T : ι) (hτ : ∀ n, τ n ≤ T) (a : ℝ≥0) :
    (a : ℝ≥0∞) * Q {ω | ∃ n, (a : ℝ) ≤ ‖X (τ n) ω‖ ^ 2} ≤
      ENNReal.ofReal (∫ ω, ‖X T ω‖ ^ 2 ∂Q) := by
  classical
  let A : ℕ → Set Ω := fun n => {ω | ∃ k ≤ n, (a : ℝ) ≤ ‖X (τ k) ω‖ ^ 2}
  have hA : Monotone A := by
    intro m n hmn ω hω
    obtain ⟨k, hk, hka⟩ := hω
    exact ⟨k, hk.trans hmn, hka⟩
  have hb (n : ℕ) : (a : ℝ≥0∞) * Q (A n) ≤
      ENNReal.ofReal (∫ ω, ‖X T ω‖ ^ 2 ∂Q) := by
    have hf := maximal_finset Q F X hX h2 ((Finset.range (n + 1)).image τ) T
      (by intro t ht; obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ht; exact hτ k) a
    have he : A n = {ω | ∃ t ∈ (Finset.range (n + 1)).image τ,
        (a : ℝ) ≤ ‖X t ω‖ ^ 2} := by
      ext ω
      simp only [A, Finset.mem_image, Finset.mem_range, Nat.lt_succ_iff, Set.mem_ofPred_eq]
      aesop
    rw [he]
    exact hf
  have he : {ω | ∃ n, (a : ℝ) ≤ ‖X (τ n) ω‖ ^ 2} = ⋃ n, A n := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, A]
    aesop
  rw [he, hA.measure_iUnion, ENNReal.mul_iSup]
  exact iSup_le hb

end PBGSO.MartingaleMaximalL2
