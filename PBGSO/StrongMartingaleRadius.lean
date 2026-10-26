import PBGSO.DoobStrongL2
import PBGSO.MonotoneSquareRadius
import Mathlib.Data.Finset.Sort
import Mathlib.Topology.Sequences

/-! # A constructed L² path radius for actual continuous martingales -/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
namespace PBGSO.DoobStrongL2
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem le_running (f : ℕ → Ω → ℝ) (n k : ℕ) (hk : k < n) (ω : Ω) :
    f k ω ≤ running f n ω := by
  exact (le_max_right (running f k ω) (f k ω)).trans
    (running_mono f ω (Nat.succ_le_of_lt hk))

theorem running_le (f : ℕ → Ω → ℝ) (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (ω : Ω) (h : ∀ k < n, f k ω ≤ C) : running f n ω ≤ C := by
  induction n with
  | zero => exact hC
  | succ n ih => exact max_le (ih (fun k hk => h k (Nat.lt_succ_of_lt hk))) (h n (Nat.lt_succ_self _))

section Bounds
variable {H ι : Type*} [LinearOrder ι]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (F : Filtration ι mΩ)
  (X : ι → Ω → H) (hX : Martingale X F Q) (h2 : ∀ t, MemLp (X t) 2 Q)
include hX h2

/-- Arbitrary finite observations are sorted internally, giving the same
strong maximal moment bound at their common terminal time. -/
theorem finite_family_square (τ : ℕ → ι) (T : ι) (hτ : ∀ k, τ k ≤ T) (n : ℕ) :
    (∫ ω, running (fun k ω => ‖X (τ k) ω‖) n ω ^ 2 ∂Q) ≤
      4 * ∫ ω, ‖X T ω‖ ^ 2 ∂Q := by
  classical
  let s := (Finset.range n).image τ
  let σ : ℕ → ι := fun k => if hk : k < s.card then s.orderEmbOfFin rfl ⟨k, hk⟩ else T
  have hσ : Monotone σ := by
    intro i j hij
    dsimp [σ]
    split_ifs with hi hj
    · exact (s.orderEmbOfFin rfl).monotone hij
    · obtain ⟨k, _, hk⟩ := Finset.mem_image.mp (s.orderEmbOfFin_mem rfl ⟨i, hi⟩)
      rw [← hk]
      exact hτ k
    · omega
    · rfl
  have hend : σ s.card = T := by simp [σ]
  have hb := finite_grid Q F X hX h2 σ hσ s.card
  rw [hend] at hb
  apply le_trans _ hb
  have hsq (a : ℕ → ι) (k : ℕ) :
      Integrable (fun ω => running (fun j ω => ‖X (a j) ω‖) k ω ^ 2) Q := by
    have hi := running_memLp Q (fun j ω => ‖X (a j) ω‖) (fun j => (h2 (a j)).norm) k
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mp hi
  apply integral_mono (hsq τ n) (hsq σ s.card)
  intro ω
  apply pow_le_pow_left₀ (running_nonneg _ _ _) _ 2
  apply running_le _ n _ (running_nonneg _ _ _) ω
  intro k hk
  have hmem : τ k ∈ s := Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
  have hrange : τ k ∈ Set.range (s.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hmem
  obtain ⟨j, hj⟩ := hrange
  have he : σ j.val = τ k := by simp only [σ, dif_pos j.isLt, hj]
  simpa only [he] using le_running (fun k ω => ‖X (σ k) ω‖) s.card j.val j.isLt ω

/-- Actual terminal square integrability constructs a measurable L² radius
for every countable family of earlier observations. -/
theorem exists_countable_radius (τ : ℕ → ι) (T : ι) (hτ : ∀ k, τ k ≤ T) :
    ∃ C : Ω → ℝ, Measurable C ∧ (∀ ω, 0 ≤ C ω) ∧ MemLp C 2 Q ∧
      (∫ ω, C ω ^ 2 ∂Q) ≤ 4 * ∫ ω, ‖X T ω‖ ^ 2 ∂Q ∧
      ∀ᵐ ω ∂Q, ∀ k, ‖X (τ k) ω‖ ≤ C ω := by
  let f := fun k ω => ‖X (τ k) ω‖
  have hf (k : ℕ) : StronglyMeasurable (f k) :=
    ((hX.stronglyAdapted (τ k)).mono (F.le _)).norm
  have hu (n : ℕ) : Measurable (running f n) := by
    induction n with
    | zero => exact measurable_const
    | succ n ih => exact ih.max (hf n).measurable
  have hR : 0 ≤ 4 * ∫ ω, ‖X T ω‖ ^ 2 ∂Q :=
    mul_nonneg (by norm_num) (integral_nonneg (fun _ => sq_nonneg _))
  obtain ⟨C, hCm, hC0, hC2, hCB, hCu⟩ := MonotoneSquareRadius.exists_radius Q (running f)
    hu (running_memLp Q f (fun k => (h2 (τ k)).norm)) (running_nonneg f)
    (running_mono f) _ hR (finite_family_square Q F X hX h2 τ T hτ)
  refine ⟨C, hCm, hC0, hC2, hCB, ?_⟩
  filter_upwards [hCu] with ω hω k
  exact (le_running f (k + 1) k (Nat.lt_succ_self _) ω).trans (hω (k + 1))

/-- A countable dense observation family and actual path continuity extend
the constructed L² radius to the whole observation window. -/
theorem exists_continuous_radius [TopologicalSpace ι] [SecondCountableTopology ι]
    (s : Set ι) (hs : s.Nonempty) (T : ι) (hsT : ∀ t ∈ s, t ≤ T)
    (hc : ∀ᵐ ω ∂Q, ContinuousOn (fun t => X t ω) s) :
    ∃ C : Ω → ℝ, Measurable C ∧ (∀ ω, 0 ≤ C ω) ∧ MemLp C 2 Q ∧
      (∫ ω, C ω ^ 2 ∂Q) ≤ 4 * ∫ ω, ‖X T ω‖ ^ 2 ∂Q ∧
      ∀ᵐ ω ∂Q, ∀ t ∈ s, ‖X t ω‖ ≤ C ω := by
  classical
  letI : Nonempty s := hs.to_subtype
  let τ := TopologicalSpace.denseSeq s
  obtain ⟨C, hCm, hC0, hC2, hCB, hCτ⟩ := exists_countable_radius Q F X hX h2
    (fun k => (τ k).val) T (fun k => hsT _ (τ k).property)
  refine ⟨C, hCm, hC0, hC2, hCB, ?_⟩
  filter_upwards [hc, hCτ] with ω hω hτ t ht
  have hcont : Continuous (fun t : s => ‖X t.val ω‖) :=
    (continuousOn_iff_continuous_domRestrict.mp hω).norm
  have hclosed : IsClosed {t : s | ‖X t.val ω‖ ≤ C ω} := isClosed_le hcont continuous_const
  have hr : Set.range τ ⊆ {t : s | ‖X t.val ω‖ ≤ C ω} := by
    rintro _ ⟨k, rfl⟩
    exact hτ k
  have hd : closure (Set.range τ) = Set.univ := (TopologicalSpace.denseRange_denseSeq s).closure_range
  exact hclosed.closure_subset_iff.mpr hr (by rw [hd]; exact Set.mem_univ (⟨t, ht⟩ : s))
end Bounds
end PBGSO.DoobStrongL2
