import UnadjustedLangevin.LangevinUniqueness

/-! # Global additive integral dynamics for an arbitrary Banach vector field

Finite Picard solutions are glued by actual common-input uniqueness. The
result covers deterministic ODEs and random complete particle states, with
arbitrary continuous additive inputs. No global solution is a hypothesis.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace PBGSO
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_global_integral_solution
    (f : E → E) (L : ℝ≥0) (hf : LipschitzWith L f) (initial : E)
    (B : ℝ → E) (hB : Continuous B) (hB0 : B 0 = 0) :
    ∃ Y : ℝ → E, Continuous Y ∧ Y 0 = initial ∧
      ∀ t, 0 ≤ t → Y t - initial = (∫ r in 0..t, f (Y r)) + B t := by
  classical
  have exists_finite (T : ℝ) (hT : 0 ≤ T) : ∃ Y : ℝ → E,
      Continuous Y ∧ Y 0 = initial ∧ ∀ t ∈ Icc 0 T,
        Y t - initial = (∫ r in 0..t, f (Y r)) + B t := by
    obtain ⟨Y, hc, hi, he⟩ := ULA.exists_langevin_integral
      (fun z => -f z) L hf.neg initial B hB hB0 T hT
    exact ⟨Y, hc, hi, fun t ht => by
      simpa only [intervalIntegral.integral_neg, neg_neg] using he t ht⟩
  let flow := fun n : ℕ ↦ Classical.choose
    (exists_finite ((n : ℝ) + 1) (Nat.cast_add_one_pos n).le)
  have hs (n : ℕ) : Continuous (flow n) ∧ flow n 0 = initial ∧
      ∀ t ∈ Icc 0 ((n : ℝ) + 1), flow n t - initial =
        (∫ r in 0..t, f (flow n r)) + B t :=
    Classical.choose_spec
      (exists_finite ((n : ℝ) + 1) (Nat.cast_add_one_pos n).le)
  have coherent (m n : ℕ) (r : ℝ) (hr : 0 ≤ r)
      (hm : r ≤ (m : ℝ) + 1) (hn : r ≤ (n : ℝ) + 1) : flow m r = flow n r := by
    have hg : LipschitzWith L (fun z ↦ -f z) := hf.neg
    have he := ULA.langevin_integral_unique (fun z ↦ -f z) L hg initial
      (fun t ↦ B t) (flow m) (flow n) (hs m).1 (hs n).1 r hr
      (fun t ht ↦ by
        simpa only [intervalIntegral.integral_neg, neg_neg] using
          (hs m).2.2 t ⟨ht.1, ht.2.trans hm⟩)
      (fun t ht ↦ by
        simpa only [intervalIntegral.integral_neg, neg_neg] using
          (hs n).2.2 t ⟨ht.1, ht.2.trans hn⟩)
    exact he ⟨hr, le_rfl⟩
  let Y := fun t : ℝ ↦ flow (Nat.ceil (max 0 t)) (max 0 t)
  have agree (n : ℕ) (r : ℝ) (hr : max 0 r ≤ (n : ℝ) + 1) :
      Y r = flow n (max 0 r) := by
    apply coherent _ n _ (le_max_left _ _)
    · exact (Nat.le_ceil _).trans (by linarith)
    · exact hr
  have hcont : Continuous Y := by
    apply continuous_iff_continuousAt.mpr
    intro t
    let n := Nat.ceil (max 0 t)
    have ht : max 0 t < (n : ℝ) + 1 := lt_of_le_of_lt (Nat.le_ceil _) (by linarith)
    have hc : Continuous (fun r : ℝ ↦ max 0 r) := continuous_const.max continuous_id
    have hev : ∀ᶠ r in 𝓝 t, max 0 r < (n : ℝ) + 1 := hc.continuousAt.eventually (gt_mem_nhds ht)
    apply ((hs n).1.comp hc).continuousAt.congr_of_eventuallyEq
    exact hev.mono fun r hr ↦ agree n r hr.le
  have hzero : Y 0 = initial := by
    have h : Y 0 = flow 0 0 := by simpa only [max_self] using agree 0 0 (by norm_num)
    exact h.trans (hs 0).2.1
  refine ⟨Y, hcont, hzero, ?_⟩
  intro t ht
  let n := Nat.ceil t
  have hnt : t ≤ (n : ℝ) + 1 := (Nat.le_ceil t).trans (by linarith)
  have he (r : ℝ) (hr : r ∈ Icc 0 t) : Y r = flow n r := by
    simpa only [max_eq_right hr.1] using agree n r (by rw [max_eq_right hr.1]; exact hr.2.trans hnt)
  have hint : (∫ r in 0..t, f (Y r)) = ∫ r in 0..t, f (flow n r) := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le ht] at hr
    change f (Y r) = f (flow n r)
    rw [he r hr]
  rw [he t ⟨ht, le_rfl⟩, hint]
  exact (hs n).2.2 t ⟨ht, hnt⟩

end PBGSO
