import PBGSO.MartingaleMaximalL2
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Strong L² maximal control from actual martingales
A finite running maximum, conditional expectation, and Young's inequality
prove the factor-four moment bound. Weak-L² tails are not integrated as if
they implied a finite second maximal moment.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace PBGSO.DoobStrongL2
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Running maximum includes zero and the first n observations. -/
def running (f : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun ω => max (running f n ω) (f n ω)

theorem running_nonneg (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : 0 ≤ running f n ω := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact ih.trans (le_max_left _ _)

theorem running_mono (f : ℕ → Ω → ℝ) (ω : Ω) : Monotone (fun n => running f n ω) :=
  monotone_nat_of_le_succ (fun _ => le_max_left _ _)

theorem sum_running_increments (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    (∑ k ∈ Finset.range n, (running f (k + 1) ω - running f k ω)) = running f n ω := by
  induction n with
  | zero => simp [running]
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

theorem running_memLp (Q : Measure Ω) (f : ℕ → Ω → ℝ) (hf : ∀ n, MemLp (f n) 2 Q)
    (n : ℕ) : MemLp (running f n) 2 Q := by
  induction n with
  | zero => exact MemLp.zero'
  | succ n ih => exact ih.sup (hf n)

theorem running_stronglyMeasurable (F : Filtration ℕ mΩ) (f : ℕ → Ω → ℝ)
    (hf : StronglyAdapted F f) (n t : ℕ) (hnt : n ≤ t + 1) :
    StronglyMeasurable[F t] (running f n) := by
  induction n with
  | zero => exact stronglyMeasurable_const
  | succ n ih =>
    exact ((ih (by omega)).measurable.max
      (((hf n).mono (F.mono (by omega))).measurable)).stronglyMeasurable

/-- The maximum increases only when the current observation attains it. -/
theorem running_square_bound (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    (running f n ω) ^ 2 ≤ 2 * ∑ k ∈ Finset.range n,
      f k ω * (running f (k + 1) ω - running f k ω) := by
  induction n with
  | zero => simp [running]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hi : (running f (n + 1) ω) ^ 2 - (running f n ω) ^ 2 ≤
        2 * f n ω * (running f (n + 1) ω - running f n ω) := by
      by_cases h : f n ω ≤ running f n ω
      · simp only [running, max_eq_left h, sub_self, mul_zero, le_refl]
      · simp only [running, max_eq_right (le_of_not_ge h)]
        nlinarith [sq_nonneg (f n ω - running f n ω)]
    linarith

section Submartingale
variable (Q : Measure Ω) [IsProbabilityMeasure Q] (F : Filtration ℕ mΩ)
  (f : ℕ → Ω → ℝ) (hf : Submartingale f F Q) (h2 : ∀ n, MemLp (f n) 2 Q)
include hf h2

/-- A nonnegative past-measurable L² weight transfers an observation to the
terminal submartingale value by actual conditional expectation. -/
theorem weighted_expectation_le (k n : ℕ) (hkn : k ≤ n)
    (H : Ω → ℝ) (hH : StronglyMeasurable[F k] H) (hH2 : MemLp H 2 Q)
    (hH0 : ∀ ω, 0 ≤ H ω) :
    (∫ ω, H ω * f k ω ∂Q) ≤ ∫ ω, H ω * f n ω ∂Q := by
  have hik := hH2.integrable_mul (h2 k)
  have hin := hH2.integrable_mul (h2 n)
  have hpull := condExp_mul_of_stronglyMeasurable_left hH hin (hf.integrable n)
  have hic : Integrable (fun ω => H ω * Q[f n | F k] ω) Q := integrable_condExp.congr hpull
  calc
    _ ≤ ∫ ω, H ω * Q[f n | F k] ω ∂Q := by
      apply integral_mono_ae hik hic
      filter_upwards [hf.2.1 k n hkn] with ω hω
      exact mul_le_mul_of_nonneg_left hω (hH0 ω)
    _ = _ := (integral_congr_ae hpull).symm.trans (integral_condExp (F.le k))

/-- Strong Doob L² on an actual finite observation sequence. The running
maximum uses observations strictly before n; n is the terminal time. -/
theorem finite_maximum_square (n : ℕ) :
    (∫ ω, (running f n ω) ^ 2 ∂Q) ≤ 4 * ∫ ω, (f n ω) ^ 2 ∂Q := by
  let H (k : ℕ) (ω : Ω) := running f (k + 1) ω - running f k ω
  have hH2 (k : ℕ) : MemLp (H k) 2 Q :=
    (running_memLp Q f h2 (k + 1)).sub (running_memLp Q f h2 k)
  have hH (k : ℕ) : StronglyMeasurable[F k] (H k) :=
    (running_stronglyMeasurable F f hf.stronglyAdapted (k + 1) k le_rfl).sub
      (running_stronglyMeasurable F f hf.stronglyAdapted k k (by omega))
  have hH0 (k : ℕ) (ω : Ω) : 0 ≤ H k ω := sub_nonneg.mpr (running_mono f ω (Nat.le_succ k))
  have hsquare := (memLp_two_iff_integrable_sq_norm
    (running_memLp Q f h2 n).aestronglyMeasurable).mp (running_memLp Q f h2 n)
  have hsquare' : Integrable (fun ω => (running f n ω) ^ 2) Q := by
    simpa only [Real.norm_eq_abs, sq_abs] using hsquare
  have hterminal := (memLp_two_iff_integrable_sq_norm (h2 n).aestronglyMeasurable).mp (h2 n)
  have hterminal' : Integrable (fun ω => (f n ω) ^ 2) Q := by
    simpa only [Real.norm_eq_abs, sq_abs] using hterminal
  have hprod := (running_memLp Q f h2 n).integrable_mul (h2 n)
  have hfirst : (∫ ω, (running f n ω) ^ 2 ∂Q) ≤
      2 * ∑ k ∈ Finset.range n, (∫ ω, H k ω * f k ω ∂Q) := by
    change (∫ ω, (running f n ω) ^ 2 ∂Q) ≤
      2 * ∑ k ∈ Finset.range n, (∫ ω, (H k * f k) ω ∂Q)
    rw [← integral_finsetSum _ (fun k _ => (hH2 k).integrable_mul (h2 k)),
      ← integral_const_mul]
    apply integral_mono hsquare'
      ((integrable_finsetSum _ (fun k _ => (hH2 k).integrable_mul (h2 k))).const_mul 2)
    intro ω
    simpa only [H, Pi.mul_apply, mul_comm (f _ ω)] using running_square_bound f n ω
  have htransfer : (∑ k ∈ Finset.range n, (∫ ω, H k ω * f k ω ∂Q)) ≤
      ∫ ω, running f n ω * f n ω ∂Q := by
    calc
      _ ≤ ∑ k ∈ Finset.range n, (∫ ω, H k ω * f n ω ∂Q) := by
        apply Finset.sum_le_sum
        intro k hk
        exact weighted_expectation_le Q F f hf h2 k n (Finset.mem_range.mp hk).le
          (H k) (hH k) (hH2 k) (hH0 k)
      _ = _ := by
        change (∑ k ∈ Finset.range n, (∫ ω, (H k * f n) ω ∂Q)) = _
        rw [← integral_finsetSum _ (fun k _ => (hH2 k).integrable_mul (h2 n))]
        apply integral_congr_ae
        apply ae_of_all
        intro ω
        change (∑ k ∈ Finset.range n, H k ω * f n ω) = running f n ω * f n ω
        rw [← Finset.sum_mul]
        have hsum : ∑ k ∈ Finset.range n, H k ω = running f n ω :=
          sum_running_increments f n ω
        rw [hsum]
  have hyoung : (∫ ω, running f n ω * f n ω ∂Q) ≤
      (1 / 4 : ℝ) * (∫ ω, (running f n ω) ^ 2 ∂Q) +
        (∫ ω, (f n ω) ^ 2 ∂Q) := by
    rw [← integral_const_mul, ← integral_add (hsquare'.const_mul _) hterminal']
    apply integral_mono hprod ((hsquare'.const_mul _).add hterminal')
    intro ω
    change running f n ω * f n ω ≤ (1 / 4 : ℝ) * (running f n ω) ^ 2 + (f n ω) ^ 2
    nlinarith [sq_nonneg (running f n ω - 2 * f n ω)]
  linarith
end Submartingale



section Martingale
variable {H ι : Type*} [Preorder ι]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (F : Filtration ι mΩ)
  (X : ι → Ω → H) (hX : Martingale X F Q) (h2 : ∀ t, MemLp (X t) 2 Q)
include hX h2

/-- Actual conditional Jensen gives the nonnegative norm submartingale. -/
theorem norm_submartingale : Submartingale (fun t ω => ‖X t ω‖) F Q := by
  refine ⟨fun t => (hX.stronglyAdapted t).norm, ?_, ?_⟩
  · intro s t hst
    filter_upwards [norm_condExp_le (μ := Q) (m := F s) (X t),
      hX.condExp_ae_eq hst] with ω hj he
    rw [he] at hj
    exact hj
  · intro t
    exact (hX.integrable t).norm

/-- The strong factor-four maximal second-moment bound on a genuine
monotone observation grid of an actual square-integrable martingale. -/
theorem finite_grid (τ : ℕ → ι) (hτ : Monotone τ) (n : ℕ) :
    (∫ ω, (running (fun k ω => ‖X (τ k) ω‖) n ω) ^ 2 ∂Q) ≤
      4 * ∫ ω, ‖X (τ n) ω‖ ^ 2 ∂Q := by
  exact finite_maximum_square Q (MartingaleMaximalL2.sampledFiltration (F := F) τ hτ)
    (fun k ω => ‖X (τ k) ω‖)
    (norm_submartingale Q _ (fun k => X (τ k))
      (MartingaleMaximalL2.sampled_martingale Q hX τ hτ) (fun k => h2 (τ k)))
    (fun k => (h2 (τ k)).norm) n
end Martingale

end PBGSO.DoobStrongL2
