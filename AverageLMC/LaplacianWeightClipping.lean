import AverageLMC.LaplacianWeightedTest
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option linter.style.header false

/-!
# Bounded initial weights approximate arbitrary `L²` weights

Radial clipping keeps the norm below that of the original vector and makes
every scalar coordinate bounded. Dominated convergence then transfers
weighted Dynkin identities to the actual initial coupling error, which need
only have a finite second moment.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace AverageLMC

section Generic

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Radial clipping to the ball of radius `n+1`. The harmless value of the
real quotient at zero gives the correct clipped vector there as well. -/
def clipWeight (n : ℕ) (x : H) : H :=
  min 1 (((n : ℝ) + 1) / ‖x‖) • x

theorem norm_clipWeight_le (n : ℕ) (x : H) : ‖clipWeight n x‖ ≤ ‖x‖ := by
  have hc : 0 ≤ min 1 (((n : ℝ) + 1) / ‖x‖) := le_min (by norm_num) (by positivity)
  rw [clipWeight, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (min_le_left 1 (((n : ℝ) + 1) / ‖x‖)) (norm_nonneg x)

theorem norm_clipWeight_le_radius (n : ℕ) (x : H) : ‖clipWeight n x‖ ≤ (n : ℝ) + 1 := by
  by_cases hx : x = 0
  · simp only [hx, clipWeight, smul_zero, norm_zero]
    positivity
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hc : 0 ≤ min 1 (((n : ℝ) + 1) / ‖x‖) := le_min (by norm_num) (by positivity)
  rw [clipWeight, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  calc
    _ ≤ (((n : ℝ) + 1) / ‖x‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hn.le
    _ = _ := div_mul_cancel₀ _ hn.ne'

theorem clipWeight_eq_of_norm_le (n : ℕ) (x : H) (hx : ‖x‖ ≤ (n : ℝ) + 1) :
    clipWeight n x = x := by
  by_cases hx0 : x = 0
  · simp only [hx0, clipWeight, smul_zero]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hc : 1 ≤ ((n : ℝ) + 1) / ‖x‖ := (le_div_iff₀ hn).mpr (by simpa using hx)
  simp only [clipWeight, min_eq_left hc, one_smul]

theorem clipWeight_eventually_eq (x : H) : ∀ᶠ n : ℕ in atTop, clipWeight n x = x := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
  filter_upwards [eventually_ge_atTop N] with n hn
  apply clipWeight_eq_of_norm_le
  have hcast : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
  linarith

theorem measurable_clipWeight [MeasurableSpace H] [BorelSpace H] (n : ℕ) :
    Measurable (@clipWeight H _ _ n) := by
  unfold clipWeight
  fun_prop

end Generic

section Lp

variable {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  (P : Measure Ω) [IsProbabilityMeasure P]

theorem clippedWeight_memLp (X : Lp H 2 P) (n : ℕ) :
    MemLp (fun a ↦ clipWeight n (X a)) 2 P := by
  exact (Lp.memLp X).of_le
    (((measurable_clipWeight n).comp (Lp.stronglyMeasurable X).measurable).aestronglyMeasurable)
    (ae_of_all _ (fun a ↦ norm_clipWeight_le n (X a)))

def lpClippedWeight (X : Lp H 2 P) (n : ℕ) : Lp H 2 P :=
  (clippedWeight_memLp P X n).toLp (fun a ↦ clipWeight n (X a))

theorem lpClippedWeight_coe (X : Lp H 2 P) (n : ℕ) :
    lpClippedWeight P X n =ᵐ[P] fun a ↦ clipWeight n (X a) :=
  (clippedWeight_memLp P X n).coeFn_toLp

theorem lpClippedWeight_norm_le (X : Lp H 2 P) (n : ℕ) : ‖lpClippedWeight P X n‖ ≤ ‖X‖ := by
  have hbound : ‖lpClippedWeight P X n‖ ≤ (1 : ℝ) * ‖X‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [lpClippedWeight_coe P X n] with a ha
    rw [ha, one_mul]
    exact norm_clipWeight_le n (X a)
  simpa only [one_mul] using hbound

/-- The clipped vector weights converge against every fixed `L²` vector.
This is the precise dense-weight bridge needed for the initial error. -/
theorem lpClippedWeight_inner_tendsto (X D : Lp H 2 P) :
    Tendsto (fun n ↦ inner ℝ (lpClippedWeight P X n) D) atTop (𝓝 (inner ℝ X D)) := by
  have hbound : Integrable (fun a ↦ ‖X a‖ * ‖D a‖) P :=
    (show MemLp (fun a ↦ ‖X a‖ * ‖D a‖) 1 P from
      (Lp.memLp X).norm.mul (Lp.memLp D).norm).integrable le_rfl
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun a ↦ inner ℝ (clipWeight n (X a)) (D a)) P := by
    exact (((measurable_clipWeight n).comp
      (Lp.stronglyMeasurable X).measurable).aestronglyMeasurable).inner
        (Lp.aestronglyMeasurable D)
  have hdom (n : ℕ) : ∀ᵐ a ∂P,
      ‖inner ℝ (clipWeight n (X a)) (D a)‖ ≤ ‖X a‖ * ‖D a‖ := by
    exact ae_of_all _ (fun a ↦ (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
      (mul_le_mul_of_nonneg_right (norm_clipWeight_le n (X a)) (norm_nonneg _)))
  have hpoint : ∀ᵐ a ∂P, Tendsto (fun n ↦ inner ℝ (clipWeight n (X a)) (D a))
      atTop (𝓝 (inner ℝ (X a) (D a))) := by
    exact ae_of_all _ (fun a ↦ tendsto_const_nhds.congr'
      ((clipWeight_eventually_eq (X a)).mono (fun n hn ↦ by
        change inner ℝ (X a) (D a) = inner ℝ (clipWeight n (X a)) (D a)
        rw [hn])))
  have hd := tendsto_integral_of_dominated_convergence _ hmeas hbound hdom hpoint
  have hi (n : ℕ) : inner ℝ (lpClippedWeight P X n) D =
      ∫ a, inner ℝ (clipWeight n (X a)) (D a) ∂P := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [lpClippedWeight_coe P X n] with a ha
    rw [ha]
  simp_rw [hi]
  simpa only [L2.inner_def] using hd

end Lp
end AverageLMC
