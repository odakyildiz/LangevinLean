import PBGSO.DyadicInterpolation

/-! # Past-only grid samples and their actual polygon comparison
The left sample time never exceeds the observation time. Its deterministic
mesh error and polygon distance justify retaining the original filtration
when constructing continuous Brownian modifications.
-/
noncomputable section
open Set Filter
open scoped Topology
namespace PBGSO.DyadicInterpolation
variable {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]

def leftIndex (N : ℕ) (t : ℝ) : ℕ := ⌊(N : ℝ) * t⌋₊
def leftTime (N : ℕ) (t : ℝ) : ℝ := (leftIndex N t : ℝ) / N

theorem leftTime_nonneg (N : ℕ) (t : ℝ) : 0 ≤ leftTime N t := by
  unfold leftTime
  positivity

theorem leftTime_le (N : ℕ) (hN : 0 < N) (t : ℝ) (ht : 0 ≤ t) :
    leftTime N t ≤ t := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [leftTime, div_le_iff₀ hNr]
  simpa only [leftIndex, mul_comm] using Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) ht)

theorem leftTime_gap (N : ℕ) (hN : 0 < N) (t : ℝ) :
    t - leftTime N t ≤ (N : ℝ)⁻¹ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hf := (Nat.lt_floor_add_one ((N : ℝ) * t)).le
  apply (mul_le_mul_iff_of_pos_right hNr).mp
  dsimp [leftTime, leftIndex]
  field_simp
  rw [mul_comm (N : ℝ) t] at hf
  nlinarith

/-- The past sample index lies in the actual finite interpolation grid. -/
theorem leftIndex_le (N : ℕ) (t : ℝ) (ht : t ∈ Icc 0 1) : leftIndex N t ≤ N := by
  have hm : (N : ℝ) * t ≤ N := mul_le_of_le_one_right (Nat.cast_nonneg N) ht.2
  have hf := Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) ht.1)
  exact_mod_cast hf.trans hm

/-- On the whole unit interval, including its right endpoint, the actual
polygon is within one adjacent-increment bound of the past-only sample. -/
theorem polygon_past_bound (N : ℕ) (hN : 0 < N) (f : ℕ → R) (t : ℝ)
    (ht : t ∈ Icc 0 1) (a : ℝ) (ha : 0 ≤ a)
    (hstep : ∀ j < N, ‖f (j + 1) - f j‖ ≤ a) :
    ‖polygon N f t - f (leftIndex N t)‖ ≤ a := by
  have hf := Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) ht.1)
  have hf' := (Nat.lt_floor_add_one ((N : ℝ) * t)).le
  change (leftIndex N t : ℝ) ≤ (N : ℝ) * t at hf
  change (N : ℝ) * t ≤ (leftIndex N t : ℝ) + 1 at hf'
  by_cases hk : leftIndex N t < N
  · exact polygon_left_bound N _ hk f t hf hf' a ha (hstep _ hk)
  · have he : leftIndex N t = N := by have := leftIndex_le N t ht; omega
    have hx : (N : ℝ) * t = N := by
      rw [he] at hf
      exact le_antisymm (mul_le_of_le_one_right (Nat.cast_nonneg N) ht.2) hf
    have hlast : ((N - 1 : ℕ) : ℝ) + 1 = N := by exact_mod_cast Nat.sub_add_cancel hN
    have hp := polygon_cell N (N - 1) (by omega) f t (by rw [hx]; linarith) (by rw [hx]; linarith)
    rw [hp, hx, hlast, sub_self, zero_smul, zero_add, he]
    have hone : (N : ℝ) - ((N - 1 : ℕ) : ℝ) = 1 := by linarith
    rw [hone, one_smul, Nat.sub_add_cancel hN, sub_self, norm_zero]
    exact ha

/-- Actual past dyadic sample times converge to every nonnegative observation time. -/
theorem leftTime_dyadic_tendsto (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n => leftTime (2 ^ n) t) atTop (𝓝 t) := by
  have hinv : Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hg : Tendsto (fun n => t - leftTime (2 ^ n) t) atTop (𝓝 0) :=
    squeeze_zero (fun n => sub_nonneg.mpr (leftTime_le _ (by positivity) t ht))
      (fun n => by simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        leftTime_gap (2 ^ n) (by positivity) t) hinv
  have he : (fun n => leftTime (2 ^ n) t) = fun n => t - (t - leftTime (2 ^ n) t) := by
    funext n
    ring
  rw [he]
  simpa only [sub_zero] using tendsto_const_nhds.sub hg

end PBGSO.DyadicInterpolation
