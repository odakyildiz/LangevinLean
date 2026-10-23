import AverageLMC.LaplacianRecurrence
import UnadjustedLangevin.LocalError

set_option linter.style.header false

/-!
# A first-order total defect suffices for the Laplacian theorem (source `th:3`)

The order `h` theorem needs cancellation only in the cross term. Its total
local-defect norm can be bounded using the existing first-order Brownian
increment argument. At `hM ≤ 1` that argument gives the coefficient `3/2`.
This avoids an additional stochastic-integral isometry construction.
-/

noncomputable section
open MeasureTheory
open scoped NNReal

namespace AverageLMC

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- The existing integral equation and noise/score moments give a `3/2`
total local defect whenever `hM ≤ 1`. -/
theorem localDefect_three_halves_bound
    (g : H → H) (Y B : ℝ → H) (M : ℝ≥0) (h d : ℝ)
    (hh : 0 ≤ h) (hd : 0 ≤ d) (hsmall : h * (M : ℝ) ≤ 1)
    (hLip : LipschitzWith M g)
    (hG : ∀ t ∈ Set.Icc 0 h, ‖g (Y t)‖ ≤ Real.sqrt ((M : ℝ) * d))
    (hB : ∀ t ∈ Set.Icc 0 h, ‖B t‖ ≤ Real.sqrt (2 * d) * Real.sqrt t)
    (heq : ∀ t ∈ Set.Icc 0 h,
      Y t - Y 0 = -(∫ s in 0..t, g (Y s)) + B t) :
    ‖ULA.localDefect g Y h‖ ≤
      (3 / 2 : ℝ) * (M : ℝ) * h * Real.sqrt h * Real.sqrt d := by
  have hroot : h * Real.sqrt ((M : ℝ) * d) ≤ Real.sqrt h * Real.sqrt d := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg M.coe_nonneg hd),
      Real.sq_sqrt hh, Real.sq_sqrt hd]
    have hb := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hh hd)
    nlinarith
  have htwo : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 3 / 2)).mp
    norm_num
  have hnum : (1 / 2 : ℝ) + (2 / 3 : ℝ) * Real.sqrt 2 ≤ 3 / 2 := by linarith
  have hb := ULA.localDefect_bound g Y B M h
    (Real.sqrt ((M : ℝ) * d)) (Real.sqrt (2 * d)) hh hLip hG hB heq
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) d] at hb
  have hscale := mul_le_mul_of_nonneg_left hroot
    (by positivity : 0 ≤ (M : ℝ) * h / 2)
  have hscale2 := mul_le_mul_of_nonneg_right hnum
    (by positivity : 0 ≤ (M : ℝ) * h * Real.sqrt h * Real.sqrt d)
  nlinarith

/-- The same exact final coefficient of the Laplacian theorem (source `th:3`) follows from the coarser
first-order total-defect norm. The improved score moment is needed only in
the drift/cross coefficient `M*A+δ`. -/
theorem laplacian_recurrence_bound_of_global_defect
    (e : ℕ → ℝ) (m M h A δ S : ℝ)
    (he : ∀ k, 0 ≤ e k) (hm : 0 < m) (hmM : m ≤ M)
    (hh : 0 ≤ h) (hhM : h * M ≤ 1)
    (hA : 0 ≤ A) (hmA : m ≤ A ^ 2) (hδ : 0 ≤ δ) (hS : 0 ≤ S)
    (hstep : ∀ k, (e (k + 1)) ^ 2 ≤
      (1 - m * h) ^ 2 * (e k) ^ 2 +
        (1 - m * h) * h ^ 2 * (M * A + δ) * S * e k +
          ((3 / 2 : ℝ) * M * h * Real.sqrt h * S) ^ 2) (n : ℕ) :
    e n ≤ (1 - m * h) ^ n * e 0 + (2 * M * A + δ) * h * S / m := by
  have hM : 0 ≤ M := (hm.trans_le hmM).le
  have hmh : m * h ≤ 1 := by nlinarith [mul_nonneg hh (sub_nonneg.mpr hmM)]
  let q := 1 - m * h
  let C := h ^ 2 / 2 * (M * A + δ) * S
  let B := (3 / 2 : ℝ) * M * h * Real.sqrt h * S
  let a := h * (M * A + δ) * S / (2 * m)
  let b := 3 * h * M * A * S / (2 * m)
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hq1 : q ≤ 1 := by dsimp [q]; nlinarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hCa : C ≤ (1 - q) * a := by
    dsimp [C, q, a]
    field_simp
    ring_nf
    exact le_rfl
  have hBb0 : B ^ 2 ≤ (m * h) * b ^ 2 := by
    have hs := mul_le_mul_of_nonneg_left hmA
      (by positivity : 0 ≤ 9 * h ^ 3 * M ^ 2 * S ^ 2)
    have hBsq : B ^ 2 = 9 * h ^ 3 * M ^ 2 * S ^ 2 / 4 := by
      dsimp [B]
      rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hh]
      ring
    have hbsq : (m * h) * b ^ 2 = 9 * h ^ 3 * M ^ 2 * S ^ 2 * A ^ 2 / (4 * m) := by
      dsimp [b]
      field_simp
      ring
    rw [hBsq, hbsq]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * m)).mpr
    nlinarith
  have hBb : B ^ 2 ≤ (1 - q ^ 2) * b ^ 2 := by
    apply hBb0.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg b)
    dsimp [q]
    nlinarith [mul_nonneg (mul_nonneg hm.le hh) (sub_nonneg.mpr hmh)]
  have hs (k : ℕ) : (e (k + 1)) ^ 2 ≤
      q ^ 2 * (e k) ^ 2 + 2 * q * C * e k + B ^ 2 := by
    convert hstep k using 1 <;> dsimp [q, C, B] <;> ring
  have hbound := quadratic_recurrence_split_floor e q C B a b he hq hq1
    hC ha hb hCa hBb hs n
  have hab : a + b ≤ (2 * M * A + δ) * h * S / m := by
    calc
      a + b = h * (4 * M * A + δ) * S / (2 * m) := by dsimp [a, b]; ring
      _ ≤ h * (4 * M * A + 2 * δ) * S / (2 * m) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [mul_nonneg (mul_nonneg hh hδ) hS]
      _ = _ := by ring
  rw [add_assoc] at hbound
  simpa only [q] using hbound.trans (add_le_add le_rfl hab)

end AverageLMC
