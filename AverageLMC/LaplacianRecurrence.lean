import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option linter.style.header false

/-!
# The quadratic error recurrence in the Laplacian theorem (source `th:3`)

The arguments here are scalar. They are used after obtaining the stochastic
one-step estimate; no statement in this file asserts that an LMC law satisfies
that estimate.
-/

namespace AverageLMC

/-- A quadratic recurrence with a certified invariant floor. The linear term
is retained, instead of applying the triangle inequality to the martingale
part and losing the order `h` final error. -/
theorem quadratic_recurrence_floor
    (e : ℕ → ℝ) (q C B F : ℝ)
    (he : ∀ k, 0 ≤ e k) (hq : 0 ≤ q) (_hq1 : q ≤ 1)
    (hC : 0 ≤ C) (hF : 0 ≤ F)
    (hCF : C ≤ (1 - q) * F)
    (hfloor : 2 * q * C * F + B ^ 2 ≤ (1 - q ^ 2) * F ^ 2)
    (hstep : ∀ k, (e (k + 1)) ^ 2 ≤
      q ^ 2 * (e k) ^ 2 + 2 * q * C * e k + B ^ 2) (n : ℕ) :
    e n ≤ q ^ n * e 0 + F := by
  induction n with
  | zero => simpa using hF
  | succ n ih =>
    let t := q ^ n * e 0
    have ht : 0 ≤ t := mul_nonneg (pow_nonneg hq n) (he 0)
    have hsq := (sq_le_sq₀ (he n) (add_nonneg ht hF)).mpr ih
    have hmono := add_le_add
      (mul_le_mul_of_nonneg_left hsq (sq_nonneg q))
      (mul_le_mul_of_nonneg_left ih (by positivity : 0 ≤ 2 * q * C))
    have hcoeff : 0 ≤ 2 * q * t * ((1 - q) * F - C) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hCF)
    have hnext : (e (n + 1)) ^ 2 ≤ (q * t + F) ^ 2 := by
      nlinarith [hstep n]
    have hbound := (sq_le_sq₀ (he (n + 1)) (by positivity : 0 ≤ q * t + F)).mp hnext
    simpa only [t, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hbound

/-- A drift floor and a martingale floor separately certify the quadratic
recurrence. This is the recurrence lemma used in the paper's proof. -/
theorem quadratic_recurrence_split_floor
    (e : ℕ → ℝ) (q C B a b : ℝ)
    (he : ∀ k, 0 ≤ e k) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hCa : C ≤ (1 - q) * a)
    (hBb : B ^ 2 ≤ (1 - q ^ 2) * b ^ 2)
    (hstep : ∀ k, (e (k + 1)) ^ 2 ≤
      q ^ 2 * (e k) ^ 2 + 2 * q * C * e k + B ^ 2) (n : ℕ) :
    e n ≤ q ^ n * e 0 + a + b := by
  have hq0 : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  have hCF : C ≤ (1 - q) * (a + b) := by
    nlinarith [mul_nonneg hq0 hb]
  have hcross := mul_le_mul_of_nonneg_left hCa
    (by positivity : 0 ≤ 2 * q * (a + b))
  have hrest : 0 ≤ (1 - q) ^ 2 * a ^ 2 + 2 * (1 - q) * a * b := by
    positivity
  have hfloor : 2 * q * C * (a + b) + B ^ 2 ≤
      (1 - q ^ 2) * (a + b) ^ 2 := by
    nlinarith
  simpa only [add_assoc] using quadratic_recurrence_floor e q C B (a + b)
    he hq hq1 hC (add_nonneg ha hb) hCF hfloor hstep n

/-- The numerical step in the Laplacian theorem (source `th:3`). `A` is `sqrt M_av` and `S` is
`sqrt p`. The coefficients are the exact drift and total-defect bounds in
the paper's proof, with `h^(3/2)` written `h * sqrt h`. -/
theorem laplacian_quadratic_recurrence_bound
    (e : ℕ → ℝ) (m M h A δ S : ℝ)
    (he : ∀ k, 0 ≤ e k) (hm : 0 < m) (hmM : m ≤ M)
    (hh : 0 ≤ h) (hhM : h * M ≤ 1)
    (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hS : 0 ≤ S)
    (hstep : ∀ k, (e (k + 1)) ^ 2 ≤
      (1 - m * h) ^ 2 * (e k) ^ 2 +
        (1 - m * h) * h ^ 2 * (M * A + δ) * S * e k +
          (h ^ 2 / 2 * δ * S +
            (3 / 2 : ℝ) * h * Real.sqrt h * Real.sqrt M * A * S) ^ 2) (n : ℕ) :
    e n ≤ (1 - m * h) ^ n * e 0 + (2 * M * A + δ) * h * S / m := by
  have hM : 0 ≤ M := (hm.trans_le hmM).le
  have hmh : m * h ≤ 1 := by nlinarith [mul_nonneg hh (sub_nonneg.mpr hmM)]
  let q := 1 - m * h
  let C := h ^ 2 / 2 * (M * A + δ) * S
  let B := h ^ 2 / 2 * δ * S +
    (3 / 2 : ℝ) * h * Real.sqrt h * Real.sqrt M * A * S
  let a := h * (M * A + δ) * S / (2 * m)
  let b := h * (3 * M * A + δ) * S / (2 * m)
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hq1 : q ≤ 1 := by dsimp [q]; nlinarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hCa : C ≤ (1 - q) * a := by
    dsimp [C, q, a]
    have hm0 : m ≠ 0 := ne_of_gt hm
    field_simp
    ring_nf
    exact le_rfl
  have hroot1 : Real.sqrt h * Real.sqrt m ≤ 1 := by
    apply (sq_le_sq₀ (by positivity) (by norm_num : (0 : ℝ) ≤ 1)).mp
    rw [mul_pow, Real.sq_sqrt hh, Real.sq_sqrt hm.le]
    simpa [mul_comm] using hmh
  have hroot2 : Real.sqrt M * Real.sqrt m ≤ M := by
    apply (sq_le_sq₀ (by positivity) hM).mp
    rw [mul_pow, Real.sq_sqrt hM, Real.sq_sqrt hm.le]
    simpa only [pow_two] using mul_le_mul_of_nonneg_left hmM hM
  have hcoeff : Real.sqrt h * Real.sqrt m * δ +
      3 * (Real.sqrt M * Real.sqrt m) * A ≤ δ + 3 * M * A := by
    nlinarith [mul_le_mul_of_nonneg_right hroot1 hδ,
      mul_le_mul_of_nonneg_right hroot2 hA]
  have hBs : B * Real.sqrt m ≤
      h * Real.sqrt h * (3 * M * A + δ) * S / 2 := by
    have hmultiply := mul_le_mul_of_nonneg_left hcoeff
      (by positivity : 0 ≤ h * Real.sqrt h * S / 2)
    convert hmultiply using 1 <;> (try simp only [B]) <;> ring_nf <;>
      simp only [Real.sq_sqrt hh] <;> ring
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hsquare := (sq_le_sq₀ (mul_nonneg hB0 (Real.sqrt_nonneg _))
    (by positivity : 0 ≤ h * Real.sqrt h * (3 * M * A + δ) * S / 2)).mpr hBs
  have hBb0 : B ^ 2 ≤ (m * h) * b ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hm.le] at hsquare
    have hidentity :
        (h * Real.sqrt h * (3 * M * A + δ) * S / 2) ^ 2 =
          m * ((m * h) * b ^ 2) := by
      dsimp [b]
      rw [div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hh]
      field_simp
    rw [hidentity] at hsquare
    exact (mul_le_mul_iff_right₀ hm).mp (by simpa [mul_comm] using hsquare)
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
  have hab : a + b = (2 * M * A + δ) * h * S / m := by
    dsimp [a, b]
    ring
  rw [add_assoc, hab] at hbound
  simpa only [q] using hbound

end AverageLMC
