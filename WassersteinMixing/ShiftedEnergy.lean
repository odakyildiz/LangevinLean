import WassersteinMixing.Parameters
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

set_option linter.style.header false

/-! # The shifted error and its martingale energy

The deterministic quadratic estimate is derived from symmetry and curvature
bounds. Conditional centering is used through the actual orthogonal projection
in the Hilbert space of square-integrable random variables.
-/

noncomputable section
open MeasureTheory

namespace WassersteinMixing

section Deterministic
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A positive self-adjoint contraction is firmly nonexpansive. This is proved
from its quadratic form, rather than assumed as an error estimate. -/
theorem positive_contraction_cocoercive (T : H →L[ℝ] H)
    (hsym : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y))
    (hpos : ∀ x, 0 ≤ inner ℝ x (T x))
    (hupper : ∀ x, inner ℝ x (T x) ≤ ‖x‖ ^ 2) (x : H) :
    ‖T x‖ ^ 2 ≤ inner ℝ x (T x) := by
  have hcross (u v : H) : inner ℝ v (T u) = inner ℝ u (T v) := by
    exact (real_inner_comm (T u) v).trans (hsym u v)
  have hlower (u v : H) :
      (1 / 2 : ℝ) * inner ℝ u (T u) + inner ℝ (T u) (v - u) ≤
        (1 / 2 : ℝ) * inner ℝ v (T v) := by
    have hp := hpos (v - u)
    simp only [map_sub, inner_sub_left, inner_sub_right] at hp
    rw [hcross u v] at hp
    rw [inner_sub_right, hsym, hsym]
    nlinarith
  have hmodel (u v : H) :
      (1 / 2 : ℝ) * inner ℝ v (T v) ≤
        (1 / 2 : ℝ) * inner ℝ u (T u) + inner ℝ (T u) (v - u) +
          1 / 2 * ‖v - u‖ ^ 2 := by
    have hp := hupper (v - u)
    simp only [map_sub, inner_sub_left, inner_sub_right] at hp
    rw [hcross u v] at hp
    rw [inner_sub_right, hsym, hsym]
    nlinarith
  have hc := ULA.cocoercive_of_quadratic_models
    (fun u : H ↦ (1 / 2 : ℝ) * inner ℝ u (T u)) T 1 (by norm_num)
    hlower hmodel x 0
  simpa only [map_zero, sub_zero, one_mul, hsym] using hc

/-- The paper's deterministic weighted interpolation inequality. -/
theorem weighted_interpolation (T : H →L[ℝ] H) (a b : ℝ)
    (hsym : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y))
    (hpos : ∀ x, 0 ≤ inner ℝ x (T x))
    (hupper : ∀ x, inner ℝ x (T x) ≤ ‖x‖ ^ 2)
    (hlower : ∀ x, a * ‖x‖ ^ 2 ≤ inner ℝ x (T x))
    (hbound : ∀ x, inner ℝ x (T x) ≤ b * ‖x‖ ^ 2) (u v : H) :
    ‖u - T u + T v‖ ^ 2 ≤ (1 - a) * ‖u‖ ^ 2 + b * ‖v‖ ^ 2 := by
  have hc := positive_contraction_cocoercive T hsym hpos hupper (v - u)
  have heq : u - T u + T v = u + T (v - u) := by simp; abel
  rw [heq, norm_add_sq_real]
  have hs : inner ℝ v (T u) = inner ℝ u (T v) := by
    exact (real_inner_comm (T u) v).trans (hsym u v)
  simp only [map_sub, inner_sub_left, inner_sub_right] at hc ⊢
  rw [hs] at hc
  have hlu := hlower u
  have hbv := hbound v
  nlinarith

/-- Explicit substitution of the paper's curvature and step bounds. -/
theorem curvature_weighted_interpolation (P : Parameters) (A : H →L[ℝ] H)
    (hsym : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    (hlower : ∀ x, P.alpha * ‖x‖ ^ 2 ≤ inner ℝ x (A x))
    (hupper : ∀ x, inner ℝ x (A x) ≤ P.beta * ‖x‖ ^ 2) (u v : H) :
    ‖u - P.step • A u + P.step • A v‖ ^ 2 ≤
      P.contraction * ‖u‖ ^ 2 + P.step * P.beta * ‖v‖ ^ 2 := by
  let T := P.step • A
  have hsymT (x y : H) : inner ℝ (T x) y = inner ℝ x (T y) := by
    simp only [T, smul_apply, real_inner_smul_left,
      real_inner_smul_right, hsym]
  have hlowT (x : H) : P.alpha * P.step * ‖x‖ ^ 2 ≤ inner ℝ x (T x) := by
    simpa only [T, smul_apply, real_inner_smul_right,
      mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left (hlower x) P.step_pos.le
  have hupperT (x : H) : inner ℝ x (T x) ≤ P.step * P.beta * ‖x‖ ^ 2 := by
    simpa only [T, smul_apply, real_inner_smul_right, mul_assoc] using
      mul_le_mul_of_nonneg_left (hupper x) P.step_pos.le
  exact weighted_interpolation T (P.alpha * P.step) (P.step * P.beta) hsymT
    (fun x ↦ (mul_nonneg (mul_nonneg P.alpha_pos.le P.step_pos.le)
      (sq_nonneg _)).trans (hlowT x))
    (fun x ↦ (hupperT x).trans (by nlinarith [sq_nonneg ‖x‖, P.step_beta_le]))
    hlowT hupperT u v

/-- Inserting the Poisson decomposition produces the exact shifted recursion. -/
theorem shifted_error_identity (A : H →L[ℝ] H) (h : ℝ)
    (z znext g gnext defect martingale : H)
    (hstep : znext = z - h • A z + defect)
    (hdefect : defect = g - gnext + martingale) :
    znext + gnext = (z + g) - h • A (z + g) + h • A g + martingale := by
  rw [hstep, hdefect, map_add, smul_add]
  module

/-- Centering removes the cross term in an actual Hilbert norm. -/
theorem centered_energy_identity (predictable martingale : H)
    (horthogonal : inner ℝ predictable martingale = 0) :
    ‖predictable + martingale‖ ^ 2 = ‖predictable‖ ^ 2 + ‖martingale‖ ^ 2 := by
  rw [norm_add_sq_real, horthogonal]
  ring

omit [InnerProductSpace ℝ H] in
/-- The constants in the two local estimates give exactly the source's 18. -/
theorem martingale_residual_bound (D increment : H) (c : ℝ)
    (hD : ‖D‖ ^ 2 ≤ 3 * c) (hg : ‖increment‖ ^ 2 ≤ 6 * c) :
    ‖D - increment‖ ^ 2 ≤ 18 * c := by
  have htri := norm_sub_le D increment
  have hnonneg : 0 ≤ ‖D‖ + ‖increment‖ := by positivity
  have hs := mul_self_le_mul_self (norm_nonneg (D - increment)) htri
  nlinarith [sq_nonneg (‖D‖ - ‖increment‖)]

end Deterministic

section ConditionalExpectation
variable {Ω H : Type*} [m0 : MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (Q : Measure Ω)

/-- Actual conditional expectation gives orthogonality against every adapted
square-integrable predictable term. -/
theorem conditional_centering_orthogonal {m : MeasurableSpace Ω} (hm : m ≤ m0)
    (M U : Lp H 2 Q) (hU : AEStronglyMeasurable[m] U Q)
    (hM : (condExpL2 H ℝ hm M : Lp H 2 Q) = 0) : inner ℝ U M = 0 := by
  have h := inner_condExpL2_eq_inner_fun (𝕜 := ℝ) hm M U hU
  rw [hM, inner_zero_left] at h
  rw [real_inner_comm, ← h]

/-- The one-step shifted energy is a conclusion of centering and the
deterministic estimate; no energy recurrence is part of the hypotheses. -/
theorem conditional_shifted_energy {m : MeasurableSpace Ω} (hm : m ≤ m0)
    (U M : Lp H 2 Q) (hU : AEStronglyMeasurable[m] U Q)
    (hM : (condExpL2 H ℝ hm M : Lp H 2 Q) = 0)
    (q current forcing : ℝ) (hpredictable : ‖U‖ ^ 2 ≤ q * current + forcing) :
    ‖U + M‖ ^ 2 ≤ q * current + forcing + ‖M‖ ^ 2 := by
  have ho := conditional_centering_orthogonal (m0 := m0) Q hm M U hU hM
  rw [centered_energy_identity U M ho]
  linarith

end ConditionalExpectation
end WassersteinMixing
