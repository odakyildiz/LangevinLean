import UnadjustedLangevin.Recurrence
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Accumulating the first-order kinetic coupling error

This file proves the numerical part of the KLMC convergence proof, starting
with the explicit contraction-plus-local-defect inequality.  It does not
assert the missing stochastic identification with the Gibbs law.  In
particular, the coupling inequality and the reference velocity moment are
visible inputs, rather than fields of a purported convergence theorem.
-/

noncomputable section

namespace KineticLangevin

/-- The one-sided second-order exponential estimate used in the paper. -/
theorem exp_neg_le_quadratic (x : ℝ) (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  let F : ℝ → ℝ := fun t ↦ 1 - t + t ^ 2 / 2 - Real.exp (-t)
  have hd (t : ℝ) : HasDerivAt F (-1 + t + Real.exp (-t)) t := by
    convert (((hasDerivAt_id t).const_sub 1).add
      (((hasDerivAt_id t).pow 2).div_const 2)).sub ((hasDerivAt_id t).neg.exp) using 1 <;>
      first | (funext s; rfl) | (simp only [id_eq, Pi.neg_apply]; ring)
  have hm : Monotone F := monotone_of_deriv_nonneg
    (fun t ↦ (hd t).differentiableAt) (fun t ↦ by
      rw [(hd t).deriv]
      have hb := Real.add_one_le_exp (-t)
      linarith)
  have hb := hm hx
  dsimp [F] at hb
  simp only [sub_zero, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero,
    neg_zero, Real.exp_zero, sub_self] at hb
  linarith

/-- The contraction plus `3Mh²/4` local correction is at most
`1-3rh/4`, provided `2r²≤M` and `4Mh≤r`. -/
theorem firstOrder_coefficient_bound (r M h : ℝ) (hr : 0 ≤ r) (hM : 0 ≤ M)
    (hh : 0 ≤ h) (hcurvature : 2 * r ^ 2 ≤ M) (hstep : 4 * M * h ≤ r) :
    Real.exp (-r * h) + (3 / 4 : ℝ) * M * h ^ 2 ≤ 1 - (3 / 4 : ℝ) * r * h := by
  have he := exp_neg_le_quadratic (r * h) (mul_nonneg hr hh)
  rw [← neg_mul] at he
  have hc := mul_le_mul_of_nonneg_right hcurvature (sq_nonneg h)
  have hs := mul_le_mul_of_nonneg_right hstep hh
  nlinarith

/-- The original kinetic parameter restrictions imply the two scalar
conditions required in the preceding coefficient estimate. -/
theorem kinetic_scalar_conditions (m M γ h : ℝ) (hm : 0 < m) (hmM : m ≤ M)
    (hγ : 0 < γ) (hfriction : m + M ≤ γ ^ 2) (hh : 0 ≤ h)
    (hstep : 4 * γ * M * h ≤ m) :
    2 * (m / γ) ^ 2 ≤ M ∧ 4 * M * h ≤ m / γ := by
  have hM : 0 ≤ M := hm.le.trans hmM
  have hmult := mul_le_mul_of_nonneg_left hfriction hM
  have hfactor : 0 ≤ (M - m) * (M + 2 * m) := by positivity
  constructor
  · rw [div_pow]
    have hdiv : 2 * m ^ 2 / γ ^ 2 ≤ M := by
      apply (div_le_iff₀ (sq_pos_of_pos hγ)).mpr
      nlinarith
    convert hdiv using 1 <;> ring
  · exact (le_div_iff₀ hγ).mpr (by nlinarith)

/-- Explicitly iterating the proved local coupling inequality gives a linear
step-size bias. This is the numerical implication used in Theorem 2; the
stochastic coupling inequality itself is still an explicit hypothesis. -/
theorem firstOrder_coupling_recurrence_bound (e : ℕ → ℝ) (r M h C : ℝ)
    (hr : 0 < r) (hM : 0 ≤ M) (hh : 0 < h) (hC : 0 ≤ C)
    (hcurvature : 2 * r ^ 2 ≤ M) (hstep : 4 * M * h ≤ r)
    (hnonneg : ∀ n, 0 ≤ e n)
    (hlocal : ∀ n, e (n + 1) ≤ Real.exp (-r * h) * e n +
      (3 / 4 : ℝ) * M * h ^ 2 * (C + e n)) (n : ℕ) :
    e n ≤ (1 - (3 / 4 : ℝ) * r * h) ^ n * e 0 + M * h * C / r := by
  let q := 1 - (3 / 4 : ℝ) * r * h
  have hcoeff := firstOrder_coefficient_bound r M h hr.le hM hh.le hcurvature hstep
  have hq : 0 ≤ q := by
    have hexp := Real.exp_pos (-r * h)
    have hlocalnonneg : 0 ≤ (3 / 4 : ℝ) * M * h ^ 2 := by positivity
    dsimp [q]
    linarith
  have hq1 : q < 1 := by dsimp [q]; nlinarith [mul_pos hr hh]
  have hrec : ∀ n, e (n + 1) ≤ q * e n + (3 / 4 : ℝ) * M * h ^ 2 * C := by
    intro n
    have hc := mul_le_mul_of_nonneg_right hcoeff (hnonneg n)
    dsimp [q]
    nlinarith [hlocal n]
  have hr := ULA.affine_recurrence_bound e q ((3 / 4 : ℝ) * M * h ^ 2 * C)
    hq hq1 (by positivity) hrec n
  have hfloor : ((3 / 4 : ℝ) * M * h ^ 2 * C) / (1 - q) = M * h * C / r := by
    dsimp [q]
    field_simp
    ring
  rw [hfloor] at hr
  exact hr

/-- The same numerical conclusion with the original parameters of the paper.
The local contraction-defect inequality is explicitly conditional; no law
of an SDE or of a KLMC iterate is postulated or identified here. -/
theorem kinetic_firstOrder_coupling_bound (e : ℕ → ℝ) (m M γ h C : ℝ)
    (hm : 0 < m) (hmM : m ≤ M) (hγ : 0 < γ)
    (hfriction : m + M ≤ γ ^ 2) (hh : 0 < h) (hC : 0 ≤ C)
    (hstep : 4 * γ * M * h ≤ m) (hnonneg : ∀ n, 0 ≤ e n)
    (hlocal : ∀ n, e (n + 1) ≤ Real.exp (-(m / γ) * h) * e n +
      (3 / 4 : ℝ) * M * h ^ 2 * (C + e n)) (n : ℕ) :
    e n ≤ (1 - 3 * m * h / (4 * γ)) ^ n * e 0 + γ * M * h * C / m := by
  obtain ⟨hc, hs⟩ := kinetic_scalar_conditions m M γ h hm hmM hγ hfriction hh.le hstep
  have he := firstOrder_coupling_recurrence_bound e (m / γ) M h C
    (div_pos hm hγ) (hm.le.trans hmM) hh hC hc hs hnonneg hlocal n
  have hcoeff : 1 - (3 / 4 : ℝ) * (m / γ) * h = 1 - 3 * m * h / (4 * γ) := by ring
  have hfloor : M * h * C / (m / γ) = γ * M * h * C / m := by field_simp
  simpa only [hcoeff, hfloor] using he

/-- Position projection and equal initial velocities produce exactly the
first-order bias `Mh√2 C/m` from the explicit coupling recurrence. `C=√p`
is the reference velocity moment in the paper.  This is not an assertion of
Gibbs stationarity or of a Wasserstein law endpoint. -/
theorem kinetic_firstOrder_projected_bound (e d : ℕ → ℝ) (m M γ h C : ℝ)
    (hm : 0 < m) (hmM : m ≤ M) (hγ : 0 < γ)
    (hfriction : m + M ≤ γ ^ 2) (hh : 0 < h) (hC : 0 ≤ C)
    (hstep : 4 * γ * M * h ≤ m) (hnonneg : ∀ n, 0 ≤ e n)
    (hlocal : ∀ n, e (n + 1) ≤ Real.exp (-(m / γ) * h) * e n +
      (3 / 4 : ℝ) * M * h ^ 2 * (C + e n))
    (hproject : ∀ n, d n ≤ Real.sqrt 2 / γ * e n)
    (hinitial : e 0 ≤ γ * d 0) (n : ℕ) :
    d n ≤ Real.sqrt 2 * (1 - 3 * m * h / (4 * γ)) ^ n * d 0 +
      M * h * Real.sqrt 2 * C / m := by
  have he := kinetic_firstOrder_coupling_bound e m M γ h C hm hmM hγ
    hfriction hh hC hstep hnonneg hlocal n
  have hfactor : 0 ≤ Real.sqrt 2 / γ := by positivity
  have hp := mul_le_mul_of_nonneg_left he hfactor
  have hc := firstOrder_coefficient_bound (m / γ) M h
    (div_nonneg hm.le hγ.le) (hm.le.trans hmM) hh.le
    (kinetic_scalar_conditions m M γ h hm hmM hγ hfriction hh.le hstep).1
    (kinetic_scalar_conditions m M γ h hm hmM hγ hfriction hh.le hstep).2
  have hq : 0 ≤ 1 - 3 * m * h / (4 * γ) := by
    have hlocalnonneg : 0 ≤ (3 / 4 : ℝ) * M * h ^ 2 := by
      have hM := hm.le.trans hmM
      positivity
    have hexp := Real.exp_pos (-(m / γ) * h)
    have hid : (3 / 4 : ℝ) * (m / γ) * h = 3 * m * h / (4 * γ) := by ring
    rw [hid] at hc
    linarith
  have hi := mul_le_mul_of_nonneg_left hinitial
    (mul_nonneg hfactor (pow_nonneg hq n))
  have hfirst : Real.sqrt 2 / γ * (1 - 3 * m * h / (4 * γ)) ^ n * (γ * d 0) =
      Real.sqrt 2 * (1 - 3 * m * h / (4 * γ)) ^ n * d 0 := by
    field_simp
  have hfloor : Real.sqrt 2 / γ * (γ * M * h * C / m) =
      M * h * Real.sqrt 2 * C / m := by field_simp
  calc
    d n ≤ Real.sqrt 2 / γ * e n := hproject n
    _ ≤ Real.sqrt 2 / γ * ((1 - 3 * m * h / (4 * γ)) ^ n * e 0 +
        γ * M * h * C / m) := hp
    _ ≤ Real.sqrt 2 / γ * (1 - 3 * m * h / (4 * γ)) ^ n * (γ * d 0) +
        Real.sqrt 2 / γ * (γ * M * h * C / m) := by nlinarith
    _ = _ := by rw [hfirst, hfloor]

end KineticLangevin
