import KineticLangevin.Geometry
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # The genuine first-order kinetic local defect

The velocity defect is the exponentially weighted integral of the gradient
change along the exact position path.  Its position counterpart is its time
integral.  A bounded velocity yields the `h²/2` and `h³/6` bounds appearing in
the proof of Theorem 2.  The ambient Banach space can be an L² space, in which
case the assumptions are bounds on velocity moments. Stationarity supplying
those moments remains a separate probabilistic statement.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal

namespace KineticLangevin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact force-freezing error in velocity, coupled with the same noise. -/
def velocityDefect (g : E → E) (x : ℝ → E) (γ t : ℝ) : E :=
  ∫ s in 0..t, Real.exp (-γ * (t - s)) • (g (x s) - g (x 0))

/-- The position error obtained by integrating the velocity defect. -/
def positionDefect (g : E → E) (x : ℝ → E) (γ t : ℝ) : E :=
  ∫ s in 0..t, velocityDefect g x γ s

/-- Position increments are of order `t`, because position is the time
integral of velocity; this is the extra regularity that improves on ULA. -/
theorem kinematic_increment_bound (x v : ℝ → E) (T C : ℝ)
    (hbound : ∀ s ∈ Icc 0 T, ‖v s‖ ≤ C)
    (hkin : ∀ s ∈ Icc 0 T, x s - x 0 = ∫ r in 0..s, v r)
    {t : ℝ} (ht : t ∈ Icc 0 T) : ‖x t - x 0‖ ≤ C * t := by
  rw [hkin t ht]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := t) (C := C) (f := v) (fun s hs ↦ ?_)
  · simpa [abs_of_nonneg ht.1] using hb
  · rw [uIoc_of_le ht.1] at hs
    exact hbound s ⟨hs.1.le, hs.2.trans ht.2⟩

/-- The actual exponentially weighted force defect has the sharp elementary
bound `M C t²/2`. No error bound is built into its definition. -/
theorem velocityDefect_bound (g : E → E) (M : ℝ≥0) (hg : LipschitzWith M g)
    (x v : ℝ → E) (γ T C : ℝ) (hγ : 0 ≤ γ) (hC : 0 ≤ C)
    (hbound : ∀ s ∈ Icc 0 T, ‖v s‖ ≤ C)
    (hkin : ∀ s ∈ Icc 0 T, x s - x 0 = ∫ r in 0..s, v r)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖velocityDefect g x γ t‖ ≤ (M : ℝ) * C * t ^ 2 / 2 := by
  have hb (s : ℝ) (hs : s ∈ Ioc 0 t) :
      ‖Real.exp (-γ * (t - s)) • (g (x s) - g (x 0))‖ ≤ (M : ℝ) * C * s := by
    have hkernel : Real.exp (-γ * (t - s)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith [mul_nonneg hγ (sub_nonneg.mpr hs.2)]
    have hi := kinematic_increment_bound x v T C hbound hkin
      (t := s) ⟨hs.1.le, hs.2.trans ht.2⟩
    have hforce := (hg.norm_sub_le (x s) (x 0)).trans
      (mul_le_mul_of_nonneg_left hi M.coe_nonneg)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hk := mul_le_mul_of_nonneg_right hkernel (norm_nonneg (g (x s) - g (x 0)))
    nlinarith
  have hint : IntervalIntegrable (fun s : ℝ ↦ (M : ℝ) * C * s) volume 0 t :=
    (by fun_prop : Continuous (fun s : ℝ ↦ (M : ℝ) * C * s)).intervalIntegrable _ _
  unfold velocityDefect
  calc
    _ ≤ ∫ s in 0..t, (M : ℝ) * C * s :=
      intervalIntegral.norm_integral_le_of_norm_le ht.1 (Filter.Eventually.of_forall hb) hint
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_id]
      ring

/-- Integrating the preceding velocity defect gives `M C t³/6`, including
the correct cubic time inside the integral. -/
theorem positionDefect_bound (g : E → E) (M : ℝ≥0) (hg : LipschitzWith M g)
    (x v : ℝ → E) (γ T C : ℝ) (hγ : 0 ≤ γ) (hC : 0 ≤ C)
    (hbound : ∀ s ∈ Icc 0 T, ‖v s‖ ≤ C)
    (hkin : ∀ s ∈ Icc 0 T, x s - x 0 = ∫ r in 0..s, v r)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖positionDefect g x γ t‖ ≤ (M : ℝ) * C * t ^ 3 / 6 := by
  have hb (s : ℝ) (hs : s ∈ Ioc 0 t) :
      ‖velocityDefect g x γ s‖ ≤ (M : ℝ) * C / 2 * s ^ 2 := by
    have hd := velocityDefect_bound g M hg x v γ T C hγ hC hbound hkin
      (t := s) ⟨hs.1.le, hs.2.trans ht.2⟩
    convert hd using 1 <;> ring
  have hint : IntervalIntegrable (fun s : ℝ ↦ (M : ℝ) * C / 2 * s ^ 2) volume 0 t :=
    (by fun_prop : Continuous (fun s : ℝ ↦ (M : ℝ) * C / 2 * s ^ 2)).intervalIntegrable _ _
  unfold positionDefect
  calc
    _ ≤ ∫ s in 0..t, (M : ℝ) * C / 2 * s ^ 2 :=
      intervalIntegral.norm_integral_le_of_norm_le ht.1 (Filter.Eventually.of_forall hb) hint
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      norm_num
      ring

/-- The two component estimates imply the paper's `0.75` constant after
the change of coordinates, under `γh≤1/4`. This is a statement about the
explicit local defects, not an assumed one-step error estimate. -/
theorem localDefect_energy_bound {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (g : F → F) (M : ℝ≥0) (hg : LipschitzWith M g)
    (x v : ℝ → F) (γ h C : ℝ) (hγ : 0 ≤ γ) (hh : 0 ≤ h) (hC : 0 ≤ C)
    (hsmall : γ * h ≤ 1 / 4)
    (hbound : ∀ s ∈ Icc 0 h, ‖v s‖ ≤ C)
    (hkin : ∀ s ∈ Icc 0 h, x s - x 0 = ∫ r in 0..s, v r) :
    transformEnergy γ 0 (velocityDefect g x γ h, positionDefect g x γ h) ≤
      ((3 / 4 : ℝ) * (M : ℝ) * C * h ^ 2) ^ 2 := by
  let B : ℝ := (M : ℝ) * C * h ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hv := velocityDefect_bound g M hg x v γ h C hγ hC hbound hkin
    (t := h) ⟨hh, le_rfl⟩
  have hp := positionDefect_bound g M hg x v γ h C hγ hC hbound hkin
    (t := h) ⟨hh, le_rfl⟩
  have hv' : ‖velocityDefect g x γ h‖ ≤ B / 2 := hv
  have hp' : ‖positionDefect g x γ h‖ ≤ B * h / 6 := by
    dsimp [B]
    nlinarith [hp]
  have ht := norm_add_le (velocityDefect g x γ h) (γ • positionDefect g x γ h)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ] at ht
  have hsum : ‖velocityDefect g x γ h + γ • positionDefect g x γ h‖ ≤
      (13 / 24 : ℝ) * B := by
    have hγp := mul_le_mul_of_nonneg_left hp' hγ
    have hγh := mul_le_mul_of_nonneg_left hsmall hB
    nlinarith
  have hsqsum := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ (13 / 24 : ℝ) * B)).mpr hsum
  have hsqv := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ B / 2)).mpr hv'
  simp only [transformEnergy, transform, sub_zero, zero_smul, norm_neg]
  change _ ≤ ((3 / 4 : ℝ) * (M : ℝ) * C * h ^ 2) ^ 2
  have he : ((3 / 4 : ℝ) * (M : ℝ) * C * h ^ 2) ^ 2 = ((3 / 4 : ℝ) * B) ^ 2 := by
    dsimp [B]
    ring
  rw [he]
  nlinarith [sq_nonneg B]

end KineticLangevin
