import PBGSO.RawLocalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Deterministic damping after a genuine stopping time
After the stopping time the state is extended by exponential contraction.
The original stopped Brownian noise stays unchanged. This supplies sharp
dissipation at all times without a stochastic product-rule premise.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace PBGSO.DampedContinuation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def damping (ρ τ t : ℝ) : ℝ := Real.exp (-ρ * (t - min t τ))

def extension (ρ τ : ℝ) (x : ℝ → E) (t : ℝ) : E := damping ρ τ t • x (min t τ)

def drift (ρ τ : ℝ) (x b : ℝ → E) (r : ℝ) : E :=
  if r ≤ τ then b r else -ρ • extension ρ τ x r

def correction (ρ τ r : ℝ) : ℝ :=
  if τ < r then -ρ * Real.exp (-ρ * (r - τ)) else 0

theorem extension_before (ρ τ : ℝ) (x : ℝ → E) {t : ℝ} (ht : t ≤ τ) :
    extension ρ τ x t = x t := by simp [extension,damping,min_eq_left ht]

theorem extension_after (ρ τ : ℝ) (x : ℝ → E) {t : ℝ} (ht : τ ≤ t) :
    extension ρ τ x t = Real.exp (-ρ * (t - τ)) • x τ := by
  simp only [extension,damping,min_eq_right ht]

theorem correction_integrable (ρ τ a t : ℝ) :
    IntervalIntegrable (correction ρ τ) volume a t := by
  rw [intervalIntegrable_iff]
  have h : Continuous (fun r : ℝ => -ρ * Real.exp (-ρ * (r - τ))) := by fun_prop
  exact (h.integrableOn_Icc).mono_set (uIoc_subset_uIcc) |>.indicator measurableSet_Ioi

/-- The after-stop correction is an ordinary deterministic exponential
primitive, even though the stopping time will later depend on the sample. -/
theorem integral_correction (ρ τ t : ℝ) (hτ : 0 ≤ τ) (ht : 0 ≤ t) :
    (∫ r in (0 : ℝ)..t, correction ρ τ r) = damping ρ τ t - 1 := by
  have hd (r : ℝ) : HasDerivAt (fun r => Real.exp (-ρ * (r - τ)))
      (-ρ * Real.exp (-ρ * (r - τ))) r := by
    simpa only [id_eq, mul_one, mul_comm] using ((((hasDerivAt_id r).sub_const τ).const_mul (-ρ)).exp)
  by_cases h : t ≤ τ
  · have hz : (∫ r in (0 : ℝ)..t, correction ρ τ r) = 0 := by
      apply intervalIntegral.integral_zero_ae
      apply ae_of_all
      intro r hr
      simp only [uIoc_of_le ht,mem_Ioc] at hr
      exact ite_eq_right (not_lt_of_ge (hr.2.trans h))
    rw [hz]
    simp [damping,min_eq_left h]
  · have hτt : τ ≤ t := (lt_of_not_ge h).le
    rw [intervalIntegral.integral_of_le ht]
    change (∫ r in Ioc 0 t, (Ioi τ).indicator
      (fun r => -ρ * Real.exp (-ρ * (r - τ))) r) = _
    rw [setIntegral_indicator measurableSet_Ioi]
    have hs : Ioc (0 : ℝ) t ∩ Ioi τ = Ioc τ t := by
      ext r
      simp only [mem_inter_iff,mem_Ioc,mem_Ioi]
      constructor
      · rintro ⟨⟨hr0,hrt⟩,hrτ⟩
        exact ⟨hrτ,hrt⟩
      · rintro ⟨hrτ,hrt⟩
        exact ⟨⟨lt_of_le_of_lt hτ hrτ,hrt⟩,hrτ⟩
    rw [hs, ← intervalIntegral.integral_of_le hτt]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _ => hd r) (by exact (by fun_prop : Continuous (fun r : ℝ => -ρ * Real.exp (-ρ * (r - τ)))).intervalIntegrable τ t)]
    simp [damping,min_eq_right hτt]

/-- The new drift differs from the genuinely stopped original drift only
by the explicit ordinary exponential correction. -/
theorem drift_decomposition (ρ τ : ℝ) (x b : ℝ → E) (r : ℝ) :
    drift ρ τ x b r = (if r ≤ τ then b r else 0) + correction ρ τ r • x τ := by
  by_cases h : r ≤ τ
  · simp [drift,correction,h,not_lt_of_ge h]
  · rw [drift,ite_eq_right h,ite_eq_right h,zero_add,
      extension_after ρ τ x (le_of_not_ge h),correction,ite_eq_left (lt_of_not_ge h),smul_smul]

/-- Actual original stopped integral equations imply the damped integral
equation. No stochastic integration-by-parts or multiplied-noise identity
is assumed. -/
theorem extension_integral_equation (ρ τ t : ℝ) (hτ : 0 ≤ τ) (ht : 0 ≤ t)
    (x b m : ℝ → E)
    (hb : IntervalIntegrable (fun r => if r ≤ τ then b r else 0) volume 0 t)
    (heq : x (min t τ) = x 0 + (∫ r in (0 : ℝ)..t, if r ≤ τ then b r else 0) + m t) :
    extension ρ τ x t = x 0 + (∫ r in (0 : ℝ)..t, drift ρ τ x b r) + m t := by
  have hc : IntervalIntegrable (fun r => correction ρ τ r • x τ) volume 0 t := by
    rw [intervalIntegrable_iff] at *
    exact (correction_integrable ρ τ 0 t).def'.smul_const (x τ)
  have hdecomp : (fun r => drift ρ τ x b r) =
      (fun r => if r ≤ τ then b r else 0) + fun r => correction ρ τ r • x τ :=
    funext (drift_decomposition ρ τ x b)
  rw [hdecomp]
  change extension ρ τ x t = x 0 + (∫ r in (0 : ℝ)..t,
    (if r ≤ τ then b r else 0) + correction ρ τ r • x τ) + m t
  rw [intervalIntegral.integral_add hb hc, intervalIntegral.integral_smul_const,
    integral_correction ρ τ t hτ ht]
  have hext : extension ρ τ x t = x (min t τ) + (damping ρ τ t - 1) • x τ := by
    by_cases h : t ≤ τ
    · simp [extension,damping,min_eq_left h]
    · simp only [extension,damping,min_eq_right (le_of_not_ge h)]
      rw [sub_smul,one_smul]
      abel
  rw [hext,heq]
  abel

theorem damping_nonneg (ρ τ t : ℝ) : 0 ≤ damping ρ τ t := (Real.exp_pos _).le

theorem damping_le_one {ρ : ℝ} (hρ : 0 ≤ ρ) (τ t : ℝ) : damping ρ τ t ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hρ)
    (sub_nonneg.mpr (min_le_left t τ))

/-- Damping never enlarges the original stopped state. -/
theorem extension_norm_le {ρ : ℝ} (hρ : 0 ≤ ρ) (τ : ℝ) (x : ℝ → E) (t : ℝ) :
    ‖extension ρ τ x t‖ ≤ ‖x (min t τ)‖ := by
  rw [extension,norm_smul,Real.norm_eq_abs,abs_of_nonneg (damping_nonneg ρ τ t)]
  exact mul_le_of_le_one_left (norm_nonneg _) (damping_le_one hρ τ t)

theorem drift_integrable (ρ τ : ℝ) (x b : ℝ → E) (a t : ℝ)
    (hb : IntervalIntegrable (fun r => if r ≤ τ then b r else 0) volume a t) :
    IntervalIntegrable (drift ρ τ x b) volume a t := by
  have hc : IntervalIntegrable (fun r => correction ρ τ r • x τ) volume a t := by
    rw [intervalIntegrable_iff]
    exact (correction_integrable ρ τ a t).def'.smul_const (x τ)
  change IntervalIntegrable (fun r => drift ρ τ x b r) volume a t
  simp_rw [drift_decomposition]
  exact hb.add hc

/-- The extended drift has a genuinely square-integrable random variation
budget whenever the stopped state has one; no new uniform cap is imposed. -/
theorem drift_variation_le {ρ : ℝ} (hρ : 0 ≤ ρ) (τ T c C : ℝ) (hT : 0 ≤ T)
    (x b : ℝ → E)
    (hb : IntervalIntegrable (fun r => if r ≤ τ then b r else 0) volume 0 T)
    (hTV : (∫ r in (0 : ℝ)..T, ‖if r ≤ τ then b r else 0‖) ≤ c)
    (hC : ∀ r ∈ Icc 0 T, ‖x (min r τ)‖ ≤ C) :
    (∫ r in (0 : ℝ)..T, ‖drift ρ τ x b r‖) ≤ c + ρ * T * C := by
  have hi := (drift_integrable ρ τ x b 0 T hb).norm
  have hconst : IntervalIntegrable (fun _ : ℝ => ρ * C) volume 0 T := intervalIntegrable_const
  have hbnd (r : ℝ) (hr : r ∈ Icc 0 T) :
      ‖drift ρ τ x b r‖ ≤ ‖if r ≤ τ then b r else 0‖ + ρ * C := by
    by_cases h : r ≤ τ
    · simp only [drift,ite_eq_left h]
      have hC0 : 0 ≤ C := (norm_nonneg (x (min r τ))).trans (hC r hr)
      linarith [mul_nonneg hρ hC0]
    · simp only [drift,ite_eq_right h,norm_zero,zero_add,norm_smul,Real.norm_eq_abs,abs_neg,
        abs_of_nonneg hρ]
      exact mul_le_mul_of_nonneg_left ((extension_norm_le hρ τ x r).trans (hC r hr)) hρ
  have hm := intervalIntegral.integral_mono_on hT hi (hb.norm.add hconst) hbnd
  rw [intervalIntegral.integral_add hb.norm hconst,intervalIntegral.integral_const] at hm
  simp only [sub_zero,smul_eq_mul] at hm
  nlinarith

end PBGSO.DampedContinuation
