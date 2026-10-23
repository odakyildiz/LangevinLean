import KineticLangevin.Coefficients

noncomputable section
open MeasureTheory Set
namespace KineticLangevin

/-- Integration by parts moves one primitive from one scalar response factor to the other. -/
theorem psi_convolution_shift (γ t : ℝ) (k j : ℕ) :
    (∫ s in 0..t,psi γ k s*psi γ (j+1) (t-s))=
      ∫ s in 0..t,psi γ (k+1) s*psi γ j (t-s) := by
  have hd : ∀ s∈uIcc 0 t,HasDerivAt
      (fun s ↦ psi γ (k+1) s*psi γ (j+1) (t-s))
      (psi γ k s*psi γ (j+1) (t-s)-psi γ (k+1) s*psi γ j (t-s)) s := by
    intro s _
    convert (hasDerivAt_psi_succ γ s k).mul
      ((hasDerivAt_psi_succ γ (t-s) j).comp s ((hasDerivAt_const s t).sub (hasDerivAt_id s))) using 1 <;> first | rfl | (simp only [Function.comp_apply]; ring)
  have hc1 : Continuous (fun s : ℝ ↦ psi γ k s*psi γ (j+1) (t-s)) :=
    (continuous_psi γ k).mul ((continuous_psi γ (j+1)).comp (continuous_const.sub continuous_id))
  have hc2 : Continuous (fun s : ℝ ↦ psi γ (k+1) s*psi γ j (t-s)) :=
    (continuous_psi γ (k+1)).mul ((continuous_psi γ j).comp (continuous_const.sub continuous_id))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((hc1.sub hc2).intervalIntegrable 0 t)
  rw [intervalIntegral.integral_sub (hc1.intervalIntegrable 0 t) (hc2.intervalIntegrable 0 t)] at hi
  simpa [psi_at_zero,sub_eq_zero] using hi

/-- The full second convolution identity of the source lemma, for every pair of indices. -/
theorem phi_eq_psi_convolution (γ t : ℝ) (k j : ℕ) :
    phi γ (k+j+1) t=∫ s in 0..t,psi γ k s*psi γ j (t-s) := by
  induction j generalizing k with
  | zero =>
    simp only [Nat.add_zero,phi_succ,psi_zero]
    apply intervalIntegral.integral_congr
    intro s _
    ring
  | succ j ih =>
    rw [psi_convolution_shift γ t k j,← ih (k+1)]
    congr 1
    omega

/-- The complete friction recurrence for every nonzero correction index. -/
theorem phi_add_friction_phi_succ (γ t : ℝ) (k : ℕ) :
    phi γ (k+1) t+γ*phi γ (k+2) t=psi γ (k+1) t := by
  have hi := phi_eq_psi_convolution γ t k 1
  have hidx : k+1+1=k+2 := by omega
  rw [hidx] at hi
  rw [hi,← intervalIntegral.integral_const_mul]
  have he : (fun s ↦ γ*(psi γ k s*psi γ 1 (t-s)))=
      (fun s ↦ psi γ k s-Real.exp (-γ*(t-s))*psi γ k s) := by
    funext s
    rw [show γ*(psi γ k s*psi γ 1 (t-s))=psi γ k s*(γ*psi γ 1 (t-s)) by ring,
      friction_mul_psi_one,psi_zero]
    ring
  have hc : Continuous (fun s : ℝ ↦ Real.exp (-γ*(t-s))*psi γ k s) :=
    (by fun_prop : Continuous (fun s : ℝ ↦ Real.exp (-γ*(t-s)))).mul (continuous_psi γ k)
  have hI : IntervalIntegrable (fun s : ℝ ↦ Real.exp (-γ*(t-s))*psi γ k s) volume 0 t := hc.intervalIntegrable 0 t
  rw [he,intervalIntegral.integral_sub ((continuous_psi γ k).intervalIntegrable 0 t) hI]
  change phi γ (k+1) t+(psi γ (k+1) t-phi γ (k+1) t)=_
  ring

/-- Differentiating the factored convolution gives its true response equation. -/
theorem hasDerivAt_phi_succ (γ t : ℝ) (k : ℕ) :
    HasDerivAt (phi γ (k+1)) (psi γ k t-γ*phi γ (k+1) t) t := by
  have hc : Continuous (fun s : ℝ ↦ Real.exp (γ*s)*psi γ k s) :=
    (by fun_prop : Continuous (fun s : ℝ ↦ Real.exp (γ*s))).mul (continuous_psi γ k)
  have hd := (((hasDerivAt_id t).const_mul (-γ)).exp).mul
    (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt)
  have he : Real.exp (-γ*t)*Real.exp (γ*t)=1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  convert hd.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s ↦ phi_factor γ s k)) using 1
  · simp only [id_eq,mul_one]
    rw [phi_factor]
    linear_combination -(psi γ k t)*he

/-- The source primitive identity with its necessary nonzero-index restriction. -/
theorem phi_succ_eq_integral_phi (γ t : ℝ) (k : ℕ) :
    phi γ (k+2) t=∫ s in 0..t,phi γ (k+1) s := by
  have hd : ∀ s∈uIcc 0 t,HasDerivAt (phi γ (k+2)) (phi γ (k+1) s) s := by
    intro s _
    have he := phi_add_friction_phi_succ γ s k
    convert hasDerivAt_phi_succ γ s (k+1) using 1
    linarith
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_phi γ (k+1)).intervalIntegrable 0 t)
  simpa only [phi_at_zero,sub_zero] using hi.symm

end KineticLangevin
