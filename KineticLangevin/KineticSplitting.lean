import KineticLangevin.HamiltonianConvergence
import KineticLangevin.Coefficients

/-! # Concrete Verlet--Ornstein--Uhlenbeck splitting estimates -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal
namespace KineticLangevin
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Damping acts only on velocity. -/
def velocityDamping (δ : ℝ) (z : E×E) : E×E := (δ • z.1,z.2)

/-- A thermal damping coefficient between zero and one is nonexpansive in
phase space with its usual maximum product norm. -/
theorem velocityDamping_norm_sub_le (δ : ℝ) (hδ0 : 0≤δ) (hδ1 : δ≤1)
    (z w : E×E) : ‖velocityDamping δ z-velocityDamping δ w‖ ≤ ‖z-w‖ := by
  have hv : ‖z.1-w.1‖ ≤ ‖z-w‖ := by simpa using norm_fst_le (z-w)
  have hx : ‖z.2-w.2‖ ≤ ‖z-w‖ := by simpa using norm_snd_le (z-w)
  change max ‖δ • z.1-δ • w.1‖ ‖z.2-w.2‖ ≤ _
  apply max_le _ hx
  rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg hδ0]
  exact (mul_le_of_le_one_left (norm_nonneg _) hδ1).trans hv

/-- The actual Lie splitting: velocity Verlet followed by one exact
Ornstein--Uhlenbeck damping and a supplied filtered velocity increment. -/
def kineticSplitStep (g : E → E) (γ h : ℝ) (z : E×E) (N : E) : E×E :=
  ornsteinStep (Real.exp (-γ*h)) 1 N (verletStep g h z)

/-- Synchronous additive thermostat inputs cancel and the full splitting
inherits Verlet's stable first-order Lipschitz bound. -/
theorem kineticSplitStep_norm_sub_le (g : E → E) (M : ℝ≥0) (hg : LipschitzWith M g)
    (γ h : ℝ) (hγ : 0≤γ) (hh : 0≤h) (hh1 : h≤1) (z w : E×E) (N : E) :
    ‖kineticSplitStep g γ h z N-kineticSplitStep g γ h w N‖ ≤
      (1+((M : ℝ)+1)^2*h)*‖z-w‖ := by
  have he : kineticSplitStep g γ h z N-kineticSplitStep g γ h w N =
      velocityDamping (Real.exp (-γ*h)) (verletStep g h z)-
        velocityDamping (Real.exp (-γ*h)) (verletStep g h w) := by
    ext <;> simp [kineticSplitStep,velocityDamping,ornsteinStep]
  rw [he]
  exact (velocityDamping_norm_sub_le _ (Real.exp_pos _).le
    (Real.exp_le_one_iff.mpr (by nlinarith)) _ _).trans
    (verletStep_norm_sub_le g M hg h hh hh1 z w)

/-- Two exact friction balances supply the quadratic exponential Euler
remainder without dividing by the friction. -/
theorem damping_euler_remainder (γ h : ℝ) (hγ : 0≤γ) (hh : 0≤h) :
    |Real.exp (-γ*h)-1+γ*h| ≤ γ^2*h^2/2 := by
  have h1 := friction_mul_psi_one γ h
  have h2 := friction_mul_psi_two γ h
  have hnon := psi_nonneg γ 2 hh
  have hbound := mul_le_mul_of_nonneg_left (psi_two_le hγ hh) (sq_nonneg γ)
  have hid : Real.exp (-γ*h)-1+γ*h = γ^2*psi γ 2 h := by
    rw [psi_zero] at h1
    nlinarith [h1,h2]
  rw [hid,abs_of_nonneg (mul_nonneg (sq_nonneg γ) hnon)]
  nlinarith

/-- The loss of velocity damping is at most friction times elapsed time. -/
theorem one_sub_damping_le (γ h : ℝ) (hγ : 0≤γ) (hh : 0≤h) :
    0 ≤ 1-Real.exp (-γ*h) ∧ 1-Real.exp (-γ*h) ≤ γ*h := by
  refine ⟨sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith)),?_⟩
  have he := Real.add_one_le_exp (-γ*h)
  linarith

/-- The actual damped Hamiltonian Euler stage differs from full kinetic
Euler by a quadratic local drift term. -/
theorem damping_hamiltonianEuler_defect (g : E → E) (M : ℝ≥0) (hg : LipschitzWith M g)
    (γ h : ℝ) (hγ : 0≤γ) (hh : 0≤h) (z : E×E) :
    ‖velocityDamping (Real.exp (-γ*h)) (z-h • kineticNegativeDrift g 0 1 z)-
      (z-h • kineticNegativeDrift g γ 1 z)‖ ≤
      h^2*(γ^2/2+γ*((M : ℝ)+1))*(‖z‖+‖g 0‖) := by
  let δ := Real.exp (-γ*h)
  have hv : ‖z.1‖ ≤ ‖z‖ := norm_fst_le z
  have hx : ‖z.2‖ ≤ ‖z‖ := norm_snd_le z
  have hgrowth : ‖g z.2‖ ≤ (M : ℝ)*‖z‖+‖g 0‖ := by
    have ht := norm_sub_le (g z.2-g 0) (-g 0)
    have hl := hg.norm_sub_le z.2 0
    simp only [sub_neg_eq_add,sub_add_cancel,norm_neg,sub_zero] at ht hl
    nlinarith [mul_le_mul_of_nonneg_left hx M.coe_nonneg]
  have hid : velocityDamping δ (z-h • kineticNegativeDrift g 0 1 z)-
      (z-h • kineticNegativeDrift g γ 1 z) =
      ((δ-1+γ*h) • z.1+((1-δ)*h) • g z.2,0) := by
    ext <;> simp only [velocityDamping,kineticNegativeDrift,Prod.fst_sub,Prod.snd_sub,
      Prod.smul_fst,Prod.smul_snd,zero_smul,one_smul,zero_add,neg_smul]
    · module
    · module
  rw [hid,Prod.norm_mk,norm_zero,max_eq_left (norm_nonneg _)]
  have he := damping_euler_remainder γ h hγ hh
  have hδ := one_sub_damping_le γ h hγ hh
  have hs := norm_add_le ((δ-1+γ*h) • z.1) (((1-δ)*h) • g z.2)
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_mul,abs_of_nonneg hh,abs_of_nonneg hδ.1] at hs
  have ha := mul_le_mul he hv (norm_nonneg _) (by positivity : 0≤γ^2*h^2/2)
  have hb := mul_le_mul
    (mul_le_mul_of_nonneg_right hδ.2 hh) hgrowth (norm_nonneg _) (by positivity : 0≤γ*h*h)
  dsimp [δ]
  dsimp [δ] at hs
  have hm := M.coe_nonneg
  calc
    _ ≤ γ^2*h^2/2*‖z‖+γ*h*h*((M : ℝ)*‖z‖+‖g 0‖) :=
      hs.trans (add_le_add ha hb)
    _ = h^2*((γ^2/2+γ*(M : ℝ))*‖z‖+γ*‖g 0‖) := by ring
    _ ≤ h^2*((γ^2/2+γ*((M : ℝ)+1))*(‖z‖+‖g 0‖)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg h)
      have hc : 0 ≤ γ^2/2+γ*(M : ℝ) := by positivity
      nlinarith [mul_nonneg hc (norm_nonneg (g 0)),mul_nonneg hγ (norm_nonneg z)]
    _ = _ := by ring

/-- The complete concrete splitting differs from full kinetic Euler by a
quadratic deterministic defect; the supplied noise is retained exactly. -/
theorem kineticSplitStep_euler_defect (g : E → E) (M : ℝ≥0) (hg : LipschitzWith M g)
    (γ h : ℝ) (hγ : 0≤γ) (hh : 0≤h) (hh1 : h≤1) (z : E×E) (N : E) :
    ‖kineticSplitStep g γ h z N-(z-h • kineticNegativeDrift g γ 1 z+(N,0))‖ ≤
      h^2*(((M : ℝ)+1)*((M : ℝ)+2)+γ^2/2+γ*((M : ℝ)+1))*(‖z‖+‖g 0‖) := by
  have he : kineticSplitStep g γ h z N-(z-h • kineticNegativeDrift g γ 1 z+(N,0)) =
      velocityDamping (Real.exp (-γ*h)) (verletStep g h z)-
        (z-h • kineticNegativeDrift g γ 1 z) := by
    ext <;> simp [kineticSplitStep,ornsteinStep,velocityDamping]
  rw [he]
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (velocityDamping (Real.exp (-γ*h)) (verletStep g h z))
    (velocityDamping (Real.exp (-γ*h)) (z-h • kineticNegativeDrift g 0 1 z))
    (z-h • kineticNegativeDrift g γ 1 z)
  have h1 := (velocityDamping_norm_sub_le (Real.exp (-γ*h)) (Real.exp_pos _).le
    (Real.exp_le_one_iff.mpr (by nlinarith)) _ _).trans
    (verletStep_euler_defect g M hg h hh hh1 z)
  have h2 := damping_hamiltonianEuler_defect g M hg γ h hγ hh z
  exact (htri.trans (add_le_add h1 h2)).trans_eq (by ring)

/-- The filtered additive increment, written by deterministic integration
by parts against the continuous additive input. -/
def ouInputIncrement (γ : ℝ) (B : ℝ → E) (a h : ℝ) : E :=
  B (a+h)-B a - γ • ∫ s in 0..h, Real.exp (-γ*(h-s)) • (B (a+s)-B a)

/-- The OU increment differs from the matching additive increment by at most
friction times step length times the actual input's local oscillation. -/
theorem ouInputIncrement_defect (γ : ℝ) (hγ : 0≤γ) (B : ℝ → E)
    (a h ε : ℝ) (hh : 0≤h) (hε : 0≤ε)
    (hmod : ∀ s ∈ Icc 0 h, ‖B (a+s)-B a‖ ≤ ε) :
    ‖ouInputIncrement γ B a h-(B (a+h)-B a)‖ ≤ γ*h*ε := by
  have hid : ouInputIncrement γ B a h-(B (a+h)-B a) =
      -(γ • ∫ s in 0..h, Real.exp (-γ*(h-s)) • (B (a+s)-B a)) := by
    unfold ouInputIncrement
    module
  rw [hid,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_nonneg hγ]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := h) (C := ε) (f := fun s ↦ Real.exp (-γ*(h-s)) • (B (a+s)-B a))
    (fun s hs ↦ ?_)
  · simp only [sub_zero,abs_of_nonneg hh] at hi
    nlinarith [mul_le_mul_of_nonneg_left hi hγ]
  · rw [uIoc_of_le hh] at hs
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-γ*(h-s)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hs.2])
    exact (mul_le_of_le_one_left (norm_nonneg _) he).trans
      (hmod s ⟨hs.1.le,hs.2⟩)

end KineticLangevin
