import PBGSO.PaperTheorems

/-! # Time-uniform comparison without numerical contractivity
The chains below satisfy their actual numerical and reference update equations.
Only the exact update is contractive. The numerical defect may grow linearly
with its input radius; that radius is bounded by the derived comparison error
plus the exact reference radius and is absorbed for a sufficiently small step.
-/
noncomputable section
set_option linter.unusedSectionVars false
open scoped NNReal
namespace PBGSO.UniformDiscrete

private theorem affine_recurrence_bound (u : ℕ → ℝ) (r β : ℝ) (hr : 0 ≤ r)
    (hr1 : r < 1) (hstep : ∀ n, u (n+1) ≤ r*u n+β) (n : ℕ) :
    u n ≤ r^n*u 0+β/(1-r)*(1-r^n) := by
  have hden : 1-r ≠ 0 := ne_of_gt (sub_pos.mpr hr1)
  have hB : r*(β/(1-r))+β=β/(1-r) := by field_simp; ring
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      u (n+1) ≤ r*u n+β := hstep n
      _ ≤ r*(r^n*u 0+β/(1-r)*(1-r^n))+β := by gcongr
      _ = r^(n+1)*u 0+β/(1-r)*(1-r^(n+1)) := by rw [pow_succ]; nlinarith [hB]

section Chains
variable {H K : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- The actual two updates imply the affine error recursion. No numerical
Lipschitz or numerical contraction condition is required. -/
theorem chain_error_step (C : H →L[ℝ] K) (A Φ : ℕ → H → H) (X Y : ℕ → H)
    (q ε a b R : ℝ) (hε : 0 ≤ ε) (hb : 0 ≤ b)
    (hX : ∀ n, X (n+1)=A n (X n)) (hY : ∀ n, Y (n+1)=Φ n (Y n))
    (hcontract : ∀ n x y, ‖C (Φ n x-Φ n y)‖ ≤ q*‖C (x-y)‖)
    (hdefect : ∀ n x, ‖C (A n x-Φ n x)‖ ≤ ε*(a+b*‖C x‖))
    (hreference : ∀ n, ‖C (Y n)‖ ≤ R) (n : ℕ) :
    ‖C (X (n+1)-Y (n+1))‖ ≤
      (q+ε*b)*‖C (X n-Y n)‖+ε*(a+b*R) := by
  have hradius : ‖C (X n)‖ ≤ ‖C (X n-Y n)‖+R := by
    have he : C (X n)=C (X n-Y n)+C (Y n) := by simp
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add (le_refl _) (hreference n))
  have he : C (X (n+1)-Y (n+1))=
      C (A n (X n)-Φ n (X n))+C (Φ n (X n)-Φ n (Y n)) := by
    rw [hX,hY]
    simp
  rw [he]
  calc
    _ ≤ ‖C (A n (X n)-Φ n (X n))‖+‖C (Φ n (X n)-Φ n (Y n))‖ := norm_add_le _ _
    _ ≤ ε*(a+b*‖C (X n)‖)+q*‖C (X n-Y n)‖ :=
      add_le_add (hdefect n (X n)) (hcontract n (X n) (Y n))
    _ ≤ ε*(a+b*(‖C (X n-Y n)‖+R))+q*‖C (X n-Y n)‖ := by gcongr
    _ = _ := by ring

/-- Closed-form time-uniform comparison for actual chains. The defect's
linear dependence on the numerical radius is absorbed into r=q+εb<1. -/
theorem chain_error_bound (C : H →L[ℝ] K) (A Φ : ℕ → H → H) (X Y : ℕ → H)
    (q ε a b R : ℝ) (hq : 0 ≤ q) (hε : 0 ≤ ε) (hb : 0 ≤ b)
    (hsmall : q+ε*b<1)
    (hX : ∀ n, X (n+1)=A n (X n)) (hY : ∀ n, Y (n+1)=Φ n (Y n))
    (hcontract : ∀ n x y, ‖C (Φ n x-Φ n y)‖ ≤ q*‖C (x-y)‖)
    (hdefect : ∀ n x, ‖C (A n x-Φ n x)‖ ≤ ε*(a+b*‖C x‖))
    (hreference : ∀ n, ‖C (Y n)‖ ≤ R) (n : ℕ) :
    ‖C (X n-Y n)‖ ≤ (q+ε*b)^n*‖C (X 0-Y 0)‖+
      (ε*(a+b*R))/(1-(q+ε*b))*(1-(q+ε*b)^n) :=
  affine_recurrence_bound (fun k => ‖C (X k-Y k)‖) (q+ε*b) (ε*(a+b*R))
    (by positivity) hsmall
    (chain_error_step C A Φ X Y q ε a b R hε hb hX hY hcontract hdefect hreference) n

/-- The same construction yields a uniform bound on numerical moments;
stability is a conclusion of the actual comparison argument. -/
theorem chain_radius_bound (C : H →L[ℝ] K) (A Φ : ℕ → H → H) (X Y : ℕ → H)
    (q ε a b R : ℝ) (hq : 0 ≤ q) (hε : 0 ≤ ε) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hR : 0 ≤ R) (hsmall : q+ε*b<1)
    (hX : ∀ n, X (n+1)=A n (X n)) (hY : ∀ n, Y (n+1)=Φ n (Y n))
    (hcontract : ∀ n x y, ‖C (Φ n x-Φ n y)‖ ≤ q*‖C (x-y)‖)
    (hdefect : ∀ n x, ‖C (A n x-Φ n x)‖ ≤ ε*(a+b*‖C x‖))
    (hreference : ∀ n, ‖C (Y n)‖ ≤ R) (n : ℕ) :
    ‖C (X n)‖ ≤ R+‖C (X 0-Y 0)‖+(ε*(a+b*R))/(1-(q+ε*b)) := by
  have hp0 : 0 ≤ (q+ε*b)^n := pow_nonneg (by positivity) _
  have hp1 : (q+ε*b)^n ≤ 1 := pow_le_one₀ (by positivity) hsmall.le
  have hβ : 0 ≤ (ε*(a+b*R))/(1-(q+ε*b)) := by positivity
  have he := chain_error_bound C A Φ X Y q ε a b R hq hε hb hsmall hX hY hcontract hdefect hreference n
  have htri : ‖C (X n)‖ ≤ ‖C (X n-Y n)‖+R := by
    have heq : C (X n)=C (X n-Y n)+C (Y n) := by simp
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add (le_refl _) (hreference n))
  have hfirst : (q+ε*b)^n*‖C (X 0-Y 0)‖ ≤ ‖C (X 0-Y 0)‖ :=
    mul_le_of_le_one_left (norm_nonneg _) hp1
  have hsecond : ((ε*(a+b*R))/(1-(q+ε*b)))*(1-(q+ε*b)^n) ≤
      (ε*(a+b*R))/(1-(q+ε*b)) := mul_le_of_le_one_right hβ (by linarith)
  linarith
end Chains

/-- An elementary exponential estimate used for one-step absorption. -/
theorem exp_neg_le_one_sub_half (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (-x) ≤ 1-x/2 := by
  have hpos : 0 < 1+x := by linarith
  have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) (Real.exp_pos (-x)).le
  have heq : Real.exp x*Real.exp (-x)=1 := by rw [← Real.exp_add]; simp
  rw [heq] at he
  have hi : Real.exp (-x) ≤ 1/(1+x) := (le_div_iff₀ hpos).mpr (by nlinarith [he])
  apply hi.trans
  apply (div_le_iff₀ hpos).mpr
  nlinarith [mul_nonneg hx (sub_nonneg.mpr hx1)]

/-- The numerical defect is absorbed by exact one-step contraction for
an explicit positive step range; numerical contractivity is not assumed. -/
theorem one_step_absorption (ρ h b : ℝ) (hρ : 0 < ρ) (hh : 0 < h)
    (hρh : ρ*h≤1) (hsmall : b*Real.sqrt h≤ρ/4) :
    Real.exp (-ρ*h)+b*(h*Real.sqrt h) ≤ 1-ρ*h/4 := by
  have he := exp_neg_le_one_sub_half (ρ*h) (mul_nonneg hρ.le hh.le) hρh
  have hs := mul_le_mul_of_nonneg_right hsmall hh.le
  rw [← neg_mul] at he
  nlinarith

section OneStep
variable {H K : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- One-step local defects of size h√h yield a time-uniform √h bound
for the actual numerical chain, even though it is not assumed contractive. -/
theorem one_step_uniform_error (C : H →L[ℝ] K) (A Φ : ℕ → H → H) (X Y : ℕ → H)
    (ρ h a b R : ℝ) (hρ : 0 < ρ) (hh : 0 < h) (hb : 0 ≤ b)
    (hρh : ρ*h≤1) (hsmall : b*Real.sqrt h≤ρ/4)
    (hX : ∀ n, X (n+1)=A n (X n)) (hY : ∀ n, Y (n+1)=Φ n (Y n))
    (hcontract : ∀ n x y, ‖C (Φ n x-Φ n y)‖ ≤ Real.exp (-ρ*h)*‖C (x-y)‖)
    (hdefect : ∀ n x, ‖C (A n x-Φ n x)‖ ≤ (h*Real.sqrt h)*(a+b*‖C x‖))
    (hreference : ∀ n, ‖C (Y n)‖ ≤ R) (n : ℕ) :
    ‖C (X n-Y n)‖ ≤ (1-ρ*h/4)^n*‖C (X 0-Y 0)‖+
      (4*(a+b*R)/ρ)*Real.sqrt h*(1-(1-ρ*h/4)^n) := by
  let p := 1-ρ*h/4
  have hp : 0 ≤ p := by dsimp [p]; linarith
  have hp1 : p<1 := by dsimp [p]; nlinarith
  have hrec (k : ℕ) : ‖C (X (k+1)-Y (k+1))‖ ≤
      p*‖C (X k-Y k)‖+(h*Real.sqrt h)*(a+b*R) := by
    have he := chain_error_step C A Φ X Y (Real.exp (-ρ*h)) (h*Real.sqrt h) a b R
      (by positivity) hb hX hY hcontract hdefect hreference k
    have hm := mul_le_mul_of_nonneg_right (one_step_absorption ρ h b hρ hh hρh hsmall)
      (norm_nonneg (C (X k-Y k)))
    exact he.trans (by dsimp [p]; nlinarith [hm])
  have he := affine_recurrence_bound (fun k => ‖C (X k-Y k)‖) p
    ((h*Real.sqrt h)*(a+b*R)) hp hp1 hrec n
  have hc : ((h*Real.sqrt h)*(a+b*R))/(1-p)=(4*(a+b*R)/ρ)*Real.sqrt h := by
    dsimp [p]
    field_simp
    ring
  simpa only [hc] using he
/-- In synchronous initialization, the original numerical/reference error
is bounded uniformly over every iteration by an explicit constant times √h. -/
theorem one_step_same_initial_uniform (C : H →L[ℝ] K) (A Φ : ℕ → H → H) (X Y : ℕ → H)
    (ρ h a b R : ℝ) (hρ : 0 < ρ) (hh : 0 < h) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hR : 0 ≤ R) (hρh : ρ*h≤1) (hsmall : b*Real.sqrt h≤ρ/4)
    (hX : ∀ n, X (n+1)=A n (X n)) (hY : ∀ n, Y (n+1)=Φ n (Y n))
    (hcontract : ∀ n x y, ‖C (Φ n x-Φ n y)‖ ≤ Real.exp (-ρ*h)*‖C (x-y)‖)
    (hdefect : ∀ n x, ‖C (A n x-Φ n x)‖ ≤ (h*Real.sqrt h)*(a+b*‖C x‖))
    (hreference : ∀ n, ‖C (Y n)‖ ≤ R) (hinit : X 0=Y 0) (n : ℕ) :
    ‖C (X n-Y n)‖ ≤ (4*(a+b*R)/ρ)*Real.sqrt h := by
  have he := one_step_uniform_error C A Φ X Y ρ h a b R hρ hh hb hρh hsmall
    hX hY hcontract hdefect hreference n
  rw [hinit,sub_self,map_zero,norm_zero,mul_zero,zero_add] at he
  have hp : 0 ≤ (1-ρ*h/4)^n := pow_nonneg (by linarith) _
  have hK : 0 ≤ (4*(a+b*R)/ρ)*Real.sqrt h := by positivity
  exact he.trans (mul_le_of_le_one_right hK (by linarith))

/-- A coercivity bound on the actual metric transform converts the proved
uniform metric estimate to the original state-space norm. -/
theorem one_step_same_initial_uniform_norm (C : H →L[ℝ] K) (A Φ : ℕ → H → H) (X Y : ℕ → H)
    (ρ h a b R m : ℝ) (hρ : 0 < ρ) (hh : 0 < h) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hR : 0 ≤ R) (hm : 0 < m) (hcoerc : ∀ z, m*‖z‖≤‖C z‖)
    (hρh : ρ*h≤1) (hsmall : b*Real.sqrt h≤ρ/4)
    (hX : ∀ n, X (n+1)=A n (X n)) (hY : ∀ n, Y (n+1)=Φ n (Y n))
    (hcontract : ∀ n x y, ‖C (Φ n x-Φ n y)‖ ≤ Real.exp (-ρ*h)*‖C (x-y)‖)
    (hdefect : ∀ n x, ‖C (A n x-Φ n x)‖ ≤ (h*Real.sqrt h)*(a+b*‖C x‖))
    (hreference : ∀ n, ‖C (Y n)‖ ≤ R) (hinit : X 0=Y 0) (n : ℕ) :
    ‖X n-Y n‖ ≤ ((4*(a+b*R)/ρ)*Real.sqrt h)/m := by
  apply (le_div_iff₀ hm).mpr
  have he := one_step_same_initial_uniform C A Φ X Y ρ h a b R hρ hh ha hb hR
    hρh hsmall hX hY hcontract hdefect hreference hinit n
  nlinarith [hcoerc (X n-Y n)]

end OneStep
end PBGSO.UniformDiscrete
