import PBGSO.GlobalMeshRegularity
import PBGSO.AdditiveContraction
import PBGSO.MethodIntegralSegments

/-! # Explicit local and uniform moments for additive integral trajectories

Local radii are derived from the actual integral equation and a bound on the
input. They depend affinely on the initial norm, with no compactness-chosen or
horizon-dependent constant. Uniform radii will use exact-flow contraction.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology RealInnerProductSpace InnerProductSpace
namespace PBGSO.UniformIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- An explicit radius on every time interval of length at most one. -/
def radius (L : ℝ≥0) (fzero noise initial : ℝ) : ℝ :=
  Real.exp ((L : ℝ) + 1) * (initial + fzero + noise)

theorem radius_nonneg (L : ℝ≥0) {fzero noise initial : ℝ}
    (hf : 0 ≤ fzero) (hnoise : 0 ≤ noise) (hi : 0 ≤ initial) :
    0 ≤ radius L fzero noise initial := by unfold radius; positivity

/-- The primitive Lipschitz integral equation gives an explicit radius.
The input need not be differentiable, adapted or independent of the initial
state. Brownian increments supply its bound in the applications. -/
theorem local_radius (f : E → E) (L : ℝ≥0) (hf : LipschitzWith L f)
    (Y B : ℝ → E) (hY : Continuous Y) (hB : Continuous B)
    (T Ξ : ℝ) (hT : T ≤ 1) (hΞ : 0 ≤ Ξ)
    (heq : ∀ t ∈ Icc 0 T, Y t - Y 0 = (∫ r in 0..t, f (Y r)) + B t)
    (hinput : ∀ t ∈ Icc 0 T, ‖B t‖ ≤ Ξ)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖Y t‖ ≤ radius L ‖f 0‖ Ξ ‖Y 0‖ := by
  let K : ℝ := (L : ℝ) + 1
  let c : ℝ := ‖f 0‖ + Ξ
  have hK : 0 < K := by dsimp [K]; positivity
  have hforce : Continuous (fun r => f (Y r)) := hf.continuous.comp hY
  have hidentity (r : ℝ) (hr : r ∈ Icc 0 T) :
      Y r - B r = Y 0 + ∫ s in 0..r, f (Y s) := by
    have he := heq r hr
    rw [sub_eq_iff_eq_add] at he
    rw [he]
    abel
  have hder : ∀ r ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Y s-B s) (f (Y r)) (Ici r) r := by
    intro r hr
    have hd := intervalIntegral.integral_hasDerivAt_right (a := 0) (b := r)
      (hforce.intervalIntegrable 0 r) (hforce.stronglyMeasurableAtFilter volume (𝓝 r))
      hforce.continuousAt
    have hmem : Icc 0 T ∈ 𝓝[Ici r] r := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hr.2)] with s hs hsT
      exact ⟨hr.1.trans hs, hsT⟩
    have he : (fun s => Y s-B s) =ᶠ[𝓝[Ici r] r]
        (fun s => Y 0 + ∫ u in 0..s, f (Y u)) := by
      filter_upwards [hmem] with s hs
      exact hidentity s hs
    exact (hd.const_add (Y 0)).hasDerivWithinAt.congr_of_eventuallyEq he
      (hidentity r ⟨hr.1,hr.2.le⟩)
  have hbzero : B 0 = 0 := by
    have he := heq 0 ⟨le_rfl,ht.1.trans ht.2⟩
    simpa using he.symm
  have hbound : ∀ r ∈ Ico 0 T,
      ‖f (Y r)‖ ≤ K * ‖Y r-B r‖ + K*c := by
    intro r hr
    have hi := hinput r ⟨hr.1,hr.2.le⟩
    have hfn : ‖f (Y r)‖ ≤ (L : ℝ)*‖Y r‖ + ‖f 0‖ := by
      have hl := hf.norm_sub_le (Y r) 0
      simp only [sub_zero] at hl
      exact (norm_le_norm_sub_add (f (Y r)) (f 0)).trans (add_le_add hl le_rfl)
    have hyn : ‖Y r‖ ≤ ‖Y r-B r‖ + Ξ :=
      (norm_le_norm_sub_add (Y r) (B r)).trans (add_le_add le_rfl hi)
    have hp := mul_le_mul_of_nonneg_left hyn L.coe_nonneg
    dsimp [K,c]
    nlinarith [norm_nonneg (Y r-B r), norm_nonneg (f 0)]
  have hv := norm_le_gronwallBound_of_norm_deriv_right_le
    (hY.sub hB).continuousOn hder
    (show ‖Y 0-B 0‖ ≤ ‖Y 0‖ by simp [hbzero]) hbound t ht
  rw [sub_zero, gronwallBound, ite_eq_right (ne_of_gt hK)] at hv
  have hcdiv : K*c/K = c := by field_simp
  rw [hcdiv] at hv
  have he : Real.exp (K*t) ≤ Real.exp K :=
    Real.exp_le_exp.mpr (by nlinarith [ht.2.trans hT])
  have hprod := mul_le_mul_of_nonneg_left he
    (show 0 ≤ ‖Y 0‖+c by dsimp [c]; positivity)
  have hyt : ‖Y t‖ ≤ ‖Y t-B t‖ + Ξ :=
    (norm_le_norm_sub_add (Y t) (B t)).trans (add_le_add le_rfl (hinput t ht))
  change ‖Y t‖ ≤ Real.exp K * (‖Y 0‖+‖f 0‖+Ξ)
  dsimp [c] at hv hprod
  nlinarith [norm_nonneg (f 0)]

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Drift growth follows from the derived radius and primitive Lipschitzness. -/
theorem drift_bound (f : E → E) (L : ℝ≥0) (hf : LipschitzWith L f)
    (x : E) (P : ℝ) (hx : ‖x‖ ≤ P) :
    ‖f x‖ ≤ ‖f 0‖ + (L : ℝ)*P := by
  have hb := (norm_le_norm_sub_add (f x) (f 0)).trans
    (add_le_add (hf.norm_sub_le x 0) le_rfl)
  simp only [sub_zero] at hb
  nlinarith [mul_le_mul_of_nonneg_left hx L.coe_nonneg]

/-- Explicit one-step state, drift and square-root increment bounds.
Every constant is affine in the initial norm and independent of start time. -/
theorem local_regularity (f : E → E) (L : ℝ≥0) (hf : LipschitzWith L f)
    (Y B : ℝ → E) (hY : Continuous Y) (hB : Continuous B)
    (T Ξ : ℝ) (hT0 : 0 ≤ T) (hT : T ≤ 1) (hΞ : 0 ≤ Ξ)
    (heq : ∀ t ∈ Icc 0 T, Y t - Y 0 = (∫ r in 0..t, f (Y r)) + B t)
    (hinput : ∀ t ∈ Icc 0 T, ‖B t‖ ≤ Ξ * Real.sqrt t) :
    ∀ t ∈ Icc 0 T,
      ‖Y t‖ ≤ radius L ‖f 0‖ Ξ ‖Y 0‖ ∧
      ‖f (Y t)‖ ≤ ‖f 0‖+(L : ℝ)*radius L ‖f 0‖ Ξ ‖Y 0‖ ∧
      ‖Y t-Y 0‖ ≤ (‖f 0‖+(L : ℝ)*radius L ‖f 0‖ Ξ ‖Y 0‖+Ξ)*Real.sqrt t := by
  let P := radius L ‖f 0‖ Ξ ‖Y 0‖
  let D := ‖f 0‖+(L : ℝ)*P
  have hP : 0 ≤ P := radius_nonneg L (norm_nonneg _) hΞ (norm_nonneg _)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hunit : ∀ t ∈ Icc 0 T, ‖B t‖ ≤ Ξ := by
    intro t ht
    exact (hinput t ht).trans (by
      have hs : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr (ht.2.trans hT)
      nlinarith)
  have hstate (t : ℝ) (ht : t ∈ Icc 0 T) : ‖Y t‖ ≤ P :=
    local_radius f L hf Y B hY hB T Ξ hT hΞ heq hunit t ht
  have hdrift (t : ℝ) (ht : t ∈ Icc 0 T) : ‖f (Y t)‖ ≤ D :=
    drift_bound f L hf (Y t) P (hstate t ht)
  have hbzero : B 0 = 0 := by
    simpa using (heq 0 ⟨le_rfl,hT0⟩).symm
  intro t ht
  refine ⟨hstate t ht,hdrift t ht,?_⟩
  have hm := integral_segment_sqrt_modulus f Y B T 0 t D Ξ
    (hf.continuous.comp hY) (le_refl 0) ht.1 (ht.2.trans hT)
    (by simpa using ht.2) hD heq hdrift
    (by simpa only [zero_add,hbzero,sub_zero] using hinput t ht)
  simpa only [zero_add] using hm

section Contractive
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The actual integral equations, rather than a numerical stability premise,
give contraction in a quadratic metric. -/
theorem contraction (f : E → E) (L : ℝ≥0) (hf : LipschitzWith L f)
    (C : E →L[ℝ] H) (ρ : ℝ)
    (hmono : ∀ x y, ⟪C (x-y),C (f x-f y)⟫_ℝ ≤ -ρ*‖C (x-y)‖^2)
    (Y Z B : ℝ → E) (hY : Continuous Y) (hZ : Continuous Z) (T : ℝ)
    (heY : ∀ t ∈ Icc 0 T, Y t-Y 0 = (∫ r in 0..t, f (Y r))+B t)
    (heZ : ∀ t ∈ Icc 0 T, Z t-Z 0 = (∫ r in 0..t, f (Z r))+B t)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖C (Y t-Z t)‖ ≤ Real.exp (-ρ*t)*‖C (Y 0-Z 0)‖ := by
  apply transformed_additive_integral_contraction (fun x => -f x) L hf.neg C ρ ?_
    Y Z B hY hZ T ?_ ?_ t ht
  · intro x y
    have hm := hmono x y
    have he : -f x- -f y = -(f x-f y) := by abel
    rw [he,map_neg,inner_neg_right]
    linarith
  · intro s hs
    simpa only [intervalIntegral.integral_neg,neg_neg] using heY s hs
  · intro s hs
    simpa only [intervalIntegral.integral_neg,neg_neg] using heZ s hs

/-- Uniform bound for any exact continuous trajectory. Zero-start Picard
segments are constructed at every time, and strict contraction controls their
initial-state dependence. Only the primitive increment bound is supplied. -/
theorem uniform_moment (f : E → E) (L : ℝ≥0) (hf : LipschitzWith L f)
    (C : E →L[ℝ] H) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : ∀ x y, ⟪C (x-y),C (f x-f y)⟫_ℝ ≤ -ρ*‖C (x-y)‖^2)
    (Y B : ℝ → E) (hY : Continuous Y) (hB : Continuous B)
    (heq : ∀ t, 0 ≤ t → Y t-Y 0 = (∫ r in 0..t, f (Y r))+B t)
    (Ξ : ℝ) (hΞ : 0 ≤ Ξ)
    (hincrement : ∀ a s, 0 ≤ a → s ∈ Icc 0 1 →
      ‖B (a+s)-B a‖ ≤ Ξ*Real.sqrt s)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖C (Y t)‖ ≤ ‖C (Y 0)‖ +
      (‖C‖*radius L ‖f 0‖ Ξ 0)/(1-Real.exp (-ρ)) +
      ‖C‖*radius L ‖f 0‖ Ξ 0 := by
  let S : ℝ := ‖C‖*radius L ‖f 0‖ Ξ 0
  let q : ℝ := Real.exp (-ρ)
  have hS : 0 ≤ S := mul_nonneg (norm_nonneg _)
    (radius_nonneg L (norm_nonneg _) hΞ (le_refl 0))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgap : 0 < 1-q := by linarith
  have hsegment (a s : ℝ) (ha : 0 ≤ a) (hs : s ∈ Icc 0 1) :
      ‖C (Y (a+s))‖ ≤ Real.exp (-ρ*s)*‖C (Y a)‖+S := by
    let Bshift := fun r => B (a+r)-B a
    have hBc : Continuous Bshift :=
      (hB.comp (continuous_const.add continuous_id)).sub continuous_const
    have hB0 : Bshift 0 = 0 := by simp [Bshift]
    obtain ⟨Z,hZ,hZ0,hZe⟩ := ULA.exists_langevin_integral
      (fun x => -f x) L hf.neg (0 : E) Bshift hBc hB0 1 (by norm_num)
    have heZ (r : ℝ) (hr : r ∈ Icc 0 1) :
        Z r-Z 0 = (∫ u in 0..r, f (Z u))+Bshift r := by
      simpa only [hZ0,intervalIntegral.integral_neg,neg_neg] using hZe r hr
    have heY (r : ℝ) (hr : r ∈ Icc 0 1) :
        Y (a+r)-Y (a+0) = (∫ u in 0..r, f (Y (a+u)))+Bshift r := by
      simpa only [add_zero,Bshift] using
        MethodSegments.integral_shift Y (fun r => f (Y r)) B
          (hf.continuous.comp hY) heq a r ha hr.1
    have hloc := (local_regularity f L hf Z Bshift hZ hBc 1 Ξ
      (by norm_num) (le_refl 1) hΞ heZ
      (fun r hr => hincrement a r ha hr) s hs).1
    rw [hZ0,norm_zero] at hloc
    have hc := contraction f L hf C ρ hmono (fun r => Y (a+r)) Z Bshift
      (hY.comp (continuous_const.add continuous_id)) hZ 1 heY heZ s hs
    simp only [add_zero,hZ0,sub_zero] at hc
    have hh := (norm_le_norm_sub_add (C (Y (a+s))) (C (Z s)))
    rw [← map_sub] at hh
    have hcz := (C.le_opNorm (Z s)).trans
      (mul_le_mul_of_nonneg_left hloc (norm_nonneg C))
    exact hh.trans (add_le_add hc hcz)
  have hn : ∀ n : ℕ, ‖C (Y (n : ℝ))‖ ≤ ‖C (Y 0)‖+S/(1-q) := by
    intro n
    induction n with
    | zero =>
      simpa using (le_add_of_nonneg_right (div_nonneg hS hgap.le) :
        ‖C (Y 0)‖ ≤ ‖C (Y 0)‖+S/(1-q))
    | succ n ih =>
      have hs := hsegment (n : ℝ) 1 (Nat.cast_nonneg n) (by constructor <;> norm_num)
      simp only [Nat.cast_add,Nat.cast_one,mul_one] at hs ⊢
      have hm := mul_le_mul_of_nonneg_left ih hq0
      have he : (1-q)*(S/(1-q))=S := by field_simp
      have hqnorm := mul_le_mul_of_nonneg_right hq1.le (norm_nonneg (C (Y 0)))
      change ‖C (Y ((n : ℝ)+1))‖ ≤ q*‖C (Y (n : ℝ))‖+S at hs
      nlinarith
  let n : ℕ := ⌊t⌋₊
  let s : ℝ := t-(n : ℝ)
  have hnle : (n : ℝ) ≤ t := Nat.floor_le ht
  have hlt : t < (n : ℝ)+1 := Nat.lt_floor_add_one t
  have hs : s ∈ Icc 0 1 := ⟨by dsimp [s]; linarith,by dsimp [s]; linarith⟩
  have hseg := hsegment (n : ℝ) s (Nat.cast_nonneg n) hs
  have he : (n : ℝ)+s=t := by dsimp [s]; ring
  rw [he] at hseg
  have hexp : Real.exp (-ρ*s) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hs.1])
  have hm := mul_le_mul_of_nonneg_right hexp (norm_nonneg (C (Y (n : ℝ))))
  change ‖C (Y t)‖ ≤ ‖C (Y 0)‖+S/(1-q)+S
  linarith [hn n]

end Contractive

end PBGSO.UniformIntegral
