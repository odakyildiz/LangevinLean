import PBGSO.MomentumUniformDefect
import PBGSO.UniformDiscrete

/-! # Actual time-uniform M-MFPO discretisation
The exact step maps are constructed by Picard iteration. Their contraction,
the affine numerical defect, and every exact reference moment are derived.
Numerical contractivity and numerical moments are conclusions, not premises.
-/
noncomputable section
open MeasureTheory Set
open scoped NNReal InnerProductSpace
namespace PBGSO.Methods
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The explicit uniform exact-reference radius in metric coordinates. -/
def momentumUniformReferenceRadius (L γ : ℝ≥0) (fzero β ρ : ℝ)
    (C : (E × E) →L[ℝ] H) (initial : E × E) : ℝ :=
  let S := ‖C‖ * UniformIntegral.radius (L+γ+1) fzero β 0
  ‖C initial‖ + S / (1-Real.exp (-ρ)) + S

/-- The affine defect coefficients in the actual contracting metric. -/
def momentumMetricDefect (L γ : ℝ≥0) (fzero Ξ β : ℝ)
    (C : (E × E) →L[ℝ] H) (m : ℝ) : ℝ × ℝ :=
  (‖C‖ * (momentumUniformDefect L γ fzero Ξ β).1,
    ‖C‖ * (momentumUniformDefect L γ fzero Ξ β).2 / m)

/-- The complete explicit constant multiplying sqrt(h). -/
def momentumUniformErrorConstant (L γ : ℝ≥0) (fzero Ξ β ρ : ℝ)
    (C : (E × E) →L[ℝ] H) (m : ℝ) (initial : E × E) : ℝ :=
  let ab := momentumMetricDefect L γ fzero Ξ β C m
  4 * (ab.1 + ab.2 * momentumUniformReferenceRadius L γ fzero β ρ C initial) / (ρ*m)

/-- Time-uniform error for the actual OBABO iteration and original kinetic
integral trajectory. Primitive global force regularity, original drift
monotonicity, metric coercivity and the actual input/innovation identities
imply the bound. There is no reference-moment, local-defect, numerical
stability or numerical contraction hypothesis. -/
theorem obabo_time_uniform (G : E → E) (L γ : ℝ≥0) (hLip : LipschitzWith L G)
    (C : (E × E) →L[ℝ] H) (m ρ : ℝ) (hm : 0 < m) (hρ : 0 < ρ)
    (hcoerc : ∀ x, m*‖x‖ ≤ ‖C x‖)
    (hmono : ∀ x y, ⟪C (x-y),C (uniformMomentumDrift G γ x-uniformMomentumDrift G γ y)⟫_ℝ
      ≤ -ρ*‖C (x-y)‖^2)
    (Y : ℝ → E × E) (b : ℝ → E) (hY : Continuous Y) (hb : Continuous b)
    (heq : ∀ t, 0 ≤ t → Y t-Y 0 =
      (∫ r in 0..t, uniformMomentumDrift G γ (Y r)) + (b t,0))
    (Ξ β : ℝ) (hΞ : 0 ≤ Ξ) (hβ : 0 ≤ β)
    (hincrement : ∀ a s, 0 ≤ a → s ∈ Icc 0 1 →
      ‖b (a+s)-b a‖ ≤ β*Real.sqrt s)
    (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) (hρh : ρ*h ≤ 1)
    (hsmall : (momentumMetricDefect L γ ‖G 0‖ Ξ β C m).2 * Real.sqrt h ≤ ρ/4)
    (ξ : ℕ → E × E) (hξ : ∀ k, ‖(ξ k).1‖ ≤ Ξ ∧ ‖(ξ k).2‖ ≤ Ξ)
    (hbrown : ∀ k : ℕ, b ((k : ℝ)*h+h)-b ((k : ℝ)*h) =
      Real.sqrt ((γ : ℝ)*h) • ((ξ k).1+(ξ k).2)) (n : ℕ) :
    ‖trajectory (fun s r ↦ KineticLangevin.obaboStep G h (Real.exp (-(γ : ℝ)*h/2))
      (Real.sqrt (1-Real.exp (-(γ : ℝ)*h))) s r.1 r.2) ξ (Y 0) n - Y (n*h)‖ ≤
      momentumUniformErrorConstant L γ ‖G 0‖ Ξ β ρ C m (Y 0)*Real.sqrt h := by
  let f := uniformMomentumDrift G γ
  let K : ℝ≥0 := L+γ+1
  have hf : LipschitzWith K f := uniformMomentumDrift_lipschitz G L γ hLip
  let B : ℝ → E × E := fun t ↦ (b t,0)
  have hB : Continuous B := hb.prodMk continuous_const
  let shifted : ℕ → ℝ → E × E := fun k t ↦ (b ((k : ℝ)*h+t)-b ((k : ℝ)*h),0)
  have hscont (k : ℕ) : Continuous (shifted k) :=
    ((hb.comp (continuous_const.add continuous_id)).sub continuous_const).prodMk continuous_const
  have hexists (k : ℕ) (x : E × E) : ∃ Z : ℝ → E × E,
      Continuous Z ∧ Z 0=x ∧ ∀ t ∈ Icc 0 h,
        Z t-Z 0=(∫ r in 0..t, f (Z r))+shifted k t := by
    obtain ⟨Z,hZ,hZ0,hZe⟩ := ULA.exists_langevin_integral
      (fun x ↦ -f x) K hf.neg x (shifted k) (hscont k) (by simp [shifted]) h hh.le
    refine ⟨Z,hZ,hZ0,?_⟩
    intro t ht
    simpa only [hZ0,intervalIntegral.integral_neg,neg_neg] using hZe t ht
  choose Z hZ hZ0 hZe using hexists
  let Φ : ℕ → (E × E) → E × E := fun k x ↦ Z k x h
  let A : ℕ → (E × E) → E × E := fun k x ↦
    KineticLangevin.obaboStep G h (Real.exp (-(γ : ℝ)*h/2))
      (Real.sqrt (1-Real.exp (-(γ : ℝ)*h))) x (ξ k).1 (ξ k).2
  let X : ℕ → E × E := trajectory (fun s r ↦ KineticLangevin.obaboStep G h
    (Real.exp (-(γ : ℝ)*h/2)) (Real.sqrt (1-Real.exp (-(γ : ℝ)*h))) s r.1 r.2) ξ (Y 0)
  let Ygrid : ℕ → E × E := fun k ↦ Y ((k : ℝ)*h)
  let ab := momentumMetricDefect L γ ‖G 0‖ Ξ β C m
  let R := momentumUniformReferenceRadius L γ ‖G 0‖ β ρ C (Y 0)
  have hab := momentumUniformDefect_nonneg L γ ‖G 0‖ Ξ β (norm_nonneg _) hΞ hβ
  have ha0 := hab.1
  have hb0 := hab.2
  have ha : 0 ≤ ab.1 := by dsimp [ab,momentumMetricDefect]; positivity
  have hb' : 0 ≤ ab.2 := by dsimp [ab,momentumMetricDefect]; positivity
  have hgap : 0 < 1-Real.exp (-ρ) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hrad := UniformIntegral.radius_nonneg K (norm_nonneg (G 0)) hβ (le_refl 0)
  have hR : 0 ≤ R := by dsimp [R,momentumUniformReferenceRadius]; positivity
  have hcontract (k : ℕ) (x y : E × E) :
      ‖C (Φ k x-Φ k y)‖ ≤ Real.exp (-ρ*h)*‖C (x-y)‖ := by
    have hc := UniformIntegral.contraction f K hf C ρ hmono (Z k x) (Z k y)
      (shifted k) (hZ k x) (hZ k y) h (hZe k x) (hZe k y) h ⟨hh.le,le_rfl⟩
    simpa only [Φ,hZ0] using hc
  have hseg (k : ℕ) (t : ℝ) (ht : t ∈ Icc 0 h) :
      Y ((k : ℝ)*h+t)-Y ((k : ℝ)*h+0) =
        (∫ r in 0..t, f (Y ((k : ℝ)*h+r)))+shifted k t := by
    simpa only [B,shifted,add_zero,Prod.mk_sub_mk,sub_zero] using
      MethodSegments.integral_shift Y (fun r ↦ f (Y r)) B (hf.continuous.comp hY)
        heq ((k : ℝ)*h) t (mul_nonneg (Nat.cast_nonneg k) hh.le) ht.1
  have hYstep (k : ℕ) : Ygrid (k+1)=Φ k (Ygrid k) := by
    have hc := UniformIntegral.contraction f K hf C ρ hmono (Z k (Ygrid k))
      (fun r ↦ Y ((k : ℝ)*h+r)) (shifted k) (hZ k (Ygrid k))
      (hY.comp (continuous_const.add continuous_id)) h (hZe k (Ygrid k)) (hseg k)
      h ⟨hh.le,le_rfl⟩
    simp only [hZ0,add_zero,Ygrid,sub_self,map_zero,norm_zero,mul_zero] at hc
    have hnorm := hcoerc (Z k (Ygrid k) h-Y ((k : ℝ)*h+h))
    have he : Z k (Ygrid k) h=Y ((k : ℝ)*h+h) := by
      apply sub_eq_zero.mp
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (Z k (Ygrid k) h-Y ((k : ℝ)*h+h))]
    change Y (((k+1 : ℕ) : ℝ)*h)=Z k (Ygrid k) h
    rw [he]
    congr 1
    push_cast
    ring
  have hdefect (k : ℕ) (x : E × E) :
      ‖C (A k x-Φ k x)‖ ≤ (h*Real.sqrt h)*(ab.1+ab.2*‖C x‖) := by
    have hl := obabo_affine_local_defect G L γ hLip (Z k x)
      (fun t ↦ b ((k : ℝ)*h+t)-b ((k : ℝ)*h)) (hZ k x)
      ((hb.comp (continuous_const.add continuous_id)).sub continuous_const)
      Ξ β h hΞ hβ hh hh1 (hZe k x)
      (fun t ht ↦ hincrement _ t (mul_nonneg (Nat.cast_nonneg k) hh.le) ⟨ht.1,ht.2.trans hh1⟩)
      (ξ k).1 (ξ k).2 (hξ k).1 (hξ k).2 (hbrown k)
    rw [hZ0] at hl
    have hmetric := (transformed_norm_sub_le_phaseError C (A k x) (Φ k x)).trans
      (mul_le_mul_of_nonneg_left hl (norm_nonneg C))
    have hxn : ‖x‖ ≤ ‖C x‖/m := (le_div_iff₀ hm).mpr (by simpa only [mul_comm] using hcoerc x)
    calc
      _ ≤ ‖C‖ * (((momentumUniformDefect L γ ‖G 0‖ Ξ β).1+
          (momentumUniformDefect L γ ‖G 0‖ Ξ β).2 * ‖x‖)*h*Real.sqrt h) := hmetric
      _ ≤ ‖C‖ * (((momentumUniformDefect L γ ‖G 0‖ Ξ β).1+
          (momentumUniformDefect L γ ‖G 0‖ Ξ β).2 * (‖C x‖/m))*h*Real.sqrt h) := by gcongr
      _ = _ := by dsimp [ab,momentumMetricDefect]; ring
  have href (k : ℕ) : ‖C (Ygrid k)‖ ≤ R := by
    have hr := UniformIntegral.uniform_moment f K hf C ρ hρ hmono Y B hY hB heq β hβ
      (by intro a s ha hs; simpa [B] using hincrement a s ha hs) ((k : ℝ)*h)
      (mul_nonneg (Nat.cast_nonneg k) hh.le)
    simpa only [f,uniformMomentumDrift_zero_norm,R,momentumUniformReferenceRadius,Ygrid,K] using hr
  have he := UniformDiscrete.one_step_same_initial_uniform_norm C A Φ X Ygrid
    ρ h ab.1 ab.2 R m hρ hh ha hb' hR hm hcoerc hρh hsmall
    (fun k ↦ rfl) hYstep hcontract hdefect href (by simp [X,Ygrid,trajectory]) n
  change ‖X n-Ygrid n‖ ≤ _
  apply he.trans_eq
  dsimp [momentumUniformErrorConstant,ab,R]
  ring
end PBGSO.Methods
