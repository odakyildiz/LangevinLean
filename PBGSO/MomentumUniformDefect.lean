import PBGSO.MomentumUniformLocal
import PBGSO.UniformIntegralMoments

/-! # Derived affine local defect of actual M-MFPO
The primitive Lipschitz kinetic integral equation and Brownian input modulus
produce every reference radius used by the actual OBABO local error bound.
-/
noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace PBGSO.Methods
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Exact coefficients of the initial-norm dependence of the OBABO defect. -/
def momentumUniformDefect (L γ : ℝ≥0) (fzero Ξ β : ℝ) : ℝ × ℝ :=
  let K : ℝ≥0 := L + γ + 1
  let c := Real.exp ((K : ℝ) + 1)
  momentumDefectAffine L γ Ξ 0 1 fzero L
    (fzero + (K : ℝ) * c * (fzero + β) + β) ((K : ℝ) * c)

/-- The one-step kinetic integral equation implies the original component
position and momentum equations. -/
theorem uniformMomentum_component_equations (G : E → E) (L γ : ℝ≥0)
    (hLip : LipschitzWith L G) (Y : ℝ → E × E) (b : ℝ → E)
    (hY : Continuous Y) (h : ℝ)
    (heq : Y h - Y 0 =
      (∫ r in 0..h, uniformMomentumDrift G γ (Y r)) + (b h, 0)) :
    (Y h).1 = (Y 0).1 -
      (∫ r in 0..h, G (Y r).2 + (γ : ℝ) • (Y r).1) + b h ∧
    (Y h).2 = (Y 0).2 + (∫ r in 0..h, (Y r).1) := by
  have hc := (uniformMomentumDrift_lipschitz G L γ hLip).continuous.comp hY
  have hi : IntervalIntegrable (fun r ↦ uniformMomentumDrift G γ (Y r)) volume 0 h :=
    hc.intervalIntegrable 0 h
  have hp := congrArg Prod.fst heq
  have hq := congrArg Prod.snd heq
  have hip := (ContinuousLinearMap.fst ℝ E E).intervalIntegral_comp_comm hi
  have hiq := (ContinuousLinearMap.snd ℝ E E).intervalIntegral_comp_comm hi
  simp only [Prod.fst_sub, Prod.fst_add] at hp
  simp only [Prod.snd_sub, Prod.snd_add, add_zero] at hq
  change (∫ r in 0..h, (uniformMomentumDrift G γ (Y r)).1) =
    (∫ r in 0..h, uniformMomentumDrift G γ (Y r)).1 at hip
  change (∫ r in 0..h, (uniformMomentumDrift G γ (Y r)).2) =
    (∫ r in 0..h, uniformMomentumDrift G γ (Y r)).2 at hiq
  rw [← hip] at hp
  rw [← hiq] at hq
  have hm : (fun r ↦ (uniformMomentumDrift G γ (Y r)).1) =
      fun r ↦ -(G (Y r).2 + (γ : ℝ) • (Y r).1) := by
    funext r
    dsimp [uniformMomentumDrift]
    module
  change (Y h).1 - (Y 0).1 =
    (∫ r in 0..h, (uniformMomentumDrift G γ (Y r)).1) + b h at hp
  rw [hm, intervalIntegral.integral_neg] at hp
  change (Y h).2 - (Y 0).2 = ∫ r in 0..h, (Y r).1 at hq
  constructor
  · rw [sub_eq_iff_eq_add] at hp
    rw [hp]
    module
  · rw [sub_eq_iff_eq_add] at hq
    rw [hq]
    module

/-- Local consistency with all moment and increment radii derived from the
original equation and the primitive Brownian square-root increment bound.
The right side is explicitly affine in the actual initial norm. -/
theorem obabo_affine_local_defect (G : E → E) (L γ : ℝ≥0)
    (hLip : LipschitzWith L G) (Y : ℝ → E × E) (b : ℝ → E)
    (hY : Continuous Y) (hb : Continuous b)
    (Ξ β h : ℝ) (hΞ : 0 ≤ Ξ) (hβ : 0 ≤ β) (hh : 0 < h) (hh1 : h ≤ 1)
    (heq : ∀ t ∈ Icc 0 h, Y t - Y 0 =
      (∫ r in 0..t, uniformMomentumDrift G γ (Y r)) + (b t, 0))
    (hinput : ∀ t ∈ Icc 0 h, ‖b t‖ ≤ β * Real.sqrt t)
    (ξ ξ' : E) (hξ : ‖ξ‖ ≤ Ξ) (hξ' : ‖ξ'‖ ≤ Ξ)
    (hbrown : b h = Real.sqrt ((γ : ℝ) * h) • (ξ + ξ')) :
    phaseError
      (KineticLangevin.obaboStep G h (Real.exp (-(γ : ℝ) * h / 2))
        (Real.sqrt (1 - Real.exp (-(γ : ℝ) * h))) (Y 0) ξ ξ')
      (Y h) ≤
      ((momentumUniformDefect L γ ‖G 0‖ Ξ β).1 +
        (momentumUniformDefect L γ ‖G 0‖ Ξ β).2 * ‖Y 0‖) * h * Real.sqrt h := by
  let K : ℝ≥0 := L + γ + 1
  let R := ‖G 0‖ + (K : ℝ) * UniformIntegral.radius K ‖G 0‖ β ‖Y 0‖ + β
  have hreg := UniformIntegral.local_regularity (uniformMomentumDrift G γ) K
    (uniformMomentumDrift_lipschitz G L γ hLip) Y (fun t ↦ (b t, 0)) hY
    (hb.prodMk continuous_const) h β hh.le hh1 hβ heq
    (by intro t ht; simpa using hinput t ht)
  simp only [uniformMomentumDrift_zero_norm] at hreg
  have hrad : 0 ≤ UniformIntegral.radius K ‖G 0‖ β ‖Y 0‖ :=
    UniformIntegral.radius_nonneg K (norm_nonneg _) hβ (norm_nonneg _)
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hmod (t : ℝ) (ht : t ∈ Icc 0 h) :
      ‖(Y t).1 - (Y 0).1‖ ≤ R * Real.sqrt t ∧
      ‖(Y t).2 - (Y 0).2‖ ≤ R * Real.sqrt t :=
    ⟨(norm_fst_le (Y t-Y 0)).trans (hreg t ht).2.2,
      (norm_snd_le (Y t-Y 0)).trans (hreg t ht).2.2⟩
  have hf : ‖G (Y 0).2‖ ≤ ‖G 0‖ + (L : ℝ) * ‖Y 0‖ := by
    exact UniformIntegral.drift_bound G L hLip (Y 0).2 ‖Y 0‖ (norm_snd_le _)
  have hc : Continuous (fun t ↦ G (Y t).2 + (γ : ℝ) • (Y t).1) :=
    (hLip.continuous.comp (continuous_snd.comp hY)).add
      ((continuous_fst.comp hY).const_smul _)
  have he := uniformMomentum_component_equations G L γ hLip Y b hY h (heq h ⟨hh.le,le_rfl⟩)
  have hlocal := obabo_integral_local_sqrt_bound G L γ h ‖Y 0‖
    (‖G 0‖ + (L : ℝ)*‖Y 0‖) Ξ R L.coe_nonneg γ.coe_nonneg hh hh1
    (norm_nonneg _) (by positivity) hΞ hR (fun x y ↦ hLip.norm_sub_le x y)
    (fun t ↦ (Y t).1) (fun t ↦ (Y t).2) ξ ξ' (b h)
    ((continuous_fst.comp hY).intervalIntegrable 0 h) (hc.intervalIntegrable 0 h)
    he.1 he.2 hmod (norm_fst_le _) hf hξ hξ' hbrown
  have hconstant : momentumLocalDefectConstant L γ ‖Y 0‖
      (‖G 0‖+(L : ℝ)*‖Y 0‖) Ξ R =
      (momentumUniformDefect L γ ‖G 0‖ Ξ β).1 +
        (momentumUniformDefect L γ ‖G 0‖ Ξ β).2 * ‖Y 0‖ := by
    unfold R UniformIntegral.radius momentumUniformDefect momentumDefectAffine
      momentumLocalDefectConstant momentumLocalConsistencyConstant
    dsimp [K]
    ring
  rw [hconstant] at hlocal
  exact hlocal

/-- Both explicit affine consistency coefficients are nonnegative. -/
theorem momentumUniformDefect_nonneg (L γ : ℝ≥0) (fzero Ξ β : ℝ)
    (hfzero : 0 ≤ fzero) (hΞ : 0 ≤ Ξ) (hβ : 0 ≤ β) :
    0 ≤ (momentumUniformDefect L γ fzero Ξ β).1 ∧
      0 ≤ (momentumUniformDefect L γ fzero Ξ β).2 := by
  unfold momentumUniformDefect
  apply momentumDefectAffine_nonneg L γ Ξ 0 1 fzero L _ _
    L.coe_nonneg γ.coe_nonneg hΞ (le_refl 0) (by norm_num) hfzero L.coe_nonneg
  · positivity
  · positivity

omit [CompleteSpace E] in
/-- A metric coordinate map converts the actual phase consistency error
into its Hilbert norm. The physical phase norm is bounded by its sum norm. -/
theorem transformed_norm_sub_le_phaseError
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (C : (E × E) →L[ℝ] H) (z w : E × E) :
    ‖C (z-w)‖ ≤ ‖C‖ * phaseError z w := by
  apply (C.le_opNorm (z-w)).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg C)
  change max ‖z.1-w.1‖ ‖z.2-w.2‖ ≤ ‖z.1-w.1‖+‖z.2-w.2‖
  exact max_le (le_add_of_nonneg_right (norm_nonneg _))
    (le_add_of_nonneg_left (norm_nonneg _))

end PBGSO.Methods
