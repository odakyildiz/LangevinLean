import AverageLMC.GradientStep
import ProximalLangevin.SplittingL2Energy
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.style.header false
noncomputable section
open MeasureTheory Set
open scoped NNReal RealInnerProductSpace
namespace AverageLMC

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- Smooth potentials have at most quadratic growth, hence are integrable on L². -/
theorem integrable_smooth_compLp (f : E → ℝ) (L : ℝ≥0)
    (hf : Differentiable ℝ f) (hLip : LipschitzWith L (gradient f))
    (X : Lp E 2 P) : Integrable (fun ω ↦ f (X ω)) P := by
  have hu (x : E) := ULA.Analysis.smooth_upper_bound f L hf hLip 0 x
  have hneg : gradient (fun x ↦ -f x) = fun x ↦ -gradient f x := by
    funext x
    apply (InnerProductSpace.toDual ℝ E).injective
    simp [toDual_gradient, fderiv_neg]
  have hLn : LipschitzWith L (gradient (fun x ↦ -f x)) := by
    rw [hneg]
    exact hLip.neg
  have hl (x : E) := ULA.Analysis.smooth_upper_bound (fun x ↦ -f x) L hf.neg hLn 0 x
  have hgrowth (x : E) : ‖f x‖ ≤ |f 0| + ‖gradient f 0‖ * ‖x‖ +
      (L : ℝ) / 2 * ‖x‖ ^ 2 := by
    have hup := hu x
    have hlo := hl x
    simp only [sub_zero, hneg, inner_neg_left] at hup hlo
    have hi := abs_real_inner_le_norm (gradient f 0) x
    rw [Real.norm_eq_abs, abs_le] at *
    constructor <;> nlinarith [le_abs_self (f 0), neg_abs_le (f 0)]
  have hn : Integrable (fun ω ↦ ‖X ω‖) P :=
    ((Lp.memLp X).integrable (by norm_num)).norm
  have hn2 : Integrable (fun ω ↦ ‖X ω‖ ^ 2) P :=
    (Lp.memLp X).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  exact (((integrable_const |f 0|).add (hn.const_mul _)).add (hn2.const_mul _)).mono'
    (hf.continuous.aestronglyMeasurable.comp_aemeasurable
      (Lp.aestronglyMeasurable X).aemeasurable) (ae_of_all _ fun ω ↦ hgrowth (X ω))

/-- The same integrability statement for an arbitrary square-integrable representative. -/
theorem integrable_smooth_comp (f : E → ℝ) (L : ℝ≥0)
    (hf : Differentiable ℝ f) (hLip : LipschitzWith L (gradient f))
    (X : Ω → E) (hX : MemLp X 2 P) : Integrable (fun ω ↦ f (X ω)) P := by
  apply (integrable_smooth_compLp P f L hf hLip (hX.toLp X)).congr
  filter_upwards [hX.coeFn_toLp] with ω hω
  rw [hω]

/-- The strong supporting-plane inequality integrated on the actual L² space. -/
theorem lp_strong_gradient_support (f : E → ℝ) (m : ℝ) (L : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith L (gradient f)) (X Y : Lp E 2 P) :
    2 * ⟪X - Y, ULA.lpDrift P (gradient f) hLip Y⟫ ≤
      2 * ((∫ ω, f (X ω) ∂P) - ∫ ω, f (Y ω) ∂P) - m * ‖X - Y‖ ^ 2 := by
  have hiX := integrable_smooth_compLp P f L hf hLip X
  have hiY := integrable_smooth_compLp P f L hf hLip Y
  have hn : Integrable (fun ω ↦ ‖(X - Y) ω‖ ^ 2) P :=
    (Lp.memLp (X - Y)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hright := ((hiX.sub hiY).const_mul 2).sub (hn.const_mul m)
  have hi := integral_mono_ae ((L2.integrable_inner (X - Y)
      (ULA.lpDrift P (gradient f) hLip Y)).const_mul 2) hright (show
      ∀ᵐ ω ∂P, 2 * ⟪(X - Y) ω, ULA.lpDrift P (gradient f) hLip Y ω⟫ ≤
      2 * (f (X ω) - f (Y ω)) - m * ‖(X - Y) ω‖ ^ 2 from by
    filter_upwards [Lp.coeFn_sub X Y, ULA.lpDrift_coe P (gradient f) hLip Y]
      with ω hsub hg
    simp only [hsub, hg, Pi.sub_apply]
    have hs := ULA.strong_first_order hf hsc (Y ω) (X ω)
    rw [real_inner_comm] at hs
    linarith)
  change (∫ ω, 2 * ⟪(X - Y) ω, ULA.lpDrift P (gradient f) hLip Y ω⟫ ∂P) ≤
    ∫ ω, 2 * (f (X ω) - f (Y ω)) - m * ‖(X - Y) ω‖ ^ 2 ∂P at hi
  have heq : (∫ ω, 2 * (f (X ω) - f (Y ω)) - m * ‖(X - Y) ω‖ ^ 2 ∂P) =
      2 * ((∫ ω, f (X ω) ∂P) - ∫ ω, f (Y ω) ∂P) - m * ‖X - Y‖ ^ 2 := by
    rw [integral_sub]
    · rw [integral_const_mul, integral_sub hiX hiY, integral_const_mul,
        ← ProximalLangevin.lp_norm_sq_eq_integral P]
    · exact (hiX.sub hiY).const_mul 2
    · exact hn.const_mul m
  rw [integral_const_mul, ← L2.inner_def, heq] at hi
  exact hi

omit [MeasurableSpace E] [BorelSpace E] [IsProbabilityMeasure P] in
/-- Exact energy identity for the noise-cancelled integral equation. -/
theorem integral_curve_norm_sq (g : ℝ → E) (hg : Continuous g) (A : E) (h : ℝ) :
    ‖A + ∫ s in 0..h, g s‖ ^ 2 = ‖A‖ ^ 2 +
      ∫ t in 0..h, 2 * ⟪A + ∫ s in 0..t, g s, g t⟫ := by
  let G := fun t ↦ A + ∫ s in 0..t, g s
  have hd (t : ℝ) : HasDerivAt G (g t) t := by
    exact (intervalIntegral.integral_hasDerivAt_right
      (hg.intervalIntegrable 0 t)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt).const_add A
  have hn (t : ℝ) : HasDerivAt (fun t ↦ ‖G t‖ ^ 2) (2 * ⟪G t, g t⟫) t := by
    simpa [real_inner_comm] using (hd t).norm_sq
  have hG : Continuous G := continuous_iff_continuousAt.mpr fun t ↦ (hd t).continuousAt
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hn t)
    ((continuous_const.mul (hG.inner hg) :
      Continuous (fun t ↦ (2 : ℝ) * ⟪G t, g t⟫)).intervalIntegrable 0 h)
  simpa [G, add_comm] using (eq_add_of_sub_eq he.symm)

/-- The common Brownian noise cancels before differentiating the L² error. -/
theorem langevin_energy_identity (f : E → ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient f)) (X : Lp E 2 P)
    (Y B : ℝ → Lp E 2 P) (hY : Continuous Y) (h : ℝ) (hh : 0 ≤ h)
    (hYe : ∀ t ∈ Icc 0 h, Y t - Y 0 =
      -(∫ s in 0..t, ULA.lpDrift P (gradient f) hLip (Y s)) + B t) :
    ‖X + B h - Y h‖ ^ 2 = ‖X - Y 0‖ ^ 2 +
      ∫ t in 0..h, 2 * ⟪X + B t - Y t, ULA.lpDrift P (gradient f) hLip (Y t)⟫ := by
  let g := fun t ↦ ULA.lpDrift P (gradient f) hLip (Y t)
  have hg : Continuous g := (ULA.lpDrift_lipschitz P (gradient f) hLip).continuous.comp hY
  have he (t : ℝ) (ht : t ∈ Icc 0 h) :
      X + B t - Y t = (X - Y 0) + ∫ s in 0..t, g s := by
    have hy := eq_add_of_sub_eq (hYe t ht)
    rw [hy]
    dsimp [g]
    module
  rw [he h ⟨hh, le_rfl⟩]
  rw [integral_curve_norm_sq g hg (X - Y 0) h]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  change 2 * ⟪(X - Y 0) + ∫ s in 0..t, g s, g t⟫ = _
  rw [← he t (uIcc_of_le hh ▸ ht)]

end AverageLMC
