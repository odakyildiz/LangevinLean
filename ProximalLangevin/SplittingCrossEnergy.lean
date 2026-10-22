import ProximalLangevin.SplittingProcess
import ProximalLangevin.SplittingOrthogonality

/-!
# Nonsmooth energy cancellation in the actual synchronous splitting argument

Convex supporting planes, stationary reference expectations, and future-noise
orthogonality give an error of order `h² + h*delta`. This estimate never
uses the inverse smoothing scale as a drift-increment constant.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped NNReal RealInnerProductSpace
namespace ProximalLangevin

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (P : Measure Ω) [IsProbabilityMeasure P]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- A finite uniform value gap controls its actual expectation. -/
theorem expectation_gap_le {f e : E → ℝ} {Kf Ke : ℝ≥0}
    (hf : LipschitzWith Kf f) (he : LipschitzWith Ke e)
    (delta : ℝ) (hgap : ∀ x, f x ≤ e x + delta) (X : Lp E 2 P) :
    (∫ ω, f (X ω) ∂P) - (∫ ω, e (X ω) ∂P) ≤ delta := by
  have hi := integral_mono (integrable_lipschitz_compLp P hf X)
    ((integrable_lipschitz_compLp P he X).add (integrable_const delta)) (fun ω => hgap _)
  simp only [Pi.add_apply] at hi
  rw [integral_add (f := fun ω => e (X ω)) (g := fun _ => delta)
    (integrable_lipschitz_compLp P he X) (integrable_const delta),
    integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
  linarith

/-- The integrated reference-gradient cross term cancels the original
nonsmooth energy up to a finite value gap and a drift error of order `h²`.
The orthogonality premise is instantiated by the actual Brownian construction
in `lp_langevin_future_inner_zero`, not by a convergence assumption. -/
theorem splitting_cross_energy_le {f e : E → ℝ}
    (he : Differentiable ℝ e) (hconv : ConvexOn ℝ univ e)
    {L Ke Kf Lg : ℝ≥0} (hegrad : LipschitzWith L (gradient e))
    (heLip : LipschitzWith Ke e) (hfLip : LipschitzWith Kf f)
    (delta : ℝ) (hgap : ∀ x, e x ≤ f x ∧ f x ≤ e x + delta)
    (g : Lp E 2 P → Lp E 2 P) (hg : LipschitzWith Lg g)
    (Y B : ℝ → Lp E 2 P) (hY : Continuous Y) (h : ℝ) (hh : 0 ≤ h)
    (G K : ℝ) (hG : 0 ≤ G) (hK : 0 ≤ K)
    (hgBound : ∀ t ∈ Icc 0 h, ‖g (Y t)‖ ≤ G)
    (hbBound : ∀ t ∈ Icc 0 h, ‖ULA.lpDrift P (gradient e) hegrad (Y t)‖ ≤ K)
    (hYe : ∀ t ∈ Icc 0 h, Y t - Y 0 = -(∫ s in 0..t, g (Y s)) + B t)
    (horth : ∀ t ∈ Icc 0 h,
      ⟪ULA.lpDrift P (gradient e) hegrad (Y t), B h - B t⟫ = 0)
    (hstationary : ∀ t ∈ Icc 0 h,
      (∫ ω, e (Y t ω) ∂P) = ∫ ω, e (Y h ω) ∂P)
    (S : Lp E 2 P) :
    2 * ⟪S - Y h, ∫ t in 0..h, ULA.lpDrift P (gradient e) hegrad (Y t)⟫ -
      2 * h * ((∫ ω, f (S ω) ∂P) - ∫ ω, f (Y h ω) ∂P) ≤
      2 * h * delta + 2 * h ^ 2 * G * K := by
  let b := fun t => ULA.lpDrift P (gradient e) hegrad (Y t)
  have hbCont : Continuous b := (ULA.lpDrift_lipschitz P (gradient e) hegrad).continuous.comp hY
  have hcCont : Continuous (fun t => ⟪S - Y h, b t⟫) := continuous_const.inner hbCont
  have hpoint (t : ℝ) (ht : t ∈ Icc 0 h) :
      ⟪S - Y h, b t⟫ ≤
        (∫ ω, e (S ω) ∂P) - (∫ ω, e (Y h ω) ∂P) + h * G * K := by
    have hs := lp_convex_gradient_cross P he hconv hegrad heLip S (Y t) (Y h)
    have hfut := reference_future_inner_le g hg Y B hY h t ht.1 ht.2 G K hG hK
      hgBound hYe (b t) (hbBound t ht) (horth t ht)
    rw [hstationary t ht] at hs
    have hcoarse : (h - t) * G * K ≤ h * G * K := by
      nlinarith [mul_nonneg hG hK, mul_nonneg ht.1 (mul_nonneg hG hK)]
    exact hs.trans (add_le_add le_rfl (hfut.trans hcoarse))
  have hi := intervalIntegral.integral_mono_on (μ := volume) hh (hcCont.intervalIntegrable 0 h)
    intervalIntegrable_const hpoint
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hi
  have hinner := (innerSL ℝ (S - Y h)).intervalIntegral_comp_comm (μ := volume)
    (hbCont.intervalIntegrable 0 h)
  change (∫ t in 0..h, ⟪S - Y h, b t⟫) = ⟪S - Y h, ∫ t in 0..h, b t⟫ at hinner
  rw [hinner] at hi
  have hS := expectation_gap_le P heLip hfLip 0 (fun x => by simpa using (hgap x).1) S
  have hYgap := expectation_gap_le P hfLip heLip delta (fun x => (hgap x).2) (Y h)
  change 2 * ⟪S - Y h, ∫ t in 0..h, b t⟫ - _ ≤ _
  have hsum : ((∫ ω, e (S ω) ∂P) - ∫ ω, e (Y h ω) ∂P) -
      ((∫ ω, f (S ω) ∂P) - ∫ ω, f (Y h ω) ∂P) ≤ delta := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2 * h by positivity)
  linear_combination 2 * hi + hmul

end ProximalLangevin
