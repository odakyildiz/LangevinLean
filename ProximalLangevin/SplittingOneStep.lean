import ProximalLangevin.SplittingCrossEnergy

/-!
# A derived one-step synchronous splitting bound

This analytic integration theorem proves the coupling estimate from a genuine
pointwise proximal energy inequality and the actual reference integral equation.
The canonical endpoint constructs every reference, law, and orthogonality input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped NNReal RealInnerProductSpace
namespace ProximalLangevin

/-- Explicit local forcing in the synchronous splitting proof. -/
def splittingCouplingForcing (m h L G noise K delta : ℝ) : ℝ :=
  (1 + (m * h)⁻¹) * (L * h * (G * h + noise * Real.sqrt h)) ^ 2 +
    2 * h * delta + 2 * h ^ 2 * G * K + h ^ 2 * K ^ 2

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- One splitting step compared with an actual smooth stationary reference.
The pointwise energy premise is proved for the actual averaged joint proximal
map; the reference hypotheses are discharged by its canonical Brownian
construction. No stochastic error recurrence is assumed. -/
theorem splitting_one_step_of_integral_solution
    {f₁ f e : E → ℝ} {T : E → E} {L₁ Le Kf Ke LT K : ℝ≥0}
    (hf₁ : Differentiable ℝ f₁) (he : Differentiable ℝ e)
    (m h : ℝ) (hm : 0 < m) (hh : 0 < h)
    (hsc : StrongConvexOn univ m f₁)
    (hLip₁ : LipschitzWith L₁ (gradient f₁)) (hmL : m ≤ (L₁ : ℝ))
    (hsmall : h ≤ 2 / (m + (L₁ : ℝ)))
    (heconv : ConvexOn ℝ univ e) (hegrad : LipschitzWith Le (gradient e))
    (heLip : LipschitzWith Ke e) (hfLip : LipschitzWith Kf f)
    (hT : LipschitzWith LT T)
    (henergy : ∀ x y, ‖T x - y‖ ^ 2 ≤
      ‖x - y‖ ^ 2 - 2 * h * (f x - f y) + h ^ 2 * (K : ℝ) ^ 2)
    (delta : ℝ) (hgap : ∀ x, e x ≤ f x ∧ f x ≤ e x + delta)
    (Y B : ℝ → Lp E 2 P) (hY : Continuous Y)
    (G noise : ℝ) (hG : 0 ≤ G) (hnoise : 0 ≤ noise)
    (hgbound : ∀ t ∈ Icc 0 h,
      ‖ULA.lpDrift P (gradient f₁) hLip₁ (Y t) +
        ULA.lpDrift P (gradient e) hegrad (Y t)‖ ≤ G)
    (hbbound : ∀ t ∈ Icc 0 h,
      ‖ULA.lpDrift P (gradient e) hegrad (Y t)‖ ≤ (K : ℝ))
    (hB : ∀ t ∈ Icc 0 h, ‖B t‖ ≤ noise * Real.sqrt t)
    (hYe : ∀ t ∈ Icc 0 h, Y t - Y 0 =
      -(∫ s in 0..t, ULA.lpDrift P (gradient f₁) hLip₁ (Y s) +
        ULA.lpDrift P (gradient e) hegrad (Y s)) + B t)
    (horth : ∀ t ∈ Icc 0 h,
      ⟪ULA.lpDrift P (gradient e) hegrad (Y t), B h - B t⟫ = 0)
    (hstationary : ∀ t ∈ Icc 0 h,
      (∫ ω, e (Y t ω) ∂P) = ∫ ω, e (Y h ω) ∂P)
    (X : Lp E 2 P) :
    ‖ULA.lpDrift P T hT
      (X - h • ULA.lpDrift P (gradient f₁) hLip₁ X + B h) - Y h‖ ^ 2 ≤
      (1 - m * h) * ‖X - Y 0‖ ^ 2 +
        splittingCouplingForcing m h (L₁ : ℝ) G noise (K : ℝ) delta := by
  let a := ULA.lpDrift P (gradient f₁) hLip₁
  let b := ULA.lpDrift P (gradient e) hegrad
  let g := fun Z => a Z + b Z
  have ha : LipschitzWith L₁ a := ULA.lpDrift_lipschitz P (gradient f₁) hLip₁
  have hb : LipschitzWith Le b := ULA.lpDrift_lipschitz P (gradient e) hegrad
  have hg : LipschitzWith (L₁ + Le) g := ha.add hb
  let S := X - h • a X + B h
  let v := (X - h • a X) - (Y 0 - h • a (Y 0))
  let R := ULA.localDefect a Y h
  let H := ∫ t in 0..h, b (Y t)
  have hIa : IntervalIntegrable (fun t => a (Y t)) volume 0 h :=
    (ha.continuous.comp hY).intervalIntegrable _ _
  have hIb : IntervalIntegrable (fun t => b (Y t)) volume 0 h :=
    (hb.continuous.comp hY).intervalIntegrable _ _
  have hYh := hYe h ⟨hh.le, le_rfl⟩
  change Y h - Y 0 = -(∫ t in 0..h, a (Y t) + b (Y t)) + B h at hYh
  rw [intervalIntegral.integral_add hIa hIb] at hYh
  have hR : R = (∫ t in 0..h, a (Y t)) - h • a (Y 0) :=
    ULA.localDefect_eq_integral_sub a Y h hIa
  have hdecomp : S - Y h = v + R + H := by
    dsimp [S, v, H]
    rw [hR, eq_add_of_sub_eq hYh]
    module
  have hnorm : ‖S - Y h‖ ^ 2 =
      ‖v + R‖ ^ 2 + 2 * ⟪S - Y h, H⟫ - ‖H‖ ^ 2 := by
    rw [hdecomp]
    exact norm_sum_rearranged v R H
  have hbase := lp_energy_of_pointwise P hT hfLip h (h ^ 2 * (K : ℝ) ^ 2)
    henergy S (Y h)
  rw [hnorm] at hbase
  have hmh : m * h ≤ 1 := by
    have hs := (le_div_iff₀ (by positivity : 0 < m + (L₁ : ℝ))).mp hsmall
    have hc := mul_le_mul_of_nonneg_right hmL hh.le
    nlinarith
  have hv : ‖v‖ ≤ (1 - m * h) * ‖X - Y 0‖ :=
    ULA.lpDrift_gradient_contract P f₁ m h L₁ hf₁ hsc hLip₁ hmL
      (by positivity) hh.le hsmall X (Y 0)
  have hweighted := norm_add_sq_le_of_contraction (X - Y 0) v R (mul_pos hm hh) hmh hv
  have hRbound := splitting_localDefect_bound a g ha hg Y B hY h hh.le G noise
    hG hnoise hgbound hB hYe
  change ‖R‖ ≤ (L₁ : ℝ) * h * (G * h + noise * Real.sqrt h) at hRbound
  have hR2 : ‖R‖ ^ 2 ≤ ((L₁ : ℝ) * h * (G * h + noise * Real.sqrt h)) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hRbound
  have hRweighted := mul_le_mul_of_nonneg_left hR2
    (show 0 ≤ 1 + (m * h)⁻¹ by positivity)
  have hcross := splitting_cross_energy_le P he heconv hegrad heLip hfLip delta hgap
    g hg Y B hY h hh.le G (K : ℝ) hG K.coe_nonneg hgbound hbbound hYe horth hstationary S
  change 2 * ⟪S - Y h, H⟫ - _ ≤ _ at hcross
  change ‖ULA.lpDrift P T hT S - Y h‖ ^ 2 ≤ _
  unfold splittingCouplingForcing
  nlinarith [sq_nonneg ‖H‖]

end ProximalLangevin
