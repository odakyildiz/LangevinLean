import AverageLMC.PathwiseEnergy

set_option linter.style.header false
noncomputable section
open MeasureTheory
open scoped NNReal RealInnerProductSpace

namespace AverageLMC
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- The paper's gradient-step energy bound integrated in the actual L² space. -/
theorem lp_gradient_step (f : E → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ m f)
    (hLip : LipschitzWith L (gradient f)) (hh : 0 ≤ h) (X Y : Lp E 2 P) :
    ‖X - h • ULA.lpDrift P (gradient f) hLip X - Y‖ ^ 2 ≤
      (1 - m * h) * ‖X - Y‖ ^ 2 +
      2 * h * ((∫ ω, f (Y ω) ∂P) - ∫ ω, f (X ω) ∂P) +
      h ^ 2 * ‖ULA.lpDrift P (gradient f) hLip X‖ ^ 2 := by
  have hs := lp_strong_gradient_support P f m L hf hsc hLip Y X
  have hn : ‖Y - X‖ = ‖X - Y‖ := norm_sub_rev Y X
  have hi : ⟪Y - X, ULA.lpDrift P (gradient f) hLip X⟫ =
      -⟪X - Y, ULA.lpDrift P (gradient f) hLip X⟫ := by
    rw [show Y - X = -(X - Y) by module, inner_neg_left]
  rw [hn, hi] at hs
  have hscaled := mul_le_mul_of_nonneg_left hs hh
  rw [show X - h • ULA.lpDrift P (gradient f) hLip X - Y =
    (X - Y) - h • ULA.lpDrift P (gradient f) hLip X by module,
    norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hh]
  nlinarith

/-- The deterministic descent inequality integrated in L², with all potential
and score integrability derived from the Lipschitz gradient. -/
theorem lp_gradient_descent (f : E → ℝ) (h : ℝ) (L : ℝ≥0)
    (hf : Differentiable ℝ f) (hLip : LipschitzWith L (gradient f))
    (hh : 0 ≤ h) (X : Lp E 2 P) :
    2 * ((∫ ω, f ((X - h • ULA.lpDrift P (gradient f) hLip X) ω) ∂P) -
      ∫ ω, f (X ω) ∂P) ≤
      -h * (2 - h * (L : ℝ)) * ‖ULA.lpDrift P (gradient f) hLip X‖ ^ 2 := by
  let G := ULA.lpDrift P (gradient f) hLip X
  have hiX := integrable_smooth_compLp P f L hf hLip X
  have hiY := integrable_smooth_compLp P f L hf hLip (X - h • G)
  have hiG := (Lp.memLp G).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hpoint : ∀ᵐ ω ∂P, 2 * (f ((X - h • G) ω) - f (X ω)) ≤
      (-h * (2 - h * (L : ℝ))) * ‖G ω‖ ^ 2 := by
    filter_upwards [Lp.coeFn_sub X (h • G), Lp.coeFn_smul h G,
      ULA.lpDrift_coe P (gradient f) hLip X] with ω hsub hsmul hG
    simp only [hsub, Pi.sub_apply, hsmul, Pi.smul_apply]
    change 2 * (f (X ω - h • G ω) - f (X ω)) ≤
      -h * (2 - h * (L : ℝ)) * ‖G ω‖ ^ 2
    change G ω = gradient f (X ω) at hG
    rw [hG]
    exact gradient_descent f L hf hLip (X ω) h hh
  have hb := integral_mono_ae ((hiY.sub hiX).const_mul 2)
    (hiG.const_mul (-h * (2 - h * (L : ℝ)))) hpoint
  change (∫ ω, 2 * (f ((X - h • G) ω) - f (X ω)) ∂P) ≤
    ∫ ω, (-h * (2 - h * (L : ℝ))) * ‖G ω‖ ^ 2 ∂P at hb
  rw [integral_const_mul, integral_sub hiY hiX, integral_const_mul,
    ← ProximalLangevin.lp_norm_sq_eq_integral P] at hb
  exact hb

end AverageLMC
