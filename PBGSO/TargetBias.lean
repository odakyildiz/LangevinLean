import PBGSO.GeneralProcess

/-! # Bias caused by changing the sampler target

The hybrid HOL method observes the original force while sampling a smoothed
law. It need not have the original objective's critical point. Strong
monotonicity of the original gradient and an actual coupling of the original
and surrogate sampler laws give the explicit bias bound below. No smoothing
coupling bound or validity of the manuscript's TV prior is silently assumed.
-/

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace NNReal
namespace PBGSO

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A residual gradient bounds distance to a strongly monotone critical point. -/
theorem critical_point_residual_bound (g : H → H) (m δ : ℝ) (hm : 0 < m)
    (a star : H) (hstar : g star = 0)
    (hmono : m * ‖a - star‖ ^ 2 ≤ ⟪a - star, g a - g star⟫)
    (hresidual : ‖g a‖ ≤ δ) : ‖a - star‖ ≤ δ / m := by
  have hinner := real_inner_le_norm (a - star) (g a)
  rw [hstar, sub_zero] at hmono
  have hupper := mul_le_mul_of_nonneg_left hresidual (norm_nonneg (a - star))
  by_cases ha : ‖a - star‖ = 0
  · rw [ha]
    have hδ : 0 ≤ δ := (norm_nonneg (g a)).trans hresidual
    exact div_nonneg hδ hm.le
  · have hp : 0 < ‖a - star‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm ha)
    have hprod : m * ‖a - star‖ ≤ δ := by nlinarith
    exact (le_div_iff₀ hm).mpr (by nlinarith)

section CoupledTargets
variable {Ω Z : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [CompleteSpace H]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- Actual coupled sampler variables control the difference between their
Bochner force expectations. Independence is neither needed nor assumed. -/
theorem coupled_observation_expectation_bound (f : Z → H) (L : ℝ≥0)
    (hf : LipschitzWith L f) (X Y : Lp Z 2 Q) :
    ‖(∫ ω, f (X ω) ∂Q) - (∫ ω, f (Y ω) ∂Q)‖ ≤ (L : ℝ) * ‖X - Y‖ := by
  have hX : (∫ ω, f (X ω) ∂Q) =
      ProximalLangevin.lpExpectationCLM Q (liftMap Q f hf X) :=
    (integral_congr_ae (liftMap_coe Q f hf X)).symm
  have hY : (∫ ω, f (Y ω) ∂Q) =
      ProximalLangevin.lpExpectationCLM Q (liftMap Q f hf Y) :=
    (integral_congr_ae (liftMap_coe Q f hf Y)).symm
  rw [hX, hY, ← map_sub]
  exact (ProximalLangevin.lpExpectationCLM_norm_le Q _).trans
    ((liftMap_lipschitz Q f hf).norm_sub_le X Y)

/-- Explicit hybrid-target bias. `X` represents the original target at `a`,
`Y` its surrogate. The original gradient identity and surrogate stationarity
are explicit, and the true objective's gradient must be strongly monotone.
Any separately proved coupling radius epsilon gives bias at most L epsilon/m. -/
theorem hybrid_target_bias (g : H → H) (f : Z → H) (L : ℝ≥0)
    (hf : LipschitzWith L f) (m ε : ℝ) (hm : 0 < m)
    (a star : H) (hstar : g star = 0)
    (hmono : m * ‖a - star‖ ^ 2 ≤ ⟪a - star, g a - g star⟫)
    (X Y : Lp Z 2 Q)
    (hgradient : g a = ∫ ω, f (X ω) ∂Q)
    (hsurrogate : (∫ ω, f (Y ω) ∂Q) = 0)
    (hcoupling : ‖X - Y‖ ≤ ε) :
    ‖a - star‖ ≤ (L : ℝ) * ε / m := by
  apply critical_point_residual_bound g m ((L : ℝ) * ε) hm a star hstar hmono
  have he := coupled_observation_expectation_bound Q f L hf X Y
  rw [hsurrogate, sub_zero, ← hgradient] at he
  exact he.trans (mul_le_mul_of_nonneg_left hcoupling L.coe_nonneg)

end CoupledTargets
end PBGSO
