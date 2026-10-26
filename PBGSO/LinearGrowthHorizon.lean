import PBGSO.LinearGrowthMoment

/-! # Horizon-uniform moments of actual computed linear-growth equations
The endpoint may be any time within the original Brownian integration
horizon; no change-of-integral-horizon premise is needed.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.LinearGrowthMoment
open FilteredBrownian
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

/-- Any endpoint of the actual original computed equation has its derived
linear-growth moment bound; the integrator remains the original horizon T. -/
theorem computed_endpoint_moment_bound_at (X b : ℝ → Lp Z 2 Q)
    (σ : ℝ → ColumnHilbert (I := I) (Z := Z) Q) (T : ℝ≥0) {A L : ℝ}
    (hL : 0 ≤ L)
    (hb : MemLp b 2 (volume.restrict (Ioc 0 (T : ℝ))))
    (hσ : MemLp σ 2 (volume.restrict (Ioc 0 (T : ℝ))))
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ t i) Q)
    (heq : ∀ t ∈ Icc 0 (T : ℝ), X t = X 0 + (∫ r in 0..t, b r) +
      ConstructedPredictableModel.integral Q D T σ hσ hA t)
    (hgrowth : ∀ r ∈ Ioc 0 (T : ℝ),
      ‖b r‖ ^ 2 + ‖σ r‖ ^ 2 ≤ L * (A + ‖X r‖ ^ 2))
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    ‖X t‖ ^ 2 ≤ Real.exp ((3 * (t+1) * L) * t) * (3 * ‖X 0‖ ^ 2 + A) - A := by
  have hbi : IntervalIntegrable b volume 0 (T : ℝ) := by
    rw [intervalIntegrable_iff, uIoc_of_le T.coe_nonneg]
    exact hb.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hi := (IntegralQuadraticEnergy.integral_absolutelyContinuous b hbi).continuousOn
  rw [uIcc_of_le T.coe_nonneg] at hi
  have hcont : ContinuousOn X (Icc 0 (T : ℝ)) :=
    ((continuousOn_const.add hi).add
      (ConstructedPredictableModel.integral_continuous Q D T σ hσ hA).continuousOn).congr
        (fun t ht => heq t ht)
  have hsq : IntervalIntegrable (fun r => ‖X r‖ ^ 2) volume 0 t :=
    ((hcont.norm.pow 2).mono (by
      rw [uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl ht.2)).intervalIntegrable
  have hsub : volume.restrict (Ioc 0 t) ≤ volume.restrict (Ioc 0 (T : ℝ)) :=
    Measure.restrict_mono (Ioc_subset_Ioc le_rfl ht.2) le_rfl
  exact endpoint_moment_bound X b
    (ConstructedPredictableModel.integral Q D T σ hσ hA) σ ht.1 hL
    (hb.mono_measure hsub) (hσ.mono_measure hsub) hsq
    (fun r hr => heq r ⟨hr.1, hr.2.trans ht.2⟩)
    (fun r hr => le_of_eq (computed_noise_norm_sq Q D T σ hσ hA r
      ⟨hr.1,hr.2.trans ht.2⟩))
    (fun r hr => hgrowth r ⟨hr.1,hr.2.trans ht.2⟩)

/-- The same explicit constant bounds all original observation times on a
finite horizon and is independent of a stopping-localization index. -/
theorem computed_uniform_moment_bound (X b : ℝ → Lp Z 2 Q)
    (σ : ℝ → ColumnHilbert (I := I) (Z := Z) Q) (T : ℝ≥0) {A L : ℝ}
    (hA0 : 0 ≤ A) (hL : 0 ≤ L)
    (hb : MemLp b 2 (volume.restrict (Ioc 0 (T : ℝ))))
    (hσ : MemLp σ 2 (volume.restrict (Ioc 0 (T : ℝ))))
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ t i) Q)
    (heq : ∀ t ∈ Icc 0 (T : ℝ), X t = X 0 + (∫ r in 0..t, b r) +
      ConstructedPredictableModel.integral Q D T σ hσ hA t)
    (hgrowth : ∀ r ∈ Ioc 0 (T : ℝ),
      ‖b r‖ ^ 2 + ‖σ r‖ ^ 2 ≤ L * (A + ‖X r‖ ^ 2))
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    ‖X t‖ ^ 2 ≤ Real.exp ((3 * (T+1) * L) * T) * (3 * ‖X 0‖ ^ 2 + A) - A := by
  have hmoment := computed_endpoint_moment_bound_at Q D X b σ T hL hb hσ hA heq hgrowth t ht
  have hs := pow_le_pow_left₀ ht.1 ht.2 2
  have hc : (3 * (t+1) * L) * t ≤ (3 * (T+1) * L) * T := by
    have h1 := mul_le_mul_of_nonneg_left hs hL
    have h2 := mul_le_mul_of_nonneg_left ht.2 hL
    nlinarith
  have hexp := Real.exp_le_exp.mpr hc
  have hm := mul_le_mul_of_nonneg_right hexp
    (show 0 ≤ 3 * ‖X 0‖ ^ 2 + A by positivity)
  linarith

end PBGSO.LinearGrowthMoment
