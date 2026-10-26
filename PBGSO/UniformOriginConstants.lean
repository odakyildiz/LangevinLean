import PBGSO.MethodMetricComparisons

/-! # Primitive force values in the explicit numerical constants
The actual empirical and coordinatewise L² lifts at zero are constant random
variables.  Under the standard Euclidean cloud encoding their norms reduce
exactly to `‖F 0 0‖` and `sqrt N * ‖G 0 0‖`.
-/
noncomputable section
open MeasureTheory
open scoped NNReal BigOperators
namespace PBGSO.UniformOrigin
open Methods

variable {Ω A J : Type*} {N : ℕ} [MeasurableSpace Ω] [Fintype J]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  (D : ParticleForceData A (EuclideanSpace ℝ J) (EuclideanSpace ℝ (Fin N × J)) N)

/-- Exact original optimiser force, with no empirical approximation at zero. -/
theorem meanForceLp_zero : D.meanForceLp Q 0 0 = Lp.const 2 Q (D.F 0 0) := by
  apply Lp.ext
  filter_upwards [D.meanForceLp_coe Q 0 0,
    Lp.coeFn_zero A 2 Q, Lp.coeFn_zero (EuclideanSpace ℝ (Fin N × J)) 2 Q,
    Lp.coeFn_const 2 Q (D.F 0 0)] with ω hf ha hx hc
  rw [hf, ha, hx, hc]
  simp only [Pi.zero_apply, map_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Pi.zero_apply]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast Nat.ne_of_gt D.nonempty), one_smul]
  rfl

/-- Actual zero-state sampler lift is the repacked constant cloud. -/
theorem samplerForceLp_zero : D.samplerForceLp Q 0 0 =
    Lp.const 2 Q (D.cloud.symm (fun _ ↦ D.G 0 0)) := by
  apply Lp.ext
  filter_upwards [D.samplerForceLp_coe_cloud Q 0 0,
    Lp.coeFn_zero A 2 Q, Lp.coeFn_zero (EuclideanSpace ℝ (Fin N × J)) 2 Q,
    Lp.coeFn_const 2 Q (D.cloud.symm (fun _ ↦ D.G 0 0))] with ω hf ha hx hc
  rw [hf, ha, hx, hc]
  simp only [ParticleForceData.samplerForce, map_zero, Pi.zero_apply]
  rfl

/-- Euclidean flattening of a cloud with one fixed value has the exact sqrt-N norm. -/
theorem constant_cloud_norm (v : EuclideanSpace ℝ J) :
    ‖(euclideanParticleEncoding N J).symm (fun _ ↦ v)‖ =
      Real.sqrt (N : ℝ) * ‖v‖ := by
  have hs := MethodMetricComparisons.cloud_norm_sq
    ((euclideanParticleEncoding N J).symm (fun _ ↦ v))
  simp only [ContinuousLinearEquiv.apply_symm_apply, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hsqrt := Real.sq_sqrt (show 0 ≤ (N : ℝ) by positivity)
  nlinarith [norm_nonneg ((euclideanParticleEncoding N J).symm (fun _ ↦ v)),
    mul_nonneg (Real.sqrt_nonneg (N : ℝ)) (norm_nonneg v)]

/-- The primitive optimiser origin norm is exactly its actual lifted norm. -/
theorem meanForceLp_zero_norm : ‖D.meanForceLp Q 0 0‖ = ‖D.F 0 0‖ := by
  rw [meanForceLp_zero Q D, Lp.norm_const 2 Q (D.F 0 0) (by norm_num)]
  simp

/-- The primitive sampler origin norm includes exactly sqrt-N cloud scaling. -/
theorem samplerForceLp_zero_norm (hcloud : D.cloud = euclideanParticleEncoding N J) :
    ‖D.samplerForceLp Q 0 0‖ = Real.sqrt (N : ℝ) * ‖D.G 0 0‖ := by
  rw [samplerForceLp_zero Q D, Lp.norm_const 2 Q _ (by norm_num)]
  simp [hcloud, constant_cloud_norm]

/-- Full raw force uses the product max norm in the actual implementation. -/
theorem coupledForce_zero_norm (hcloud : D.cloud = euclideanParticleEncoding N J) :
    ‖coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) 0‖ =
      max ‖D.F 0 0‖ (Real.sqrt (N : ℝ) * ‖D.G 0 0‖) := by
  change max ‖D.meanForceLp Q 0 0‖ ‖D.samplerForceLp Q 0 0‖ = _
  rw [meanForceLp_zero_norm, samplerForceLp_zero_norm Q D hcloud]

/-- The actual full HOL drift at zero has the same raw max norm. -/
theorem holDrift_zero_norm (hcloud : D.cloud = euclideanParticleEncoding N J) (α γ : ℝ) :
    ‖holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ 0‖ =
      max ‖D.F 0 0‖ (Real.sqrt (N : ℝ) * ‖D.G 0 0‖) := by
  simp only [holDrift, Prod.fst_zero, Prod.snd_zero, smul_zero, add_zero,
    sub_zero, Prod.norm_def, norm_neg, norm_zero,
    max_eq_left (norm_nonneg (D.samplerForceLp Q 0 0))]
  rw [meanForceLp_zero_norm, samplerForceLp_zero_norm Q D hcloud]
  rw [max_eq_right (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]

end PBGSO.UniformOrigin
