import PBGSO.EmpiricalMonotonicity
import Mathlib.MeasureTheory.Function.L2Space

/-! # A one-sided work criterion for the constant-diffusion branch
The paper's joint condition implies pointwise frozen-sampler dissipativity.
Only the parameter-cross drift can contribute uncontrolled positive work.
The resulting positive-work integrability criterion is strictly weaker than
square integrability of the full sampler drift or its total variation.
The parameter-cross assumptions below are explicit additional conditions;
this file does not claim that minimal source A1(i) implies them.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open MeasureTheory Set Filter
open scoped BigOperators RealInnerProductSpace InnerProductSpace ENNReal
namespace PBGSO.ConstantNoiseWork
variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [MeasurableSpace Z] [MeasurableSingletonClass Z] [Fintype I]
  (M : Model S Θ Z X I) (D : TwistedGeometry S Z) (ρ : ℝ)
  (hmono : TwistedJointMonotonicity M D ρ)
include hmono

omit hmono in
/-- Constant diffusion cancels exactly in the source synchronous coupling
work, leaving the actual sampler drift pairing. -/
theorem sampler_work_eq_drift
    (hσ : ∀ θ θ' z w i, M.diffusion θ z i = M.diffusion θ' w i)
    (s s' : S) (z w : Z) :
    samplerCouplingWork M D s s' (z,w) =
      ⟪z-w, D.samplerWeight (M.drift (M.parameter s) z - M.drift (M.parameter s') w)⟫_ℝ := by
  have hz : ∑ i, D.samplerSq (M.diffusion (M.parameter s) z i - M.diffusion (M.parameter s') w i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [hσ (M.parameter s) (M.parameter s') z w i, sub_self]
    simp [TwistedGeometry.samplerSq]
  simp only [samplerCouplingWork, hz, mul_zero, add_zero]

/-- The full law-level source A3 implies the pointwise frozen sampler
condition, by actual one-point empirical laws. -/
theorem frozen_sampler_work_le (s : S) (z w : Z) :
    samplerCouplingWork M D s s (z,w) ≤ -ρ * D.samplerSq (z - w) := by
  have h := particleCouplingWork_le M D ρ hmono 1 (by norm_num) 0 (by norm_num)
    s s (fun _ => z) (fun _ => w)
  simpa [particleCouplingWork, particleCouplingEnergy, TwistedGeometry.optimizerSq,
    Fin.sum_univ_one] using h

/-- Dropping the nonnegative diffusion correction gives frozen drift
one-sided monotonicity without any drift growth hypothesis. -/
theorem frozen_drift_le (s : S) (z w : Z) :
    ⟪z-w, D.samplerWeight (M.drift (M.parameter s) z - M.drift (M.parameter s) w)⟫_ℝ ≤
      -ρ * D.samplerSq (z-w) := by
  have h := frozen_sampler_work_le M D ρ hmono s z w
  have hn : 0 ≤ (1/2 : ℝ) * ∑ i,
      D.samplerSq (M.diffusion (M.parameter s) z i - M.diffusion (M.parameter s) w i) :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => D.samplerSq_nonneg _))
  unfold samplerCouplingWork at h
  exact (le_add_of_nonneg_right hn).trans h

/-- Frozen superlinear dissipation is retained; only the genuine parameter
change needs an upper work bound. -/
theorem parameter_cross_work_le (s s' : S) (z w : Z) :
    ⟪z-w, D.samplerWeight (M.drift (M.parameter s) z - M.drift (M.parameter s') w)⟫_ℝ ≤
      -ρ * D.samplerSq (z-w) + ‖D.samplerWeight‖ * ‖z-w‖ *
        ‖M.drift (M.parameter s) w - M.drift (M.parameter s') w‖ := by
  have he : M.drift (M.parameter s) z - M.drift (M.parameter s') w =
      (M.drift (M.parameter s) z - M.drift (M.parameter s) w) +
      (M.drift (M.parameter s) w - M.drift (M.parameter s') w) := by abel
  rw [he, map_add, inner_add_right]
  apply add_le_add (frozen_drift_le M D ρ hmono s z w)
  calc
    _ ≤ ‖z-w‖ * ‖D.samplerWeight (M.drift (M.parameter s) w - M.drift (M.parameter s') w)‖ :=
      real_inner_le_norm _ _
    _ ≤ ‖z-w‖ * (‖D.samplerWeight‖ *
        ‖M.drift (M.parameter s) w - M.drift (M.parameter s') w‖) :=
      mul_le_mul_of_nonneg_left (D.samplerWeight.le_opNorm _) (norm_nonneg _)
    _ = _ := by ring

/-- The positive part of actual sampler drift work is dominated solely by
parameter-cross work, rather than the norm of the whole drift. -/
theorem positive_work_le (hρ : 0 ≤ ρ) (s s' : S) (z w : Z) :
    max ⟪z-w, D.samplerWeight (M.drift (M.parameter s) z - M.drift (M.parameter s') w)⟫_ℝ 0 ≤
      ‖D.samplerWeight‖ * ‖z-w‖ * ‖M.drift (M.parameter s) w - M.drift (M.parameter s') w‖ := by
  apply max_le
  · exact (parameter_cross_work_le M D ρ hmono s s' z w).trans
      (add_le_of_nonpos_left (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hρ)
        (D.samplerSq_nonneg _)))
  · positivity

section Integrability
variable {A : Type*} [MeasurableSpace A] (μ : Measure A)
  (a a' : A → S) (x y : A → Z)
  (hx : AEStronglyMeasurable x μ) (hy : AEStronglyMeasurable y μ)
  (hb : AEStronglyMeasurable (fun r => M.drift (M.parameter (a r)) (x r)) μ)
  (hb' : AEStronglyMeasurable (fun r => M.drift (M.parameter (a' r)) (y r)) μ)
include hx hy hb hb'

/-- Actual positive work is integrable whenever the parameter-cross norm
product is integrable. Full drift L² or L² total variation is not required. -/
theorem positive_work_integrable (hρ : 0 ≤ ρ)
    (hcross : Integrable (fun r => ‖x r-y r‖ *
      ‖M.drift (M.parameter (a r)) (y r) - M.drift (M.parameter (a' r)) (y r)‖) μ) :
    Integrable (fun r => max ⟪x r-y r,
      D.samplerWeight (M.drift (M.parameter (a r)) (x r) - M.drift (M.parameter (a' r)) (y r))⟫_ℝ 0) μ := by
  have hm : AEStronglyMeasurable (fun r => ⟪x r-y r,
      D.samplerWeight (M.drift (M.parameter (a r)) (x r) - M.drift (M.parameter (a' r)) (y r))⟫_ℝ) μ :=
    (hx.sub hy).inner (D.samplerWeight.continuous.comp_aestronglyMeasurable (hb.sub hb'))
  apply (hcross.const_mul ‖D.samplerWeight‖).mono'
    (continuous_max.comp_aestronglyMeasurable (hm.prodMk aestronglyMeasurable_const))
  apply Eventually.of_forall
  intro r
  rw [Real.norm_of_nonneg (le_max_right _ _)]
  simpa only [mul_assoc] using positive_work_le M D ρ hmono hρ (a r) (a' r) (x r) (y r)

end Integrability

section ParameterGrowth
variable {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsFiniteMeasure μ]
  (a a' : A → S) (x y : A → Z)

/-- A parameter-Lipschitz drift with linear sampler growth controls positive
work under actual state L² moments, even for a superlinear frozen drift. -/
theorem positive_work_integrable_of_parameter_growth
    (hρ : 0 ≤ ρ) (L K : ℝ) (hL : 0 ≤ L)
    (hparam : ∀ r, ‖M.parameter (a r) - M.parameter (a' r)‖ ≤ K)
    (hcross : ∀ θ θ' z, ‖M.drift θ z - M.drift θ' z‖ ≤
      L * ‖θ-θ'‖ * (1 + ‖z‖))
    (hx : MemLp x 2 μ) (hy : MemLp y 2 μ)
    (hb : AEStronglyMeasurable (fun r => M.drift (M.parameter (a r)) (x r)) μ)
    (hb' : AEStronglyMeasurable (fun r => M.drift (M.parameter (a' r)) (y r)) μ) :
    Integrable (fun r => max ⟪x r-y r,
      D.samplerWeight (M.drift (M.parameter (a r)) (x r) - M.drift (M.parameter (a' r)) (y r))⟫_ℝ 0) μ := by
  have hi : Integrable (fun r => ‖x r-y r‖ * (1 + ‖y r‖)) μ :=
    (hx.sub hy).norm.integrable_mul ((memLp_const (1 : ℝ)).add hy.norm)
  have hm : AEStronglyMeasurable (fun r => ⟪x r-y r,
      D.samplerWeight (M.drift (M.parameter (a r)) (x r) - M.drift (M.parameter (a' r)) (y r))⟫_ℝ) μ :=
    (hx.aestronglyMeasurable.sub hy.aestronglyMeasurable).inner
      (D.samplerWeight.continuous.comp_aestronglyMeasurable (hb.sub hb'))
  apply (hi.const_mul (‖D.samplerWeight‖ * L * K)).mono'
    (continuous_max.comp_aestronglyMeasurable (hm.prodMk aestronglyMeasurable_const))
  apply Eventually.of_forall
  intro r
  rw [Real.norm_of_nonneg (le_max_right _ _)]
  calc
    _ ≤ ‖D.samplerWeight‖ * ‖x r-y r‖ *
        ‖M.drift (M.parameter (a r)) (y r) - M.drift (M.parameter (a' r)) (y r)‖ :=
      positive_work_le M D ρ hmono hρ (a r) (a' r) (x r) (y r)
    _ ≤ ‖D.samplerWeight‖ * ‖x r-y r‖ * (L * K * (1+‖y r‖)) := by
      gcongr
      exact (hcross _ _ _).trans (by gcongr; exact hparam r)
    _ = _ := by ring

end ParameterGrowth
end PBGSO.ConstantNoiseWork
