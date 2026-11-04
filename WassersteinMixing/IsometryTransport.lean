import WassersteinMixing.Theorem
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option linter.style.header false

/-! # Coordinate independence of the actual Gaussian ULA theorem

Linear isometric coordinate changes preserve the normalized Gibbs measure,
the independent standard Gaussian transition, and the quadratic coupling
distance. These proved identities let the Euclidean theorem act on IPLA's
sum/product coordinate type without an additional realization assumption.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace WassersteinMixing

variable {H F : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
/-- The gradient transforms by the same orthogonal coordinate map. -/
theorem gradient_comp_isometry (e : H ≃ₗᵢ[ℝ] F) (V : H → ℝ)
    (hV : Differentiable ℝ V) (y : F) :
    gradient (V ∘ e.symm) y = e (gradient V (e.symm y)) := by
  apply ext_inner_left ℝ
  intro w
  rw [inner_gradient_right]
  have hd := (hV (e.symm y)).hasFDerivAt.comp y
    e.symm.toContinuousLinearEquiv.hasFDerivAt
  rw [hd.fderiv]
  change (fderiv ℝ V (e.symm y)) (e.symm w) = _
  rw [← inner_gradient_left, real_inner_comm]
  simpa using (e.inner_map_map (e.symm w) (gradient V (e.symm y))).symm

omit [CompleteSpace H] [CompleteSpace F] in
/-- Volume preservation identifies the literal partition functions. -/
theorem gibbsPartition_comp_isometry (e : H ≃ₗᵢ[ℝ] F) (V : H → ℝ) :
    ULA.gibbsPartition (V ∘ e.symm) = ULA.gibbsPartition V := by
  unfold ULA.gibbsPartition ULA.gibbsWeight
  simpa only [Function.comp_apply, e.symm_apply_apply] using
    (e.measurePreserving.lintegral_comp_emb e.toMeasurableEquiv.measurableEmbedding
      (fun y ↦ ENNReal.ofReal (Real.exp (-(V ∘ e.symm) y)))).symm

omit [CompleteSpace H] [CompleteSpace F] in
/-- The normalized target is transported exactly, rather than identified by
an externally supplied invariant-law hypothesis. -/
theorem gibbsMeasure_map_isometry (e : H ≃ₗᵢ[ℝ] F) (V : H → ℝ) :
    (ULA.gibbsMeasure V).map e = ULA.gibbsMeasure (V ∘ e.symm) := by
  unfold ULA.gibbsMeasure
  rw [Measure.map_smul _ e.continuous.measurable.aemeasurable,
    gibbsPartition_comp_isometry]
  congr 1
  ext s hs
  rw [Measure.map_apply e.continuous.measurable hs,
    withDensity_apply _ (e.continuous.measurable hs), withDensity_apply _ hs]
  simpa only [ULA.gibbsWeight, Function.comp_apply, e.symm_apply_apply] using
    e.measurePreserving.setLIntegral_comp_preimage_emb
      e.toMeasurableEquiv.measurableEmbedding
      (fun y ↦ ENNReal.ofReal (Real.exp (-(V ∘ e.symm) y))) s

/-- Push both coordinates of an actual transport coupling through an isometry. -/
def isometryCoupling (e : H ≃ₗᵢ[ℝ] F) {μ ν : Measure H} (c : ULA.Coupling μ ν) :
    ULA.Coupling (μ.map e) (ν.map e) where
  joint := c.joint.map (Prod.map e e)
  fst := by
    rw [Measure.map_map measurable_fst (by fun_prop)]
    have h := congrArg (Measure.map e) c.fst
    rw [Measure.map_map e.continuous.measurable measurable_fst] at h
    exact h
  snd := by
    rw [Measure.map_map measurable_snd (by fun_prop)]
    have h := congrArg (Measure.map e) c.snd
    rw [Measure.map_map e.continuous.measurable measurable_snd] at h
    exact h

omit [CompleteSpace H] [CompleteSpace F] in
/-- The exact quadratic cost of a coupling is unchanged. -/
theorem isometryCoupling_cost (e : H ≃ₗᵢ[ℝ] F) {μ ν : Measure H}
    (c : ULA.Coupling μ ν) :
    ULA.couplingCost (isometryCoupling e c).joint = ULA.couplingCost c.joint := by
  unfold ULA.couplingCost isometryCoupling
  rw [eLpNorm_map_measure (by fun_prop) (by fun_prop)]
  apply eLpNorm_congr_norm_ae (by fun_prop) (by fun_prop)
  exact Filter.Eventually.of_forall fun p ↦ by simp [← map_sub]

omit [CompleteSpace H] [CompleteSpace F] in
/-- Transporting both marginals through an isometry cannot increase cost. -/
theorem wasserstein2_map_isometry_le (e : H ≃ₗᵢ[ℝ] F) (μ ν : Measure H) :
    ULA.wasserstein2 (μ.map e) (ν.map e) ≤ ULA.wasserstein2 μ ν := by
  apply le_iInf
  intro c
  exact (ULA.wasserstein2_le_couplingCost (isometryCoupling e c)).trans_eq
    (isometryCoupling_cost e c)

omit [CompleteSpace H] [CompleteSpace F] in
/-- Orthogonal coordinate changes preserve the extended transport metric,
including its finiteness, by transporting couplings in both directions. -/
theorem wasserstein2_map_isometry (e : H ≃ₗᵢ[ℝ] F) (μ ν : Measure H) :
    ULA.wasserstein2 (μ.map e) (ν.map e) = ULA.wasserstein2 μ ν := by
  apply le_antisymm (wasserstein2_map_isometry_le e μ ν)
  have h := wasserstein2_map_isometry_le e.symm (μ.map e) (ν.map e)
  simpa [Measure.map_map e.symm.continuous.measurable e.continuous.measurable,
    Function.comp_def] using h

omit [CompleteSpace H] [CompleteSpace F] in
/-- Real transport distances are preserved after the extended equality. -/
theorem wasserstein2Real_map_isometry (e : H ≃ₗᵢ[ℝ] F) (μ ν : Measure H) :
    ULA.wasserstein2Real (μ.map e) (ν.map e) = ULA.wasserstein2Real μ ν := by
  simp only [ULA.wasserstein2Real, wasserstein2_map_isometry]

/-- The ordinary Gaussian ULA update is covariant under an orthogonal change
of coordinates. -/
theorem ulaLawStep_map_isometry (e : H ≃ₗᵢ[ℝ] F) (V : H → ℝ)
    (hV : Differentiable ℝ V) (L : ℝ≥0) (hLip : LipschitzWith L (gradient V))
    (h : ℝ) (μ : Measure H) [SFinite μ] :
    (ULA.ulaLawStep V h μ).map e =
      ULA.ulaLawStep (V ∘ e.symm) h (μ.map e) := by
  have hp : ∀ x z, ULA.malaProposal (V ∘ e.symm) h (e x) (e z) =
      e (ULA.malaProposal V h x z) := by
    intro x z
    simp only [ULA.malaProposal, gradient_comp_isometry e V hV,
      e.symm_apply_apply, map_add, map_sub, map_smul]
  unfold ULA.ulaLawStep
  rw [← stdGaussian_map e, Measure.map_prod_map _ _
    e.continuous.measurable e.continuous.measurable]
  rw [Measure.map_map e.continuous.measurable
    (ULA.malaProposal_measurable V h L hLip)]
  rw [Measure.map_map (by
    have hg : Continuous (gradient (V ∘ e.symm)) := by
      simp only [funext (gradient_comp_isometry e V hV)]
      exact e.continuous.comp (hLip.continuous.comp e.symm.continuous)
    unfold ULA.malaProposal
    fun_prop) (by fun_prop)]
  congr 1
  ext p
  exact (hp p.1 p.2).symm

omit [CompleteSpace H] [FiniteDimensional ℝ H] [CompleteSpace F] in
/-- A finite second moment remains finite after the coordinate change. -/
theorem memLp_id_map_isometry (e : H ≃ₗᵢ[ℝ] F) (μ : Measure H)
    (hμ : MemLp (id : H → H) 2 μ) : MemLp (id : F → F) 2 (μ.map e) := by
  apply (memLp_map_measure_iff (by fun_prop)
    e.continuous.measurable.aemeasurable).mpr
  exact e.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' hμ

/-- The exact change of coordinates intertwines every actual Gaussian iterate. -/
theorem ula_iterate_map_isometry (P : Parameters) (e : H ≃ₗᵢ[ℝ] F)
    (V : H → ℝ) (hV : PotentialAssumptions P V)
    (μ : Measure H) [IsProbabilityMeasure μ] (n : ℕ) :
    ((ULA.ulaLawStep V P.step)^[n] μ).map e =
      (ULA.ulaLawStep (V ∘ e.symm) P.step)^[n] (μ.map e) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let := ula_iterate_isProbability P V hV μ n
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ulaLawStep_map_isometry e V (hV.regularity.differentiable (by norm_num))
        ⟨P.beta, P.beta_pos.le⟩ hV.gradientLipschitz, ih]

end WassersteinMixing
