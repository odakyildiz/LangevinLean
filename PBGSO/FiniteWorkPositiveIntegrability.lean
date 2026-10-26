import PBGSO.DiracOptimizerGrowth
import PBGSO.RawConstantNoiseContraction

/-! # Positive-work Fubini from the explicit finite-work convention
Universal finite signed coupling work yields compact-uniform quadratic
positive sampler work. Actual product-L² states and the original optimizer
Bochner equations then derive positive joint-work integrability. No optimizer
response Lipschitz condition, drift moment, or energy identity is assumed.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators RealInnerProductSpace InnerProductSpace
namespace PBGSO.FiniteWorkPositiveIntegrability
open FilteredBrownian RawConstantNoiseContraction
variable {Ω S Θ Z X I : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [Fintype I] [DecidableEq I]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {W : Driver (I := I) Q} {M : Model S Θ Z X I} {T : ℝ≥0}
  {L K : RawLocalDiffusion (Z := Z) Q W T}

/-- Product-L² state moments, obtained independently by stopped coercivity,
justify actual positive-work Fubini under the explicit finite-integral A3
convention. The sampler drift itself may have superlinear norm. -/
theorem positive_work_integrable (U : Data Q M W T L) (V : Data Q M W T K)
    (D : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hmono : TwistedJointMonotonicity M D ρ)
    (hfull : DiracOptimizerGrowth.FiniteCouplingWork M D)
    (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i)
    (hU : MemLp (Function.uncurry U.sampler) 2 ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hV : MemLp (Function.uncurry V.sampler) 2 ((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) :
    Integrable (fun p : ℝ × Ω => max (rawMetricBilinear D
      (pairState Q M U V p.1 p.2) (pairDrift Q M U V p.1 p.2)) 0)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := by
  let μ := (volume.restrict (Ioc 0 (T : ℝ))).prod Q
  let Copt : Set S := (U.optimizer '' Icc 0 (T : ℝ)) ∪ (V.optimizer '' Icc 0 (T : ℝ))
  have hCopt : IsCompact Copt :=
    (isCompact_Icc.image_of_continuousOn (Data.optimizer_continuous Q M U)).union
      (isCompact_Icc.image_of_continuousOn (Data.optimizer_continuous Q M V))
  obtain ⟨C,hC,hbound⟩ := DiracOptimizerGrowth.positive_sampler_work_growth_on_compact
    M D ρ hρ hmono hfull Copt hCopt
  obtain ⟨R0,hR0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((Data.optimizer_continuous Q M U).sub (Data.optimizer_continuous Q M V))
  let R := max 0 R0
  have hR : 0 ≤ R := le_max_left _ _
  have hRbound (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) : ‖U.optimizer r-V.optimizer r‖ ≤ R :=
    (hR0 r hr).trans (le_max_right _ _)
  have hj : IntegrableOn (fun r => U.optimizerDrift r-V.optimizerDrift r) (Ioc 0 (T : ℝ)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mp
      (U.optimizerDrift_integrable.sub V.optimizerDrift_integrable)
  have hu2 : Integrable (fun p : ℝ × Ω => ‖U.sampler p.1 p.2‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hU.aestronglyMeasurable).mp hU
  have hv2 : Integrable (fun p : ℝ × Ω => ‖V.sampler p.1 p.2‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hV.aestronglyMeasurable).mp hV
  have hmajor : Integrable (fun p : ℝ × Ω =>
      (‖D.optimizerWeight‖*R)*‖U.optimizerDrift p.1-V.optimizerDrift p.1‖+
        C*(1+‖U.sampler p.1 p.2‖ ^ 2+‖V.sampler p.1 p.2‖ ^ 2)) μ :=
    ((hj.norm.comp_fst Q).const_mul (‖D.optimizerWeight‖*R)).add
      ((((integrable_const (1 : ℝ)).add hu2).add hv2).const_mul C)
  have hm := (rawMetricBilinear D).continuous₂.comp_stronglyMeasurable
    ((pairState_strong Q M U V).prodMk (pairDrift_strong Q M U V))
  apply hmajor.mono'
    (continuous_max.comp_aestronglyMeasurable (hm.aestronglyMeasurable.prodMk aestronglyMeasurable_const))
  have htime : ∀ᵐ p ∂μ, p.1 ∈ Icc 0 (T : ℝ) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact ae_of_all Q (fun _ => Ioc_subset_Icc_self hr)
  filter_upwards [htime] with p hp
  rw [Real.norm_of_nonneg (le_max_right _ _)]
  have huC : U.optimizer p.1 ∈ Copt := Or.inl ⟨p.1,hp,rfl⟩
  have hvC : V.optimizer p.1 ∈ Copt := Or.inr ⟨p.1,hp,rfl⟩
  have hs := hbound (U.optimizer p.1) huC (V.optimizer p.1) hvC (U.sampler p.1 p.2) (V.sampler p.1 p.2)
  rw [sampler_work_eq_drift M D hσ] at hs
  have ho : ⟪U.optimizer p.1-V.optimizer p.1,D.optimizerWeight
      (U.optimizerDrift p.1-V.optimizerDrift p.1)⟫_ℝ ≤
      (‖D.optimizerWeight‖*R)*‖U.optimizerDrift p.1-V.optimizerDrift p.1‖ := by
    calc
      _ ≤ ‖U.optimizer p.1-V.optimizer p.1‖*‖D.optimizerWeight
          (U.optimizerDrift p.1-V.optimizerDrift p.1)‖ := real_inner_le_norm _ _
      _ ≤ R*(‖D.optimizerWeight‖*‖U.optimizerDrift p.1-V.optimizerDrift p.1‖) :=
        mul_le_mul (hRbound p.1 hp) (D.optimizerWeight.le_opNorm _) (norm_nonneg _) hR
      _ = _ := by ring
  change max (⟪U.optimizer p.1-V.optimizer p.1,D.optimizerWeight
      (U.optimizerDrift p.1-V.optimizerDrift p.1)⟫_ℝ+
    ⟪U.sampler p.1 p.2-V.sampler p.1 p.2,D.samplerWeight
      (M.drift (M.parameter (U.optimizer p.1)) (U.sampler p.1 p.2)-
        M.drift (M.parameter (V.optimizer p.1)) (V.sampler p.1 p.2))⟫_ℝ) 0 ≤ _
  apply max_le
  · exact (add_le_add ho (le_max_left _ _)).trans (add_le_add le_rfl hs)
  · positivity

end PBGSO.FiniteWorkPositiveIntegrability
