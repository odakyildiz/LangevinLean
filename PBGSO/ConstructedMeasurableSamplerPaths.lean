import PBGSO.ConstructedSamplerPaths
import PBGSO.LpMeasurableContinuousVersion

/-! # Original sampler path equations with merely measurable model drift
The original field is required to be jointly strongly measurable only on the
finite time horizon. Path drift integrability is derived from the actual L¹
class and Fubini, with no continuity of the drift field assumed.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology
namespace PBGSO.ConstructedPredictableModel
open FilteredBrownian ContinuousMartingaleCompletion
variable {Ω S Θ Z X I : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {Q : Measure Ω} [IsProbabilityMeasure Q] {D : Driver (I := I) Q}
  {M : Model S Θ Z X I} {T : ℝ≥0}

/-- The original computed noise has a joint continuous realization. No raw
noise version, matching law or continuous modification is supplied as input. -/
theorem exists_joint_continuous_noise (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : MemLp u 2 (volume.restrict (Ioc 0 (T : ℝ))))
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q)
    (hB : ∀ᵐ ω ∂Q, ∀ i, Continuous (fun t => D.process i t ω)) :
    ∃ b : ℝ → Ω → Z, StronglyMeasurable (Function.uncurry b) ∧
      (∀ t, b t =ᵐ[Q] integral Q D T u hu hU t) ∧
      ∀ ω, Continuous (fun t => b t ω) := by
  let C := predictableDomain Q D T (curveHorizon Q T u hu) (curveHorizon_pastAdapted Q D T u hu hU)
  obtain ⟨V⟩ := exists_continuousWindowVersion Q D T C hB
  obtain ⟨g, hg, hgc, hge⟩ := ContinuousWindowVersion.exists_joint_realization Q D T C V
  let c : ℝ → Window T := fun t => windowClip T t.toNNReal
  have hc : Continuous c := (windowClip_continuous T).comp continuous_real_toNNReal
  let b : ℝ → Ω → Z := fun t ω => g (c t) ω
  have hb : StronglyMeasurable (Function.uncurry b) :=
    hg.comp_measurable ((hc.measurable.comp measurable_fst).prodMk measurable_snd)
  refine ⟨b, hb, ?_, fun ω => (hgc ω).comp hc⟩
  intro t
  have hgv : b t =ᵐ[Q] V.process (c t) := hge.mono (fun ω hω => hω (c t))
  have he : b t =ᵐ[Q] closedIntegral Q D T C (c t).val := hgv.trans (V.realizes (c t))
  change b t =ᵐ[Q] closedIntegral Q D T C t.toNNReal
  have hs : closedIntegral Q D T C (c t).val = closedIntegral Q D T C t.toNNReal :=
    closedIntegral_stopped Q D T C t.toNNReal
  exact he.trans (Eventually.of_forall (fun ω => congrArg (fun A : Lp Z 2 Q => A ω) hs))

/-- A simultaneous original model sampler path version under horizon-only
joint strong measurability of its original drift. Per-time AE adaptation is
proved; actual StronglyAdapted of the selected joint version is not asserted. -/
theorem Data.exists_continuous_sampler_version_of_stronglyMeasurable (U : Data Q D M T)
    (hB : ∀ᵐ ω ∂Q, ∀ i, Continuous (fun t => D.process i t ω))
    (hf : StronglyMeasurable (fun p : (Icc 0 (T : ℝ)) × Z =>
      M.drift (M.parameter (U.optimizer p.1.val)) p.2)) :
    ∃ u b : ℝ → Ω → Z,
      StronglyMeasurable (Function.uncurry u) ∧ StronglyMeasurable (Function.uncurry b) ∧
      (∀ t ∈ Icc 0 (T : ℝ), u t =ᵐ[Q] U.sampler t) ∧
      (∀ t ∈ Icc 0 (T : ℝ), b t =ᵐ[Q]
        integral Q D T U.diffusion U.diffusion_square U.diffusion_adapted t) ∧
      (∀ t : ℝ≥0, (t : ℝ) ≤ T → AEStronglyMeasurable[D.filtration t] (u t) Q) ∧
      ∀ᵐ ω ∂Q,
        ContinuousOn (fun t => u t ω) (Icc 0 (T : ℝ)) ∧
        ContinuousOn (fun t => b t ω) (Icc 0 (T : ℝ)) ∧
        u 0 ω = U.sampler 0 ω ∧
        IntervalIntegrable (fun t => M.drift (M.parameter (U.optimizer t)) (u t ω)) volume 0 (T : ℝ) ∧
        ∀ t ∈ Icc 0 (T : ℝ), u t ω - u 0 ω =
          (∫ s in 0..t, M.drift (M.parameter (U.optimizer s)) (u s ω)) + b t ω := by
  obtain ⟨b, hb, hbEq, hbc⟩ := exists_joint_continuous_noise U.diffusion U.diffusion_square U.diffusion_adapted hB
  let ct : ℝ → ℝ := fun t => min (max t 0) (T : ℝ)
  have hct : Continuous ct := (continuous_id.max continuous_const).min continuous_const
  have hct_mem (t : ℝ) : ct t ∈ Icc 0 (T : ℝ) :=
    ⟨le_min (le_max_right _ _) T.coe_nonneg, min_le_right _ _⟩
  have hct_eq (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : ct t = t := by
    simp only [ct, max_eq_left ht.1, min_eq_left ht.2]
  let cw : ℝ → Icc 0 (T : ℝ) := fun t => ⟨ct t, hct_mem t⟩
  have hcw : Continuous cw := hct.subtype_mk _
  let f : ℝ → Z → Z := fun t z => M.drift (M.parameter (U.optimizer (ct t))) z
  have hfm : StronglyMeasurable (Function.uncurry f) :=
    hf.comp_measurable ((hcw.measurable.comp measurable_fst).prodMk measurable_snd)
  have hF : IntegrableOn U.drift (Icc 0 (T : ℝ)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le T.coe_nonneg).mp U.drift_integrable
  have hfield (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : U.drift t =ᵐ[Q] fun ω => f t (U.sampler t ω) := by
    simpa only [f, hct_eq t ht] using U.drift_realizes t ht
  have heq (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : U.sampler t - U.sampler 0 =
      (∫ s in 0..t, U.drift s) + integral Q D T U.diffusion U.diffusion_square U.diffusion_adapted t := by
    rw [U.sampler_integral t ht]
    abel
  obtain ⟨u, hu, huEq, hupath⟩ := LpContinuousVersion.exists_continuous_integral_version_of_stronglyMeasurable Q
    (T : ℝ) T.coe_nonneg U.sampler U.drift
    (integral Q D T U.diffusion U.diffusion_square U.diffusion_adapted)
    hF b hb (fun t _ => hbEq t) (Eventually.of_forall (fun ω => (hbc ω).continuousOn)) f hfm hfield heq
  refine ⟨u, b, hu, hb, huEq, (fun t _ => hbEq t), ?_, ?_⟩
  · intro t ht
    exact (U.sampler_adapted t).congr (huEq t ⟨t.coe_nonneg, ht⟩).symm
  · filter_upwards [hupath] with ω hω
    have hfeq (s : ℝ) (hs : s ∈ Icc 0 (T : ℝ)) :
        f s (u s ω) = M.drift (M.parameter (U.optimizer s)) (u s ω) := by
      simp only [f, hct_eq s hs]
    have hfi : IntervalIntegrable
        (fun s => M.drift (M.parameter (U.optimizer s)) (u s ω)) volume 0 (T : ℝ) :=
      hω.2.2.1.congr (fun s hs => hfeq s (by
        rw [uIoc_of_le T.coe_nonneg] at hs
        exact ⟨hs.1.le, hs.2⟩))
    refine ⟨hω.1, (hbc ω).continuousOn, hω.2.1, hfi, ?_⟩
    intro t ht
    have hi : (∫ s in 0..t, f s (u s ω)) =
        ∫ s in 0..t, M.drift (M.parameter (U.optimizer s)) (u s ω) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      exact hfeq s ⟨hs.1, hs.2.trans ht.2⟩
    rw [← hi]
    exact hω.2.2.2 t ht

end PBGSO.ConstructedPredictableModel
