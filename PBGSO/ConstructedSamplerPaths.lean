import PBGSO.ConstructedPredictableModel
import PBGSO.ClosedIntegralContinuousVersion
import PBGSO.LpContinuousVersion

/-! # Simultaneous original sampler equations for computed model trajectories
The Brownian path regularity and joint drift regularity in this realization
subclass are explicit. The constructed sampler is jointly measurable, realizes
the actual L² state at each time, is adapted almost everywhere at each time,
and satisfies one original nonlinear drift equation simultaneously in time.
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

/-- The actual sampler path version and actual computed noise realization.
AE adaptation is stated precisely; no StronglyAdapted claim for this selected
joint sampler version is made. -/
theorem Data.exists_continuous_sampler_version (U : Data Q D M T)
    (hB : ∀ᵐ ω ∂Q, ∀ i, Continuous (fun t => D.process i t ω))
    (hf : ContinuousOn (fun p : ℝ × Z => M.drift (M.parameter (U.optimizer p.1)) p.2)
      ((Icc 0 (T : ℝ)) ×ˢ (Set.univ : Set Z))) :
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
  let C := predictableDomain Q D T (curveHorizon Q T U.diffusion U.diffusion_square)
    (curveHorizon_pastAdapted Q D T U.diffusion U.diffusion_square U.diffusion_adapted)
  obtain ⟨V⟩ := exists_continuousWindowVersion Q D T C hB
  obtain ⟨g, hg, hgc, hge⟩ := ContinuousWindowVersion.exists_joint_realization Q D T C V
  let c : ℝ → Window T := fun t => windowClip T t.toNNReal
  have hc : Continuous c := (windowClip_continuous T).comp continuous_real_toNNReal
  let b : ℝ → Ω → Z := fun t ω => g (c t) ω
  have hb : StronglyMeasurable (Function.uncurry b) :=
    hg.comp_measurable ((hc.measurable.comp measurable_fst).prodMk measurable_snd)
  have hbc (ω : Ω) : Continuous (fun t => b t ω) := (hgc ω).comp hc
  have hbEq (t : ℝ) (_ht : t ∈ Icc 0 (T : ℝ)) : b t =ᵐ[Q]
      integral Q D T U.diffusion U.diffusion_square U.diffusion_adapted t := by
    have hgv : b t =ᵐ[Q] V.process (c t) := hge.mono (fun ω hω => hω (c t))
    have he : b t =ᵐ[Q] closedIntegral Q D T C (c t).val := hgv.trans (V.realizes (c t))
    change b t =ᵐ[Q] closedIntegral Q D T C t.toNNReal
    have hs : closedIntegral Q D T C (c t).val = closedIntegral Q D T C t.toNNReal :=
      closedIntegral_stopped Q D T C t.toNNReal
    exact he.trans (Eventually.of_forall (fun ω => congrArg (fun A : Lp Z 2 Q => A ω) hs))
  let ct : ℝ → ℝ := fun t => ((c t).val : ℝ)
  have hct : Continuous ct := continuous_subtype_val.comp (continuous_subtype_val.comp hc)
  have hct_mem (t : ℝ) : ct t ∈ Icc 0 (T : ℝ) :=
    ⟨(c t).val.coe_nonneg, by exact_mod_cast (c t).property⟩
  have hct_eq (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : ct t = t := by
    change ((min t.toNNReal T : ℝ≥0) : ℝ) = t
    have hh : t.toNNReal ≤ T := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ht.1]
      exact ht.2
    rw [min_eq_left hh, Real.coe_toNNReal _ ht.1]
  let f : ℝ → Z → Z := fun t z => M.drift (M.parameter (U.optimizer (ct t))) z
  have hfc : Continuous (Function.uncurry f) :=
    hf.comp_continuous ((hct.comp continuous_fst).prodMk continuous_snd)
      (fun p => ⟨hct_mem p.1, Set.mem_univ p.2⟩)
  have hF : IntegrableOn U.drift (Icc 0 (T : ℝ)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le T.coe_nonneg).mp U.drift_integrable
  have hfield (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : U.drift t =ᵐ[Q] fun ω => f t (U.sampler t ω) := by
    simpa only [f, hct_eq t ht] using U.drift_realizes t ht
  have heq (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : U.sampler t - U.sampler 0 =
      (∫ s in 0..t, U.drift s) + integral Q D T U.diffusion U.diffusion_square U.diffusion_adapted t := by
    rw [U.sampler_integral t ht]
    abel
  obtain ⟨u, hu, huEq, hupath⟩ := LpContinuousVersion.exists_continuous_integral_version Q
    (T : ℝ) T.coe_nonneg U.sampler U.drift
    (integral Q D T U.diffusion U.diffusion_square U.diffusion_adapted)
    hF b hb hbEq (Eventually.of_forall (fun ω => (hbc ω).continuousOn)) f hfc hfield heq
  refine ⟨u, b, hu, hb, huEq, hbEq, ?_, ?_⟩
  · intro t ht
    exact (U.sampler_adapted t).congr (huEq t ⟨t.coe_nonneg, ht⟩).symm
  · filter_upwards [hupath] with ω hω
    have hdpath : ContinuousOn
        (fun t => M.drift (M.parameter (U.optimizer t)) (u t ω)) (Icc 0 (T : ℝ)) :=
      hf.comp (continuousOn_id.prodMk hω.1) (fun t ht => ⟨ht, Set.mem_univ _⟩)
    refine ⟨hω.1, (hbc ω).continuousOn, hω.2.1, hdpath.intervalIntegrable_of_Icc T.coe_nonneg, ?_⟩
    intro t ht
    have hi : (∫ s in 0..t, f s (u s ω)) =
        ∫ s in 0..t, M.drift (M.parameter (U.optimizer s)) (u s ω) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s ∈ Icc 0 (T : ℝ) := by
        rw [uIcc_of_le ht.1] at hs
        exact ⟨hs.1, hs.2.trans ht.2⟩
      simp only [f, hct_eq s hs']
    rw [← hi]
    exact hω.2.2 t ht

end PBGSO.ConstructedPredictableModel
