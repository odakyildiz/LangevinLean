import PBGSO.RawLocalPullback

/-! # Local Brownian integrals commute with probability pullback

Only samplewise local square integrability is required. The actual first-hit
stops pull back literally, their computed stopped stochastic integrals obey
the already proved global isometry construction, and their continuous local
limits agree. No global expected diffusion energy or output-law hypothesis
is assumed.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.FilteredBrownian
variable {Ω Ω' I Z : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
  [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {R : Measure Ω'} [IsProbabilityMeasure R]
  {f : Ω → Ω'} (hf : MeasurePreserving f Q R)
  {D : Driver (I := I) R} (E : Driver (I := I) Q)
  (he : ∀ t, (pullbackDriver hf D).filtration t ≤ E.filtration t)
  (hp : ∀ i t, (pullbackDriver hf D).process i t =ᵐ[Q] E.process i t)
  {T : ℝ≥0} (L : RawLocalDiffusion (Z := Z) R D T)

/-- Actual path energies and first-hit thresholds commute samplewise with
the raw probability pullback. -/
theorem RawLocalDiffusion.pullback_stop (n : ℕ) (ω : Ω) :
    (L.pullback hf E he).stop n ω = L.stop n (f ω) := rfl

include hp

/-- The computed localized stochastic integrals transport before any
limiting local-noise construction is invoked. -/
theorem RawLocalDiffusion.pullback_stopped_noise (n : ℕ) (t : ℝ≥0) :
    (L.pullback hf E he).noise n t = lpPullbackCLM hf (L.noise n t) := by
  exact rawDiffusionIntegral_pullback_enlarge_ae hf D E hp he T
    (L.stoppedSigma n) (L.stoppedSigma_strong n) (L.stoppedSigma_square n)
    (L.stoppedSigma_adapted n) t

/-- The actual continuous martingale versions have their proved pulled
values at every deterministic time. No version-matching premise is used. -/
theorem RawLocalDiffusion.pullback_version_ae (n : ℕ) (t : ℝ≥0) :
    (L.pullback hf E he).version n t =ᵐ[Q] fun ω => L.version n t (f ω) := by
  have h := (L.pullback hf E he).version_ae n t
  rw [L.pullback_stopped_noise hf E he hp n t] at h
  exact h.trans ((lpPullback_coe hf _).trans
    (hf.quasiMeasurePreserving.ae_eq_comp (L.version_ae n t).symm))

/-- Natural local Itô integration on the original locally square-integrable
class. Global expected diffusion energy is not a premise. -/
theorem RawLocalDiffusion.pullback_localNoise_ae (t : ℝ≥0) (ht : t ≤ T) :
    (L.pullback hf E he).localNoise t =ᵐ[Q] fun ω => L.localNoise t (f ω) := by
  filter_upwards [ae_all_iff.mpr (fun n : ℕ => L.pullback_version_ae hf E he hp n t),
    (L.pullback hf E he).version_eventually_localNoise,
    hf.quasiMeasurePreserving.ae (L.version_eventually_localNoise)] with ω hn hk hl
  obtain ⟨n, hnk, hnl⟩ := ((hk t ht).and (hl t ht)).exists
  exact hnk.symm.trans ((hn n).trans hnl)

/-- One common event supports the actual pullback identity on the complete
finite horizon. This permits random stopping times and raw path equations. -/
theorem RawLocalDiffusion.pullback_localNoise_on_horizon :
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T →
      (L.pullback hf E he).localNoise t ω = L.localNoise t (f ω) := by
  let A := Iic T
  letI : Nonempty A := ⟨⟨0,by simp [A]⟩⟩
  let τ := TopologicalSpace.denseSeq A
  filter_upwards [(L.pullback hf E he).localNoise_continuous,
    hf.quasiMeasurePreserving.ae (L.localNoise_continuous),
    ae_all_iff.mpr (fun n => L.pullback_localNoise_ae hf E he hp (τ n).val (τ n).property)]
    with ω hl hk hn
  have hc : Continuous (fun t : A => (L.pullback hf E he).localNoise t.val ω) :=
    hl.comp continuous_subtype_val
  have hc' : Continuous (fun t : A => L.localNoise t.val (f ω)) :=
    hk.comp continuous_subtype_val
  have heq := (TopologicalSpace.denseRange_denseSeq A).equalizer hc hc' (funext hn)
  intro t ht
  exact congrFun heq (⟨t,ht⟩ : A)

end PBGSO.FilteredBrownian
