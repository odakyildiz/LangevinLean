import PBGSO.RawLocalNoiseCongruence

/-! # Pullback of actual locally defined Brownian inputs
Primitive locally integrable raw diffusion fields transport through actual
measure-preserving maps and valid filtration enlargement. When the diffusion
has global expected square integrability, its actual glued local noise agrees
with the pullback on one event over the entire finite horizon.
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
  {T : ℝ≥0}

/-- Raw diffusion and its actual local energy, pulled to the full enlarged
past. Local integrability is samplewise and needs no global moment bound. -/
def RawLocalDiffusion.pullback (L : RawLocalDiffusion (Z := Z) R D T) :
    RawLocalDiffusion (Z := Z) Q E T where
  sigma i r ω := L.sigma i r (f ω)
  sigma_strong := rawPullback_stronglyMeasurable hf L.sigma L.sigma_strong
  sigma_adapted t i := (rawPullback_adapted hf D L.sigma L.sigma_adapted t i).mono (he t)
  q r ω := L.q r (f ω)
  q_strong := L.q_strong.comp_measurable
    (measurable_fst.prodMk (hf.measurable.comp measurable_snd))
  q_nonneg r ω := L.q_nonneg r (f ω)
  q_local ω := L.q_local (f ω)
  q_progressive t := by
    have hm : @Measurable Ω Ω' (E.filtration t) (D.filtration t) f :=
      measurable_iff_comap_le.mpr (he t)
    have hmap : @Measurable (ℝ × Ω) (ℝ × Ω')
        ((inferInstance : MeasurableSpace ℝ).prod (E.filtration t))
        ((inferInstance : MeasurableSpace ℝ).prod (D.filtration t))
        (fun p => (p.1,f p.2)) := measurable_fst.prodMk (hm.comp measurable_snd)
    exact (L.q_progressive t).comp_measurable hmap
  sigma_control r ω := L.sigma_control r (f ω)

variable (hp : (pullbackDriver hf D).process = E.process)
  (L : RawLocalDiffusion (Z := Z) R D T)
  (h2 : ∀ i, Integrable (fun p : ℝ × Ω' => ‖L.sigma i p.1 p.2‖ ^ 2)
    ((volume.restrict (Ioc 0 (T : ℝ))).prod R))
include hp h2

/-- Deterministic-time identity of the actual local noise, derived through
global completion and its proved naturality. -/
theorem RawLocalDiffusion.pullback_noise_ae (t : ℝ≥0) (ht : t ≤ T) :
    (L.pullback hf E he).localNoise t =ᵐ[Q] fun ω => L.localNoise t (f ω) := by
  let K := L.pullback hf E he
  have hK2 := rawPullback_square hf T L.sigma h2
  have hi := rawDiffusionIntegral_pullback_enlarge hf D E hp he T L.sigma L.sigma_strong h2
    L.sigma_adapted t
  have heq : rawDiffusionIntegral Q E T K.sigma K.sigma_strong hK2 K.sigma_adapted t =
      lpPullbackCLM hf (rawDiffusionIntegral R D T L.sigma L.sigma_strong h2 L.sigma_adapted t) := by
    exact hi
  have hs := K.localNoise_eq_global_of_square hK2 t ht
  rw [heq] at hs
  exact hs.trans ((lpPullback_coe hf _).trans
    (hf.quasiMeasurePreserving.ae_eq_comp (L.localNoise_eq_global_of_square h2 t ht).symm))

/-- Continuous actual local noise gives one pullback identity at all times
of the finite horizon, rather than separate deterministic-time events. -/
theorem RawLocalDiffusion.pullback_noise_on_horizon :
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T →
      (L.pullback hf E he).localNoise t ω = L.localNoise t (f ω) := by
  let A := Iic T
  letI : Nonempty A := ⟨⟨0,by simp [A]⟩⟩
  let τ := TopologicalSpace.denseSeq A
  have ht (n : ℕ) : (τ n).val ≤ T := (τ n).property
  filter_upwards [(L.pullback hf E he).localNoise_continuous,
    hf.quasiMeasurePreserving.ae (L.localNoise_continuous),
    ae_all_iff.mpr (fun n => L.pullback_noise_ae hf E he hp h2 (τ n).val (ht n))]
    with ω hl hk hn
  have hc : Continuous (fun t : A => (L.pullback hf E he).localNoise t.val ω) :=
    hl.comp continuous_subtype_val
  have hc' : Continuous (fun t : A => L.localNoise t.val (f ω)) := hk.comp continuous_subtype_val
  have heq := (TopologicalSpace.denseRange_denseSeq A).equalizer hc hc' (funext hn)
  intro t ht
  exact congrFun heq (⟨t,ht⟩ : A)

end PBGSO.FilteredBrownian
