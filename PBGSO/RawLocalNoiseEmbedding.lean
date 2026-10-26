import PBGSO.RawIntegralNoiseEmbedding
import PBGSO.RawLocalGauge

/-! # Literal noise-index inclusions for actual local stochastic integrals
The original locally square diffusion is padded by zero in the larger noise
vector. Its local energy is unchanged, hence its true first-hit stops are
identical. Actual global stopped integral identities pass to the original
local process without an expected-square moment hypothesis.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.FilteredBrownian
variable {Ω I J Z : Type*} [mΩ : MeasurableSpace Ω]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {D : Driver (I := I) Q} (f : I ↪ J) (E : Driver (I := J) Q)
  (hF : D.filtration = E.filtration) {T : ℝ≥0}

theorem embedFamily_norm_sq (v : I → Z) :
    ∑ j, ‖embedFamily f v j‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  classical
  let A := Finset.univ.image f
  have he : ∑ j ∈ A, ‖embedFamily f v j‖ ^ 2 = ∑ j, ‖embedFamily f v j‖ ^ 2 := by
    apply Finset.sum_subset (Finset.subset_univ A)
    intro j hj hja
    have hjr : j ∉ range f := by
      rintro ⟨i,rfl⟩
      exact hja (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)
    rw [embedFamily_outside f v j hjr]
    simp
  rw [← he]
  dsimp only [A]
  rw [Finset.sum_image (fun i hi k hk h => f.injective h)]
  simp only [embedFamily_image]

def RawLocalDiffusion.injectNoise (L : RawLocalDiffusion (Z := Z) Q D T) :
    RawLocalDiffusion (Z := Z) Q E T where
  sigma := rawEmbed f L.sigma
  sigma_strong := rawEmbed_stronglyMeasurable f L.sigma L.sigma_strong
  sigma_adapted := rawEmbed_adapted Q f D E hF L.sigma L.sigma_adapted
  q := L.q
  q_strong := L.q_strong
  q_nonneg := L.q_nonneg
  q_local := L.q_local
  q_progressive t := by rw [← hF]; exact L.q_progressive t
  sigma_control r ω := by
    change (∑ j, ‖embedFamily f (fun i => L.sigma i r ω) j‖ ^ 2) ≤ L.q r ω
    rw [embedFamily_norm_sq f]
    exact L.sigma_control r ω

variable (hp : ∀ i t, D.process i t = E.process (f i) t)
  (L : RawLocalDiffusion (Z := Z) Q D T)
include hF hp

theorem RawLocalDiffusion.injectNoise_stop (n : ℕ) (ω : Ω) :
    (L.injectNoise f E hF).stop n ω = L.stop n ω := rfl

theorem RawLocalDiffusion.injectNoise_stoppedSigma (n : ℕ) (j : J) (r : ℝ) (ω : Ω) :
    (L.injectNoise f E hF).stoppedSigma n j r ω = rawEmbed f (L.stoppedSigma n) j r ω := by
  change (if r ≤ (L.stop n ω : ℝ) then embedFamily f (fun i => L.sigma i r ω) j else 0) =
    embedFamily f (fun i => if r ≤ (L.stop n ω : ℝ) then L.sigma i r ω else 0) j
  by_cases hr : r ≤ (L.stop n ω : ℝ) <;> simp [hr,embedFamily]

theorem RawLocalDiffusion.injectNoise_noise (n : ℕ) (t : ℝ≥0) :
    (L.injectNoise f E hF).noise n t = L.noise n t := by
  let K := L.injectNoise f E hF
  have he : ∀ j, Function.uncurry (K.stoppedSigma n j) =ᵐ[
      (volume.restrict (Ioc 0 (T : ℝ))).prod Q] Function.uncurry (rawEmbed f (L.stoppedSigma n) j) :=
    fun j => Eventually.of_forall (fun p => L.injectNoise_stoppedSigma f E hF hp n j p.1 p.2)
  have hi := rawDiffusionIntegral_congr_ae_coefficients Q E T (K.stoppedSigma n)
    (rawEmbed f (L.stoppedSigma n)) (K.stoppedSigma_strong n)
    (rawEmbed_stronglyMeasurable f (L.stoppedSigma n) (L.stoppedSigma_strong n))
    (K.stoppedSigma_square n) (rawEmbed_square Q f T (L.stoppedSigma n) (L.stoppedSigma_square n))
    (K.stoppedSigma_adapted n)
    (rawEmbed_adapted Q f D E hF (L.stoppedSigma n) (L.stoppedSigma_adapted n)) he t
  exact hi.trans (rawDiffusionIntegral_embed Q f D E hF hp T (L.stoppedSigma n)
    (L.stoppedSigma_strong n) (L.stoppedSigma_square n) (L.stoppedSigma_adapted n) t)

theorem RawLocalDiffusion.injectNoise_version_ae (n : ℕ) (t : ℝ≥0) :
    (L.injectNoise f E hF).version n t =ᵐ[Q] L.version n t := by
  have h := (L.injectNoise f E hF).version_ae n t
  rw [L.injectNoise_noise f E hF hp n t] at h
  exact h.trans (L.version_ae n t).symm

theorem RawLocalDiffusion.injectNoise_localNoise_ae (t : ℝ≥0) (ht : t ≤ T) :
    (L.injectNoise f E hF).localNoise t =ᵐ[Q] L.localNoise t := by
  filter_upwards [ae_all_iff.mpr (fun n => L.injectNoise_version_ae f E hF hp n t),
    (L.injectNoise f E hF).version_eventually_localNoise,L.version_eventually_localNoise]
      with ω hn hk hl
  obtain ⟨n,hnk,hnl⟩ := ((hk t ht).and (hl t ht)).exists
  exact hnk.symm.trans ((hn n).trans hnl)

theorem RawLocalDiffusion.injectNoise_localNoise_on_horizon :
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → (L.injectNoise f E hF).localNoise t ω = L.localNoise t ω := by
  let H := Iic T
  letI : Nonempty H := ⟨⟨0,by simp [H]⟩⟩
  let τ := TopologicalSpace.denseSeq H
  filter_upwards [(L.injectNoise f E hF).localNoise_continuous,L.localNoise_continuous,
    ae_all_iff.mpr (fun n => L.injectNoise_localNoise_ae f E hF hp (τ n).val (τ n).property)]
      with ω hk hl hn
  have hc : Continuous (fun t : H => (L.injectNoise f E hF).localNoise t.val ω) :=
    hk.comp continuous_subtype_val
  have hc' : Continuous (fun t : H => L.localNoise t.val ω) := hl.comp continuous_subtype_val
  have he := (TopologicalSpace.denseRange_denseSeq H).equalizer hc hc' (funext hn)
  intro t ht
  exact congrFun he (⟨t,ht⟩ : H)

/-- The literal original row integral is recovered inside any larger-driver
raw realization with the actual zero-padded coefficients and arbitrary gauge. -/
theorem RawLocalDiffusion.localNoise_noiseEmbedding_congr
    (K : RawLocalDiffusion (Z := Z) Q E T)
    (hσ : ∀ᵐ ω ∂Q, ∀ j r, r ∈ Ioc 0 (T : ℝ) → K.sigma j r ω = rawEmbed f L.sigma j r ω) :
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → K.localNoise t ω = L.localNoise t ω := by
  filter_upwards [K.localNoise_gauge_congr_on_horizon (L.injectNoise f E hF) hσ,
    L.injectNoise_localNoise_on_horizon f E hF hp] with ω hg hl
  intro t ht
  exact (hg t ht).trans (hl t ht)

end PBGSO.FilteredBrownian
