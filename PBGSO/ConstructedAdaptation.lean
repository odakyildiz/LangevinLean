import PBGSO.IntegralAdaptation
import PBGSO.ConstructedParameterBound

/-! # Adaptation of the actual canonical additive constructions
The original canonical input, initial variables and selected mean-field and
particle trajectories are identified with the constructed filtered Brownian
driver. Adaptation follows from the actual equations and primitive Lipschitz
maps, without a supplied adapted-solution premise.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace PBGSO.ConstructedAdaptation
open IntegralAdaptation
variable {A G Z J : Type*} [Fintype J] [DecidableEq J]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  (μ : Measure Z) [IsProbabilityMeasure μ]

/-- The actual pulled one-copy input equals the full filtered driver's
physical Brownian input on the same initial/noise seed. -/
theorem canonical_input_eq (K : EuclideanSpace ℝ J →L[ℝ] Z) (t : ℝ) :
    AdditiveCanonical.input (ULA.CanonicalBrownian.vectorProbability J) μ
      (samplerBrownianInput (ULA.CanonicalBrownian.vectorProbability J) K
        ULA.CanonicalBrownian.coordinate ULA.CanonicalBrownian.coordinate_isPreBrownian 0) t =
      samplerBrownianInput (μ.prod (ULA.CanonicalBrownian.vectorProbability J)) K
        (CanonicalBrownianDriver.driver (I := J) μ).process
        (CanonicalBrownianDriver.driver (I := J) μ).brownian 0 t := by
  let R := ULA.CanonicalBrownian.vectorProbability J
  let hf := measurePreserving_snd (μ := μ) (ν := R)
  apply Lp.ext
  filter_upwards [lpPullback_coe hf (samplerBrownianInput R K ULA.CanonicalBrownian.coordinate
      ULA.CanonicalBrownian.coordinate_isPreBrownian 0 t),
    hf.quasiMeasurePreserving.ae_eq_comp
      (samplerBrownianInput_coe R K ULA.CanonicalBrownian.coordinate
        ULA.CanonicalBrownian.coordinate_isPreBrownian 0 t),
    samplerBrownianInput_coe (μ.prod R) K
      (CanonicalBrownianDriver.driver (I := J) μ).process
      (CanonicalBrownianDriver.driver (I := J) μ).brownian 0 t] with p hp hn hd
  change ((lpPullbackCLM hf) (samplerBrownianInput R K ULA.CanonicalBrownian.coordinate
    ULA.CanonicalBrownian.coordinate_isPreBrownian 0 t)) p = _
  rw [hp]
  change (samplerBrownianInput R K ULA.CanonicalBrownian.coordinate
    ULA.CanonicalBrownian.coordinate_isPreBrownian 0 t) p.2 = _ at hn
  rw [hn, hd]
  rfl

/-- The actual initial sampler is measurable in the full initial/noise
filtration at time zero. -/
theorem canonical_initial_measurable (hμ : MemLp (fun z : Z ↦ z) 2 μ) :
    AEStronglyMeasurable[(CanonicalBrownianDriver.driver (I := J) μ).filtration 0]
      (AdditiveCanonical.initialSampler (ULA.CanonicalBrownian.vectorProbability J) μ hμ)
      (μ.prod (ULA.CanonicalBrownian.vectorProbability J)) := by
  have h : StronglyMeasurable[CanonicalInitialFiltration.filtration (Z := Z) (I := J) 0]
      (CanonicalInitialFiltration.process (Z := Z) (I := J) 0) :=
    Filtration.stronglyAdapted_natural
      (fun r ↦ (CanonicalInitialFiltration.process_measurable (Z := Z) (I := J) r).stronglyMeasurable) 0
  have hm := continuous_fst.comp_stronglyMeasurable h
  exact hm.aestronglyMeasurable.congr
    (AdditiveCanonical.initialSampler_coe (ULA.CanonicalBrownian.vectorProbability J) μ hμ).symm

/-- The actual globally constructed canonical mean-field sampler has a
current-past measurable L² variable at every time, with its canonical
initial variable and physical Brownian input rather than adaptation premises. -/
theorem canonical_meanField_aestronglyAdapted
    (L : LipschitzDynamics A Z G) (hμ : MemLp (fun z : Z ↦ z) 2 μ) (a : A)
    (K : EuclideanSpace ℝ J →L[ℝ] Z) (t : ℝ≥0) :
    let B := samplerBrownianInput (ULA.CanonicalBrownian.vectorProbability J) K
      ULA.CanonicalBrownian.coordinate ULA.CanonicalBrownian.coordinate_isPreBrownian 0
    AEStronglyMeasurable[(CanonicalBrownianDriver.driver (I := J) μ).filtration t]
      (AdditiveCanonical.flow (ULA.CanonicalBrownian.vectorProbability J) L μ hμ a B
        (samplerBrownianInput_continuous _ _ _ _ _) (samplerBrownianInput_zero _ _ _ _ _) t).2
      (μ.prod (ULA.CanonicalBrownian.vectorProbability J)) := by
  let R := ULA.CanonicalBrownian.vectorProbability J
  let B := samplerBrownianInput R K ULA.CanonicalBrownian.coordinate
    ULA.CanonicalBrownian.coordinate_isPreBrownian 0
  let hB := samplerBrownianInput_continuous R K ULA.CanonicalBrownian.coordinate
    ULA.CanonicalBrownian.coordinate_isPreBrownian 0
  let hB0 := samplerBrownianInput_zero R K ULA.CanonicalBrownian.coordinate
    ULA.CanonicalBrownian.coordinate_isPreBrownian 0
  let D := CanonicalBrownianDriver.driver (I := J) μ
  have hs := AdditiveCanonical.flow_spec R L μ hμ a B hB hB0
  apply meanField_aestronglyAdapted (μ.prod R) L D.filtration _ (AdditiveCanonical.input R μ B)
    hs.1 ((lpPullbackCLM (measurePreserving_snd (μ := μ) (ν := R))).continuous.comp hB)
    (by
      change (lpPullbackCLM (measurePreserving_snd (μ := μ) (ν := R))) (B 0) = 0
      rw [show B 0 = 0 from hB0, map_zero])
  · rw [hs.2]
    exact canonical_initial_measurable μ hμ
  · intro r
    rw [canonical_input_eq]
    exact samplerBrownianInput_aestronglyMeasurable (μ.prod R) D K r

end PBGSO.ConstructedAdaptation

namespace PBGSO.ConstructedAdaptation
open IntegralAdaptation
variable {A G Z X J I : Type*} [Fintype J] [DecidableEq J] [Fintype I]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  (μ : Measure Z) [IsProbabilityMeasure μ] (N : ℕ)

/-- The actual independent-reference initial cloud is measurable in the
constructed full initial-cloud/joint-noise filtration at zero. -/
theorem particle_initial_measurable (hμ : MemLp (fun z : Z ↦ z) 2 μ) (a : A) :
    AEStronglyMeasurable[(ParticleBrownianDriver.driver (J := J) μ N).filtration 0]
      (independentReferenceCLM (A := A) (Z := Z)
        (μ.prod (ULA.CanonicalBrownian.vectorProbability J)) N
        (a, AdditiveCanonical.initialSampler (ULA.CanonicalBrownian.vectorProbability J) μ hμ))
      (ParticleNoiseSpace.probability (J := J) μ N) := by
  let R := ULA.CanonicalBrownian.vectorProbability J
  let Q := μ.prod R
  let QN := ParticleNoiseSpace.probability (J := J) μ N
  let hf := ParticleNoiseSpace.initial_noise_preserving (J := J) μ N
  let D := ParticleBrownianDriver.driver (J := J) μ N
  have h : StronglyMeasurable[CanonicalInitialFiltration.filtration
      (Z := Fin N → Z) (I := Fin N × J) 0]
      (CanonicalInitialFiltration.process (Z := Fin N → Z) (I := Fin N × J) 0) :=
    Filtration.stronglyAdapted_natural
      (fun r ↦ (CanonicalInitialFiltration.process_measurable
        (Z := Fin N → Z) (I := Fin N × J) r).stronglyMeasurable) 0
  have hfst := continuous_fst.comp_stronglyMeasurable h
  have hpull : StronglyMeasurable[D.filtration 0]
      (fun ω : Fin N → Z × ULA.CanonicalBrownian.VectorSample J ↦ fun i ↦ (ω i).1) :=
    hfst.comp_measurable (measurable_iff_comap_le.mpr le_rfl)
  have hraw : StronglyMeasurable[D.filtration 0]
      (fun ω : Fin N → Z × ULA.CanonicalBrownian.VectorSample J ↦ (a, fun i ↦ (ω i).1)) :=
    stronglyMeasurable_const.prodMk hpull
  have hall : ∀ᵐ ω ∂QN, ∀ i : Fin N, AdditiveCanonical.initialSampler R μ hμ (ω i) = (ω i).1 := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : Fin N ↦ Q) i).quasiMeasurePreserving.ae_eq_comp
      (AdditiveCanonical.initialSampler_coe R μ hμ)
  apply hraw.aestronglyMeasurable.congr
  filter_upwards [independentReferenceCLM_coe (A := A) (Z := Z) Q N
    (a, AdditiveCanonical.initialSampler R μ hμ), hall] with ω hp hi
  have hcloud : (a, fun i : Fin N ↦ AdditiveCanonical.initialSampler R μ hμ (ω i)) =
      (a, fun i : Fin N ↦ (ω i).1) := Prod.ext rfl (funext hi)
  exact (hp.trans hcloud).symm

/-- The actual copied canonical sampler input is the physical Brownian
input of the constructed full particle driver. -/
theorem particle_input_eq (K : EuclideanSpace ℝ J →L[ℝ] Z) (t : ℝ) :
    independentReferenceCLM (A := A) (Z := Z)
      (μ.prod (ULA.CanonicalBrownian.vectorProbability J)) N
      (0, AdditiveCanonical.input (ULA.CanonicalBrownian.vectorProbability J) μ
        (samplerBrownianInput (ULA.CanonicalBrownian.vectorProbability J) K
          ULA.CanonicalBrownian.coordinate ULA.CanonicalBrownian.coordinate_isPreBrownian 0) t) =
      samplerBrownianInput (ParticleNoiseSpace.probability (J := J) μ N)
        (ParticleBrownianInput.diffusion (A := A) N K)
        (ParticleBrownianDriver.driver (J := J) μ N).process
        (ParticleBrownianDriver.driver (J := J) μ N).brownian 0 t :=
  ParticleBrownianInput.packed_input_eq μ N K 0 t

/-- Every actual canonical particle realization, including the selected
constructed realization, has a current-past measurable L² state. Its
continuity, initial identity and original equation are used; no adaptedness
or final measurability conclusion is included in that realization structure. -/
theorem particleRealization_aestronglyAdapted
    (L : LipschitzDynamics A Z G) (M : Model A G Z X I)
    (Geo : TwistedGeometry A Z) (hN : 0 < N)
    (hμ : MemLp (fun z : Z ↦ z) 2 μ) (a : A)
    (K : EuclideanSpace ℝ J →L[ℝ] Z) (V : ℝ)
    (P :
      let R := ULA.CanonicalBrownian.vectorProbability J
      let B := samplerBrownianInput R K ULA.CanonicalBrownian.coordinate
        ULA.CanonicalBrownian.coordinate_isPreBrownian 0
      AdditiveParticleRealization (μ.prod R) L M Geo N hN
        (AdditiveCanonical.flow R L μ hμ a B (samplerBrownianInput_continuous _ _ _ _ _)
          (samplerBrownianInput_zero _ _ _ _ _)) (AdditiveCanonical.input R μ B) V)
    (t : ℝ≥0) :
    AEStronglyMeasurable[(ParticleBrownianDriver.driver (J := J) μ N).filtration t]
      (P.state t) (ParticleNoiseSpace.probability (J := J) μ N) := by
  let R := ULA.CanonicalBrownian.vectorProbability J
  let Q := μ.prod R
  let QN := ParticleNoiseSpace.probability (J := J) μ N
  let D := ParticleBrownianDriver.driver (J := J) μ N
  let B := samplerBrownianInput R K ULA.CanonicalBrownian.coordinate
    ULA.CanonicalBrownian.coordinate_isPreBrownian 0
  let hB := samplerBrownianInput_continuous R K ULA.CanonicalBrownian.coordinate
    ULA.CanonicalBrownian.coordinate_isPreBrownian 0
  let hB0 := samplerBrownianInput_zero R K ULA.CanonicalBrownian.coordinate
    ULA.CanonicalBrownian.coordinate_isPreBrownian 0
  let BN := samplerBrownianInput QN (ParticleBrownianInput.diffusion (A := A) N K)
    D.process D.brownian 0
  apply particle_integral_aestronglyAdapted QN L N hN D.filtration P.state BN P.continuous
    (samplerBrownianInput_continuous _ _ _ _ _) (samplerBrownianInput_zero _ _ _ _ _)
  · intro r hr
    have he := P.equation r hr
    rw [particle_input_eq] at he
    exact he
  · rw [P.initial, (AdditiveCanonical.flow_spec R L μ hμ a B hB hB0).2]
    exact particle_initial_measurable μ N hμ a
  · intro r
    exact samplerBrownianInput_aestronglyMeasurable QN D (ParticleBrownianInput.diffusion (A := A) N K) r

end PBGSO.ConstructedAdaptation
