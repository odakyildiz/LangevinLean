import PBGSO.RawSamplerGrowth
import PBGSO.RawLocalSolutionTransport
import PBGSO.CanonicalSeparable
import PBGSO.ConstructedItoLaw

/-! # Genuine law contraction in the natural linear-growth class
The original raw equations are pulled to each actual initial-coupling
Brownian extension. Primitive linear growth and measurability are preserved;
all coefficient moments and stochastic identities are derived. Taking the
true initial-coupling infimum yields the law bound.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.RawSamplerGrowth
open FilteredBrownian RawLocalStationarity
variable {Ω Ω' S Θ Z X I : Type*}
  [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω'] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {R : Measure Ω'} [IsProbabilityMeasure R]
  {f : Ω → Ω'} (hf : MeasurePreserving f Q R)
  {D : Driver (I := I) R} (E : Driver (I := I) Q)
  (he : ∀ t, (pullbackDriver hf D).filtration t ≤ E.filtration t)
  (hp : ∀ i t, (pullbackDriver hf D).process i t =ᵐ[Q] E.process i t)
  {M : Model S Θ Z X I} {T : ℝ≥0}

/-- Original primitive realization regularity is preserved under the actual
initial/noise map and a valid larger Brownian filtration. -/
def Regularity.pullback {U : RawLocalStationarity.Data R D M T} (A : Regularity U) :
    Regularity (U.pullback hf E he hp) where
  drift_strong := A.drift_strong.comp_measurable
    (measurable_fst.prodMk (hf.measurable.comp measurable_snd))
  drift_progressive t := by
    have hm : @Measurable Ω Ω' (E.filtration t) (D.filtration t) f :=
      measurable_iff_comap_le.mpr (he t)
    exact (A.drift_progressive t).comp_measurable
      (measurable_fst.prodMk (hm.comp measurable_snd))
  diffusion_strong i := (A.diffusion_strong i).comp_measurable
    (measurable_fst.prodMk (hf.measurable.comp measurable_snd))
  drift_borel := A.drift_borel
  diffusion_borel := A.diffusion_borel
  projection_continuous := A.projection_continuous
  growthConstant := A.growthConstant
  growth_nonneg := A.growth_nonneg
  linear_growth := A.linear_growth

/-- The natural source P₂ law condition supplies the actual raw L² state. -/
theorem sampler_memLp (U : RawLocalStationarity.Data Q E M T)
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : MemLp (U.sampler.state t) 2 Q := by
  apply (memLp_two_iff_integrable_sq_norm
    (U.sampler.measurable t ht).stronglyMeasurable.aestronglyMeasurable).mpr
  exact (integrable_map_measure (by fun_prop) (U.sampler.measurable t ht).aemeasurable).mp
    (U.second_moment t ht)

/-- Actual fixed-time L² sections commute with the genuine probability-space
pullback; no prescribed sampler realization is required. -/
theorem pullback_section (U : RawLocalStationarity.Data R D M T)
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    ProductLpSections.sectionLp Q (U.pullback hf E he hp).sampler.state t =
      lpPullbackCLM hf (ProductLpSections.sectionLp R U.sampler.state t) := by
  apply Lp.ext
  have hl := ProductLpSections.sectionLp_ae Q (U.pullback hf E he hp).sampler.state
    (sampler_memLp E (U.pullback hf E he hp) t ht)
  have hr := (lpPullback_coe hf (ProductLpSections.sectionLp R U.sampler.state t)).trans
    (hf.quasiMeasurePreserving.ae_eq_comp (ProductLpSections.sectionLp_ae R U.sampler.state
      (sampler_memLp D U t ht)))
  exact hl.trans hr.symm

end PBGSO.RawSamplerGrowth

namespace PBGSO.RawSamplerGrowthLaw
open FilteredBrownian RawLocalStationarity RawSamplerGrowth ConstructedItoLaw
variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype I] [DecidableEq I]
  (μ ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  (hμ : MemLp (fun z : Z => z) 2 μ) (hν : MemLp (fun z : Z => z) 2 ν)

include hμ hν

/-- Original raw solution laws contract over the genuine infimum of all
initial couplings. The hypotheses are natural original equations, P₂ laws,
primitive realization regularity and linear growth, and source A3. Global
coefficient moments, matching noise and positive-work bounds are derived. -/
theorem law_distance_decay {M : Model S Θ Z X I} {T : ℝ≥0}
    (U : RawLocalStationarity.Data (μ.prod (brownianProbability (I := I)))
      (CanonicalBrownianDriver.driver (I := I) μ) M T)
    (V : RawLocalStationarity.Data (ν.prod (brownianProbability (I := I)))
      (CanonicalBrownianDriver.driver (I := I) ν) M T)
    (A : Regularity U) (B : Regularity V)
    (hU0 : U.sampler.state 0 =ᵐ[μ.prod (brownianProbability (I := I))] fun ω => ω.1)
    (hV0 : V.sampler.state 0 =ᵐ[ν.prod (brownianProbability (I := I))] fun ω => ω.1)
    (G : TwistedGeometry S Z) (ρ : ℝ) (hmono : TwistedJointMonotonicity M G ρ) :
    optimizerLawDistance (U.optimizer T) (V.optimizer T)
      ((μ.prod (brownianProbability (I := I))).map (U.sampler.state T))
      ((ν.prod (brownianProbability (I := I))).map (V.sampler.state T)) ≤
      Real.sqrt G.conditionNumber * Real.exp (-ρ * (T : ℝ)) *
        optimizerLawDistance (U.optimizer 0) (V.optimizer 0) μ ν := by
  have hUI : ProductLpSections.sectionLp (μ.prod (brownianProbability (I := I))) U.sampler.state 0 =
      AdditiveCanonical.initialSampler (brownianProbability (I := I)) μ hμ := by
    apply Lp.ext
    exact (ProductLpSections.sectionLp_ae _ U.sampler.state
      (sampler_memLp _ U 0 ⟨le_rfl,T.coe_nonneg⟩)).trans
      (hU0.trans (AdditiveCanonical.initialSampler_coe _ μ hμ).symm)
  have hVI : ProductLpSections.sectionLp (ν.prod (brownianProbability (I := I))) V.sampler.state 0 =
      AdditiveCanonical.initialSampler (brownianProbability (I := I)) ν hν := by
    apply Lp.ext
    exact (ProductLpSections.sectionLp_ae _ V.sampler.state
      (sampler_memLp _ V 0 ⟨le_rfl,T.coe_nonneg⟩)).trans
      (hV0.trans (AdditiveCanonical.initialSampler_coe _ ν hν).symm)
  apply bound_of_all_finite_couplings μ ν (ULA.wasserstein2_ne_top_of_memLp μ ν hμ hν)
    (fun c => Real.sqrt G.conditionNumber * Real.exp (-ρ * (T : ℝ)) *
      Real.sqrt (‖U.optimizer 0-V.optimizer 0‖ ^ 2+c ^ 2)) (by fun_prop)
  intro c hc
  let Q := ULA.initialExtension c (brownianProbability (I := I))
  letI : IsProbabilityMeasure c.joint := c.isProbabilityMeasure
  letI : IsProbabilityMeasure Q := ULA.initialExtension_isProbabilityMeasure c _
  letI : IsSeparable Q := CanonicalSeparable.initial_vector_isSeparable (I := I) c.joint
  let hf := AdditiveCanonical.extension_left_preserving (brownianProbability (I := I)) μ ν c
  let hg := AdditiveCanonical.extension_right_preserving (brownianProbability (I := I)) μ ν c
  let E := CoupledBrownianFiltration.fullDriver (I := I) μ ν c
  have hp : ∀ i t, (pullbackDriver hf (CanonicalBrownianDriver.driver (I := I) μ)).process i t =ᵐ[Q]
      E.process i t := fun i t => Filter.EventuallyEq.of_eq
        (congrFun (congrFun (CoupledBrownianFiltration.left_process_eq μ ν c) i) t)
  have hq : ∀ i t, (pullbackDriver hg (CanonicalBrownianDriver.driver (I := I) ν)).process i t =ᵐ[Q]
      E.process i t := fun i t => Filter.EventuallyEq.of_eq
        (congrFun (congrFun (CoupledBrownianFiltration.right_process_eq μ ν c) i) t)
  let he := CoupledBrownianFiltration.left_filtration_le (I := I) μ ν c
  let hk := CoupledBrownianFiltration.right_filtration_le (I := I) μ ν c
  let Uc := U.pullback hf E he hp
  let Vc := V.pullback hg E hk hq
  have h := RawSamplerGrowth.law_distance_decay Uc Vc
    (A.pullback hf E he hp) (B.pullback hg E hk hq) G ρ hmono
  have huLaw : Q.map (Uc.sampler.state T) = (μ.prod (brownianProbability (I := I))).map (U.sampler.state T) :=
    U.sampler.pullback_law hf E he hp T ⟨T.coe_nonneg,le_rfl⟩
  have hvLaw : Q.map (Vc.sampler.state T) = (ν.prod (brownianProbability (I := I))).map (V.sampler.state T) :=
    V.sampler.pullback_law hg E hk hq T ⟨T.coe_nonneg,le_rfl⟩
  rw [huLaw,hvLaw] at h
  change optimizerLawDistance (U.optimizer T) (V.optimizer T)
    ((μ.prod (brownianProbability (I := I))).map (U.sampler.state T))
    ((ν.prod (brownianProbability (I := I))).map (V.sampler.state T)) ≤
    Real.sqrt G.conditionNumber * Real.exp (-ρ * (T : ℝ)) *
      Real.sqrt (‖U.optimizer 0-V.optimizer 0‖ ^ 2+
        ‖ProductLpSections.sectionLp Q Uc.sampler.state 0-
          ProductLpSections.sectionLp Q Vc.sampler.state 0‖ ^ 2) at h
  rw [pullback_section (ht := ⟨le_rfl,T.coe_nonneg⟩),
    pullback_section (ht := ⟨le_rfl,T.coe_nonneg⟩),hUI,hVI,
    initial_difference_norm_sq μ ν hμ hν c] at h
  exact h

end PBGSO.RawSamplerGrowthLaw
