import PBGSO.RawNaturalSampler
import PBGSO.RawCoerciveMoment
import PBGSO.DiracSamplerCoercivity

/-! Natural constant-diffusion equations have actual product-space second
moments under source joint monotonicity. The stochastic energy and moment
bounds are derived; no work-integrability convention is needed here. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators RealInnerProductSpace InnerProductSpace
namespace PBGSO.RawSamplerCoerciveMoment
open FilteredBrownian
variable {Ω S Θ Z X I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [FiniteDimensional ℝ Z]
  {Q : Measure Ω} [IsProbabilityMeasure Q] {D : Driver (I := I) Q}
  {M : Model S Θ Z X I} {T : ℝ≥0} {a : ℝ → S}

theorem realization_moments (U : RawLocalStationarity.SamplerData Q D M T a)
    (R : RawNaturalSampler.Realization U) (ha : ContinuousOn a (Icc 0 (T : ℝ)))
    (G : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M G ρ)
    (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i) :
    (∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc 0 (T : ℝ),
      ∃ hx : MemLp (U.state t) 2 Q, ‖hx.toLp (U.state t)‖^2 ≤ B) ∧
    MemLp (Function.uncurry U.state) 2 ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := by
  classical
  let K := a '' Icc 0 (T : ℝ)
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn ha
  obtain ⟨C,hC,hCr⟩ := DiracSamplerCoercivity.radial_coercivity_on_compact
    M G ρ hρ.le hmono hρ K hK
  let c : I → Z := M.diffusion (M.parameter (a 0)) 0
  let S : ℝ := ∑ i, G.samplerSq (c i)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => G.samplerSq_nonneg _)
  have hwork : ∀ r ∈ Icc 0 (T : ℝ), ∀ᵐ ω ∂Q,
      ⟪R.data.state r ω,G.samplerWeight (R.data.drift r ω)⟫_ℝ ≤ C := by
    intro r hr
    filter_upwards [R.drift_realizes] with ω hb
    rw [hb r hr]
    exact hCr (a r) ⟨r,hr,rfl⟩ _
  have hnoise : ∀ r ∈ Icc 0 (T : ℝ), ∀ᵐ ω ∂Q,
      (∑ i, ⟪R.localDiffusion.sigma i r ω,G.samplerWeight (R.localDiffusion.sigma i r ω)⟫_ℝ) ≤ S := by
    intro r hr
    filter_upwards [R.sigma_realizes] with ω hσr
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro i hi
    rw [hσr r hr i,hσ (a r) (a 0) (R.data.state r ω) 0 i]
    rfl
  have hcoerc : ∀ z, G.lower*‖z‖^2 ≤ ⟪z,G.samplerWeight z⟫_ℝ := G.sampler_lower
  let B := RawCoerciveMoment.budget R.data G.samplerWeight G.lower C S
  have hB : 0 ≤ B := RawCoerciveMoment.budget_nonneg R.data G.samplerWeight
    G.sampler_symmetric G.lower C S G.lower_pos hC hS hcoerc hwork hnoise
  have hbound := RawCoerciveMoment.state_moment_bound R.data G.samplerWeight
    G.sampler_symmetric G.lower C S G.lower_pos hC hS hcoerc hwork hnoise
  have hp := RawCoerciveMoment.state_product_memLp R.data G.samplerWeight
    G.sampler_symmetric G.lower C S G.lower_pos hC hS hcoerc hwork hnoise
  have heq : Function.uncurry R.data.state =ᵐ[(volume.restrict (Ioc 0 (T : ℝ))).prod Q]
      Function.uncurry U.state := by
    have hx := (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (Ioc 0 (T : ℝ))) (ν := Q)).ae R.state_eq
    have hr := (Measure.quasiMeasurePreserving_fst
      (μ := volume.restrict (Ioc 0 (T : ℝ))) (ν := Q)).ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hx,hr] with p hx hr
    exact hx p.1 (Ioc_subset_Icc_self hr)
  refine ⟨⟨B,hB,?_⟩,(memLp_congr_ae heq).mp hp⟩
  intro t ht
  obtain ⟨hx,hxb⟩ := hbound t ht
  have he : R.data.state t =ᵐ[Q] U.state t := R.state_eq.mono (fun _ h => h t ht)
  have hu : MemLp (U.state t) 2 Q := (memLp_congr_ae he).mp hx
  refine ⟨hu,?_⟩
  rwa [← hx.toLp_congr hu he]

theorem natural_moments (U : RawLocalStationarity.Data Q D M T)
    (hDrift : Measurable (fun p : S × Z => M.drift (M.parameter p.1) p.2))
    (G : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M G ρ)
    (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i) :
    (∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc 0 (T : ℝ),
      ∃ hx : MemLp (U.sampler.state t) 2 Q, ‖hx.toLp (U.sampler.state t)‖^2 ≤ B) ∧
    MemLp (Function.uncurry U.sampler.state) 2 ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) :=
  realization_moments U.sampler (RawNaturalSampler.build_model U hDrift)
    (RawSamplerGrowth.optimizer_continuous U) G ρ hρ hmono hσ

/-- A common whole-horizon version change preserves the derived actual
product moment, including when the original version was not jointly Borel. -/
theorem product_memLp_congr_on_horizon {x y : ℝ → Ω → Z}
    (hx : MemLp (Function.uncurry x) 2 ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (he : ∀ᵐ ω ∂Q, ∀ r ∈ Icc 0 (T : ℝ), x r ω = y r ω) :
    MemLp (Function.uncurry y) 2 ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := by
  have heq : Function.uncurry x =ᵐ[(volume.restrict (Ioc 0 (T : ℝ))).prod Q]
      Function.uncurry y := by
    have hh := (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (Ioc 0 (T : ℝ))) (ν := Q)).ae he
    have hr := (Measure.quasiMeasurePreserving_fst
      (μ := volume.restrict (Ioc 0 (T : ℝ))) (ν := Q)).ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hh,hr] with p hh hr
    exact hh p.1 (Ioc_subset_Icc_self hr)
  exact (memLp_congr_ae heq).mp hx

end PBGSO.RawSamplerCoerciveMoment
