import PBGSO.RawLinearGrowthState

/-! # Original model realization in the linear-growth branch
Primitive original local equations and linear growth derive all global
coefficient moments and the literal constructed predictable model data.
The coefficient identities are original pointwise model realizations on one
full-probability event; no stochastic, law or energy conclusion is supplied.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.RawLinearGrowthModel
open FilteredBrownian ProductLpSections ConstructedPredictableModel
variable {Ω I Z S Θ X : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {D : Driver (I := I) Q} {T : ℝ≥0}

/-- A single full-probability coefficient realization yields genuine
product-a.e. coefficient equality on the finite horizon. -/
theorem product_ae_of_sections (f g : ℝ → Ω → Z)
    (hf : StronglyMeasurable (Function.uncurry f))
    (hg : StronglyMeasurable (Function.uncurry g))
    (he : ∀ r ∈ Icc 0 (T : ℝ), f r =ᵐ[Q] g r) :
    Function.uncurry f =ᵐ[(volume.restrict (Ioc 0 (T : ℝ))).prod Q]
      Function.uncurry g := by
  apply (Measure.ae_prod_iff_ae_ae (hf.measurableSet_eq_fun hg)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  exact he r (Ioc_subset_Icc_self hr)

/-- Original raw model realization. All coefficient and state moments in
this structure are conclusions of `RawLinearGrowthState.Data`, not inputs. -/
structure Realization (M : Model S Θ Z X I)
    (L : RawLocalDiffusion (Z := Z) Q D T) (K P : ℝ)
    (U : RawLinearGrowthState.Data L K P) where
  optimizer : ℝ → S
  optimizerDrift : ℝ → S
  optimizerDrift_integrable : IntervalIntegrable optimizerDrift volume 0 (T : ℝ)
  state_adapted : ∀ t : ℝ≥0, AEStronglyMeasurable[D.filtration t] (U.state t) Q
  diffusion_borel : ∀ θ i, Measurable (fun z => M.diffusion θ z i)
  drift_strong : StronglyMeasurable
    (Function.uncurry (originalRawDrift M optimizer U.state))
  diffusion_strong : ∀ i, StronglyMeasurable
    (Function.uncurry (originalRawDiffusion M optimizer U.state i))
  coefficients : ∀ᵐ ω ∂Q, ∀ r ∈ Icc 0 (T : ℝ),
    U.drift r ω = originalRawDrift M optimizer U.state r ω ∧
      ∀ i, L.sigma i r ω = originalRawDiffusion M optimizer U.state i r ω
  optimizer_field : ∀ t ∈ Icc 0 (T : ℝ), optimizerDrift t =
    M.optimizerField t (optimizer t) (Q.map (U.state t))
  optimizer_equation : ∀ t ∈ Icc 0 (T : ℝ),
    optimizer t = optimizer 0 + ∫ r in 0..t, optimizerDrift r
  observation_integrable : ∀ t ∈ Icc 0 (T : ℝ), Integrable
    (fun z => M.observation (M.parameter (optimizer t)) (M.position z)) (Q.map (U.state t))

namespace Realization
variable {M : Model S Θ Z X I} {L : RawLocalDiffusion (Z := Z) Q D T} {K P : ℝ}
  {U : RawLinearGrowthState.Data L K P} (R : Realization M L K P U)

theorem drift_ae (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) :
    U.drift r =ᵐ[Q] originalRawDrift M R.optimizer U.state r := by
  filter_upwards [R.coefficients] with ω h
  exact (h r hr).1

theorem diffusion_ae (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) (i : I) :
    L.sigma i r =ᵐ[Q] originalRawDiffusion M R.optimizer U.state i r := by
  filter_upwards [R.coefficients] with ω h
  exact (h r hr).2 i

theorem drift_product_ae : Function.uncurry U.drift =ᵐ[
    (volume.restrict (Ioc 0 (T : ℝ))).prod Q]
      Function.uncurry (originalRawDrift M R.optimizer U.state) :=
  product_ae_of_sections U.drift _ U.drift_strong R.drift_strong R.drift_ae

theorem diffusion_product_ae (i : I) : Function.uncurry (L.sigma i) =ᵐ[
    (volume.restrict (Ioc 0 (T : ℝ))).prod Q]
      Function.uncurry (originalRawDiffusion M R.optimizer U.state i) :=
  product_ae_of_sections (L.sigma i) _ (L.sigma_strong i) (R.diffusion_strong i)
    (fun r hr => R.diffusion_ae r hr i)

/-- Global product square moments of the original MODEL coefficients are
transferred from the proved localized moment bounds. -/
theorem coefficients_square :
    Integrable (fun p : ℝ × Ω => ‖originalRawDrift M R.optimizer U.state p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) ∧
    ∀ i, Integrable (fun p : ℝ × Ω =>
      ‖originalRawDiffusion M R.optimizer U.state i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := by
  refine ⟨U.coefficients_square.1.congr (R.drift_product_ae.fun_comp (fun z => ‖z‖ ^ 2)), ?_⟩
  intro i
  exact (U.coefficients_square.2 i).congr
    ((R.diffusion_product_ae i).fun_comp (fun z => ‖z‖ ^ 2))

theorem drift_memLp (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) :
    MemLp (originalRawDrift M R.optimizer U.state r) 2 Q :=
  (memLp_congr_ae (R.drift_ae r hr)).mp (U.global_coefficients r hr).choose

theorem diffusion_memLp (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) (i : I) :
    MemLp (originalRawDiffusion M R.optimizer U.state i r) 2 Q := by
  have hσ := (U.global_coefficients r hr).choose_spec.choose
  have hi : MemLp (L.sigma i r) 2 Q :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : I => Z) i).comp_memLp' hσ
  exact (memLp_congr_ae (R.diffusion_ae r hr i)).mp hi

/-- The original local strong equation is the original MODEL's global
computed integral equation. Both the noise transfer and drift identity are
proved; neither is an interface hypothesis. -/
theorem model_equation (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    U.state t =ᵐ[Q] fun ω => U.state 0 ω +
      (∫ r in 0..t, originalRawDrift M R.optimizer U.state r ω) +
      rawDiffusionIntegral Q D T (originalRawDiffusion M R.optimizer U.state)
        R.diffusion_strong R.coefficients_square.2
        (originalRawDiffusion_adapted Q D M R.optimizer U.state
          R.state_adapted R.diffusion_borel) t.toNNReal ω := by
  have hn := rawDiffusionIntegral_congr_ae_coefficients Q D T L.sigma
    (originalRawDiffusion M R.optimizer U.state) L.sigma_strong R.diffusion_strong
    U.coefficients_square.2 R.coefficients_square.2 L.sigma_adapted
    (originalRawDiffusion_adapted Q D M R.optimizer U.state R.state_adapted R.diffusion_borel)
    R.diffusion_product_ae t.toNNReal
  filter_upwards [U.global_equation t ht, R.coefficients] with ω he hc
  rw [← hn]
  rw [he]
  congr 2
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le ht.1] at hr
  exact (hc r ⟨hr.1, hr.2.trans ht.2⟩).1

/-- Actual predictable Model data are constructed from primitive original
local strong equations and linear growth. Global state/coefficient moments,
noise matching, L² section identities and the sampler equation are derived. -/
def predictableData : ConstructedPredictableModel.Data Q D M T :=
  dataOfRaw Q D M T R.optimizer R.optimizerDrift U.state
    R.optimizerDrift_integrable U.state_memLp R.state_adapted R.diffusion_borel
    R.drift_strong R.diffusion_strong R.coefficients_square.1 R.coefficients_square.2
    R.drift_memLp R.diffusion_memLp R.optimizer_field R.optimizer_equation
    R.model_equation R.observation_integrable

/-- The constructed sampler law is exactly the original raw sampler law. -/
theorem predictableData_law (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    Q.map (R.predictableData.sampler t) = Q.map (U.state t) :=
  rawSampler_section_law Q U.state t (U.state_memLp t ht)

end Realization
end PBGSO.RawLinearGrowthModel
