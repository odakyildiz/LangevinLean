import PBGSO.RawDiffusionAlgebra
import PBGSO.ConstructedPredictableModel
import PBGSO.LpIntegralSections

/-! # Original raw model equations yield actual L² model data
The sampler, drift and diffusion L² curves are literal constructed sections
of the original raw fields. Product square integrability supplies their
Bochner time integrability; Fubini derives the L² sampler integral equation.
No matching L² curve, noise law, or expected energy identity is supplied.
This is an intermediate factory: raw product/fixed-time moments are explicit
inputs to be derived from the paper's growth/solution assumptions separately.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.ConstructedPredictableModel
open FilteredBrownian ProductLpSections
variable {Ω I Z S Θ X : Type*} [mΩ : MeasurableSpace Ω]
  [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  (D : Driver (I := I) Q) (M : Model S Θ Z X I)

/-- Constructing the actual sampler section preserves its literal marginal
law; this is equality of measures, not a supplied output-law premise. -/
theorem rawSampler_section_law (Y : ℝ → Ω → Z) (t : ℝ) (ht : MemLp (Y t) 2 Q) :
    Q.map (sectionLp Q Y t) = Q.map (Y t) :=
  Measure.map_congr (sectionLp_ae Q Y ht)

/-- The original model drift evaluated on the actual raw trajectory. -/
def originalRawDrift (a : ℝ → S) (Y : ℝ → Ω → Z) : ℝ → Ω → Z :=
  fun t ω => M.drift (M.parameter (a t)) (Y t ω)

/-- The original finite diffusion columns on the actual raw trajectory. -/
def originalRawDiffusion (a : ℝ → S) (Y : ℝ → Ω → Z) : I → ℝ → Ω → Z :=
  fun i t ω => M.diffusion (M.parameter (a t)) (Y t ω) i

/-- Original coefficient measurability and actual raw-state adaptedness
suffice to prove adaptedness of the original diffusion fields. -/
theorem originalRawDiffusion_adapted (a : ℝ → S) (Y : ℝ → Ω → Z)
    (hY : ∀ t : ℝ≥0, AEStronglyMeasurable[D.filtration t] (Y t) Q)
    (hσ : ∀ θ i, Measurable (fun z => M.diffusion θ z i))
    (t : ℝ≥0) (i : I) :
    AEStronglyMeasurable[D.filtration t] (originalRawDiffusion M a Y i t) Q := by
  let g : Z → Z := fun z => M.diffusion (M.parameter (a t)) z i
  refine ⟨g ∘ (hY t).mk (Y t), ?_, ?_⟩
  · exact ((hσ _ i).comp (hY t).stronglyMeasurable_mk.measurable).stronglyMeasurable
  · exact (hY t).ae_eq_mk.fun_comp g

/-- The actual drift section curve is Bochner time-L¹ on the finite horizon,
derived from raw product-time square integrability and finite time measure. -/
theorem rawDrift_sections_intervalIntegrable (T : ℝ≥0) (b : ℝ → Ω → Z)
    (hb : StronglyMeasurable (Function.uncurry b))
    (h2 : Integrable (fun p : ℝ × Ω => ‖b p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) :
    IntervalIntegrable (sectionLp Q b) volume 0 (T : ℝ) := by
  rw [intervalIntegrable_iff, uIoc_of_le T.coe_nonneg]
  exact (sectionLp_memLp (volume.restrict (Ioc 0 (T : ℝ))) Q b hb h2).integrable (by norm_num)

/-- Bochner integration of constructed raw drift sections agrees with the
literal pathwise drift primitive; proved by product Fubini on every subinterval. -/
theorem rawDrift_sections_integral_ae (T : ℝ≥0) (b : ℝ → Ω → Z)
    (hb : StronglyMeasurable (Function.uncurry b))
    (h2 : Integrable (fun p : ℝ × Ω => ‖b p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    (∫ r in 0..t, sectionLp Q b r) =ᵐ[Q] (fun ω => ∫ r in 0..t, b r ω) := by
  have hi := (rawDrift_sections_intervalIntegrable Q T b hb h2).mono_set (by
    rw [uIcc_of_le ht.1, uIcc_of_le T.coe_nonneg]
    exact Icc_subset_Icc le_rfl ht.2)
  have hle : (volume : Measure ℝ).restrict (Ioc 0 t) ≤ volume.restrict (Ioc 0 (T : ℝ)) :=
    Measure.restrict_mono_set _ (Ioc_subset_Ioc le_rfl ht.2)
  have hsec : ∀ᵐ r ∂volume.restrict (Ioc 0 t), b r =ᵐ[Q] sectionLp Q b r := by
    filter_upwards [(ae_memLp (volume.restrict (Ioc 0 (T : ℝ))) Q b hb h2).filter_mono
      (ae_mono hle)] with r hr
    exact (sectionLp_ae Q b hr).symm
  simp_rw [intervalIntegral.integral_of_le ht.1]
  exact LpIntegralSections.integral_coe_ae Q (volume.restrict (Ioc 0 t))
    (sectionLp Q b) hi.1 b hb.aestronglyMeasurable hsec

/-- A literal factory from original raw trajectory equations to constructed
predictable model data. All L² curves and their sampler equation are derived.
Raw fixed-time/product moments remain explicit intermediate hypotheses. -/
def dataOfRaw (T : ℝ≥0) (a g : ℝ → S) (Y : ℝ → Ω → Z)
    (hg : IntervalIntegrable g volume 0 (T : ℝ))
    (hY2 : ∀ t ∈ Icc 0 (T : ℝ), MemLp (Y t) 2 Q)
    (hY : ∀ t : ℝ≥0, AEStronglyMeasurable[D.filtration t] (Y t) Q)
    (hσBorel : ∀ θ i, Measurable (fun z => M.diffusion θ z i))
    (hb : StronglyMeasurable (Function.uncurry (originalRawDrift M a Y)))
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (originalRawDiffusion M a Y i)))
    (hb2 : Integrable (fun p : ℝ × Ω => ‖originalRawDrift M a Y p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hσ2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖originalRawDiffusion M a Y i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hbt : ∀ t ∈ Icc 0 (T : ℝ), MemLp (originalRawDrift M a Y t) 2 Q)
    (hσt : ∀ t ∈ Icc 0 (T : ℝ), ∀ i, MemLp (originalRawDiffusion M a Y i t) 2 Q)
    (hgField : ∀ t ∈ Icc 0 (T : ℝ), g t = M.optimizerField t (a t) (Q.map (Y t)))
    (haEq : ∀ t ∈ Icc 0 (T : ℝ), a t = a 0 + ∫ r in 0..t, g r)
    (hYEq : ∀ t ∈ Icc 0 (T : ℝ), Y t =ᵐ[Q] (fun ω => Y 0 ω +
      (∫ r in 0..t, originalRawDrift M a Y r ω) +
      rawDiffusionIntegral Q D T (originalRawDiffusion M a Y) hσ hσ2
        (originalRawDiffusion_adapted Q D M a Y hY hσBorel) t.toNNReal ω))
    (hobs : ∀ t ∈ Icc 0 (T : ℝ), Integrable
      (fun z => M.observation (M.parameter (a t)) (M.position z)) (Q.map (Y t))) :
    Data Q D M T where
  optimizer := a
  optimizerDrift := g
  sampler := sectionLp Q Y
  drift := sectionLp Q (originalRawDrift M a Y)
  diffusion := rawDiffusionCurve Q (originalRawDiffusion M a Y)
  optimizerDrift_integrable := hg
  drift_integrable := rawDrift_sections_intervalIntegrable Q T _ hb hb2
  diffusion_square := rawDiffusionCurve_square Q T _ hσ hσ2
  sampler_adapted t := sectionLp_adapted Q (D.filtration t) Y t (hY t)
  diffusion_adapted := rawDiffusionCurve_adapted Q D _
    (originalRawDiffusion_adapted Q D M a Y hY hσBorel)
  optimizerDrift_realizes t ht := by
    rw [Measure.map_congr (sectionLp_ae Q Y (hY2 t ht))]
    exact hgField t ht
  optimizer_integral := haEq
  sampler_integral t ht := by
    change sectionLp Q Y t = sectionLp Q Y 0 + (∫ r in 0..t, sectionLp Q (originalRawDrift M a Y) r) +
      rawDiffusionIntegral Q D T (originalRawDiffusion M a Y) hσ hσ2
        (originalRawDiffusion_adapted Q D M a Y hY hσBorel) t.toNNReal
    apply Lp.ext
    filter_upwards [sectionLp_ae Q Y (hY2 t ht), sectionLp_ae Q Y (hY2 0 ⟨le_rfl,T.coe_nonneg⟩),
      rawDrift_sections_integral_ae Q T _ hb hb2 t ht, hYEq t ht,
      Lp.coeFn_add (sectionLp Q Y 0 + ∫ r in 0..t, sectionLp Q (originalRawDrift M a Y) r)
        (rawDiffusionIntegral Q D T (originalRawDiffusion M a Y) hσ hσ2
          (originalRawDiffusion_adapted Q D M a Y hY hσBorel) t.toNNReal),
      Lp.coeFn_add (sectionLp Q Y 0) (∫ r in 0..t, sectionLp Q (originalRawDrift M a Y) r)]
      with ω hyt hy0 hi he ha hb
    rw [ha, Pi.add_apply, hb, Pi.add_apply, hyt, hy0, hi]
    exact he
  drift_realizes t ht := by
    filter_upwards [sectionLp_ae Q (originalRawDrift M a Y) (hbt t ht),
      sectionLp_ae Q Y (hY2 t ht)] with ω hb hy
    rw [hb, hy]
    rfl
  diffusion_realizes t ht i := by
    filter_upwards [sectionLp_ae Q (originalRawDiffusion M a Y i) (hσt t ht i),
      sectionLp_ae Q Y (hY2 t ht)] with ω hb hy
    change sectionLp Q (originalRawDiffusion M a Y i) t ω = _
    rw [hb, hy]
    rfl
  observation_integrable t ht := by
    rw [Measure.map_congr (sectionLp_ae Q Y (hY2 t ht))]
    exact hobs t ht

end PBGSO.ConstructedPredictableModel
