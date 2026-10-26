import PBGSO.PathEnergyStopping
import PBGSO.ProductLpSections
import PBGSO.PredictableCurveIntegral

/-! # Actual L² diffusion columns obtained by first-hit localization
The primitive path energy is an integral of the raw local square coefficient.
No stopped energy budget or time-L²-valued coefficient curve is assumed.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter TopologicalSpace
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.LocalizedDiffusion
variable {Ω Z : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]

/-- Literal restriction of the raw coefficient at the actual random time. -/
def stoppedField (τ : Ω → ℝ≥0) (f : ℝ → Ω → Z) (r : ℝ) (ω : Ω) : Z :=
  if r ≤ (τ ω : ℝ) then f r ω else 0

theorem stoppedField_stronglyMeasurable (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (f : ℝ → Ω → Z) (hf : StronglyMeasurable (Function.uncurry f)) :
    StronglyMeasurable (Function.uncurry (stoppedField τ f)) := by
  exact hf.piecewise (measurableSet_le measurable_fst
    (measurable_coe_nnreal_real.comp (hτ.comp measurable_snd))) stronglyMeasurable_const

/-- The stopping mask uses only information available at the current time. -/
theorem stoppedField_adapted (ℱ : Filtration ℝ≥0 mΩ) (τ : Ω → ℝ≥0)
    (hstop : ∀ t, MeasurableSet[ℱ t] {ω | τ ω ≤ t}) (f : ℝ → Ω → Z)
    (Q : Measure Ω)
    (hf : ∀ t : ℝ≥0, AEStronglyMeasurable[ℱ t] (f t) Q) (t : ℝ≥0) :
    AEStronglyMeasurable[ℱ t] (stoppedField τ f t) Q := by
  have hs : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)) := by
    intro t
    simpa only [WithTop.coe_le_coe] using hstop t
  have hm : MeasurableSet[ℱ t] {ω | (t : ℝ) ≤ (τ ω : ℝ)} := by
    simpa only [WithTop.coe_le_coe, NNReal.coe_le_coe] using hs.measurableSet_ge t
  refine ⟨{ω | (t : ℝ) ≤ (τ ω : ℝ)}.indicator ((hf t).mk (f t)),
    (hf t).stronglyMeasurable_mk.indicator hm, ?_⟩
  filter_upwards [(hf t).ae_eq_mk] with ω hω
  unfold stoppedField
  by_cases h : t ≤ τ ω <;> simp [h, hω, NNReal.coe_le_coe]

/-- A local raw scalar energy becomes genuinely product-integrable after
first-hit stopping. The cap follows from continuity and first-hit minimality. -/
theorem firstHit_scalar_integrable
    (Q : Measure Ω) [IsProbabilityMeasure Q] (T : ℝ≥0)
    (q : ℝ → Ω → ℝ) (hq : StronglyMeasurable (Function.uncurry q))
    (hpos : ∀ r ω, 0 ≤ q r ω)
    (hlocal : ∀ ω, IntegrableOn (fun r => q r ω) (Ioc 0 (T : ℝ)))
    (A : ℝ≥0 → Ω → ℝ) (hA : ∀ ω, Continuous (fun t => A t ω))
    (hint : ∀ t : ℝ≥0, t ≤ T → ∀ ω, A t ω = ∫ r in Ioc 0 (t : ℝ), q r ω)
    (c : ℝ) (hc : 0 ≤ c)
    (hτ : Measurable (PathEnergyStopping.firstHit T A c)) :
    Integrable (fun p : ℝ × Ω =>
      stoppedField (PathEnergyStopping.firstHit T A c) q p.1 p.2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) ∧
    (∫ p : ℝ × Ω,
      stoppedField (PathEnergyStopping.firstHit T A c) q p.1 p.2
        ∂((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) ≤ c := by
  let τ := PathEnergyStopping.firstHit T A c
  have hτT (ω) : τ ω ≤ T := PathEnergyStopping.firstHit_le_horizon T A c ω (hA ω)
  have hzero (ω) : A 0 ω ≤ c := by
    rw [hint 0 bot_le ω]
    simpa using hc
  have hcap (ω) : A (τ ω) ω ≤ c :=
    PathEnergyStopping.firstHit_energy_le T A c ω (hA ω) (hzero ω)
  have hfield := stoppedField_stronglyMeasurable τ hτ q hq
  have hsection (ω) : IntegrableOn (fun r => stoppedField τ q r ω) (Ioc 0 (T : ℝ)) := by
    change Integrable (fun r => if r ≤ (τ ω : ℝ) then q r ω else 0) _
    exact (hlocal ω).indicator measurableSet_Iic
  have heq (ω) : (∫ r in Ioc 0 (T : ℝ), stoppedField τ q r ω) = A (τ ω) ω := by
    rw [hint (τ ω) (hτT ω) ω]
    change (∫ r in Ioc 0 (T : ℝ), (Iic (τ ω : ℝ)).indicator (fun r => q r ω) r) = _
    rw [setIntegral_indicator measurableSet_Iic]
    have hs : Iic (τ ω : ℝ) ∩ Ioc 0 (T : ℝ) = Ioc 0 (τ ω : ℝ) := by
      ext r
      simp only [mem_inter_iff, mem_Ioc, mem_Iic]
      constructor
      · rintro ⟨hrτ,hr0,hrT⟩
        exact ⟨hr0,hrτ⟩
      · rintro ⟨hr0,hrτ⟩
        exact ⟨hrτ,hr0,hrτ.trans (by exact_mod_cast hτT ω)⟩
    rw [Set.inter_comm, hs]
  have hnorm (ω) : (∫ r in Ioc 0 (T : ℝ), ‖stoppedField τ q r ω‖) = A (τ ω) ω := by
    rw [← heq ω]
    apply integral_congr_ae
    filter_upwards with r
    exact Real.norm_of_nonneg (by unfold stoppedField; split_ifs <;> simp [hpos])
  have hiA : Integrable (fun ω => ∫ r in Ioc 0 (T : ℝ), ‖stoppedField τ q r ω‖) Q := by
    apply (integrable_const c).mono'
      hfield.norm.integral_prod_left.aestronglyMeasurable
    filter_upwards with ω
    rw [hnorm ω, Real.norm_eq_abs, abs_of_nonneg]
    · exact hcap ω
    · rw [← heq ω]
      exact integral_nonneg (fun r => by unfold stoppedField; split_ifs <;> simp [hpos])
  have hi := (integrable_prod_iff' hfield.aestronglyMeasurable).mpr
    ⟨Eventually.of_forall hsection, hiA⟩
  refine ⟨hi, ?_⟩
  change (∫ p : ℝ × Ω, Function.uncurry (stoppedField τ q) p
    ∂((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) ≤ c
  rw [integral_prod_symm _ hi]
  calc
    _ ≤ ∫ _ : Ω, c ∂Q := integral_mono hi.integral_prod_right (integrable_const c)
      (fun ω => by change (∫ r in Ioc 0 (T : ℝ), stoppedField τ q r ω) ≤ c; rw [heq ω]; exact hcap ω)
    _ = c := by simp


/-- The first-hit cap makes each original physical diffusion column
square-integrable on the actual time/sample product space. -/
theorem firstHit_column_square_integrable
    (Q : Measure Ω) [IsProbabilityMeasure Q] (T : ℝ≥0)
    (q : ℝ → Ω → ℝ) (hq : StronglyMeasurable (Function.uncurry q))
    (hpos : ∀ r ω, 0 ≤ q r ω)
    (hlocal : ∀ ω, IntegrableOn (fun r => q r ω) (Ioc 0 (T : ℝ)))
    (A : ℝ≥0 → Ω → ℝ) (hA : ∀ ω, Continuous (fun t => A t ω))
    (hint : ∀ t : ℝ≥0, t ≤ T → ∀ ω, A t ω = ∫ r in Ioc 0 (t : ℝ), q r ω)
    (c : ℝ) (hc : 0 ≤ c)
    (hτ : Measurable (PathEnergyStopping.firstHit T A c))
    (f : ℝ → Ω → Z) (hf : StronglyMeasurable (Function.uncurry f))
    (hdom : ∀ r ω, ‖f r ω‖ ^ 2 ≤ q r ω) :
    Integrable (fun p : ℝ × Ω =>
      ‖stoppedField (PathEnergyStopping.firstHit T A c) f p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := by
  have hi := (firstHit_scalar_integrable Q T q hq hpos hlocal A hA hint c hc hτ).1
  apply hi.mono'
    ((stoppedField_stronglyMeasurable _ hτ f hf).norm.pow 2).aestronglyMeasurable
  filter_upwards with p
  change ‖‖stoppedField (PathEnergyStopping.firstHit T A c) f p.1 p.2‖ ^ 2‖ ≤ _
  unfold stoppedField
  by_cases h : p.1 ≤ (PathEnergyStopping.firstHit T A c p.2 : ℝ)
  · rw [ite_eq_left h, ite_eq_left h, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ‖f p.1 p.2‖)]
    exact hdom _ _
  · simp [h]

/-- The genuine Bochner time-L² diffusion curve is constructed from the raw
locally square-integrable coefficient and a genuine first-hit stop. -/
theorem firstHit_column_sections_memLp [SeparableSpace Z]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (T : ℝ≥0)
    (q : ℝ → Ω → ℝ) (hq : StronglyMeasurable (Function.uncurry q))
    (hpos : ∀ r ω, 0 ≤ q r ω)
    (hlocal : ∀ ω, IntegrableOn (fun r => q r ω) (Ioc 0 (T : ℝ)))
    (A : ℝ≥0 → Ω → ℝ) (hA : ∀ ω, Continuous (fun t => A t ω))
    (hint : ∀ t : ℝ≥0, t ≤ T → ∀ ω, A t ω = ∫ r in Ioc 0 (t : ℝ), q r ω)
    (c : ℝ) (hc : 0 ≤ c)
    (hτ : Measurable (PathEnergyStopping.firstHit T A c))
    (f : ℝ → Ω → Z) (hf : StronglyMeasurable (Function.uncurry f))
    (hdom : ∀ r ω, ‖f r ω‖ ^ 2 ≤ q r ω) :
    MemLp (ProductLpSections.sectionLp Q
      (stoppedField (PathEnergyStopping.firstHit T A c) f)) 2
      (volume.restrict (Ioc 0 (T : ℝ))) :=
  ProductLpSections.sectionLp_memLp _ Q _
    (stoppedField_stronglyMeasurable _ hτ f hf)
    (firstHit_column_square_integrable Q T q hq hpos hlocal A hA hint c hc hτ f hf hdom)

/-- First-hit localization constructs all genuine adapted physical columns,
their time-L² membership, their raw coefficient meaning, and their total
energy bound. Only raw pathwise-local energy and actual adaptedness enter. -/
theorem firstHit_physical_columns {I : Type*} [Fintype I] [DecidableEq I]
    [SeparableSpace Z] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (ℱ : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (q : ℝ → Ω → ℝ) (hq : StronglyMeasurable (Function.uncurry q))
    (hpos : ∀ r ω, 0 ≤ q r ω)
    (hlocal : ∀ ω, IntegrableOn (fun r => q r ω) (Ioc 0 (T : ℝ)))
    (A : ℝ≥0 → Ω → ℝ) (hA : ∀ ω, Continuous (fun t => A t ω))
    (hmono : ∀ ω, Monotone (fun t => A t ω))
    (hAA : ∀ t, Measurable[ℱ t] (A t))
    (hint : ∀ t : ℝ≥0, t ≤ T → ∀ ω, A t ω = ∫ r in Ioc 0 (t : ℝ), q r ω)
    (c : ℝ) (hc : 0 ≤ c)
    (f : I → ℝ → Ω → Z) (hf : ∀ i, StronglyMeasurable (Function.uncurry (f i)))
    (hadapt : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[ℱ t] (f i t) Q)
    (hdom : ∀ r ω, ∑ i, ‖f i r ω‖ ^ 2 ≤ q r ω) :
    let τ := PathEnergyStopping.firstHit T A c
    let u := ProductLpSections.columnSections Q (fun i => stoppedField τ (f i))
    (∀ t, MeasurableSet[ℱ t] {ω | τ ω ≤ t}) ∧
    MemLp u 2 (volume.restrict (Ioc 0 (T : ℝ))) ∧
    (∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[ℱ t] ((u t).ofLp i) Q) ∧
    (∀ᵐ t ∂volume.restrict (Ioc 0 (T : ℝ)), ∀ i, (u t).ofLp i =ᵐ[Q] stoppedField τ (f i) t) ∧
    (∫ t in Ioc 0 (T : ℝ), ‖u t‖ ^ 2) ≤ c := by
  classical
  let τ := PathEnergyStopping.firstHit T A c
  have hs := PathEnergyStopping.firstHit_stopping ℱ T A c hA hmono hAA
  have hτ : Measurable τ := by
    apply measurable_of_Iic
    intro t
    exact ℱ.le t _ (hs t)
  have hdi (i : I) (r : ℝ) (ω : Ω) : ‖f i r ω‖ ^ 2 ≤ q r ω := by
    apply le_trans _ (hdom r ω)
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖f j r ω‖) (Finset.mem_univ i)
  have hm (i : I) := stoppedField_stronglyMeasurable τ hτ (f i) (hf i)
  have h2 (i : I) := firstHit_column_square_integrable Q T q hq hpos hlocal A hA hint c hc hτ
    (f i) (hf i) (hdi i)
  refine ⟨hs, ProductLpSections.columnSections_memLp _ Q _ hm h2, ?_,
    ProductLpSections.columnSections_ae _ Q _ hm h2, ?_⟩
  · intro t i
    change AEStronglyMeasurable[ℱ t]
      (ProductLpSections.sectionLp Q (stoppedField τ (f i)) (t : ℝ)) Q
    apply ProductLpSections.sectionLp_adapted Q (ℱ t)
    exact stoppedField_adapted ℱ τ hs (f i) Q (fun t => hadapt t i) t
  · rw [ProductLpSections.integral_columnSections_norm_sq _ Q _ hm h2,
      ← integral_finsetSum Finset.univ (fun i _ => h2 i)]
    have hqi := firstHit_scalar_integrable Q T q hq hpos hlocal A hA hint c hc hτ
    apply le_trans (integral_mono (integrable_finsetSum _ (fun i _ => h2 i)) hqi.1 _) hqi.2
    intro p
    change (∑ i, ‖stoppedField τ (f i) p.1 p.2‖ ^ 2) ≤ stoppedField τ q p.1 p.2
    by_cases h : p.1 ≤ (τ p.2 : ℝ)
    · simpa only [stoppedField, if_pos h] using hdom p.1 p.2
    · simp [stoppedField, h]

end PBGSO.LocalizedDiffusion
