import PBGSO.CountableProductDependence
import PBGSO.LpPullback
import Mathlib.MeasureTheory.Function.LpSeminorm.Trim
import PBGSO.LpIntegralSections
import ProximalLangevin.SplittingL2Energy
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! # Actual L² sections of product-space random fields
A jointly strongly measurable, square-integrable field induces a genuine
Bochner time-L² family of spatial L² variables. No ambient measure separability is required: the field itself determines a
countably generated spatial subalgebra, enlarged by a finite-measure cover.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal Topology
namespace PBGSO.ProductLpSections
variable {T Ω R : Type*} [mT : MeasurableSpace T] [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup R] [InnerProductSpace ℝ R] [CompleteSpace R]
  (μ : Measure T) [SFinite μ] (Q : Measure Ω) [SigmaFinite Q]

/-- The actual spatial L² section, set to zero on non-L² sections. -/
def sectionLp (f : T → Ω → R) (t : T) : Lp R 2 Q :=
  by
    classical
    exact if h : MemLp (f t) 2 Q then h.toLp (f t) else 0

theorem sectionLp_ae (f : T → Ω → R) {t : T} (ht : MemLp (f t) 2 Q) :
    sectionLp Q f t =ᵐ[Q] f t := by
  simp only [sectionLp, dite_eq_left ht]
  exact ht.coeFn_toLp

private theorem measurable_distance_criterion {A B : Type*} [MeasurableSpace A]
    [PseudoMetricSpace B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
    (g : A → B) (hg : ∀ b, Measurable (fun a => dist (g a) b)) : Measurable g := by
  have hbase : IsTopologicalBasis {s : Set B | ∃ b r, s = Metric.ball b r} := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro _ ⟨b,r,rfl⟩
      exact Metric.isOpen_ball
    · intro b s hbs hs
      obtain ⟨r,hr,hrs⟩ := Metric.isOpen_iff.mp hs b hbs
      exact ⟨Metric.ball b r, ⟨b,r,rfl⟩, Metric.mem_ball_self hr, hrs⟩
  have hm : @Measurable A B _ (borel B) g := by
    rw [hbase.borel_eq_generateFrom]
    apply measurable_generateFrom
    rintro _ ⟨b,r,rfl⟩
    exact measurableSet_lt (hg b) measurable_const
  exact hm.mono le_rfl (by rw [BorelSpace.measurable_eq (α := B)])

private theorem measurable_section_eLpNorm (f : T → Ω → R)
    (hf : StronglyMeasurable (Function.uncurry f)) :
    Measurable (fun t => eLpNorm (f t) 2 Q) := by
  have hlin : Measurable (fun t => ∫⁻ ω, ‖f t ω‖ₑ ^ (2 : ℝ) ∂Q) :=
    (hf.enorm.pow_const (2 : ℝ)).lintegral_prod_right'
  have he (t : T) : eLpNorm (f t) 2 Q =
      (∫⁻ ω, ‖f t ω‖ₑ ^ (2 : ℝ) ∂Q) ^ (1 / (2 : ℝ)) := by
    simpa using eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2:ℝ≥0∞) ≠ 0)
      (by norm_num : (2:ℝ≥0∞) ≠ ∞) (hf.of_uncurry_left.aestronglyMeasurable (μ := Q))
  simp_rw [he]
  exact hlin.pow_const _

/-- Actual measurability of spatial sections in the L² topology, proved from
joint strong measurability and product integration, rather than assumed. -/
theorem sectionLp_stronglyMeasurable_of_isSeparable [IsSeparable Q] [SeparableSpace R]
    (f : T → Ω → R) (hf : StronglyMeasurable (Function.uncurry f)) :
    StronglyMeasurable (sectionLp Q f) := by
  classical
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  borelize ↥(Lp R 2 Q)
  apply Measurable.stronglyMeasurable
  apply measurable_distance_criterion
  intro a
  have hm : MeasurableSet {t | MemLp (f t) 2 Q} := by
    have he : {t | MemLp (f t) 2 Q} = {t | eLpNorm (f t) 2 Q < ∞} := by
      ext t
      rfl
    rw [he]
    exact measurableSet_lt (measurable_section_eLpNorm Q f hf) measurable_const
  have hsub : StronglyMeasurable (fun p : T × Ω => f p.1 p.2 - a p.2) :=
    hf.sub (Lp.stronglyMeasurable a).comp_snd
  have hd : Measurable (fun t => (eLpNorm (fun ω => f t ω - a ω) 2 Q).toReal) :=
    (measurable_section_eLpNorm Q (fun t ω => f t ω - a ω) hsub).ennreal_toReal
  have he (t : T) : dist (sectionLp Q f t) a =
      if MemLp (f t) 2 Q then (eLpNorm (fun ω => f t ω - a ω) 2 Q).toReal
      else dist (0 : Lp R 2 Q) a := by
    by_cases ht : MemLp (f t) 2 Q
    · simp only [sectionLp, dite_eq_left ht, ite_eq_left ht, Lp.dist_def]
      congr 1
      exact eLpNorm_congr_ae (ht.coeFn_toLp.sub Filter.EventuallyEq.rfl)
    · simp [sectionLp, ht]
  simp_rw [he]
  exact hd.piecewise hm measurable_const

/-- Enlarge countable spatial dependence by an actual finite-measure cover. -/
theorem exists_countable_sigmaFinite_algebra [MeasurableSpace R]
    [MeasurableSpace.CountablyGenerated R] (f : T × Ω → R) (hf : Measurable f) :
    ∃ m : MeasurableSpace Ω, ∃ hm : m ≤ mΩ,
      @MeasurableSpace.CountablyGenerated Ω m ∧
      @SigmaFinite Ω m (Q.trim hm) ∧ @Measurable (T × Ω) R (mT.prod m) _ f := by
  obtain ⟨m,hm,hcg,hf⟩ := CountableProductDependence.measurable_countable_spatial_dependence f hf
  let c := MeasurableSpace.generateFrom (Set.range (spanningSets Q))
  have hc : c ≤ mΩ := MeasurableSpace.generateFrom_le (by
    rintro _ ⟨n,rfl⟩
    exact measurableSet_spanningSets Q n)
  have hcc : @MeasurableSpace.CountablyGenerated Ω c :=
    ⟨Set.range (spanningSets Q), Set.countable_range _, rfl⟩
  let m' := m ⊔ c
  have hm' : m' ≤ mΩ := sup_le hm hc
  have hset (n : ℕ) : @MeasurableSet Ω m' (spanningSets Q n) :=
    (show c ≤ m' from le_sup_right) _ (MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self n))
  have hs : @SigmaFinite Ω m' (Q.trim hm') := by
    refine ⟨⟨⟨spanningSets Q, (fun _ => Set.mem_univ _), ?_, iUnion_spanningSets Q⟩⟩⟩
    intro n
    rw [trim_measurableSet_eq hm' (hset n)]
    exact measure_spanningSets_lt_top Q n
  refine ⟨m',hm',hcg.sup hcc,hs,?_⟩
  exact hf.mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono le_sup_left)) le_rfl

/-- Actual raw section curves are strongly measurable without ambient measure
separability. Only the countable spatial algebra used by this field is needed. -/
theorem sectionLp_stronglyMeasurable [SeparableSpace R] (f : T → Ω → R)
    (hf : StronglyMeasurable (Function.uncurry f)) :
    StronglyMeasurable (ProductLpSections.sectionLp Q f) := by
  borelize R
  obtain ⟨m,hm,hcg,hs,hfm⟩ := exists_countable_sigmaFinite_algebra Q
    (Function.uncurry f) hf.measurable
  letI : MeasurableSpace Ω := mΩ
  let Ωc := ULift.{0} Ω
  letI mc : MeasurableSpace Ωc := MeasurableSpace.comap ULift.down m
  letI : MeasurableSpace.CountablyGenerated Ωc := @MeasurableSpace.CountablyGenerated.comap Ωc Ω m hcg ULift.down
  have hdown : @Measurable Ωc Ω mc m ULift.down := measurable_iff_comap_le.mpr le_rfl
  have hup : Measurable (ULift.up : Ω → Ωc) := by
    apply measurable_iff_comap_le.mpr
    change MeasurableSpace.comap ULift.up (MeasurableSpace.comap ULift.down m) ≤ mΩ
    rw [MeasurableSpace.comap_comp]
    change MeasurableSpace.comap (id : Ω → Ω) m ≤ mΩ
    simpa only [MeasurableSpace.comap_id] using hm
  let Qc : Measure Ωc := Q.map ULift.up
  have hp : MeasurePreserving (ULift.up : Ω → Ωc) Q Qc := ⟨hup,rfl⟩
  have hsQc : SigmaFinite Qc := by
    refine ⟨⟨⟨(fun n => ULift.down ⁻¹' spanningSets (Q.trim hm) n),
      (fun _ => Set.mem_univ _), ?_, ?_⟩⟩⟩
    · intro n
      have hset : MeasurableSet (ULift.down ⁻¹' spanningSets (Q.trim hm) n) :=
        hdown (measurableSet_spanningSets (Q.trim hm) n)
      rw [show Qc = Q.map ULift.up from rfl, Measure.map_apply hup hset]
      change Q (spanningSets (Q.trim hm) n) < ∞
      exact measure_spanningSets_trim_lt_top hm Q n
    · ext x
      simpa only [mem_iUnion, mem_preimage, mem_univ, iff_true] using
        Set.mem_iUnion.mp (show x.down ∈ ⋃ n, spanningSets (Q.trim hm) n by rw [iUnion_spanningSets]; trivial)
  letI := hsQc
  letI : IsSeparable Qc := isSeparable_of_sigmaFinite Qc
  let fc : T → Ωc → R := fun t ω => f t ω.down
  have hfc : StronglyMeasurable (Function.uncurry fc) :=
    (hfm.comp (measurable_fst.prodMk (hdown.comp measurable_snd))).stronglyMeasurable
  let U := ProductLpSections.sectionLp Qc fc
  let L := lpPullbackCLM (E := R) hp
  have hU : StronglyMeasurable U := ProductLpSections.sectionLp_stronglyMeasurable_of_isSeparable Qc fc hfc
  have he (t : T) : L (U t) = ProductLpSections.sectionLp Q f t := by
    have hmem : MemLp (fc t) 2 Qc ↔ MemLp (f t) 2 Q := by
      change eLpNorm (fc t) 2 Qc < ∞ ↔ eLpNorm (f t) 2 Q < ∞
      rw [← eLpNorm_comp_measurePreserving hfc.of_uncurry_left.aestronglyMeasurable hp]
      rfl
    by_cases ht : MemLp (f t) 2 Q
    · have hct := hmem.mpr ht
      apply Lp.ext
      filter_upwards [lpPullback_coe hp (U t),
        hp.quasiMeasurePreserving.ae_eq_comp (ProductLpSections.sectionLp_ae Qc fc hct),
        ProductLpSections.sectionLp_ae Q f ht] with ω hL hc hf
      exact (hL.trans hc).trans hf.symm
    · have hct := mt hmem.mp ht
      simp only [U, ProductLpSections.sectionLp, dite_eq_right ht, dite_eq_right hct, map_zero]
  have heq : (fun t => L (U t)) = ProductLpSections.sectionLp Q f := funext he
  rw [← heq]
  exact L.continuous.comp_stronglyMeasurable hU

/-- Product-square integrability supplies genuine L² sections almost everywhere. -/
theorem ae_memLp (f : T → Ω → R)
    (hf : StronglyMeasurable (Function.uncurry f))
    (h2 : Integrable (fun p : T × Ω => ‖f p.1 p.2‖ ^ 2) (μ.prod Q)) :
    ∀ᵐ t ∂μ, MemLp (f t) 2 Q := by
  filter_upwards [h2.prod_right_ae] with t ht
  exact (memLp_two_iff_integrable_sq_norm
    (hf.of_uncurry_left.aestronglyMeasurable (μ := Q))).mpr ht

/-- Section norms equal the literal expected square of the raw field. -/
theorem sectionLp_norm_sq (f : T → Ω → R) {t : T} (ht : MemLp (f t) 2 Q) :
    ‖sectionLp Q f t‖ ^ 2 = ∫ ω, ‖f t ω‖ ^ 2 ∂Q := by
  rw [ProximalLangevin.lp_norm_sq_eq_integral]
  exact integral_congr_ae ((sectionLp_ae Q f ht).fun_comp (fun z => ‖z‖ ^ 2))

/-- Actual product→iterated L² conversion, with no supplied L²-valued curve or
curve measurability. Spatial measure separability is derived on the field's countable subalgebra. -/
theorem sectionLp_memLp [SeparableSpace R]
    (f : T → Ω → R) (hf : StronglyMeasurable (Function.uncurry f))
    (h2 : Integrable (fun p : T × Ω => ‖f p.1 p.2‖ ^ 2) (μ.prod Q)) :
    MemLp (sectionLp Q f) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm
    (sectionLp_stronglyMeasurable Q f hf).aestronglyMeasurable).mpr
  have hi : Integrable (fun t => ∫ ω, ‖f t ω‖ ^ 2 ∂Q) μ := h2.integral_prod_left
  apply hi.congr
  filter_upwards [ae_memLp μ Q f hf h2] with t ht
  exact (sectionLp_norm_sq Q f ht).symm

/-- Exact time/spatial square-norm identity for the constructed Bochner curve. -/
theorem integral_sectionLp_norm_sq (f : T → Ω → R)
    (hf : StronglyMeasurable (Function.uncurry f))
    (h2 : Integrable (fun p : T × Ω => ‖f p.1 p.2‖ ^ 2) (μ.prod Q)) :
    (∫ t, ‖sectionLp Q f t‖ ^ 2 ∂μ) =
      ∫ p : T × Ω, ‖f p.1 p.2‖ ^ 2 ∂(μ.prod Q) := by
  rw [integral_prod _ h2]
  apply integral_congr_ae
  filter_upwards [ae_memLp μ Q f hf h2] with t ht
  exact sectionLp_norm_sq Q f ht

/-- A product L² equivalence class has a constructed iterated L² equivalence
class. This uses the actual representative of the product-space variable. -/
def curryLp [SeparableSpace R]
    (F : Lp R 2 (μ.prod Q)) : Lp (Lp R 2 Q) 2 μ :=
  (sectionLp_memLp μ Q (fun t ω => F (t, ω)) (Lp.stronglyMeasurable F)
    ((Lp.memLp F).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))).toLp _

/-- The constructed iterated class realizes the original product variable on
almost every section, with no joint point-evaluation measurability assumption. -/
theorem curryLp_section [SeparableSpace R]
    (F : Lp R 2 (μ.prod Q)) :
    ∀ᵐ t ∂μ, curryLp μ Q F t =ᵐ[Q] (fun ω => F (t, ω)) := by
  have hm := sectionLp_memLp μ Q (fun t ω => F (t, ω)) (Lp.stronglyMeasurable F)
    ((Lp.memLp F).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
  filter_upwards [hm.coeFn_toLp,
    ae_memLp μ Q (fun t ω => F (t, ω)) (Lp.stronglyMeasurable F)
      ((Lp.memLp F).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))] with t ht hft
  change curryLp μ Q F t = sectionLp Q (fun t ω => F (t, ω)) t at ht
  rw [ht]
  exact sectionLp_ae Q (fun t ω => F (t, ω)) hft

/-- The actual product→iterated construction preserves the full L² norm. -/
theorem curryLp_norm [SeparableSpace R]
    (F : Lp R 2 (μ.prod Q)) : ‖curryLp μ Q F‖ = ‖F‖ := by
  have hsq : ‖curryLp μ Q F‖ ^ 2 = ‖F‖ ^ 2 := by
    rw [ProximalLangevin.lp_norm_sq_eq_integral,
      ProximalLangevin.lp_norm_sq_eq_integral]
    have hm := sectionLp_memLp μ Q (fun t ω => F (t, ω)) (Lp.stronglyMeasurable F)
      ((Lp.memLp F).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
    calc
      _ = ∫ t, ‖sectionLp Q (fun t ω => F (t, ω)) t‖ ^ 2 ∂μ := by
        exact integral_congr_ae (hm.coeFn_toLp.fun_comp (fun z => ‖z‖ ^ 2))
      _ = _ := integral_sectionLp_norm_sq μ Q (fun t ω => F (t, ω))
        (Lp.stronglyMeasurable F)
        ((Lp.memLp F).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
  nlinarith [norm_nonneg (curryLp μ Q F), norm_nonneg F]

/-- Actual currying commutes with subtraction of product-space variables. -/
theorem curryLp_sub [SeparableSpace R]
    (F G : Lp R 2 (μ.prod Q)) :
    curryLp μ Q (F - G) = curryLp μ Q F - curryLp μ Q G := by
  apply Lp.ext
  have hp := Measure.ae_ae_of_ae_prod (Lp.coeFn_sub F G)
  filter_upwards [curryLp_section μ Q (F - G), curryLp_section μ Q F,
    curryLp_section μ Q G, hp,
    Lp.coeFn_sub (curryLp μ Q F) (curryLp μ Q G)] with t hfg hf hg hp ht
  rw [ht]
  apply Lp.ext
  filter_upwards [hfg, hf, hg, hp,
    Lp.coeFn_sub (curryLp μ Q F t) (curryLp μ Q G t)] with ω hfg hf hg hp hs
  change curryLp μ Q (F - G) t ω = (curryLp μ Q F t - curryLp μ Q G t) ω
  rw [hs, Pi.sub_apply, hfg, hf, hg, hp]
  rfl

/-- A genuine Fubini L² isometry, constructed from raw section integrals. -/
theorem curryLp_isometry [SeparableSpace R] :
    Isometry (curryLp (R := R) μ Q) := by
  apply Isometry.of_dist_eq
  intro F G
  rw [dist_eq_norm, dist_eq_norm, ← curryLp_sub, curryLp_norm]

/-- Actual adaptation of each constructed section follows from raw adaptation,
including the zero value chosen on any non-L² section. -/
theorem sectionLp_adapted (m : MeasurableSpace Ω) (f : T → Ω → R) (t : T)
    (hf : AEStronglyMeasurable[m] (f t) Q) :
    AEStronglyMeasurable[m] (fun ω => sectionLp (mΩ := mΩ) Q f t ω) Q := by
  classical
  by_cases ht : MemLp (f t) 2 Q
  · exact hf.congr (sectionLp_ae (mΩ := mΩ) Q f ht).symm
  · have he : sectionLp (mΩ := mΩ) Q f t = 0 := by simp [sectionLp, ht]
    rw [he]
    exact aestronglyMeasurable_zero.congr (Lp.coeFn_zero (E := R) (p := 2) (μ := Q)).symm

section Columns
variable {I : Type*} [Fintype I]

/-- Literal finite diffusion columns, each constructed from its raw section. -/
def columnSections (f : I → T → Ω → R) (t : T) :
    PiLp 2 (fun _ : I => Lp R 2 Q) :=
  WithLp.toLp 2 (fun i => sectionLp Q (f i) t)

@[simp] theorem columnSections_apply (f : I → T → Ω → R) (t : T) (i : I) :
    (columnSections Q f t).ofLp i = sectionLp Q (f i) t := rfl

/-- Genuine time-L² membership of finite diffusion columns. -/
theorem columnSections_memLp [SeparableSpace R]
    (f : I → T → Ω → R)
    (hf : ∀ i, StronglyMeasurable (Function.uncurry (f i)))
    (h2 : ∀ i, Integrable (fun p : T × Ω => ‖f i p.1 p.2‖ ^ 2) (μ.prod Q)) :
    MemLp (columnSections Q f) 2 μ := by
  apply memLp_piLp_iff.mpr
  intro i
  exact sectionLp_memLp μ Q (f i) (hf i) (h2 i)

/-- The constructed finite columns realize the original raw diffusion fields
outside one time-null set; each spatial section has its own spatial-null set. -/
theorem columnSections_ae (f : I → T → Ω → R)
    (hf : ∀ i, StronglyMeasurable (Function.uncurry (f i)))
    (h2 : ∀ i, Integrable (fun p : T × Ω => ‖f i p.1 p.2‖ ^ 2) (μ.prod Q)) :
    ∀ᵐ t ∂μ, ∀ i, (columnSections Q f t).ofLp i =ᵐ[Q] f i t := by
  have hall : ∀ᵐ t ∂μ, ∀ i, MemLp (f i t) 2 Q :=
    ae_all_iff.mpr (fun i => ae_memLp μ Q (f i) (hf i) (h2 i))
  filter_upwards [hall] with t ht
  intro i
  exact sectionLp_ae Q (f i) (ht i)

/-- Exact total finite-column energy of the constructed time-L² curve. -/
theorem integral_columnSections_norm_sq (f : I → T → Ω → R)
    (hf : ∀ i, StronglyMeasurable (Function.uncurry (f i)))
    (h2 : ∀ i, Integrable (fun p : T × Ω => ‖f i p.1 p.2‖ ^ 2) (μ.prod Q)) :
    (∫ t, ‖columnSections Q f t‖ ^ 2 ∂μ) =
      ∑ i, ∫ p : T × Ω, ‖f i p.1 p.2‖ ^ 2 ∂(μ.prod Q) := by
  classical
  simp_rw [PiLp.norm_sq_eq_of_L2]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl (fun i _ => integral_sectionLp_norm_sq μ Q (f i) (hf i) (h2 i))
  · intro i _
    have hi := (h2 i).integral_prod_left
    apply hi.congr
    filter_upwards [ae_memLp μ Q (f i) (hf i) (h2 i)] with t ht
    exact (sectionLp_norm_sq Q (f i) ht).symm

end Columns

end PBGSO.ProductLpSections
