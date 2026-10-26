import PBGSO.ParticleWeakBound
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Measurability of the actual empirical Wasserstein statistic

Finite equality-pattern strata collapse duplicate cloud points to fixed finite
weighted support indices. Every genuine empirical coupling is pulled back by
an actual finite measurable embedding inverse, and every index coupling is
pushed forward. This proves exact equality with a fixed index-coupling infimum.
Each finite-index cost is continuous; its infimum is upper semicontinuous and
measurable. The finite measurable stratum cover proves global measurability.
Neither an optimal coupling nor a Wasserstein triangle inequality is assumed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace PBGSO.EmpiricalTransportMeasurable

structure IndexCoupling {J K : Type*} [MeasurableSpace J] [MeasurableSpace K]
    (μ : Measure J) (ν : Measure K) where
  joint : Measure (J × K)
  fst : joint.map Prod.fst = μ
  snd : joint.map Prod.snd = ν

section Embedding
variable {J K H : Type*} [Fintype J] [Fintype K] [Nonempty J] [Nonempty K]
  [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace K] [MeasurableSingletonClass K]
  [NormedAddCommGroup H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  (μ : Measure J) (ν : Measure K)

theorem finite_measurableEmbedding (f : J → H) (hf : Function.Injective f) :
    MeasurableEmbedding f :=
  ⟨hf, measurable_of_countable f, fun s _ ↦ ((Set.toFinite s).countable.image f).measurableSet⟩

theorem embedding_inverse_ae (f : J → H) (hf : MeasurableEmbedding f) :
    ∀ᵐ x ∂μ.map f, f (hf.invFun x) = x := by
  apply (ae_map_iff hf.measurable.aemeasurable (by measurability)).mpr
  exact ae_of_all _ fun j ↦ congrArg f (hf.leftInverse_invFun j)

def liftCoupling (f : J → H) (g : K → H)
    (c : IndexCoupling μ ν) : ULA.Coupling (μ.map f) (ν.map g) where
  joint := c.joint.map (fun p ↦ (f p.1, g p.2))
  fst := by
    rw [Measure.map_map measurable_fst (by fun_prop)]
    change c.joint.map (f ∘ Prod.fst) = _
    rw [← Measure.map_map (measurable_of_countable f) measurable_fst, c.fst]
  snd := by
    rw [Measure.map_map measurable_snd (by fun_prop)]
    change c.joint.map (g ∘ Prod.snd) = _
    rw [← Measure.map_map (measurable_of_countable g) measurable_snd, c.snd]

theorem liftCoupling_cost (f : J → H) (g : K → H) (c : IndexCoupling μ ν) :
    ULA.couplingCost (liftCoupling μ ν f g c).joint =
      eLpNorm (fun p : J × K ↦ f p.1 - g p.2) 2 c.joint := by
  exact eLpNorm_map_measure (by fun_prop) (by fun_prop)

def pullCoupling (f : J → H) (g : K → H)
    (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g)
    (c : ULA.Coupling (μ.map f) (ν.map g)) : IndexCoupling μ ν where
  joint := c.joint.map (fun p ↦ (hf.invFun p.1, hg.invFun p.2))
  fst := by
    rw [Measure.map_map measurable_fst (by fun_prop)]
    change c.joint.map (hf.invFun ∘ Prod.fst) = _
    rw [← Measure.map_map hf.measurable_invFun measurable_fst, c.fst,
      Measure.map_map hf.measurable_invFun hf.measurable]
    have he : hf.invFun ∘ f = id := funext hf.leftInverse_invFun
    rw [he, Measure.map_id]
  snd := by
    rw [Measure.map_map measurable_snd (by fun_prop)]
    change c.joint.map (hg.invFun ∘ Prod.snd) = _
    rw [← Measure.map_map hg.measurable_invFun measurable_snd, c.snd,
      Measure.map_map hg.measurable_invFun hg.measurable]
    have he : hg.invFun ∘ g = id := funext hg.leftInverse_invFun
    rw [he, Measure.map_id]

theorem pullCoupling_cost (f : J → H) (g : K → H)
    (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g)
    (c : ULA.Coupling (μ.map f) (ν.map g)) :
    eLpNorm (fun p : J × K ↦ f p.1 - g p.2) 2 (pullCoupling μ ν f g hf hg c).joint =
      ULA.couplingCost c.joint := by
  rw [pullCoupling, eLpNorm_map_measure (by fun_prop) (by fun_prop)]
  apply eLpNorm_congr_ae
  have hleft : ∀ᵐ p ∂c.joint, f (hf.invFun p.1) = p.1 := by
    have h := embedding_inverse_ae μ f hf
    rw [← c.fst] at h
    exact (ae_map_iff measurable_fst.aemeasurable (by measurability)).mp h
  have hright : ∀ᵐ p ∂c.joint, g (hg.invFun p.2) = p.2 := by
    have h := embedding_inverse_ae ν g hg
    rw [← c.snd] at h
    exact (ae_map_iff measurable_snd.aemeasurable (by measurability)).mp h
  filter_upwards [hleft, hright] with p hp hq
  exact congrArg₂ (· - ·) hp hq

/-- No optimal-coupling or Wasserstein-triangle premise: all couplings are
actually lifted and pulled back through the finite measurable embeddings. -/
theorem transport_eq_index_inf (f : J → H) (g : K → H)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ULA.wasserstein2 (μ.map f) (ν.map g) =
      ⨅ c : IndexCoupling μ ν, eLpNorm (fun p : J × K ↦ f p.1 - g p.2) 2 c.joint := by
  apply le_antisymm
  · refine le_iInf fun c ↦ ?_
    exact (ULA.wasserstein2_le_couplingCost (liftCoupling μ ν f g c)).trans_eq
      (liftCoupling_cost μ ν f g c)
  · refine le_iInf fun c ↦ ?_
    exact (iInf_le _ (pullCoupling μ ν f g (finite_measurableEmbedding f hf)
      (finite_measurableEmbedding g hg) c)).trans_eq
      (pullCoupling_cost μ ν f g (finite_measurableEmbedding f hf)
        (finite_measurableEmbedding g hg) c)

end Embedding

section CostContinuity
variable {J K H : Type*} [Fintype J] [Fintype K]
  [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace K] [MeasurableSingletonClass K]
  [NormedAddCommGroup H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  (μ : Measure J) (ν : Measure K) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

instance indexCoupling_probability (c : IndexCoupling μ ν) : IsProbabilityMeasure c.joint := by
  haveI : IsProbabilityMeasure (c.joint.map Prod.fst) := by rw [c.fst]; infer_instance
  exact (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mp inferInstance

def indexIndependent : IndexCoupling μ ν where
  joint := μ.prod ν
  fst := (measurePreserving_fst (μ := μ) (ν := ν)).map_eq
  snd := (measurePreserving_snd (μ := μ) (ν := ν)).map_eq

def indexCost (c : IndexCoupling μ ν) (z : (J → H) × (K → H)) : ℝ≥0∞ :=
  eLpNorm (fun p : J × K ↦ z.1 p.1 - z.2 p.2) 2 c.joint

theorem indexCost_continuous (c : IndexCoupling μ ν) :
    Continuous (indexCost (H := H) μ ν c) := by
  have he (z : (J → H) × (K → H)) :
      indexCost μ ν c z =
        (∑ p : J × K, ‖z.1 p.1 - z.2 p.2‖ₑ ^ (2 : ℝ) * c.joint {p}) ^ (1 / (2 : ℝ)) := by
    rw [indexCost, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (measurable_of_countable _).aestronglyMeasurable, lintegral_fintype]
    norm_num
  change Continuous (fun z ↦ indexCost μ ν c z)
  simp_rw [he]
  apply ENNReal.continuous_rpow_const.comp
  apply continuous_finset_sum
  intro p _
  apply (ENNReal.continuous_mul_const (measure_ne_top _ _)).comp
  apply ENNReal.continuous_rpow_const.comp
  exact (((continuous_apply p.1).comp continuous_fst).sub
    ((continuous_apply p.2).comp continuous_snd)).enorm

def indexInf (z : (J → H) × (K → H)) : ℝ≥0∞ := ⨅ c : IndexCoupling μ ν, indexCost μ ν c z

theorem indexInf_upperSemicontinuous : UpperSemicontinuous (indexInf (H := H) μ ν) :=
  upperSemicontinuous_iInf fun c ↦ (indexCost_continuous μ ν c).upperSemicontinuous

theorem indexInf_measurable : Measurable (indexInf (H := H) μ ν) :=
  (indexInf_upperSemicontinuous μ ν).measurable

end CostContinuity

section CloudPatterns
variable {H : Type*} [NormedAddCommGroup H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  (N : ℕ) [NeZero N]

def CloudPattern (r : Fin N → Fin N) (z : Fin N → H) : Prop :=
  ∀ i j, z i = z j ↔ r i = r j

theorem exists_cloudPattern (z : Fin N → H) : ∃ r, CloudPattern N r z := by
  classical
  refine ⟨fun i ↦ Function.invFun z (z i), ?_⟩
  intro i j
  constructor
  · exact congrArg (Function.invFun z)
  · intro h
    have he := congrArg z h
    simpa only [Function.apply_invFun_apply] using he

theorem cloudPattern_measurableSet (r : Fin N → Fin N) :
    MeasurableSet {z : Fin N → H | CloudPattern N r z} := by
  classical
  simp only [CloudPattern, setOf_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  by_cases h : r i = r j
  · simpa only [h, iff_true] using
      measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)
  · simpa only [h, iff_false, Set.compl_setOf] using
      (measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)).compl

abbrev PatternIndex (r : Fin N → Fin N) := Set.range r

instance patternIndex_fintype (r : Fin N → Fin N) : Fintype (PatternIndex N r) :=
  Fintype.ofFinite _

instance patternIndex_nonempty (r : Fin N → Fin N) : Nonempty (PatternIndex N r) :=
  ⟨⟨r 0, ⟨0, rfl⟩⟩⟩

def patternMap (r : Fin N → Fin N) (i : Fin N) : PatternIndex N r := ⟨r i, ⟨i, rfl⟩⟩

def patternLaw (r : Fin N → Fin N) : Measure (PatternIndex N r) :=
  Model.empiricalLaw N (patternMap N r)

instance patternLaw_probability (r : Fin N → Fin N) : IsProbabilityMeasure (patternLaw N r) := by
  constructor
  simp [patternLaw, Model.empiricalLaw]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast (NeZero.ne N)) (by simp)

def patternEval (r : Fin N → Fin N) (z : Fin N → H) (j : PatternIndex N r) : H :=
  z (Function.invFun r j.val)

theorem patternEval_reconstruct {r : Fin N → Fin N} {z : Fin N → H}
    (hp : CloudPattern N r z) (i : Fin N) : patternEval N r z (patternMap N r i) = z i := by
  exact (hp _ _).mpr Function.apply_invFun_apply

theorem patternEval_injective {r : Fin N → Fin N} {z : Fin N → H}
    (hp : CloudPattern N r z) : Function.Injective (patternEval N r z) := by
  intro i j h
  apply Subtype.ext
  have he := (hp _ _).mp h
  simpa only [Function.invFun_eq i.property, Function.invFun_eq j.property] using he

theorem patternLaw_map {r : Fin N → Fin N} {z : Fin N → H} (hp : CloudPattern N r z) :
    (patternLaw N r).map (patternEval N r z) = Model.empiricalLaw N z := by
  rw [patternLaw, empiricalLaw_map N _ _ (measurable_of_countable _)]
  congr 1
  exact funext (patternEval_reconstruct N hp)

def patternCost (r s : Fin N → Fin N) (z : (Fin N → H) × (Fin N → H)) : ℝ≥0∞ :=
  indexInf (patternLaw N r) (patternLaw N s) (patternEval N r z.1, patternEval N s z.2)

theorem patternCost_measurable (r s : Fin N → Fin N) :
    Measurable (patternCost (H := H) N r s) := by
  apply (indexInf_measurable (patternLaw N r) (patternLaw N s)).comp
  apply Measurable.prodMk
  · exact Measurable.of_eval fun i ↦ (measurable_pi_apply _).comp measurable_fst
  · exact Measurable.of_eval fun i ↦ (measurable_pi_apply _).comp measurable_snd

theorem empirical_transport_eq_pattern {r s : Fin N → Fin N}
    {z w : Fin N → H} (hz : CloudPattern N r z) (hw : CloudPattern N s w) :
    ULA.wasserstein2 (Model.empiricalLaw N z) (Model.empiricalLaw N w) =
      patternCost N r s (z, w) := by
  rw [← patternLaw_map N hz, ← patternLaw_map N hw]
  exact transport_eq_index_inf (patternLaw N r) (patternLaw N s)
    (patternEval N r z) (patternEval N s w)
    (patternEval_injective N hz) (patternEval_injective N hw)

/-- The genuine empirical Wasserstein statistic is measurable even when
particles coincide. Finitely many equality-pattern strata remove duplicate
points; each stratum has a fixed actual index-coupling infimum. -/
theorem empirical_wasserstein_measurable :
    Measurable (fun z : (Fin N → H) × (Fin N → H) ↦
      ULA.wasserstein2 (Model.empiricalLaw N z.1) (Model.empiricalLaw N z.2)) := by
  intro B hB
  have he : (fun z : (Fin N → H) × (Fin N → H) ↦
      ULA.wasserstein2 (Model.empiricalLaw N z.1) (Model.empiricalLaw N z.2)) ⁻¹' B =
      ⋃ r : Fin N → Fin N, ⋃ s : Fin N → Fin N,
        {z : (Fin N → H) × (Fin N → H) | CloudPattern N r z.1 ∧ CloudPattern N s z.2} ∩
          (patternCost N r s ⁻¹' B) := by
    ext z
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_setOf_eq]
    constructor
    · intro hz
      obtain ⟨r, hr⟩ := exists_cloudPattern N z.1
      obtain ⟨s, hs⟩ := exists_cloudPattern N z.2
      exact ⟨r, s, ⟨hr, hs⟩, (empirical_transport_eq_pattern N hr hs) ▸ hz⟩
    · rintro ⟨r, s, ⟨hr, hs⟩, hz⟩
      exact (empirical_transport_eq_pattern N hr hs).symm ▸ hz
  rw [he]
  apply MeasurableSet.iUnion
  intro r
  apply MeasurableSet.iUnion
  intro s
  exact ((cloudPattern_measurableSet (H := H) N r).preimage measurable_fst |>.inter
    ((cloudPattern_measurableSet (H := H) N s).preimage measurable_snd)).inter
      (patternCost_measurable N r s hB)

end CloudPatterns

section ParticleStatistic
variable {S Z : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]

/-- The actual empirical-cloud transport statistic appearing in the source
finite-particle theorem is measurable; particles need not be distinct. -/
theorem particleEmpiricalDistanceSq_measurable (N : ℕ) (hN : 0 < N) :
    Measurable (particleEmpiricalDistanceSq (S := S) (Z := Z) N) := by
  letI : NeZero N := ⟨hN.ne'⟩
  unfold particleEmpiricalDistanceSq
  apply Measurable.add
  · fun_prop
  · apply Measurable.pow_const
    unfold ULA.wasserstein2Real
    apply ENNReal.measurable_toReal.comp
    let cloud : ParticlePair N S Z → (Fin N → Z) × (Fin N → Z) :=
      fun p ↦ (p.1.2, p.2.2)
    have hc : Measurable cloud := by
      exact (measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)
    have h := (empirical_wasserstein_measurable (H := Z) N).comp hc
    exact h

/-- This directly discharges the hmetric premise for any actual joint
particle/reference measure under the displayed Borel coordinate structure. -/
theorem particleEmpiricalDistanceSq_aestronglyMeasurable (N : ℕ) (hN : 0 < N)
    (Q : Measure (ParticlePair N S Z)) :
    AEStronglyMeasurable (particleEmpiricalDistanceSq (S := S) (Z := Z) N) Q :=
  (particleEmpiricalDistanceSq_measurable N hN).aestronglyMeasurable

end ParticleStatistic
end PBGSO.EmpiricalTransportMeasurable
