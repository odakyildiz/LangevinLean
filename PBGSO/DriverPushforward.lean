import PBGSO.FilteredBrownianPullback

/-! # Brownian drivers descend through actual probability maps

Finite-dimensional Brownian laws, spatial independence and future/past
independence descend through a measure-preserving map whose past variables
are measurable in the original past. This constructs a genuine driver on a
canonical path space without supplying its Brownian or independence claims.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.FilteredBrownian

section Probability
variable {Ω Ω' A B : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [MeasurableSpace A] [MeasurableSpace B]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {R : Measure Ω'} [IsProbabilityMeasure R]
  {f : Ω → Ω'} (hf : MeasurePreserving f Q R)

include hf

/-- Output laws descend through an actual probability-preserving input map. -/
theorem hasLaw_of_comp {Y : Ω' → A} {μ : Measure A} (hY : Measurable Y)
    (h : HasLaw (Y ∘ f) μ Q) : HasLaw Y μ R where
  aemeasurable := hY.aemeasurable
  map_eq := by rw [← hf.map_eq, Measure.map_map hY hf.measurable]; exact h.map_eq

/-- Independence descends by transporting its actual joint and marginal
laws, without an independence premise on the target probability space. -/
theorem indepFun_of_comp {Y : Ω' → A} {Z : Ω' → B}
    (hY : Measurable Y) (hZ : Measurable Z)
    (h : IndepFun (Y ∘ f) (Z ∘ f) Q) : IndepFun Y Z R := by
  apply (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable).mpr
  have hh := h.map_prod_eq_prod_map_map (hY.comp hf.measurable).aemeasurable
    (hZ.comp hf.measurable).aemeasurable
  rw [← hf.map_eq, Measure.map_map hY hf.measurable,
    Measure.map_map hZ hf.measurable, Measure.map_map (hY.prodMk hZ) hf.measurable]
  exact hh

/-- Finite families of independent original coordinates descend through
the actual probability map. -/
theorem iIndepFun_of_comp {ι : Type*} [Fintype ι]
    {Y : ι → Ω' → A} (hY : ∀ i, Measurable (Y i))
    (h : iIndepFun (fun i => Y i ∘ f) Q) : iIndepFun Y R := by
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hY i).aemeasurable)).mpr
  have hh := h.map_fun_eq_pi_map (fun i => ((hY i).comp hf.measurable).aemeasurable)
  rw [← hf.map_eq, Measure.map_map (measurable_pi_iff.mpr hY) hf.measurable]
  simp_rw [Measure.map_map (hY _) hf.measurable]
  exact hh

end Probability

section Driver
variable {Ω Ω' I : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
  [Fintype I] [DecidableEq I]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {R : Measure Ω'} [IsProbabilityMeasure R]
  {f : Ω → Ω'} (hf : MeasurePreserving f Q R)
  (D : Driver (I := I) Q)
  (b : I → ℝ≥0 → Ω' → ℝ) (ℱ : Filtration ℝ≥0 mΩ')
  (hA : ∀ i, StronglyAdapted ℱ (b i))
  (hp : ∀ i t, (fun ω => b i t (f ω)) =ᵐ[Q] D.process i t)
  (hF : ∀ t, MeasurableSpace.comap f (ℱ t) ≤ D.filtration t)

include hf D hA hp

theorem pushforward_brownian (i : I) : IsPreBrownianReal (b i) R where
  hasLaw J := by
    apply hasLaw_of_comp hf (measurable_pi_iff.mpr (fun t : J =>
      ((hA i t.val).mono (ℱ.le t.val)).measurable))
    apply ((D.brownian i).hasLaw J).congr
    filter_upwards [ae_all_iff.mpr (fun t : J => hp i t)] with ω hω
    exact funext hω

theorem pushforward_increment_coordinates (s t : ℝ≥0) (hst : s ≤ t) :
    iIndepFun (fun i ω => b i t ω - b i s ω) R := by
  apply iIndepFun_of_comp hf (fun i =>
    ((hA i t).mono (ℱ.le t)).measurable.sub ((hA i s).mono (ℱ.le s)).measurable)
  apply (D.increment_coordinates s t hst).congr
  intro i
  exact ((hp i t).sub (hp i s)).symm

include hF

theorem pushforward_future_independent (s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (fun ω i => b i t ω - b i s ω) inferInstance)
      (ℱ s) R := by
  let g : Ω' → I → ℝ := fun ω i => b i t ω - b i s ω
  have hg : Measurable g := measurable_pi_iff.mpr (fun i =>
    ((hA i t).mono (ℱ.le t)).measurable.sub ((hA i s).mono (ℱ.le s)).measurable)
  have hfm : @Measurable Ω Ω' (D.filtration s) (ℱ s) f :=
    measurable_iff_comap_le.mpr (hF s)
  have hs : @IndepFun Ω (I → ℝ) Ω' mΩ inferInstance (ℱ s)
      (fun ω i => D.process i t ω - D.process i s ω) f Q :=
    indep_of_indep_of_le_right (D.future_independent s t hst) hfm.comap_le
  have hsp : @IndepFun Ω (I → ℝ) Ω' mΩ inferInstance (ℱ s)
      (g ∘ f) f Q := by
    apply hs.congr ?_ EventuallyEq.rfl
    filter_upwards [ae_all_iff.mpr (fun i => ((hp i t).sub (hp i s)).symm)] with ω hω
    exact funext hω
  have hid : @Measurable Ω' Ω' mΩ' (ℱ s) id := measurable_iff_comap_le.mpr (by
    simpa only [MeasurableSpace.comap_id] using ℱ.le s)
  have hh := @indepFun_of_comp Ω Ω' (I → ℝ) Ω' mΩ mΩ' inferInstance (ℱ s)
    Q _ R _ f hf g id hg hid hsp
  simpa only [IndepFun, Kernel.IndepFun, Indep, MeasurableSpace.comap_id] using hh

/-- A genuine target-space Brownian driver. Its probabilistic fields are
proved from the original driver and the causal probability map. -/
def pushforwardDriver : Driver (I := I) R where
  process := b
  brownian := pushforward_brownian hf D b ℱ hA hp
  filtration := ℱ
  adapted := hA
  increment_coordinates := pushforward_increment_coordinates hf D b ℱ hA hp
  future_independent := pushforward_future_independent hf D b ℱ hA hp hF

end Driver
end PBGSO.FilteredBrownian
