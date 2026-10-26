import UnadjustedLangevin.CanonicalBrownian
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Process.Adapted

/-! # Joining independent future/past coordinate pairs -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace PBGSO
variable {Ω I E F : Type*} [MeasurableSpace Ω] [Fintype I]
  [MeasurableSpace E] [MeasurableSpace F] (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- Independent coordinate pairs whose two entries are individually independent
have independent full vectors of first and second entries. -/
theorem independent_pair_vectors
    (X : I → Ω → E) (Y : I → Ω → F)
    (hX : ∀ i, AEMeasurable (X i) Q) (hY : ∀ i, AEMeasurable (Y i) Q)
    (hpairs : iIndepFun (fun i ω => (X i ω, Y i ω)) Q)
    (hxy : ∀ i, IndepFun (X i) (Y i) Q) :
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) Q := by
  have hxind : iIndepFun X Q := hpairs.comp (fun _ p => p.1) (fun _ => measurable_fst)
  have hyind : iIndepFun Y Q := hpairs.comp (fun _ p => p.2) (fun _ => measurable_snd)
  apply (indepFun_iff_map_prod_eq_prod_map_map (.of_eval hX) (.of_eval hY)).2
  rw [hxind.map_fun_eq_pi_map hX, hyind.map_fun_eq_pi_map hY]
  let rearrange := MeasurableEquiv.arrowProdEquivProdArrow E F I
  have hrep : Q.map (fun ω => ((fun i => X i ω), fun i => Y i ω)) =
      (Q.map (fun ω i => (X i ω, Y i ω))).map rearrange := by
    exact (AEMeasurable.map_map_of_aemeasurable rearrange.measurable.aemeasurable
      (.of_eval fun i => (hX i).prodMk (hY i))).symm
  rw [hrep, hpairs.map_fun_eq_pi_map (fun i => (hX i).prodMk (hY i))]
  simp_rw [(hxy _).map_prod_eq_prod_map_map (hX _) (hY _)]
  exact (measurePreserving_arrowProdEquivProdArrow E F I
    (fun i => Q.map (X i)) (fun i => Q.map (Y i))).map_eq

end PBGSO

namespace PBGSO
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  (W : I → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) Q)
include hW

/-- Joint future Brownian paths are independent of the whole joint past,
provided the entire coordinate paths are independent. -/
theorem brownian_vector_future_past_independent
    (hpm : ∀ i, Measurable (fun ω t => W i t ω))
    (hpaths : iIndepFun (fun i ω t => W i t ω) Q) (s : ℝ≥0) :
    IndepFun (fun ω i t => W i (s + t) ω - W i s ω)
      (fun ω i (t : Set.Iic s) => W i t ω) Q := by
  apply independent_pair_vectors Q
  · intro i
    exact (measurable_pi_iff.mpr fun t => ((measurable_pi_apply (s + t)).comp (hpm i)).sub
      ((measurable_pi_apply s).comp (hpm i))).aemeasurable
  · intro i
    exact (measurable_pi_iff.mpr fun t : Set.Iic s =>
      (measurable_pi_apply (t : ℝ≥0)).comp (hpm i)).aemeasurable
  · exact hpaths.comp (fun _ p => ((fun t => p (s + t) - p s), fun (t : Set.Iic s) => p t))
      (fun _ => (measurable_pi_iff.mpr fun t => (measurable_pi_apply (s + t)).sub
        (measurable_pi_apply s)).prodMk
          (measurable_pi_iff.mpr fun t : Set.Iic s => measurable_pi_apply (t : ℝ≥0)))
  · intro i
    exact (hW i).indepFun_shift s

omit hW in
/-- The constructed canonical vector Brownian source has joint future/past
independence for all nonnegative cut times. -/
theorem canonical_brownian_vector_future_past_independent (I : Type*) [Fintype I]
    (s : ℝ≥0) :
    IndepFun (fun ω i t => ULA.CanonicalBrownian.coordinate (I := I) i (s + t) ω -
      ULA.CanonicalBrownian.coordinate i s ω)
      (fun ω i (t : Set.Iic s) => ULA.CanonicalBrownian.coordinate i t ω)
      (ULA.CanonicalBrownian.vectorProbability I) :=
  brownian_vector_future_past_independent _ _ ULA.CanonicalBrownian.coordinate_isPreBrownian
    (fun i => measurable_pi_iff.mpr fun t =>
      (ULA.CanonicalBrownian.process_measurable t).comp (measurable_pi_apply i))
    (ULA.CanonicalBrownian.coordinate_paths_independent I) s
end PBGSO

namespace PBGSO
variable {Ω E F Z : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
  [MeasurableSpace F] [MeasurableSpace Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  (μ : Measure Z) [IsProbabilityMeasure μ]

/-- Adding an independent initial variable to the past preserves independence
from the future. This follows from the actual product law, without a triple
independence premise. -/
theorem independent_future_with_initial
    (X : Ω → E) (Y : Ω → F) (hX : Measurable X) (hY : Measurable Y)
    (hxy : IndepFun X Y Q) :
    IndepFun (fun p : Z × Ω => X p.2) (fun p : Z × Ω => (p.1, Y p.2)) (μ.prod Q) := by
  let νX := Q.map X
  let νY := Q.map Y
  have hpair : MeasurePreserving (fun ω => (X ω, Y ω)) Q (νX.prod νY) :=
    ⟨hX.prodMk hY, hxy.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable⟩
  have h0 := (MeasurePreserving.id μ).prod hpair
  have h1 := (measurePreserving_prodAssoc μ νX νY).symm MeasurableEquiv.prodAssoc
  have h2 := (Measure.measurePreserving_swap (μ := μ) (ν := νX)).prod (MeasurePreserving.id νY)
  have h3 := measurePreserving_prodAssoc νX μ νY
  have hall : MeasurePreserving
      (fun p : Z × Ω => (X p.2, p.1, Y p.2)) (μ.prod Q) (νX.prod (μ.prod νY)) :=
    h3.comp (h2.comp (h1.comp h0))
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (hX.comp measurable_snd).aemeasurable
    (measurable_fst.prodMk (hY.comp measurable_snd)).aemeasurable).2
  change (μ.prod Q).map (fun p => (X p.2, p.1, Y p.2)) =
    ((μ.prod Q).map (fun p => X p.2)).prod
      ((μ.prod Q).map (fun p => (p.1, Y p.2)))
  have hx : MeasurePreserving (fun p : Z × Ω => X p.2) (μ.prod Q) νX :=
    (measurePreserving_fst (μ := νX) (ν := μ.prod νY)).comp hall
  have hy : MeasurePreserving (fun p : Z × Ω => (p.1, Y p.2)) (μ.prod Q) (μ.prod νY) :=
    (measurePreserving_snd (μ := νX) (ν := μ.prod νY)).comp hall
  rw [hall.map_eq, hx.map_eq, hy.map_eq]

end PBGSO

namespace PBGSO
variable {Ω Ω' E F : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [MeasurableSpace E] [MeasurableSpace F]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (R : Measure Ω') [IsProbabilityMeasure R]

/-- Full-law pullback preserves independence on the actual source. -/
theorem independent_pullback {f : Ω → Ω'} (hf : MeasurePreserving f Q R)
    (X : Ω' → E) (Y : Ω' → F) (hX : Measurable X) (hY : Measurable Y)
    (hxy : IndepFun X Y R) : IndepFun (X ∘ f) (Y ∘ f) Q := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (hX.comp hf.measurable).aemeasurable (hY.comp hf.measurable).aemeasurable).2
  have hx : Q.map (X ∘ f) = R.map X := by rw [← Measure.map_map hX hf.measurable, hf.map_eq]
  have hy : Q.map (Y ∘ f) = R.map Y := by rw [← Measure.map_map hY hf.measurable, hf.map_eq]
  rw [hx, hy, ← hxy.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable]
  change Q.map ((fun ω => (X ω, Y ω)) ∘ f) = _
  rw [← Measure.map_map (hX.prodMk hY) hf.measurable, hf.map_eq]

end PBGSO

namespace PBGSO
variable {Z I : Type*} [MeasurableSpace Z] [Fintype I]
  (μ : Measure Z) [IsProbabilityMeasure μ]

/-- Future vector Brownian paths are independent of both the full past
and the independent random initial state on the canonical initial/noise source. -/
theorem canonical_brownian_future_initial_past_independent (s : ℝ≥0) :
    IndepFun
      (fun p : Z × ULA.CanonicalBrownian.VectorSample I => fun i t =>
        ULA.CanonicalBrownian.coordinate i (s + t) p.2 - ULA.CanonicalBrownian.coordinate i s p.2)
      (fun p : Z × ULA.CanonicalBrownian.VectorSample I =>
        (p.1, fun i (t : Set.Iic s) => ULA.CanonicalBrownian.coordinate i t p.2))
      (μ.prod (ULA.CanonicalBrownian.vectorProbability I)) := by
  apply independent_future_with_initial (ULA.CanonicalBrownian.vectorProbability I) μ
    (fun ω i t => ULA.CanonicalBrownian.coordinate i (s + t) ω -
      ULA.CanonicalBrownian.coordinate i s ω)
    (fun ω i (t : Set.Iic s) => ULA.CanonicalBrownian.coordinate i t ω)
  · exact measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun t =>
      ((ULA.CanonicalBrownian.process_measurable (s + t)).comp (measurable_pi_apply i)).sub
        ((ULA.CanonicalBrownian.process_measurable s).comp (measurable_pi_apply i))
  · exact measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun t : Set.Iic s =>
      (ULA.CanonicalBrownian.process_measurable t).comp (measurable_pi_apply i)
  · exact canonical_brownian_vector_future_past_independent I s
end PBGSO

namespace PBGSO.CanonicalInitialFiltration
open Set
variable {Z I : Type*} [MeasurableSpace Z] [Fintype I]
  [NormedAddCommGroup Z] [BorelSpace Z] [SecondCountableTopology Z]
  (μ : Measure Z) [IsProbabilityMeasure μ]

def process (t : ℝ≥0) (p : Z × ULA.CanonicalBrownian.VectorSample I) : Z × (I → ℝ) :=
  (p.1, fun i => ULA.CanonicalBrownian.coordinate i t p.2)

theorem process_measurable (t : ℝ≥0) : Measurable (process (Z := Z) (I := I) t) :=
  measurable_fst.prodMk (measurable_pi_iff.mpr fun i =>
    ((ULA.CanonicalBrownian.process_measurable t).comp
      (measurable_pi_apply i : Measurable (fun ω : ULA.CanonicalBrownian.VectorSample I => ω i))).comp
        (measurable_snd : Measurable (Prod.snd : Z × ULA.CanonicalBrownian.VectorSample I → _)))

/-- The actual filtration of the full joint Brownian past and random initial state. -/
def filtration : Filtration ℝ≥0 (inferInstance : MeasurableSpace
    (Z × ULA.CanonicalBrownian.VectorSample I)) :=
  Filtration.natural (process (Z := Z) (I := I)) (fun t => (process_measurable t).stronglyMeasurable)

/-- Every spatial coordinate has independent future increments relative to
the complete initial-state/joint-noise natural filtration. -/
theorem increment_independent_past (i : I) (s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (fun p : Z × ULA.CanonicalBrownian.VectorSample I =>
        ULA.CanonicalBrownian.coordinate i t p.2 - ULA.CanonicalBrownian.coordinate i s p.2)
      inferInstance) (filtration (Z := Z) (I := I) s)
        (μ.prod (ULA.CanonicalBrownian.vectorProbability I)) := by
  have hi := (canonical_brownian_future_initial_past_independent (I := I) μ s).comp
    ((measurable_pi_apply (t - s)).comp (measurable_pi_apply i))
    (measurable_pi_iff.mpr fun u : Iic s => measurable_fst.prodMk
      (measurable_pi_iff.mpr fun j =>
        ((measurable_pi_apply u).comp (measurable_pi_apply j)).comp measurable_snd))
  rw [filtration, Filtration.natural_eq_comap]
  change IndepFun (fun p : Z × ULA.CanonicalBrownian.VectorSample I =>
    ULA.CanonicalBrownian.coordinate i t p.2 - ULA.CanonicalBrownian.coordinate i s p.2)
    (fun p (u : Iic s) => process u p) _
  change IndepFun (fun p : Z × ULA.CanonicalBrownian.VectorSample I =>
    ULA.CanonicalBrownian.coordinate i (s + (t - s)) p.2 -
      ULA.CanonicalBrownian.coordinate i s p.2)
    (fun p (u : Iic s) => process u p) _ at hi
  rwa [add_tsub_cancel_of_le hst] at hi

end PBGSO.CanonicalInitialFiltration
