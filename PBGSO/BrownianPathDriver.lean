import PBGSO.BrownianDriverPathLaw
import PBGSO.DriverPushforward
import PBGSO.NaturalPastTransport

/-! # Actual Brownian drivers on independent initial-state / Wiener paths

The target process is literal path evaluation and its filtration contains
the full joint initial/Brownian past. Brownian and independence properties
are proved by probability pushforward of a genuine filtered driver. The
input map is constructed from the original continuous Brownian modification.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.BrownianPathDriver
open FilteredBrownian BrownianPathSpace
variable {Ω Z I : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]

abbrev Space (Z I : Type*) := Z × (I → C(ℝ≥0,ℝ))

def probability (μ : Measure Z) : Measure (Space Z I) :=
  μ.prod (Measure.pi (fun _ : I => wiener))

instance (μ : Measure Z) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (probability (I := I) μ) := by dsimp [probability]; infer_instance

/-- The complete current initial-state / Brownian evaluation vector. -/
def process (t : ℝ≥0) (p : Space Z I) : Z × (I → ℝ) := (p.1, fun i => p.2 i t)

theorem process_measurable (t : ℝ≥0) : Measurable (process (Z := Z) (I := I) t) := by
  apply measurable_fst.prodMk
  apply measurable_pi_iff.mpr
  intro i
  exact (ContinuousMap.measurable_eval t).comp ((measurable_pi_apply i).comp measurable_snd)

def filtration : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Space Z I)) :=
  Filtration.natural (process (Z := Z) (I := I)) (fun t => (process_measurable t).stronglyMeasurable)

def coordinate (i : I) (t : ℝ≥0) (p : Space Z I) : ℝ := p.2 i t

theorem coordinate_adapted (i : I) : StronglyAdapted (filtration (Z := Z) (I := I))
    (coordinate i) := by
  intro t
  have h := Filtration.stronglyAdapted_natural
    (fun r => (process_measurable (Z := Z) (I := I) r).stronglyMeasurable) t
  exact ((continuous_apply i).comp continuous_snd).comp_stronglyMeasurable h

variable (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)
  (X : Ω → Z) (hX : Measurable X)

/-- The actual initial variable and entire continuous Brownian path. -/
def inputMap (ω : Ω) : Space Z I :=
  (X ω, vectorPathMap Q ((continuousDriver Q D).process) ω)

include hX

theorem inputMap_measurable : Measurable (inputMap Q D X) :=
  hX.prodMk (vectorPathMap_measurable Q _ (fun i t =>
    (((continuousDriver Q D).adapted i t).mono ((continuousDriver Q D).filtration.le t)).measurable))

theorem inputMap_coordinate_ae (i : I) (t : ℝ≥0) :
    (fun ω => coordinate i t (inputMap Q D X ω)) =ᵐ[Q] (continuousDriver Q D).process i t := by
  filter_upwards [vectorPathMap_ae Q ((continuousDriver Q D).process)
    (continuousDriver_continuous Q D)] with ω hω
  exact hω i t

theorem inputMap_past (hXA : AEStronglyMeasurable[D.filtration 0] X Q) (t : ℝ≥0) :
    MeasurableSpace.comap (inputMap Q D X) (filtration (Z := Z) (I := I) t) ≤
      (nullAugmentedDriver Q (continuousDriver Q D)).filtration t := by
  apply natural_comap_le_nullAugmented Q D.filtration
    (process (Z := Z) (I := I)) (fun t => (process_measurable t).stronglyMeasurable)
    (inputMap_measurable Q D X hX)
  intro r
  have hB : StronglyMeasurable[D.filtration r]
      (fun ω => fun i => (continuousDriver Q D).process i r ω) := by
    apply Measurable.stronglyMeasurable
    exact (@measurable_pi_iff Ω I (fun _ => ℝ) (D.filtration r) (fun _ => inferInstance)
      (fun ω i => (continuousDriver Q D).process i r ω)).mpr
        (fun i => ((continuousDriver Q D).adapted i r).measurable)
  have hpair := (hXA.mono (D.filtration.mono (show (0 : ℝ≥0) ≤ r from bot_le))).prodMk
    hB.aestronglyMeasurable
  apply hpair.congr
  filter_upwards [vectorPathMap_ae Q ((continuousDriver Q D).process)
    (continuousDriver_continuous Q D)] with ω hω
  change (X ω, fun i => (continuousDriver Q D).process i r ω) =
    (X ω, fun i => vectorPathMap Q ((continuousDriver Q D).process) ω i r)
  congr 1
  exact funext (fun i => (hω i r).symm)

theorem inputMap_preserving (hXA : AEStronglyMeasurable[D.filtration 0] X Q) :
    MeasurePreserving (inputMap Q D X) Q (probability (I := I) (Q.map X)) :=
  D.initialPathMap_measurePreserving Q X hX hXA

/-- A genuine Wiener-path driver. Literal coordinate evaluation, the full
joint natural past, and all Brownian fields are derived from primitive data. -/
def ofSource (hXA : AEStronglyMeasurable[D.filtration 0] X Q) :
    Driver (I := I) (probability (I := I) (Q.map X)) := by
  letI : IsProbabilityMeasure (Q.map X) := (Measure.isProbabilityMeasure_map_iff
    hX.aemeasurable).mpr inferInstance
  exact pushforwardDriver (inputMap_preserving Q D X hX hXA)
    (nullAugmentedDriver Q (continuousDriver Q D)) coordinate filtration coordinate_adapted
    (inputMap_coordinate_ae Q D X hX) (inputMap_past Q D X hX hXA)

@[simp] theorem ofSource_process (hXA : AEStronglyMeasurable[D.filtration 0] X Q) :
    (ofSource Q D X hX hXA).process = coordinate := rfl

@[simp] theorem ofSource_filtration (hXA : AEStronglyMeasurable[D.filtration 0] X Q) :
    (ofSource Q D X hX hXA).filtration = filtration := rfl

omit hX

section Canonical
variable (μ : Measure Z) [IsProbabilityMeasure μ]

theorem canonical_initial_adapted :
    AEStronglyMeasurable[(CanonicalBrownianDriver.driver (I := I) μ).filtration 0]
      (Prod.fst : Z × ULA.CanonicalBrownian.VectorSample I → Z)
      (μ.prod (ULA.CanonicalBrownian.vectorProbability I)) := by
  have h := Filtration.stronglyAdapted_natural
    (fun r => (CanonicalInitialFiltration.process_measurable (Z := Z) (I := I) r).stronglyMeasurable)
    (0 : ℝ≥0)
  exact (continuous_fst.comp_stronglyMeasurable h).aestronglyMeasurable

/-- A canonical driver on the literal independent initial-law × Wiener
path probability, constructed without a supplied Brownian-path law. -/
def driver : Driver (I := I) (probability (I := I) μ) := by
  let R := μ.prod (ULA.CanonicalBrownian.vectorProbability I)
  let D := CanonicalBrownianDriver.driver (I := I) μ
  let X : Z × ULA.CanonicalBrownian.VectorSample I → Z := Prod.fst
  have hXA : AEStronglyMeasurable[D.filtration 0] X R := canonical_initial_adapted μ
  have hf : MeasurePreserving (inputMap R D X) R (probability (I := I) μ) := by
    simpa only [R, X, Measure.map_fst_prod, measure_univ, one_smul] using
      inputMap_preserving R D X measurable_fst hXA
  exact pushforwardDriver hf (nullAugmentedDriver R (continuousDriver R D))
    coordinate filtration coordinate_adapted (inputMap_coordinate_ae R D X measurable_fst)
    (inputMap_past R D X measurable_fst hXA)

@[simp] theorem driver_process : (driver (I := I) μ).process = coordinate := rfl

@[simp] theorem driver_filtration : (driver (I := I) μ).filtration = filtration := rfl

end Canonical

end PBGSO.BrownianPathDriver
