import PBGSO.ContinuousBrownianDriver
import PBGSO.CanonicalBrownianDriver
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! # Actual continuous Brownian path laws
The actual path map is regularized on one measurable null event. Its path-law
is obtained from the original finite-dimensional Brownian laws, rather than
assuming that an arbitrary Brownian source preserves an unrelated Gaussian
seed space. This retains precisely the noise actually used by the SDE.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Classical
namespace PBGSO.BrownianPathSpace
variable {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- One actual measurable set covers all path discontinuities. -/
def bad (Q : Measure Ω) (B : ℝ≥0 → Ω → E) : Set Ω :=
  toMeasurable Q {ω | ¬ Continuous (fun t => B t ω)}

/-- A literal continuous path variable, set to zero only on its single
measurable discontinuity cover. -/
def pathMap (Q : Measure Ω) (B : ℝ≥0 → Ω → E) (ω : Ω) : C(ℝ≥0,E) :=
  if h : ω ∈ bad Q B then 0 else
    ⟨fun t => B t ω, by
      by_contra hn
      exact h (subset_toMeasurable Q _ hn)⟩

theorem bad_null (Q : Measure Ω) (B : ℝ≥0 → Ω → E)
    (hc : ∀ᵐ ω ∂Q, Continuous (fun t => B t ω)) : Q (bad Q B) = 0 := by
  rw [bad,measure_toMeasurable]
  exact ae_iff.mp hc

theorem pathMap_measurable (Q : Measure Ω) (B : ℝ≥0 → Ω → E)
    (hB : ∀ t, Measurable (B t)) : Measurable (pathMap Q B) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  have he : (fun ω => pathMap Q B ω t) = (bad Q B).piecewise (fun _ => 0) (B t) := by
    funext ω
    by_cases h : ω ∈ bad Q B
    · simp [pathMap,h]
    · simp [pathMap,h]
  rw [he]
  exact Measurable.piecewise (measurableSet_toMeasurable _ _) measurable_const (hB t)

/-- All times are represented on one common probability-one event. -/
theorem pathMap_ae (Q : Measure Ω) (B : ℝ≥0 → Ω → E)
    (hc : ∀ᵐ ω ∂Q, Continuous (fun t => B t ω)) :
    ∀ᵐ ω ∂Q, ∀ t, pathMap Q B ω t = B t ω := by
  filter_upwards [(show ∀ᵐ ω ∂Q, ω ∉ bad Q B from ae_iff.mpr (by simpa using bad_null Q B hc))] with ω hω
  intro t
  simp only [pathMap,dite_eq_right hω,ContinuousMap.coe_mk]

/-- The continuous-path sigma algebra is exactly the initial algebra of
all raw evaluation coordinates. -/
theorem path_comap_eq :
    MeasurableSpace.comap (fun f : C(ℝ≥0,E) => fun t => f t)
      (inferInstance : MeasurableSpace (ℝ≥0 → E)) =
      (inferInstance : MeasurableSpace C(ℝ≥0,E)) := by
  rw [MeasurableSpace.pi]
  simp_rw [MeasurableSpace.comap_iSup,MeasurableSpace.comap_comp]
  exact ContinuousMap.measurableSpace_eq_iSup_comap_eval.symm

/-- Raw path-law equality determines the actual continuous path law. -/
theorem measure_eq_of_raw_map_eq (μ ν : Measure C(ℝ≥0,E))
    (h : μ.map (fun f => fun t => f t) = ν.map (fun f => fun t => f t)) : μ = ν := by
  ext s hs
  have hs' : MeasurableSet[MeasurableSpace.comap
      (fun f : C(ℝ≥0,E) => fun t => f t) inferInstance] s := by
    exact (congrArg (fun m : MeasurableSpace C(ℝ≥0,E) => @MeasurableSet _ m s)
      (path_comap_eq (E := E))).mpr hs
  obtain ⟨v,hv,rfl⟩ := hs'
  have hm : Measurable (fun f : C(ℝ≥0,E) => fun t => f t) :=
    measurable_pi_iff.mpr (fun t => ContinuousMap.measurable_eval t)
  rw [← Measure.map_apply hm hv,← Measure.map_apply hm hv,h]

section Scalar
variable (Q : Measure Ω) (R : Measure Ω') [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
  (B : ℝ≥0 → Ω → ℝ) (C : ℝ≥0 → Ω' → ℝ)

/-- Actual scalar pre-Brownian motions have the same whole raw path law,
by uniqueness of their common finite-dimensional projective family. -/
theorem scalar_raw_law_eq (hB : IsPreBrownianReal B Q) (hC : IsPreBrownianReal C R)
    (hmB : ∀ t, Measurable (B t)) (hmC : ∀ t, Measurable (C t)) :
    Q.map (fun ω => fun t => B t ω) = R.map (fun ω => fun t => C t ω) := by
  have hQ : IsProjectiveLimit (Q.map (fun ω => fun t => B t ω))
      ProbabilityTheory.BrownianReal.projectiveFamily := by
    intro J
    rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict _).aemeasurable
      (measurable_pi_iff.mpr hmB).aemeasurable]
    simpa only [Function.comp_def] using (hB.hasLaw J).map_eq
  have hR : IsProjectiveLimit (R.map (fun ω => fun t => C t ω))
      ProbabilityTheory.BrownianReal.projectiveFamily := by
    intro J
    rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict _).aemeasurable
      (measurable_pi_iff.mpr hmC).aemeasurable]
    simpa only [Function.comp_def] using (hC.hasLaw J).map_eq
  exact hQ.unique hR

/-- Actual scalar Brownian continuous-path laws agree, with the raw
finite-dimensional laws and simultaneous path identities proved internally. -/
theorem scalar_path_law_eq (hB : IsBrownianReal B Q) (hC : IsBrownianReal C R)
    (hmB : ∀ t, Measurable (B t)) (hmC : ∀ t, Measurable (C t)) :
    Q.map (pathMap Q B) = R.map (pathMap R C) := by
  apply measure_eq_of_raw_map_eq
  rw [Measure.map_map (measurable_pi_iff.mpr (fun t => ContinuousMap.measurable_eval t))
      (pathMap_measurable Q B hmB),
    Measure.map_map (measurable_pi_iff.mpr (fun t => ContinuousMap.measurable_eval t))
      (pathMap_measurable R C hmC)]
  have heB : (fun ω => fun t => pathMap Q B ω t) =ᵐ[Q] (fun ω => fun t => B t ω) := by
    filter_upwards [pathMap_ae Q B hB.cont] with ω hω
    exact funext hω
  have heC : (fun ω => fun t => pathMap R C ω t) =ᵐ[R] (fun ω => fun t => C t ω) := by
    filter_upwards [pathMap_ae R C hC.cont] with ω hω
    exact funext hω
  change Q.map (fun ω => fun t => pathMap Q B ω t) =
    R.map (fun ω => fun t => pathMap R C ω t)
  rw [Measure.map_congr heB,Measure.map_congr heC]
  exact scalar_raw_law_eq Q R B C hB.toIsPreBrownianReal hC.toIsPreBrownianReal hmB hmC
end Scalar

section Vector
variable {I : Type*} [Fintype I] [DecidableEq I]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (B : I → ℝ≥0 → Ω → ℝ)

/-- The actual complete finite-dimensional Brownian path variable. -/
def vectorPathMap (ω : Ω) : I → C(ℝ≥0,ℝ) := fun i => pathMap Q (B i) ω

theorem vectorPathMap_measurable (hB : ∀ i t, Measurable (B i t)) :
    Measurable (vectorPathMap Q B) :=
  measurable_pi_iff.mpr (fun i => pathMap_measurable Q (B i) (hB i))

theorem vectorPathMap_ae (hC : ∀ i, ∀ᵐ ω ∂Q, Continuous (fun t => B i t ω)) :
    ∀ᵐ ω ∂Q, ∀ i t, vectorPathMap Q B ω i t = B i t ω :=
  ae_all_iff.mpr (fun i => pathMap_ae Q (B i) (hC i))

/-- Actual independence is preserved when moving from raw scalar paths to
continuous scalar paths with their proved evaluation-generated Borel algebra. -/
theorem vectorPathMap_independent
    (hC : ∀ i, ∀ᵐ ω ∂Q, Continuous (fun t => B i t ω))
    (hpaths : iIndepFun (fun i ω => fun t => B i t ω) Q) :
    iIndepFun (fun i ω => vectorPathMap Q B ω i) Q := by
  have he (i : I) : (fun ω => fun t => B i t ω) =ᵐ[Q]
      (fun ω => fun t => pathMap Q (B i) ω t) := by
    filter_upwards [pathMap_ae Q (B i) (hC i)] with ω hω
    exact (funext hω).symm
  have hr := hpaths.congr he
  apply (iIndepFun_iff_iIndep (fun _ : I => inferInstance) _ Q).mpr
  have hi := (iIndepFun_iff_iIndep (fun _ : I => inferInstance) _ Q).mp hr
  convert hi using 1
  funext i
  change MeasurableSpace.comap (fun ω => pathMap Q (B i) ω) _ =
    MeasurableSpace.comap (fun ω => fun t => pathMap Q (B i) ω t) _
  have hh := congrArg (MeasurableSpace.comap (fun ω => pathMap Q (B i) ω))
    (path_comap_eq (E := ℝ))
  simpa only [MeasurableSpace.comap_comp,Function.comp_def] using hh.symm
end Vector

/-- An actual canonical scalar source, used only to define its continuous
path distribution; unused Gaussian seed directions are integrated out. -/
abbrev ScalarSource := ℝ × ULA.CanonicalBrownian.VectorSample Unit

def scalarProbability : Measure ScalarSource :=
  (Measure.dirac (0 : ℝ)).prod (ULA.CanonicalBrownian.vectorProbability Unit)

instance : IsProbabilityMeasure scalarProbability := by
  dsimp only [scalarProbability]
  infer_instance

def scalarDriver : FilteredBrownian.Driver (I := Unit) scalarProbability :=
  CanonicalBrownianDriver.driver (I := Unit) (Measure.dirac (0 : ℝ))

def scalarProcess : ℝ≥0 → ScalarSource → ℝ :=
  (FilteredBrownian.continuousDriver scalarProbability scalarDriver).process ()

theorem scalarProcess_brownian : IsBrownianReal scalarProcess scalarProbability :=
  FilteredBrownian.continuousDriver_brownian scalarProbability scalarDriver ()

theorem scalarProcess_measurable (t : ℝ≥0) : Measurable (scalarProcess t) :=
  (((FilteredBrownian.continuousDriver scalarProbability scalarDriver).adapted () t).mono
    ((FilteredBrownian.continuousDriver scalarProbability scalarDriver).filtration.le t)).measurable

/-- Wiener measure is the actual distribution of the constructed continuous
Brownian path; no map back into an artificial Gaussian seed space is required. -/
def wiener : Measure C(ℝ≥0,ℝ) := scalarProbability.map (pathMap scalarProbability scalarProcess)

instance : IsProbabilityMeasure wiener :=
  (Measure.isProbabilityMeasure_map_iff
    (pathMap_measurable scalarProbability scalarProcess scalarProcess_measurable).aemeasurable).mpr
      inferInstance

/-- Every actual Brownian scalar path has this same Wiener distribution. -/
theorem pathMap_hasLaw_wiener (Q : Measure Ω) [IsProbabilityMeasure Q]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B Q) (hm : ∀ t, Measurable (B t)) :
    HasLaw (pathMap Q B) wiener Q := by
  refine ⟨(pathMap_measurable Q B hm).aemeasurable, ?_⟩
  exact scalar_path_law_eq Q scalarProbability B scalarProcess hB scalarProcess_brownian
    hm scalarProcess_measurable

/-- The whole original independent Brownian vector has the actual product
Wiener law on continuous path space. -/
theorem vectorPathMap_hasLaw {I : Type*} [Fintype I] [DecidableEq I]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (B : I → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsBrownianReal (B i) Q) (hm : ∀ i t, Measurable (B i t))
    (hi : iIndepFun (fun i ω => fun t => B i t ω) Q) :
    HasLaw (vectorPathMap Q B) (Measure.pi (fun _ : I => wiener)) Q :=
  (vectorPathMap_independent Q B (fun i => (hB i).cont) hi).hasLaw_pi
    (fun i => pathMap_hasLaw_wiener Q (B i) (hB i) (hm i))


/-- The vector continuous-path algebra is generated by exactly its original
raw coordinate paths. -/
theorem vector_comap_eq {I : Type*} :
    MeasurableSpace.comap (fun p : I → C(ℝ≥0,ℝ) => fun i t => p i t)
      (inferInstance : MeasurableSpace (I → ℝ≥0 → ℝ)) =
      (inferInstance : MeasurableSpace (I → C(ℝ≥0,ℝ))) := by
  change MeasurableSpace.comap (fun p : I → C(ℝ≥0,ℝ) => fun i t => p i t)
      (⨆ i : I, MeasurableSpace.comap (fun p : I → ℝ≥0 → ℝ => p i) inferInstance) =
    ⨆ i : I, MeasurableSpace.comap (fun p : I → C(ℝ≥0,ℝ) => p i) inferInstance
  rw [MeasurableSpace.comap_iSup]
  congr 1
  funext i
  rw [MeasurableSpace.comap_comp]
  calc
    MeasurableSpace.comap (fun p : I → C(ℝ≥0,ℝ) => fun t => p i t) _ =
        MeasurableSpace.comap (fun p : I → C(ℝ≥0,ℝ) => p i)
          (MeasurableSpace.comap (fun f : C(ℝ≥0,ℝ) => fun t => f t) _) := by
      rw [MeasurableSpace.comap_comp]
      rfl
    _ = _ := congrArg (MeasurableSpace.comap (fun p : I → C(ℝ≥0,ℝ) => p i))
      (path_comap_eq (E := ℝ))

/-- Original initial/noise independence transfers to the actual continuous
path variable, using one simultaneous original-path identity. -/
theorem initial_vectorPathMap_independent {I A : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace A] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (B : I → ℝ≥0 → Ω → ℝ) (X : Ω → A)
    (hC : ∀ i, ∀ᵐ ω ∂Q, Continuous (fun t => B i t ω))
    (hi : IndepFun X (fun ω i t => B i t ω) Q) :
    IndepFun X (vectorPathMap Q B) Q := by
  have he : (fun ω i t => B i t ω) =ᵐ[Q]
      (fun ω i t => vectorPathMap Q B ω i t) := by
    filter_upwards [vectorPathMap_ae Q B hC] with ω hω
    exact (funext (fun i => funext (hω i))).symm
  have hr := hi.congr (Filter.EventuallyEq.rfl : X =ᵐ[Q] X) he
  have hm : MeasurableSpace.comap (vectorPathMap Q B) inferInstance =
      MeasurableSpace.comap (fun ω i t => vectorPathMap Q B ω i t) inferInstance := by
    have h := congrArg (MeasurableSpace.comap (vectorPathMap Q B)) (vector_comap_eq (I := I))
    simpa only [MeasurableSpace.comap_comp,Function.comp_def] using h.symm
  change Indep (MeasurableSpace.comap X inferInstance)
    (MeasurableSpace.comap (vectorPathMap Q B) inferInstance) Q
  rw [hm]
  exact hr

/-- Actual initialization and the entire continuous Brownian path map
preserve precisely the independent initial-law × Wiener-path probability.
The target product law is derived from primitive initial/noise independence;
it is not a supplied final-law matching hypothesis. -/
theorem initial_path_measurePreserving {I A : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace A] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (B : I → ℝ≥0 → Ω → ℝ) (X : Ω → A)
    (hB : ∀ i, IsBrownianReal (B i) Q) (hm : ∀ i t, Measurable (B i t))
    (hX : Measurable X) (hpaths : iIndepFun (fun i ω => fun t => B i t ω) Q)
    (hinit : IndepFun X (fun ω i t => B i t ω) Q) :
    MeasurePreserving (fun ω => (X ω, vectorPathMap Q B ω)) Q
      ((Q.map X).prod (Measure.pi (fun _ : I => wiener))) := by
  have hi := initial_vectorPathMap_independent Q B X (fun i => (hB i).cont) hinit
  have hL := hi.hasLaw_prod (show HasLaw X (Q.map X) Q from ⟨hX.aemeasurable,rfl⟩)
    (vectorPathMap_hasLaw Q B hB hm hpaths)
  exact ⟨hX.prodMk (vectorPathMap_measurable Q B hm),hL.map_eq⟩

/-- The actual Wiener path law has the spatial separability needed by raw
coefficient section construction; it is not an additional law hypothesis. -/
theorem wiener_isSeparable : IsSeparable wiener := inferInstance

theorem vectorWiener_isSeparable {I : Type*} [Fintype I] :
    IsSeparable (Measure.pi (fun _ : I => wiener)) := inferInstance

end PBGSO.BrownianPathSpace
