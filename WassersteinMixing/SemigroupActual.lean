import WassersteinMixing.Semigroup
import WassersteinMixing.SemigroupContinuity
import WassersteinMixing.ActualComparison

/-! # Actual Gibbs Langevin evaluations and `L²` transition operators

All evaluation maps below use the canonical Brownian Langevin solution
constructed from the potential assumptions. Their isometries and the
contractive transition operators are conclusions of Gibbs stationarity.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory
open scoped ENNReal

namespace WassersteinMixing

variable {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Evaluate a target `L²` observable on the actual canonical diffusion at a grid time. -/
def actualEvaluation (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (n : ℕ) :
    Lp F 2 (ULA.gibbsMeasure V) →ₗᵢ[𝕜] Lp F 2 (actualProbability P V) :=
  Lp.compMeasurePreservingₗᵢ 𝕜 (actualReference P V hV n)
    ⟨(Lp.stronglyMeasurable _).measurable, actualReference_stationary P V hV n⟩

/-- Interior-time evaluation is likewise an isometry for the actual Gibbs diffusion. -/
def actualSegmentEvaluation (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc 0 P.step) :
    Lp F 2 (ULA.gibbsMeasure V) →ₗᵢ[𝕜] Lp F 2 (actualProbability P V) :=
  Lp.compMeasurePreservingₗᵢ 𝕜 (actualSegment P V hV n t)
    ⟨(Lp.stronglyMeasurable _).measurable, actualSegment_stationary P V hV n t ht⟩

/-- The actual grid transition on target observables, constructed by adjoint compression. -/
def actualTransition (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (n : ℕ) :
    Lp F 2 (ULA.gibbsMeasure V) →L[𝕜] Lp F 2 (ULA.gibbsMeasure V) :=
  ObservableTransition.compression (actualEvaluation (𝕜 := 𝕜) P V hV 0) (actualEvaluation (𝕜 := 𝕜) P V hV n)

/-- A continuous-local-time transition from the actual initial Gibbs state. -/
def actualSegmentTransition (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (t : ℝ) (ht : t ∈ Set.Icc 0 P.step) :
    Lp F 2 (ULA.gibbsMeasure V) →L[𝕜] Lp F 2 (ULA.gibbsMeasure V) :=
  ObservableTransition.compression (actualEvaluation (𝕜 := 𝕜) P V hV 0)
    (actualSegmentEvaluation (𝕜 := 𝕜) P V hV 0 t ht)

/-- The constructed actual grid transitions contract every target observable. -/
theorem actualTransition_norm_le (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (n : ℕ) (f : Lp F 2 (ULA.gibbsMeasure V)) :
    ‖actualTransition (𝕜 := 𝕜) P V hV n f‖ ≤ ‖f‖ :=
  ObservableTransition.compression_norm_le _ _ f

/-- The actual local-time transition is also a contraction. -/
theorem actualSegmentTransition_norm_le (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (t : ℝ) (ht : t ∈ Set.Icc 0 P.step)
    (f : Lp F 2 (ULA.gibbsMeasure V)) :
    ‖actualSegmentTransition (𝕜 := 𝕜) P V hV t ht f‖ ≤ ‖f‖ :=
  ObservableTransition.compression_norm_le _ _ f

/-- At time zero the constructed actual grid transition is the identity. -/
@[simp] theorem actualTransition_zero (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) :
    actualTransition (𝕜 := 𝕜) (F := F) P V hV 0 = ContinuousLinearMap.id 𝕜 _ :=
  ObservableTransition.compression_self _

/-- Correlations of the constructed operator are the actual two-time diffusion correlations. -/
theorem actualTransition_inner (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (n : ℕ) (f g : Lp F 2 (ULA.gibbsMeasure V)) :
    inner 𝕜 (actualTransition (𝕜 := 𝕜) P V hV n f) g =
      inner 𝕜 (actualEvaluation (𝕜 := 𝕜) P V hV n f) (actualEvaluation (𝕜 := 𝕜) P V hV 0 g) :=
  ObservableTransition.compression_inner _ _ f g

omit [CompleteSpace F] in
/-- The actual representative formula for stationary evaluation. -/
theorem actualEvaluation_coe (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (n : ℕ) (f : Lp F 2 (ULA.gibbsMeasure V)) :
    actualEvaluation (𝕜 := 𝕜) P V hV n f =ᵐ[actualProbability P V]
      fun ω ↦ f (actualReference P V hV n ω) :=
  Lp.coeFn_compMeasurePreserving _ _

/-- The correlation identity contains actual observables of the actual Brownian-driven states. -/
theorem actualTransition_correlation (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (n : ℕ) (f g : Lp F 2 (ULA.gibbsMeasure V)) :
    inner 𝕜 (actualTransition (𝕜 := 𝕜) P V hV n f) g =
      ∫ ω, inner 𝕜 (f (actualReference P V hV n ω))
        (g (actualReference P V hV 0 ω)) ∂actualProbability P V := by
  rw [actualTransition_inner, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [actualEvaluation_coe (𝕜 := 𝕜) P V hV n f,
    actualEvaluation_coe (𝕜 := 𝕜) P V hV 0 g] with ω hf hg
  rw [hf, hg]

omit [CompleteSpace F] in
/-- Every target observable has a strongly continuous actual diffusion
evaluation along each canonical Brownian segment. -/
theorem continuous_actualSegmentEvaluation [NormedSpace ℝ F]
    (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V)
    (n : ℕ) (f : Lp F 2 (ULA.gibbsMeasure V)) :
    Continuous (fun t : Set.Icc (0 : ℝ) P.step ↦
      actualSegmentEvaluation (𝕜 := 𝕜) P V hV n t t.property f) := by
  let := actualTarget_isProbability P V hV
  let := actualProbability_isProbability P V hV
  have hstate : Continuous (fun t : Set.Icc (0 : ℝ) P.step ↦ actualSegment P V hV n t) :=
    ((actualReferenceData P V hV).continuous n).comp continuous_subtype_val
  apply continuous_iff_continuousAt.mpr
  intro t
  have ht := StationaryObservables.evaluation_tendsto (𝕜 := 𝕜)
    (ULA.gibbsMeasure V) (actualProbability P V)
    (fun s : Set.Icc (0 : ℝ) P.step ↦ actualSegment P V hV n s)
    (actualSegment P V hV n t)
    (fun s ↦ actualSegment_stationary P V hV n s s.property)
    (actualSegment_stationary P V hV n t t.property) (hstate.tendsto t) f
  exact ht

/-- Strong continuity of the constructed actual local-time transition. -/
theorem continuous_actualSegmentTransition [NormedSpace ℝ F]
    (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V)
    (f : Lp F 2 (ULA.gibbsMeasure V)) :
    Continuous (fun t : Set.Icc (0 : ℝ) P.step ↦
      actualSegmentTransition (𝕜 := 𝕜) P V hV t t.property f) := by
  exact (actualEvaluation (𝕜 := 𝕜) (F := F) P V hV 0).toContinuousLinearMap.adjoint.continuous.comp
    (continuous_actualSegmentEvaluation P V hV 0 f)

end WassersteinMixing
