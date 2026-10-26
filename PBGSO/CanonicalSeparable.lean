import PBGSO.ProductLpSections
import PBGSO.CanonicalBrownianDriver

/-! # Separable canonical initial/Brownian sample measures
The isonormal Brownian source uses an actual Hilbert basis of scalar time L².
That basis is countable, derived from separability rather than postulated.
Consequently all finite-coordinate initial/noise sample spaces are countably
generated, and their actual probability measures are separable.
-/
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal
namespace PBGSO.CanonicalSeparable

instance basisIndex_countable : Countable ULA.CanonicalBrownian.basisIndex := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let e := ULA.CanonicalBrownian.basis
  have horth := e.orthonormal
  have hd : Pairwise (fun i j => Disjoint (Metric.ball (e i) (1 / 2 : ℝ))
    (Metric.ball (e j) (1 / 2 : ℝ))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have hn : ‖e i - e j‖ ^ 2 = 2 := by
      rw [norm_sub_sq_real, horth.norm_eq_one, horth.norm_eq_one,
        horth.inner_eq_zero hij]
      norm_num
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (e i - e j)]
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨e i, by simp⟩)

/-- Canonical scalar samples are countably generated because their actual
isonormal Gaussian coordinate index is countable. -/
theorem sample_countablyGenerated :
    MeasurableSpace.CountablyGenerated ULA.CanonicalBrownian.Sample := by infer_instance

/-- No separable-measure assumption is needed on actual finite-vector
canonical Brownian probability: it is proved from its constructed sample space. -/
theorem vector_isSeparable (I : Type*) [Countable I] :
    IsSeparable (ULA.CanonicalBrownian.vectorProbability I) := by infer_instance

/-- The actual random-initial/full-vector Brownian probability is separable. -/
theorem initial_vector_isSeparable {Z I : Type*} [MeasurableSpace Z]
    [TopologicalSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Countable I]
    (μ : Measure Z) [IsProbabilityMeasure μ] :
    IsSeparable (μ.prod (ULA.CanonicalBrownian.vectorProbability I)) := by infer_instance

end PBGSO.CanonicalSeparable
