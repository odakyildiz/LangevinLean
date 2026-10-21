import UnadjustedLangevin.GaussianHilbert
import UnadjustedLangevin.GaussianLinearProcess
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option linter.style.header false

/-! # A constructed Brownian source

The time indicators `1_(0,t]` live in the real Hilbert space L² of Lebesgue
measure. Their inner products are `min s t`. The isonormal Gaussian map
constructed from an independent Gaussian product therefore gives a concrete
centered Gaussian process with the Brownian covariance. No Brownian-existence
assumption is made in this construction.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ULA.CanonicalBrownian

abbrev TimeHilbert := Lp ℝ 2 (volume : Measure ℝ)

def timeIndicator (t : ℝ≥0) : TimeHilbert :=
  indicatorConstLp 2 measurableSet_Ioc
    (by simp only [Real.volume_Ioc, ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true]) (1 : ℝ)
    (s := Ioc 0 (t : ℝ))

theorem timeIndicator_inner (s t : ℝ≥0) :
    inner ℝ (timeIndicator s) (timeIndicator t) = min (s : ℝ) (t : ℝ) := by
  have hi := L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
    (μ := (volume : Measure ℝ))
    (s := Ioc 0 (s : ℝ)) (t := Ioc 0 (t : ℝ))
    measurableSet_Ioc measurableSet_Ioc
    (hμs := by simp [Real.volume_Ioc]) (hμt := by simp [Real.volume_Ioc])
  change inner ℝ (timeIndicator s) (timeIndicator t) = _ at hi
  rw [hi]
  simp only [Measure.real, Ioc_inter_Ioc, max_self, Real.volume_Ioc, sub_zero]
  rw [ENNReal.toReal_ofReal (le_min s.coe_nonneg t.coe_nonneg)]

def basisIndex : Set TimeHilbert :=
  Classical.choose (exists_hilbertBasis (𝕜 := ℝ) (E := TimeHilbert))

def basis : HilbertBasis basisIndex ℝ TimeHilbert :=
  Classical.choose (Classical.choose_spec
    (exists_hilbertBasis (𝕜 := ℝ) (E := TimeHilbert)))

abbrev Sample := basisIndex → ℝ

abbrev probability : Measure Sample := GaussianHilbert.source basisIndex

instance : IsProbabilityMeasure probability :=
  GaussianHilbert.source_isProbabilityMeasure basisIndex

def valueLp (t : ℝ≥0) : Lp ℝ 2 probability :=
  GaussianHilbert.isonormal basis (timeIndicator t)

/-- A particular strongly measurable representative at every time. -/
def process (t : ℝ≥0) : Sample → ℝ := valueLp t

theorem process_measurable (t : ℝ≥0) : Measurable (process t) :=
  (Lp.stronglyMeasurable (valueLp t)).measurable

theorem process_mean (t : ℝ≥0) : (∫ ω, process t ω ∂probability) = 0 :=
  GaussianHilbert.isonormal_mean basis (timeIndicator t)

theorem process_covariance (s t : ℝ≥0) :
    cov[process s, process t; probability] = min (s : ℝ) (t : ℝ) := by
  rw [process, process, valueLp, valueLp,
    GaussianHilbert.isonormal_covariance, timeIndicator_inner]

theorem isGaussianProcess : IsGaussianProcess process probability := by
  exact isGaussianProcess_of_linearMap_Lp probability
    (GaussianHilbert.isonormal basis).toLinearMap
    (GaussianHilbert.isonormal_hasGaussianLaw basis) timeIndicator

/-- Brownian finite-dimensional laws on the explicitly constructed source. -/
theorem isPreBrownian : IsPreBrownianReal process probability := by
  apply isGaussianProcess.isPreBrownianReal_of_covariance process_mean
  intro s t hst
  rw [process_covariance, min_eq_left (by exact_mod_cast hst)]

abbrev VectorSample (I : Type*) := I → Sample

def vectorProbability (I : Type*) : Measure (VectorSample I) :=
  Measure.infinitePi (fun _ : I ↦ probability)

instance (I : Type*) : IsProbabilityMeasure (vectorProbability I) := by
  unfold vectorProbability
  infer_instance

def coordinate {I : Type*} (i : I) (t : ℝ≥0) (ω : VectorSample I) : ℝ :=
  process t (ω i)

/-- Every vector coordinate has the constructed Brownian law. -/
theorem coordinate_isPreBrownian {I : Type*} (i : I) :
    IsPreBrownianReal (coordinate i) (vectorProbability I) where
  hasLaw s := (isPreBrownian.hasLaw s).comp
    (⟨(measurable_pi_apply i).aemeasurable,
      Measure.infinitePi_map_eval (fun _ : I ↦ probability) i⟩ :
      HasLaw (fun ω : VectorSample I ↦ ω i) probability (vectorProbability I))

/-- Entire coordinate paths are independent on the actual product source. -/
theorem coordinate_paths_independent (I : Type*) :
    iIndepFun (fun i (ω : VectorSample I) t ↦ coordinate i t ω)
      (vectorProbability I) := by
  exact iIndepFun_infinitePi (fun _ : I ↦
    measurable_pi_iff.mpr process_measurable)

/-- Restricting the independent coordinate paths to any time grid preserves
independence; this is the form required by the Gaussian Euler algorithm. -/
theorem coordinate_grid_paths_independent (I : Type*) (h : ℝ≥0) :
    iIndepFun (fun i (ω : VectorSample I) (n : ℕ) ↦
      coordinate i ((n : ℝ≥0) * h) ω) (vectorProbability I) := by
  exact (coordinate_paths_independent I).comp
    (fun _ p (n : ℕ) ↦ p ((n : ℝ≥0) * h))
    (fun _ ↦ measurable_pi_iff.mpr fun n ↦ measurable_pi_apply _)

end ULA.CanonicalBrownian
