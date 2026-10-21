import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Gaussian.Multivariate

set_option linter.style.header false

/-! # Scalar Gaussian innovations determine the vector algorithm

Independence over iteration-coordinate pairs implies the full vector-valued
iid standard Gaussian path law. Grouping coordinates introduces no hypothesis.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ULA

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- The entire vector noise path law follows from independent scalar coordinates. -/
theorem gaussianInnovations_pathLaw (W : ℕ → Ω → EuclideanSpace ℝ ι)
    (hW : ∀ n, AEMeasurable (W n) P)
    (hcoord : ∀ n i, HasLaw (fun ω ↦ W n ω i) (gaussianReal 0 1) P)
    (hind : iIndepFun (fun p : ℕ × ι ↦ fun ω ↦ W p.1 ω p.2) P) :
    P.map (fun ω n ↦ W n ω) =
      Measure.infinitePi (fun _ : ℕ ↦ stdGaussian (EuclideanSpace ℝ ι)) := by
  let flat : Ω → (ℕ × ι → ℝ) := fun ω p ↦ W p.1 ω p.2
  have hflat : AEMeasurable flat P :=
    aemeasurable_pi_iff.mpr fun p ↦ (hcoord p.1 p.2).aemeasurable
  have hlaw : P.map flat = Measure.infinitePi (fun _ : ℕ × ι ↦ gaussianReal 0 1) := by
    have hp := hind.map_fun_eq_infinitePi_map₀' (fun p : ℕ × ι ↦ (hcoord p.1 p.2).aemeasurable)
    simpa only [(hcoord _ _).map_eq] using hp
  let pack : (ℕ → ι → ℝ) → ℕ → EuclideanSpace ℝ ι :=
    fun w n ↦ WithLp.toLp 2 (w n)
  have hpack : Measurable pack := by
    exact measurable_pi_iff.mpr fun n ↦
      (WithLp.measurable_toLp 2 _).comp (measurable_pi_apply n)
  have heq : (fun ω n ↦ W n ω) =
      pack ∘ (MeasurableEquiv.curry ℕ ι ℝ) ∘ flat := by rfl
  rw [heq, ← AEMeasurable.map_map_of_aemeasurable hpack.aemeasurable
      ((MeasurableEquiv.curry ℕ ι ℝ).measurable.aemeasurable.comp_aemeasurable hflat),
    ← AEMeasurable.map_map_of_aemeasurable
      (MeasurableEquiv.curry ℕ ι ℝ).measurable.aemeasurable hflat, hlaw,
    Measure.infinitePi_map_curry (fun (_ : ℕ) (_ : ι) ↦ gaussianReal 0 1)]
  change (Measure.infinitePi (fun _ : ℕ ↦ Measure.infinitePi
    (fun _ : ι ↦ gaussianReal 0 1))).map pack = _
  rw [Measure.infinitePi_map_pi]
  · simp only [Measure.infinitePi_eq_pi, map_pi_eq_stdGaussian]
  · intro n
    exact WithLp.measurable_toLp 2 _

/-- Each innovation vector has the actual standard multivariate Gaussian law. -/
theorem gaussianInnovations_vectorLaw (W : ℕ → Ω → EuclideanSpace ℝ ι)
    (hW : ∀ n, AEMeasurable (W n) P)
    (hcoord : ∀ n i, HasLaw (fun ω ↦ W n ω i) (gaussianReal 0 1) P)
    (hind : iIndepFun (fun p : ℕ × ι ↦ fun ω ↦ W p.1 ω p.2) P) (n : ℕ) :
    P.map (W n) = stdGaussian (EuclideanSpace ℝ ι) := by
  have hp := gaussianInnovations_pathLaw P W hW hcoord hind
  calc
    P.map (W n) = (P.map (fun ω k ↦ W k ω)).map (fun w ↦ w n) := by
      rw [AEMeasurable.map_map_of_aemeasurable
        (measurable_pi_apply n).aemeasurable (aemeasurable_pi_iff.mpr hW)]
      rfl
    _ = _ := by rw [hp, Measure.infinitePi_map_eval]

/-- The vector innovations are independent over time, as a theorem rather
than a separate Gaussian algorithm assumption. -/
theorem gaussianInnovations_vectorIndependent (W : ℕ → Ω → EuclideanSpace ℝ ι)
    (hW : ∀ n, AEMeasurable (W n) P)
    (hcoord : ∀ n i, HasLaw (fun ω ↦ W n ω i) (gaussianReal 0 1) P)
    (hind : iIndepFun (fun p : ℕ × ι ↦ fun ω ↦ W p.1 ω p.2) P) :
    iIndepFun W P := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map₀' hW,
    gaussianInnovations_pathLaw P W hW hcoord hind]
  simp_rw [gaussianInnovations_vectorLaw P W hW hcoord hind]

end ULA
