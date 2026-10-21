import UnadjustedLangevin.ULAupdate
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Gaussian and Brownian noise moments in Euclidean space

The square-root noise estimate is proved from Gaussian coordinate laws.
Independence is unnecessary for this particular second-moment calculation:
the squared Euclidean norm is a sum of coordinate squares, with no cross terms.
The Brownian specialization uses mathlib's actual Brownian marginal-law theorem.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ULA

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ}

/-- The second moment of a centered real Gaussian is its variance parameter. -/
theorem centered_gaussian_second_moment (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = (v : ℝ) := by
  have hv := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at hv
  simpa only [sub_zero] using hv

/-- Gaussian coordinate laws imply genuine square integrability of a vector. -/
theorem gaussian_vector_memLp (X : Ω → E d) (v : ℝ≥0)
    (hlaw : ∀ i : Fin d, HasLaw (fun ω ↦ X ω i) (gaussianReal 0 v) P) :
    MemLp X 2 P := by
  apply memLp_piLp_iff.mpr
  intro i
  exact (hlaw i).memLp (memLp_id_gaussianReal (2 : ℝ≥0))

/-- Summing exact Gaussian coordinate moments gives the dimension factor. -/
theorem gaussian_vector_second_moment (X : Ω → E d) (v : ℝ≥0)
    (hlaw : ∀ i : Fin d, HasLaw (fun ω ↦ X ω i) (gaussianReal 0 v) P) :
    (∫ ω, ‖X ω‖ ^ 2 ∂P) = (d : ℝ) * (v : ℝ) := by
  have hmem (i : Fin d) : MemLp (fun ω ↦ X ω i) 2 P :=
    (hlaw i).memLp (memLp_id_gaussianReal (2 : ℝ≥0))
  have hmom (i : Fin d) : (∫ ω, (X ω i) ^ 2 ∂P) = (v : ℝ) := by
    exact (hlaw i).integral_comp (f := fun x : ℝ ↦ x ^ 2) (by fun_prop) |>.trans
      (centered_gaussian_second_moment v)
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum _ (fun i _ ↦ (hmem i).integrable_sq)]
  simp only [hmom, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Its L² representative has the same exact second moment. -/
theorem gaussian_vector_toLp_norm_sq (X : Ω → E d) (v : ℝ≥0)
    (hlaw : ∀ i : Fin d, HasLaw (fun ω ↦ X ω i) (gaussianReal 0 v) P) :
    ‖(gaussian_vector_memLp P X v hlaw).toLp X‖ ^ 2 = (d : ℝ) * (v : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have hid : (∫ ω, inner ℝ
      ((gaussian_vector_memLp P X v hlaw).toLp X ω)
      ((gaussian_vector_memLp P X v hlaw).toLp X ω) ∂P) = ∫ ω, ‖X ω‖ ^ 2 ∂P := by
    apply integral_congr_ae
    filter_upwards [(gaussian_vector_memLp P X v hlaw).coeFn_toLp] with ω hω
    rw [hω, real_inner_self_eq_norm_sq]
  rw [hid, gaussian_vector_second_moment P X v hlaw]

/-- The exact square-root Gaussian L² norm, including zero dimension or variance. -/
theorem gaussian_vector_toLp_norm (X : Ω → E d) (v : ℝ≥0)
    (hlaw : ∀ i : Fin d, HasLaw (fun ω ↦ X ω i) (gaussianReal 0 v) P) :
    ‖(gaussian_vector_memLp P X v hlaw).toLp X‖ = Real.sqrt ((d : ℝ) * (v : ℝ)) := by
  rw [← gaussian_vector_toLp_norm_sq P X v hlaw, Real.sqrt_sq (norm_nonneg _)]

/-- The Langevin scaling `√2` gives precisely the noise moment `√(2dv)`. -/
theorem gaussian_vector_scaled_l2_norm (X : Ω → E d) (v : ℝ≥0)
    (hlaw : ∀ i : Fin d, HasLaw (fun ω ↦ X ω i) (gaussianReal 0 v) P) :
    ‖Real.sqrt 2 • (gaussian_vector_memLp P X v hlaw).toLp X‖ =
      Real.sqrt (2 * (d : ℝ)) * Real.sqrt (v : ℝ) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    gaussian_vector_toLp_norm P X v hlaw,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ d),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- Assemble scalar Brownian coordinates into the Euclidean noise vector. -/
def brownianVector (W : Fin d → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) : Ω → E d :=
  fun ω ↦ WithLp.toLp 2 (fun i ↦ W i t ω)

/-- Mathlib's Brownian marginal laws supply the Gaussian hypotheses above. -/
theorem brownianVector_coordinate_law (W : Fin d → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P) (t : ℝ≥0) (i : Fin d) :
    HasLaw (fun ω ↦ brownianVector W t ω i) (gaussianReal 0 t) P :=
  (hW i).hasLaw_eval t

/-- A Brownian vector at any nonnegative time has finite second moment. -/
theorem brownianVector_memLp (W : Fin d → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P) (t : ℝ≥0) :
    MemLp (brownianVector W t) 2 P :=
  gaussian_vector_memLp P (brownianVector W t) t (brownianVector_coordinate_law P W hW t)

/-- The noise moment used by Dalalyan's proof follows from Brownian laws. -/
theorem brownianVector_scaled_l2_norm (W : Fin d → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P) (t : ℝ≥0) :
    ‖Real.sqrt 2 • (brownianVector_memLp P W hW t).toLp (brownianVector W t)‖ =
      Real.sqrt (2 * (d : ℝ)) * Real.sqrt (t : ℝ) :=
  gaussian_vector_scaled_l2_norm P (brownianVector W t) t
    (brownianVector_coordinate_law P W hW t)

/-- The Brownian vector increment over the interval from `a` to `a+t`. -/
def brownianVectorIncrement (W : Fin d → ℝ≥0 → Ω → ℝ) (a t : ℝ≥0) : Ω → E d :=
  fun ω ↦ brownianVector W (a + t) ω - brownianVector W a ω

/-- Brownian increments have variance equal to the elapsed time, at every
starting time. This uses the actual Brownian marginal difference law. -/
theorem brownianVectorIncrement_coordinate_law (W : Fin d → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P) (a t : ℝ≥0) (i : Fin d) :
    HasLaw (fun ω ↦ brownianVectorIncrement W a t ω i) (gaussianReal 0 t) P := by
  change HasLaw (fun ω ↦ W i (a + t) ω - W i a ω) (gaussianReal 0 t) P
  convert (hW i).hasLaw_sub (a + t) a using 1
  congr 1
  apply NNReal.eq
  simp only [coe_nndist, Real.dist_eq]
  change (t : ℝ) = |((a : ℝ) + (t : ℝ)) - (a : ℝ)|
  rw [add_sub_cancel_left, abs_of_nonneg t.coe_nonneg]

/-- The vector increment is a genuinely square-integrable random variable. -/
theorem brownianVectorIncrement_memLp (W : Fin d → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P) (a t : ℝ≥0) :
    MemLp (brownianVectorIncrement W a t) 2 P :=
  gaussian_vector_memLp P (brownianVectorIncrement W a t) t
    (brownianVectorIncrement_coordinate_law P W hW a t)

/-- Every reference segment has the same exact Langevin noise L² norm,
`√(2d)√t`, regardless of its starting time. -/
theorem brownianVector_increment_scaled_l2_norm (W : Fin d → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P) (a t : ℝ≥0) :
    ‖Real.sqrt 2 • (brownianVectorIncrement_memLp P W hW a t).toLp
      (brownianVectorIncrement W a t)‖ =
      Real.sqrt (2 * (d : ℝ)) * Real.sqrt (t : ℝ) :=
  gaussian_vector_scaled_l2_norm P (brownianVectorIncrement W a t) t
    (brownianVectorIncrement_coordinate_law P W hW a t)

end ULA
