import UnadjustedLangevin.GaussianMoments

set_option linter.style.header false

/-!
# Gaussian and Brownian moments for arbitrary finite coordinate sets

The previous Gaussian moment lemmas use `Fin d`. IPLA uses the product set of
particle blocks and within-block coordinates. This module supplies the same
exact moment bounds for `EuclideanSpace ℝ ι`, for any finite coordinate set.
Only marginal coordinate laws are needed for second moments; independence is
not added as an unnecessary hypothesis.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ULA

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  (P : Measure Ω)

/-- Gaussian coordinate laws imply square integrability on any finite
Euclidean coordinate space. -/
theorem gaussian_coordinates_memLp (X : Ω → EuclideanSpace ℝ ι) (v : ℝ≥0)
    (hlaw : ∀ i : ι, HasLaw (fun ω ↦ X ω i) (gaussianReal 0 v) P) :
    MemLp X 2 P := by
  apply memLp_piLp_iff.mpr
  intro i
  exact (hlaw i).memLp (memLp_id_gaussianReal (2 : ℝ≥0))

/-- The dimension factor is the exact cardinality of the coordinate set. -/
theorem gaussian_coordinates_second_moment (X : Ω → EuclideanSpace ℝ ι) (v : ℝ≥0)
    (hlaw : ∀ i : ι, HasLaw (fun ω ↦ X ω i) (gaussianReal 0 v) P) :
    (∫ ω, ‖X ω‖ ^ 2 ∂P) = (Fintype.card ι : ℝ) * (v : ℝ) := by
  have hmem (i : ι) : MemLp (fun ω ↦ X ω i) 2 P :=
    (hlaw i).memLp (memLp_id_gaussianReal (2 : ℝ≥0))
  have hmom (i : ι) : (∫ ω, (X ω i) ^ 2 ∂P) = (v : ℝ) := by
    exact (hlaw i).integral_comp (f := fun x : ℝ ↦ x ^ 2) (by fun_prop) |>.trans
      (centered_gaussian_second_moment v)
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum _ (fun i _ ↦ (hmem i).integrable_sq)]
  simp only [hmom, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Exact norm identity for an existing `L²` Gaussian vector. -/
theorem gaussian_coordinates_Lp_norm_sq (X : Lp (EuclideanSpace ℝ ι) 2 P) (v : ℝ≥0)
    (hlaw : ∀ i : ι, HasLaw (fun ω ↦ X ω i) (gaussianReal 0 v) P) :
    ‖X‖ ^ 2 = (Fintype.card ι : ℝ) * (v : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simpa only [real_inner_self_eq_norm_sq] using
    gaussian_coordinates_second_moment P X v hlaw

/-- Exact square-root norm identity for an existing `L²` Gaussian vector. -/
theorem gaussian_coordinates_Lp_norm (X : Lp (EuclideanSpace ℝ ι) 2 P) (v : ℝ≥0)
    (hlaw : ∀ i : ι, HasLaw (fun ω ↦ X ω i) (gaussianReal 0 v) P) :
    ‖X‖ = Real.sqrt ((Fintype.card ι : ℝ) * (v : ℝ)) := by
  rw [← gaussian_coordinates_Lp_norm_sq P X v hlaw,
    Real.sqrt_sq (norm_nonneg _)]

/-- Its `L²` representative has the original Gaussian coordinate laws. -/
theorem gaussian_coordinates_toLp_coordinateLaw
    (X : Ω → EuclideanSpace ℝ ι) (v : ℝ≥0)
    (hlaw : ∀ i : ι, HasLaw (fun ω ↦ X ω i) (gaussianReal 0 v) P) (i : ι) :
    HasLaw (fun ω ↦ (gaussian_coordinates_memLp P X v hlaw).toLp X ω i)
      (gaussianReal 0 v) P := by
  exact (hlaw i).congr
    ((gaussian_coordinates_memLp P X v hlaw).coeFn_toLp.fun_comp (fun z ↦ z i))

/-- Exact square-root norm of the canonical `L²` representative. -/
theorem gaussian_coordinates_toLp_norm (X : Ω → EuclideanSpace ℝ ι) (v : ℝ≥0)
    (hlaw : ∀ i : ι, HasLaw (fun ω ↦ X ω i) (gaussianReal 0 v) P) :
    ‖(gaussian_coordinates_memLp P X v hlaw).toLp X‖ =
      Real.sqrt ((Fintype.card ι : ℝ) * (v : ℝ)) :=
  gaussian_coordinates_Lp_norm P _ v
    (gaussian_coordinates_toLp_coordinateLaw P X v hlaw)

/-- The `√2` Langevin scaling gives exactly the required local-noise radius. -/
theorem gaussian_coordinates_scaled_l2_norm (X : Ω → EuclideanSpace ℝ ι) (v : ℝ≥0)
    (hlaw : ∀ i : ι, HasLaw (fun ω ↦ X ω i) (gaussianReal 0 v) P) :
    ‖Real.sqrt 2 • (gaussian_coordinates_memLp P X v hlaw).toLp X‖ =
      Real.sqrt (2 * (Fintype.card ι : ℝ)) * Real.sqrt (v : ℝ) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    gaussian_coordinates_toLp_norm P X v hlaw,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Fintype.card ι),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- Assemble scalar Brownian coordinates in any finite Euclidean space. -/
def brownianCoordinates (W : ι → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) :
    Ω → EuclideanSpace ℝ ι :=
  fun ω ↦ WithLp.toLp 2 (fun i ↦ W i t ω)

omit [Fintype ι] in
/-- Actual scalar Brownian laws give the vector's coordinate laws. -/
theorem brownianCoordinates_coordinateLaw (W : ι → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P) (t : ℝ≥0) (i : ι) :
    HasLaw (fun ω ↦ brownianCoordinates W t ω i) (gaussianReal 0 t) P :=
  (hW i).hasLaw_eval t

/-- A Brownian vector increment over an arbitrary starting time. -/
def brownianCoordinatesIncrement (W : ι → ℝ≥0 → Ω → ℝ) (a t : ℝ≥0) :
    Ω → EuclideanSpace ℝ ι :=
  fun ω ↦ brownianCoordinates W (a + t) ω - brownianCoordinates W a ω

omit [Fintype ι] in
/-- Every coordinate increment has Gaussian variance equal to elapsed time. -/
theorem brownianCoordinatesIncrement_coordinateLaw (W : ι → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P) (a t : ℝ≥0) (i : ι) :
    HasLaw (fun ω ↦ brownianCoordinatesIncrement W a t ω i) (gaussianReal 0 t) P := by
  change HasLaw (fun ω ↦ W i (a + t) ω - W i a ω) (gaussianReal 0 t) P
  convert (hW i).hasLaw_sub (a + t) a using 1
  congr 1
  apply NNReal.eq
  simp only [coe_nndist, Real.dist_eq]
  change (t : ℝ) = |((a : ℝ) + (t : ℝ)) - (a : ℝ)|
  rw [add_sub_cancel_left, abs_of_nonneg t.coe_nonneg]

/-- Brownian increments are square integrable in the full vector space. -/
theorem brownianCoordinatesIncrement_memLp (W : ι → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P) (a t : ℝ≥0) :
    MemLp (brownianCoordinatesIncrement W a t) 2 P :=
  gaussian_coordinates_memLp P _ t
    (brownianCoordinatesIncrement_coordinateLaw P W hW a t)

/-- The exact Langevin noise moment is derived from Brownian laws; no supplied
moment inequality or independence premise is required. -/
theorem brownianCoordinatesIncrement_scaled_l2_norm (W : ι → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P) (a t : ℝ≥0) :
    ‖Real.sqrt 2 • (brownianCoordinatesIncrement_memLp P W hW a t).toLp
      (brownianCoordinatesIncrement W a t)‖ =
      Real.sqrt (2 * (Fintype.card ι : ℝ)) * Real.sqrt (t : ℝ) :=
  gaussian_coordinates_scaled_l2_norm P _ t
    (brownianCoordinatesIncrement_coordinateLaw P W hW a t)

/-- Brownian coordinates as canonical square-integrable random variables. -/
def brownianCoordinatesLp (W : ι → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P) (t : ℝ≥0) :
    Lp (EuclideanSpace ℝ ι) 2 P :=
  (gaussian_coordinates_memLp P (brownianCoordinates W t) t
    (brownianCoordinates_coordinateLaw P W hW t)).toLp (brownianCoordinates W t)

/-- The canonical `L²` Brownian vector agrees with the coordinate process. -/
theorem brownianCoordinatesLp_coe (W : ι → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P) (t : ℝ≥0) :
    brownianCoordinatesLp P W hW t =ᵐ[P] brownianCoordinates W t :=
  (gaussian_coordinates_memLp P (brownianCoordinates W t) t
    (brownianCoordinates_coordinateLaw P W hW t)).coeFn_toLp

/-- Canonical `L²` Brownian differences have the actual Gaussian increment law
in every coordinate, including differences with reversed time order. -/
theorem brownianCoordinatesLp_sub_coordinateLaw (W : ι → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P) (t s : ℝ≥0) (i : ι) :
    HasLaw (fun ω ↦ (brownianCoordinatesLp P W hW t -
      brownianCoordinatesLp P W hW s) ω i)
      (gaussianReal 0 (nndist (t : ℝ) (s : ℝ))) P := by
  apply (hW i).hasLaw_sub t s |>.congr
  filter_upwards [Lp.coeFn_sub (brownianCoordinatesLp P W hW t)
      (brownianCoordinatesLp P W hW s),
    brownianCoordinatesLp_coe P W hW t, brownianCoordinatesLp_coe P W hW s]
    with ω hsub ht hs
  simp only [hsub, ht, hs, brownianCoordinates, Pi.sub_apply, PiLp.sub_apply]

/-- The exact `L²` norm of an arbitrary Brownian difference. -/
theorem brownianCoordinatesLp_norm_sub (W : ι → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P) (t s : ℝ≥0) :
    ‖brownianCoordinatesLp P W hW t - brownianCoordinatesLp P W hW s‖ =
      Real.sqrt ((Fintype.card ι : ℝ) * dist (t : ℝ) (s : ℝ)) := by
  simpa only [coe_nndist] using gaussian_coordinates_Lp_norm P
    (brownianCoordinatesLp P W hW t - brownianCoordinatesLp P W hW s)
    (nndist (t : ℝ) (s : ℝ)) (brownianCoordinatesLp_sub_coordinateLaw P W hW t s)

/-- Brownian coordinates are continuous as a map into `L²`. The proof derives
continuity from Gaussian increment moments and needs no path-continuity input. -/
theorem brownianCoordinatesLp_continuous (W : ι → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P) :
    Continuous (brownianCoordinatesLp P W hW) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp_rw [brownianCoordinatesLp_norm_sub P W hW]
  have hc : Continuous (fun t : ℝ≥0 ↦
      Real.sqrt ((Fintype.card ι : ℝ) * dist (t : ℝ) (s : ℝ))) := by fun_prop
  simpa only [dist_self, mul_zero, Real.sqrt_zero] using hc.tendsto s

/-- The exact `L²` Brownian increment bound in the additive Langevin equation. -/
theorem brownianCoordinatesLp_increment_scaled_norm (W : ι → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P) (a t : ℝ≥0) :
    ‖Real.sqrt 2 • (brownianCoordinatesLp P W hW (a + t) -
      brownianCoordinatesLp P W hW a)‖ =
      Real.sqrt (2 * (Fintype.card ι : ℝ)) * Real.sqrt (t : ℝ) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    brownianCoordinatesLp_norm_sub]
  simp only [NNReal.coe_add, Real.dist_eq, add_sub_cancel_left,
    abs_of_nonneg t.coe_nonneg]
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Fintype.card ι),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- The canonical Brownian vector starts at zero in `L²`. -/
@[simp] theorem brownianCoordinatesLp_zero (W : ι → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P) :
    brownianCoordinatesLp P W hW 0 = 0 := by
  apply norm_eq_zero.mp
  simpa only [brownianCoordinatesLp, NNReal.coe_zero, mul_zero, Real.sqrt_zero] using
    gaussian_coordinates_toLp_norm P (brownianCoordinates W 0) 0
      (brownianCoordinates_coordinateLaw P W hW 0)

/-- A real-time presentation, constant at zero on negative times, for use with
ordinary real interval integrals and deterministic Banach-space ODEs. -/
def brownianCoordinatesRealLp (W : ι → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P) (t : ℝ) :
    Lp (EuclideanSpace ℝ ι) 2 P :=
  brownianCoordinatesLp P W hW t.toNNReal

/-- The real-time Brownian presentation is continuous in `L²`. -/
theorem brownianCoordinatesRealLp_continuous (W : ι → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P) :
    Continuous (brownianCoordinatesRealLp P W hW) :=
  (brownianCoordinatesLp_continuous P W hW).comp continuous_real_toNNReal

@[simp] theorem brownianCoordinatesRealLp_zero (W : ι → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P) :
    brownianCoordinatesRealLp P W hW 0 = 0 := by
  simp only [brownianCoordinatesRealLp, Real.toNNReal_zero, brownianCoordinatesLp_zero]

/-- The real-time additive noise has the exact local moment required in the
Langevin error bound, for every nonnegative starting time and elapsed time. -/
theorem brownianCoordinatesRealLp_increment_scaled_norm (W : ι → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P) (a t : ℝ)
    (ha : 0 ≤ a) (ht : 0 ≤ t) :
    ‖Real.sqrt 2 • (brownianCoordinatesRealLp P W hW (a + t) -
      brownianCoordinatesRealLp P W hW a)‖ =
      Real.sqrt (2 * (Fintype.card ι : ℝ)) * Real.sqrt t := by
  simpa only [brownianCoordinatesRealLp, Real.toNNReal_add ha ht,
    Real.coe_toNNReal t ht] using
    brownianCoordinatesLp_increment_scaled_norm P W hW a.toNNReal t.toNNReal

end ULA
