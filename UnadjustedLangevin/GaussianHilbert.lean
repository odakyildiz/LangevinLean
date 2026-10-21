import UnadjustedLangevin.GaussianMoments
import UnadjustedLangevin.LpCharacteristic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

set_option linter.style.header false

/-! # An isonormal Gaussian source from an independent Gaussian product

The source measure is constructed explicitly as an infinite product of standard
real Gaussians. Its coordinate random variables form an orthonormal family in
L². Hilbert-space expansion then constructs random linear functionals, without
assuming that a Brownian probability space already exists.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical lp

namespace ULA
namespace GaussianHilbert

variable {ι : Type*}

def source (ι : Type*) : Measure (ι → ℝ) :=
  Measure.infinitePi (fun _ : ι ↦ gaussianReal 0 1)

instance source_isProbabilityMeasure (ι : Type*) : IsProbabilityMeasure (source ι) := by
  unfold source
  infer_instance

theorem coordinate_hasLaw (i : ι) :
    HasLaw (fun ω : ι → ℝ ↦ ω i) (gaussianReal 0 1) (source ι) :=
  ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩

def coordinateLp (i : ι) : Lp ℝ 2 (source ι) :=
  ((coordinate_hasLaw i).memLp (memLp_id_gaussianReal (2 : ℝ≥0))).toLp (fun ω ↦ ω i)

theorem coordinateLp_coe (i : ι) :
    coordinateLp i =ᵐ[source ι] fun ω : ι → ℝ ↦ ω i :=
  ((coordinate_hasLaw i).memLp (memLp_id_gaussianReal (2 : ℝ≥0))).coeFn_toLp

theorem coordinates_independent :
    iIndepFun (fun i (ω : ι → ℝ) ↦ ω i) (source ι) :=
  iIndepFun_infinitePi (fun _ ↦ measurable_id)

theorem coordinate_mean (i : ι) : (∫ ω, ω i ∂source ι) = 0 := by
  exact ((coordinate_hasLaw i).integral_comp (f := id) measurable_id.aestronglyMeasurable).trans
    integral_id_gaussianReal

theorem coordinateLp_inner (i j : ι) :
    inner ℝ (coordinateLp i) (coordinateLp j) = if i = j then 1 else 0 := by
  classical
  rw [L2.inner_def]
  have heq : (fun ω ↦ inner ℝ (coordinateLp i ω) (coordinateLp j ω))
      =ᵐ[source ι] fun ω ↦ ω i * ω j := by
    filter_upwards [coordinateLp_coe i, coordinateLp_coe j] with ω hi hj
    simp [hi, hj, mul_comm]
  rw [integral_congr_ae heq]
  split_ifs with hij
  · subst j
    simpa only [← sq, Function.comp_apply, NNReal.coe_one] using
      ((coordinate_hasLaw i).integral_comp (f := fun x : ℝ ↦ x ^ 2) (by fun_prop)).trans
        (centered_gaussian_second_moment 1)
  · exact ((coordinates_independent.indepFun hij).integral_mul_eq_mul_integral
      (measurable_pi_apply i).aestronglyMeasurable
      (measurable_pi_apply j).aestronglyMeasurable).trans (by
        rw [coordinate_mean, coordinate_mean, zero_mul])

theorem coordinates_orthonormal : Orthonormal ℝ (@coordinateLp ι) := by
  classical
  rw [orthonormal_iff_ite]
  exact coordinateLp_inner

/-- Independent Gaussian coordinates synthesize every square-summable
coefficient family, by the Hilbert-space orthogonal-series theorem. -/
def synthesis : ℓ²(ι, ℝ) →ₗᵢ[ℝ] Lp ℝ 2 (source ι) :=
  coordinates_orthonormal.orthogonalFamily.linearIsometry

theorem synthesis_hasSum (a : ℓ²(ι, ℝ)) :
    HasSum (fun i ↦ a i • coordinateLp i) (synthesis a) := by
  exact coordinates_orthonormal.orthogonalFamily.hasSum_linearIsometry a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The isonormal map constructed from a Hilbert basis and the explicit
Gaussian product source. It preserves all inner products. -/
def isonormal (b : HilbertBasis ι ℝ H) : H →ₗᵢ[ℝ] Lp ℝ 2 (source ι) :=
  synthesis.comp b.repr.toLinearIsometry

theorem isonormal_hasSum (b : HilbertBasis ι ℝ H) (x : H) :
    HasSum (fun i ↦ b.repr x i • coordinateLp i) (isonormal b x) :=
  synthesis_hasSum (b.repr x)

theorem integral_eq_inner_one (X : Lp ℝ 2 (source ι)) :
    (∫ ω, X ω ∂source ι) = inner ℝ (Lp.const 2 (source ι) 1) X := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const (p := 2) (source ι) (1 : ℝ)] with ω hω
  simp [hω]

theorem coordinateLp_mean (i : ι) : (∫ ω, coordinateLp i ω ∂source ι) = 0 := by
  rw [integral_congr_ae (coordinateLp_coe i)]
  exact coordinate_mean i

theorem synthesis_mean (a : ℓ²(ι, ℝ)) :
    (∫ ω, synthesis a ω ∂source ι) = 0 := by
  rw [integral_eq_inner_one]
  have hcont : Continuous (fun X : Lp ℝ 2 (source ι) ↦
      inner ℝ (Lp.const 2 (source ι) 1) X) := continuous_const.inner continuous_id
  have hlim := hcont.continuousAt.tendsto.comp (synthesis_hasSum a)
  have hzero : ∀ s : Finset ι,
      inner ℝ (Lp.const 2 (source ι) 1) (∑ i ∈ s, a i • coordinateLp i) = 0 := by
    intro s
    simp only [inner_sum, real_inner_smul_right, ← integral_eq_inner_one,
      coordinateLp_mean, mul_zero, Finset.sum_const_zero]
  have hz : Tendsto (fun s : Finset ι ↦
      inner ℝ (Lp.const 2 (source ι) 1) (∑ i ∈ s, a i • coordinateLp i))
      atTop (𝓝 0) := by simp only [hzero]; exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim hz

theorem isonormal_mean (b : HilbertBasis ι ℝ H) (x : H) :
    (∫ ω, isonormal b x ω ∂source ι) = 0 :=
  synthesis_mean (b.repr x)

theorem variance_eq_norm_sq (X : Lp ℝ 2 (source ι))
    (hmean : (∫ ω, X ω ∂source ι) = 0) :
    Var[X; source ι] = ‖X‖ ^ 2 := by
  rw [variance_eq_integral (Lp.aestronglyMeasurable X).aemeasurable, hmean]
  simp only [sub_zero]
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards with ω
  simp [pow_two]

theorem partial_sum_coe (a : ι → ℝ) (s : Finset ι) :
    (∑ i ∈ s, a i • coordinateLp i) =ᵐ[source ι]
      fun ω : ι → ℝ ↦ ∑ i ∈ s, a i * ω i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      filter_upwards [Lp.coeFn_zero ℝ 2 (source ι)] with ω hω
      simpa only [Finset.sum_empty, Pi.zero_apply] using hω
  | @insert i s his ih =>
      rw [Finset.sum_insert his]
      filter_upwards [Lp.coeFn_add (a i • coordinateLp i)
        (∑ j ∈ s, a j • coordinateLp j), Lp.coeFn_smul (a i) (coordinateLp i),
        coordinateLp_coe i, ih] with ω ha hs hi hsum
      simp only [ha, Pi.add_apply, hs, Pi.smul_apply, hi, hsum,
        Finset.sum_insert his, smul_eq_mul]

theorem partial_sum_hasGaussianLaw (a : ι → ℝ) (s : Finset ι) :
    HasGaussianLaw (∑ i ∈ s, a i • coordinateLp i : Lp ℝ 2 (source ι)) (source ι) := by
  classical
  have hi : iIndepFun (fun i : s ↦ fun ω : ι → ℝ ↦ a i * ω i) (source ι) :=
    (coordinates_independent.precomp Subtype.val_injective).comp
      (fun (i : s) (x : ℝ) ↦ a i * x) (by intro i; fun_prop)
  have hg : ∀ i : s, HasGaussianLaw (fun ω : ι → ℝ ↦ a i * ω i) (source ι) := by
    intro i
    exact ((coordinate_hasLaw (i : ι)).hasGaussianLaw).fun_smul (a i)
  have hsum := hi.hasGaussianLaw_fun_sum hg
  have heq : (fun ω : ι → ℝ ↦ ∑ i : s, a i * ω i) =
      (fun ω : ι → ℝ ↦ ∑ i ∈ s, a i * ω i) := by
    funext ω
    exact Finset.sum_coe_sort s (fun i : ι ↦ a i * ω i)
  rw [heq] at hsum
  exact hsum.congr (partial_sum_coe a s).symm

theorem partial_sum_mean (a : ι → ℝ) (s : Finset ι) :
    (∫ ω, (∑ i ∈ s, a i • coordinateLp i : Lp ℝ 2 (source ι)) ω ∂source ι) = 0 := by
  rw [integral_eq_inner_one]
  simp only [inner_sum, real_inner_smul_right, ← integral_eq_inner_one,
    coordinateLp_mean, mul_zero, Finset.sum_const_zero]

theorem partial_sum_hasLaw (a : ι → ℝ) (s : Finset ι) :
    HasLaw (∑ i ∈ s, a i • coordinateLp i : Lp ℝ 2 (source ι))
      (gaussianReal 0 (‖∑ i ∈ s, a i • coordinateLp i‖ ^ 2).toNNReal) (source ι) := by
  have hg := partial_sum_hasGaussianLaw a s
  refine ⟨hg.aemeasurable, ?_⟩
  rw [hg.map_eq_gaussianReal, partial_sum_mean,
    variance_eq_norm_sq _ (partial_sum_mean a s)]

/-- The orthogonal-series limit is genuinely Gaussian, with the variance
equal to the square of its Hilbert norm. This is proved by characteristic
function continuity, rather than postulated as a Gaussian-process input. -/
theorem synthesis_hasLaw (a : ℓ²(ι, ℝ)) :
    HasLaw (synthesis a) (gaussianReal 0 (‖a‖ ^ 2).toNNReal) (source ι) := by
  have h := hasLaw_gaussianReal_of_tendsto_Lp (source ι)
    (fun s : Finset ι ↦ ∑ i ∈ s, a i • coordinateLp i) (synthesis a)
    (synthesis_hasSum a) (partial_sum_hasLaw a)
  simpa only [LinearIsometry.norm_map] using h

theorem isonormal_hasLaw (b : HilbertBasis ι ℝ H) (x : H) :
    HasLaw (isonormal b x) (gaussianReal 0 (‖x‖ ^ 2).toNNReal) (source ι) := by
  change HasLaw (synthesis (b.repr x)) (gaussianReal 0 (‖x‖ ^ 2).toNNReal) (source ι)
  simpa only [LinearIsometryEquiv.norm_map] using synthesis_hasLaw (b.repr x)

theorem isonormal_hasGaussianLaw (b : HilbertBasis ι ℝ H) (x : H) :
    HasGaussianLaw (isonormal b x) (source ι) :=
  (isonormal_hasLaw b x).hasGaussianLaw

theorem isonormal_covariance (b : HilbertBasis ι ℝ H) (x y : H) :
    cov[isonormal b x, isonormal b y; source ι] = inner ℝ x y := by
  unfold covariance
  rw [isonormal_mean, isonormal_mean]
  simp only [sub_zero]
  rw [← (isonormal b).inner_map_map]
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards with ω
  simp [mul_comm]

end GaussianHilbert
end ULA
