import AverageLMC.PathwiseEnergy
import UnadjustedLangevin.LpDrift
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Analysis.InnerProductSpace.Calculus
import UnadjustedLangevin.GaussianMoments
import Mathlib.Probability.Distributions.Gaussian.Multivariate

set_option linter.style.header false

/-!
# The independent-coordinate smoothing lemma

The perturbation coordinates are arbitrary independent centered random variables
with unit second moment. Each coordinate is inserted once, and independence
eliminates its linear Taylor term. All potential and product integrability is
derived from the coordinate second moments and the gradient Lipschitz condition.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

namespace AverageLMC

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem memLp_gradient_comp {p : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : State p → ℝ) (M : ℝ≥0) (hLip : LipschitzWith M (gradient f))
    (X : Ω → State p) (hX : MemLp X 2 μ) :
    MemLp (fun ω ↦ gradient f (X ω)) 2 μ := by
  have h := ULA.lpDrift_memLp μ (gradient f) hLip (hX.toLp X)
  apply h.ae_eq
  filter_upwards [hX.coeFn_toLp] with ω hω
  rw [hω]

private def coordinatePartial {p : ℕ} (ξ : Fin p → Ω → ℝ)
    (s : Finset (Fin p)) (ω : Ω) : State p :=
  ∑ j ∈ s, ξ j ω • coordinateVector j

private theorem memLp_coordinatePartial {p : ℕ} (μ : Measure Ω)
    (ξ : Fin p → Ω → ℝ) (hξ : ∀ j, MemLp (ξ j) 2 μ) (s : Finset (Fin p)) :
    MemLp (coordinatePartial ξ s) 2 μ := by
  apply memLp_finsetSum s
  intro j hj
  exact ((ContinuousLinearMap.id ℝ ℝ).smulRight (coordinateVector j)).comp_memLp' (hξ j)

/-- The first conclusion of the smoothing lemma for every finite set of
coordinates. The parameter `c` can be any real scalar. -/
theorem integral_coordinatePartial_le {p : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : State p → ℝ) (M : ℝ≥0) (hf : Differentiable ℝ f)
    (hLip : LipschitzWith M (gradient f))
    (ξ : Fin p → Ω → ℝ) (hξm : ∀ j, Measurable (ξ j))
    (hξ : ∀ j, MemLp (ξ j) 2 μ) (hind : iIndepFun ξ μ)
    (hmean : ∀ j, ∫ ω, ξ j ω ∂μ = 0)
    (hvar : ∀ j, ∫ ω, ξ j ω ^ 2 ∂μ = 1)
    (x : State p) (c : ℝ) (s : Finset (Fin p)) :
    (∫ ω, f (x + c • coordinatePartial ξ s ω) ∂μ) ≤
      f x + c ^ 2 / 2 * ∑ j ∈ s, coordinateSmoothness f j := by
  have hX (t : Finset (Fin p)) :
      MemLp (fun ω ↦ x + c • coordinatePartial ξ t ω) 2 μ :=
    (memLp_const x).add ((memLp_coordinatePartial μ ξ hξ t).const_smul c)
  have hF (t : Finset (Fin p)) :=
    integrable_smooth_comp μ f M hf hLip _ (hX t)
  have hvind : iIndepFun (fun j ω ↦ ξ j ω • coordinateVector j) μ :=
    hind.comp (fun j a ↦ a • coordinateVector j) (by fun_prop)
  induction s using Finset.induction_on with
  | empty => simp [coordinatePartial]
  | @insert i t hit ih =>
    let G : Ω → ℝ := fun ω ↦ (gradient f (x + c • coordinatePartial ξ t ω)) i
    have hG : MemLp G 2 μ :=
      (memLp_gradient_comp μ f M hLip _ (hX t)).eval_piLp i
    have hGc : Continuous (fun z : State p ↦ (gradient f (x + c • z)) i) :=
      (EuclideanSpace.proj i).continuous.comp
        (hLip.continuous.comp (continuous_const.add (continuous_id.const_smul c)))
    have hIG : IndepFun (ξ i) G μ := by
      have ht := hvind.indepFun_finsetSum_of_notMem
        (fun j ↦ (hξm j).smul_const (coordinateVector j)) hit
      have h := ht.symm.comp (EuclideanSpace.proj i).measurable hGc.measurable
      simpa [Function.comp_def, coordinatePartial, G, coordinateVector] using h
    have hprod : Integrable (fun ω ↦ ξ i ω * G ω) μ := (hξ i).integrable_mul hG
    have hzero : (∫ ω, ξ i ω * G ω ∂μ) = 0 := by
      rw [hIG.integral_fun_mul_eq_mul_integral (hξ i).aestronglyMeasurable
        hG.aestronglyMeasurable, hmean i, zero_mul]
    have hsq : Integrable (fun ω ↦ ξ i ω ^ 2) μ :=
      (memLp_two_iff_integrable_sq (hξ i).aestronglyMeasurable).mp (hξ i)
    have hpoint (ω : Ω) : f (x + c • coordinatePartial ξ (insert i t) ω) ≤
        f (x + c • coordinatePartial ξ t ω) + c * (ξ i ω * G ω) +
          (coordinateSmoothness f i / 2 * c ^ 2) * ξ i ω ^ 2 := by
      have hu := coordinate_upper_bound f M hf hLip i
        (x + c • coordinatePartial ξ t ω) (c * ξ i ω)
      have heq : x + c • coordinatePartial ξ (insert i t) ω =
          (x + c • coordinatePartial ξ t ω) + (c * ξ i ω) • coordinateVector i := by
        simp [coordinatePartial, Finset.sum_insert hit, smul_add, mul_smul]
        module
      rw [heq]
      dsimp [G]
      nlinarith
    have hbound := integral_mono (hF (insert i t))
      (((hF t).add (hprod.const_mul c)).add
        (hsq.const_mul (coordinateSmoothness f i / 2 * c ^ 2))) hpoint
    change (∫ ω, f (x + c • coordinatePartial ξ (insert i t) ω) ∂μ) ≤
      ∫ ω, f (x + c • coordinatePartial ξ t ω) + c * (ξ i ω * G ω) +
        (coordinateSmoothness f i / 2 * c ^ 2) * ξ i ω ^ 2 ∂μ at hbound
    have hadd : (∫ ω, f (x + c • coordinatePartial ξ t ω) + c * (ξ i ω * G ω) +
        (coordinateSmoothness f i / 2 * c ^ 2) * ξ i ω ^ 2 ∂μ) =
        (∫ ω, f (x + c • coordinatePartial ξ t ω) + c * (ξ i ω * G ω) ∂μ) +
        ∫ ω, (coordinateSmoothness f i / 2 * c ^ 2) * ξ i ω ^ 2 ∂μ :=
      integral_add ((hF t).add (hprod.const_mul c))
        (hsq.const_mul (coordinateSmoothness f i / 2 * c ^ 2))
    have hadd' : (∫ ω, f (x + c • coordinatePartial ξ t ω) + c * (ξ i ω * G ω) ∂μ) =
        (∫ ω, f (x + c • coordinatePartial ξ t ω) ∂μ) +
        ∫ ω, c * (ξ i ω * G ω) ∂μ := integral_add (hF t) (hprod.const_mul c)
    rw [hadd, hadd', integral_const_mul, integral_const_mul, hzero, hvar i,
      mul_zero, add_zero, mul_one] at hbound
    simp only [Finset.sum_insert hit]
    nlinarith

/-- Smoothing by independent centered unit-variance coordinates, with exactly
the average of the supremum coordinate Taylor constants in the paper. -/
theorem integral_coordinate_smoothing {p : ℕ} (hp : 0 < p)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : State p → ℝ) (M : ℝ≥0) (hf : Differentiable ℝ f)
    (hLip : LipschitzWith M (gradient f))
    (ξ : Fin p → Ω → ℝ) (hξm : ∀ j, Measurable (ξ j))
    (hξ : ∀ j, MemLp (ξ j) 2 μ) (hind : iIndepFun ξ μ)
    (hmean : ∀ j, ∫ ω, ξ j ω ∂μ = 0)
    (hvar : ∀ j, ∫ ω, ξ j ω ^ 2 ∂μ = 1)
    (x : State p) (s : ℝ) (hs : 0 ≤ s) :
    (∫ ω, f (x + Real.sqrt (2 * s) • WithLp.toLp 2 (fun j ↦ ξ j ω)) - f x ∂μ) ≤
      averageSmoothness f * (p : ℝ) * s := by
  have hi := integral_coordinatePartial_le μ f M hf hLip ξ hξm hξ hind hmean hvar
    x (Real.sqrt (2 * s)) Finset.univ
  have heq (ω : Ω) : coordinatePartial ξ Finset.univ ω =
      WithLp.toLp 2 (fun j ↦ ξ j ω) := by
    ext j
    simp [coordinatePartial, coordinateVector, Pi.single_apply]
  have hX := (memLp_const x).add
    ((memLp_coordinatePartial μ ξ hξ Finset.univ).const_smul (Real.sqrt (2 * s)))
  have hF := integrable_smooth_comp μ f M hf hLip _ hX
  change Integrable (fun ω ↦ f (x + Real.sqrt (2 * s) •
    coordinatePartial ξ Finset.univ ω)) μ at hF
  simp_rw [heq] at hi hF
  rw [integral_sub hF (integrable_const _), integral_const, probReal_univ, one_smul]
  rw [Real.sq_sqrt (by positivity)] at hi
  have hsum : ∑ j : Fin p, coordinateSmoothness f j =
      averageSmoothness f * (p : ℝ) := by
    unfold averageSmoothness
    field_simp
  rw [hsum] at hi
  nlinarith

/-- The standard-Gaussian specialization used by the LMC transition. -/
theorem integral_stdGaussian_smoothing {p : ℕ} (hp : 0 < p)
    (f : State p → ℝ) (M : ℝ≥0) (hf : Differentiable ℝ f)
    (hLip : LipschitzWith M (gradient f)) (x : State p) (s : ℝ) (hs : 0 ≤ s) :
    (∫ z, f (x + Real.sqrt (2 * s) • z) - f x ∂stdGaussian (State p)) ≤
      averageSmoothness f * (p : ℝ) * s := by
  let μ : Measure (Fin p → ℝ) := Measure.pi (fun _ ↦ gaussianReal 0 1)
  have hl (j : Fin p) : HasLaw (fun z : Fin p → ℝ ↦ z j) (gaussianReal 0 1) μ :=
    ⟨(measurable_pi_apply j).aemeasurable, (measurePreserving_eval _ j).map_eq⟩
  have hξ (j : Fin p) : MemLp (fun z : Fin p → ℝ ↦ z j) 2 μ :=
    (hl j).memLp (memLp_id_gaussianReal (2 : ℝ≥0))
  have hmean (j : Fin p) : (∫ z, z j ∂μ) = 0 :=
    ((hl j).integral_comp (f := id) (by fun_prop)).trans integral_id_gaussianReal
  have hvar (j : Fin p) : (∫ z, z j ^ 2 ∂μ) = 1 := by
    exact ((hl j).integral_comp (f := fun a : ℝ ↦ a ^ 2) (by fun_prop)).trans
      (ULA.centered_gaussian_second_moment 1)
  have h := integral_coordinate_smoothing hp μ f M hf hLip
    (fun j z ↦ z j) (fun j ↦ measurable_pi_apply j) hξ
    (iIndepFun_pi (fun _ ↦ measurable_id.aemeasurable)) hmean hvar x s hs
  rw [← map_pi_eq_stdGaussian]
  have hfcont := hf.continuous
  rw [integral_map (by fun_prop) (by fun_prop)]
  exact h

end AverageLMC
