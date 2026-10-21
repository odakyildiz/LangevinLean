import UnadjustedLangevin.Gibbs
import GradientDescent.Smooth
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

set_option linter.style.header false

/-! # Gibbs score bounds from first-order smoothness

Translation invariance of Lebesgue measure and the descent lemma bound the
moment generating function of every directional Gibbs score. No Hessian or
second derivative of the potential is used.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ULA

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

omit [MeasurableSpace H] [BorelSpace H] in
/-- The pointwise exponential-score inequality supplied by the descent lemma. -/
theorem gibbsWeight_mul_exp_score_le
    (U : H → ℝ) (L : ℝ≥0) (hdiff : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (x v : H) :
    gibbsWeight U x * ENNReal.ofReal (Real.exp (-inner ℝ (gradient U x) v)) ≤
      ENNReal.ofReal (Real.exp ((L : ℝ) / 2 * ‖v‖ ^ 2)) * gibbsWeight U (x + v) := by
  have hs := GradientDescent.smooth_upper_bound U L hdiff hLip x (x + v)
  simp only [add_sub_cancel_left] at hs
  unfold gibbsWeight
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),
    ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, ← Real.exp_add]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  linarith

/-- The directional score has the exact Gaussian MGF bound. Its partition
finiteness premise follows from strong convexity in `Gibbs.lean`. -/
theorem gibbs_score_lmgf_le
    (U : H → ℝ) (L : ℝ≥0) (hdiff : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (hZ : gibbsPartition U ≠ ⊤) (v : H) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-inner ℝ (gradient U x) v)) ∂gibbsMeasure U) ≤
      ENNReal.ofReal (Real.exp ((L : ℝ) / 2 * ‖v‖ ^ 2)) := by
  have hw : Measurable (gibbsWeight U) := by
    exact (Real.continuous_exp.comp hdiff.continuous.neg).measurable.ennreal_ofReal
  have hg : Measurable (fun x ↦ ENNReal.ofReal (Real.exp (-inner ℝ (gradient U x) v))) := by
    exact (Real.continuous_exp.comp
      ((hLip.continuous.inner continuous_const).neg)).measurable.ennreal_ofReal
  have htranslate : (∫⁻ x, gibbsWeight U (x + v) ∂volume) = gibbsPartition U := by
    exact lintegral_add_right_eq_self (gibbsWeight U) v
  rw [gibbsMeasure, lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul volume hw hg]
  change (gibbsPartition U)⁻¹ *
    (∫⁻ x, gibbsWeight U x * ENNReal.ofReal (Real.exp (-inner ℝ (gradient U x) v)) ∂volume) ≤ _
  calc
    _ ≤ (gibbsPartition U)⁻¹ *
        (∫⁻ x, ENNReal.ofReal (Real.exp ((L : ℝ) / 2 * ‖v‖ ^ 2)) *
          gibbsWeight U (x + v) ∂volume) := by
      exact mul_le_mul_right
        (lintegral_mono (fun x ↦ gibbsWeight_mul_exp_score_le U L hdiff hLip x v)) _
    _ = _ := by
      rw [lintegral_const_mul _ (by fun_prop), htranslate]
      rw [mul_left_comm, ENNReal.inv_mul_cancel (ne_of_gt (gibbsPartition_pos U hdiff)) hZ,
        mul_one]

end ULA

namespace ULA
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

/-- Every linear functional of the Gibbs score is centered sub-Gaussian with
variance proxy `L * ‖v‖²`. This uses only first-order smoothness and finite
normalization; it does not assume any score moment. -/
theorem gibbs_score_subgaussian
    (U : H → ℝ) (L : ℝ≥0) (hdiff : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (hZ : gibbsPartition U ≠ ⊤) (v : H) :
    HasSubgaussianMGF (fun x ↦ inner ℝ (gradient U x) v) (L * ‖v‖₊ ^ 2)
      (gibbsMeasure U) := by
  have he (t : ℝ) :
      (∫⁻ x, ENNReal.ofReal (Real.exp (t * inner ℝ (gradient U x) v))
          ∂gibbsMeasure U) ≤
        ENNReal.ofReal (Real.exp (((L * ‖v‖₊ ^ 2 : ℝ≥0) : ℝ) * t ^ 2 / 2)) := by
    have h := gibbs_score_lmgf_le U L hdiff hLip hZ ((-t) • v)
    simp only [inner_smul_right, neg_mul, neg_neg, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, neg_sq, NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm] at h ⊢
    convert h using 1
    congr 2
    ring
  have hi (t : ℝ) : Integrable (fun x ↦ Real.exp (t * inner ℝ (gradient U x) v))
      (gibbsMeasure U) := by
    refine ⟨(Real.continuous_exp.comp
      (continuous_const.mul (hLip.continuous.inner continuous_const))).aestronglyMeasurable, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ Real.exp_nonneg _)).mpr
    exact lt_of_le_of_lt (he t) ENNReal.ofReal_lt_top
  refine ⟨hi, ?_⟩
  intro t
  change (∫ x, Real.exp (t * inner ℝ (gradient U x) v) ∂gibbsMeasure U) ≤ _
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ Real.exp_nonneg _)
    (hi t).aestronglyMeasurable]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (he t)
  simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _)] using h

end ULA

namespace ULA

/-- The symmetric exponential remainder dominates the exact quadratic term. -/
lemma sq_le_exp_add_exp_neg_sub_two (a : ℝ) :
    a ^ 2 ≤ Real.exp a + Real.exp (-a) - 2 := by
  have hp (n : ℕ) : 0 ≤ a ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    simpa only [pow_mul] using pow_nonneg (sq_nonneg a) n
  have h := sum_le_hasSum (Finset.range 2) (fun n _ ↦ hp n) (Real.hasSum_cosh a)
  norm_num [Finset.sum_range_succ, Real.cosh_eq] at h
  linarith

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The Gaussian MGF variance proxy bounds the uncentered second moment.
The proof integrates the symmetric exponential remainder and lets its scalar
step tend to zero. In particular, no mean-zero hypothesis is added. -/
theorem integral_sq_le_of_subgaussian (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (c : ℝ≥0) (hX : HasSubgaussianMGF X c μ) :
    (∫ ω, X ω ^ 2 ∂μ) ≤ (c : ℝ) := by
  have hsq : Integrable (fun ω ↦ X ω ^ 2) μ :=
    (memLp_two_iff_integrable_sq hX.aestronglyMeasurable).mp (hX.memLp 2)
  have hbound (s : ℝ) (hs : 0 < s) :
      (∫ ω, X ω ^ 2 ∂μ) ≤ (Real.exp ((c : ℝ) * s) - 1) / s := by
    let t := Real.sqrt (2 * s)
    have ht : t ^ 2 = 2 * s := Real.sq_sqrt (by positivity)
    have hp (ω : Ω) : (2 * s) * X ω ^ 2 ≤
        Real.exp (t * X ω) + Real.exp ((-t) * X ω) - 2 := by
      have h := sq_le_exp_add_exp_neg_sub_two (t * X ω)
      simpa only [mul_pow, ht, neg_mul] using h
    have hi := integral_mono (hsq.const_mul (2 * s))
      (((hX.integrable_exp_mul t).add (hX.integrable_exp_mul (-t))).sub (integrable_const 2)) hp
    simp only [Pi.add_apply, Pi.sub_apply] at hi
    have hsum : Integrable (fun ω ↦ Real.exp (t * X ω) + Real.exp ((-t) * X ω)) μ := by
      simpa only [Pi.add_def] using (hX.integrable_exp_mul t).add (hX.integrable_exp_mul (-t))
    rw [integral_const_mul, integral_sub hsum (integrable_const 2),
      integral_add (hX.integrable_exp_mul t) (hX.integrable_exp_mul (-t)),
      integral_const] at hi
    simp only [probReal_univ, one_smul] at hi
    have hplus := hX.mgf_le t
    have hminus := hX.mgf_le (-t)
    change (∫ ω, Real.exp (t * X ω) ∂μ) ≤ _ at hplus
    change (∫ ω, Real.exp ((-t) * X ω) ∂μ) ≤ _ at hminus
    rw [ht, show (c : ℝ) * (2 * s) / 2 = (c : ℝ) * s by ring] at hplus
    rw [neg_sq, ht, show (c : ℝ) * (2 * s) / 2 = (c : ℝ) * s by ring] at hminus
    apply (le_div_iff₀ hs).mpr
    linarith
  have hd : HasDerivAt (fun s : ℝ ↦ Real.exp ((c : ℝ) * s)) (c : ℝ) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).const_mul (c : ℝ)).exp)
  have hlim := hd.tendsto_slope_zero_right
  simp only [zero_add, mul_zero, Real.exp_zero, smul_eq_mul, ← div_eq_inv_mul] at hlim
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact hbound s hs

end ULA

namespace ULA
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

/-- The sharp Gibbs score moment bound in any finite-dimensional presentation:
`Eπ ‖∇U‖² ≤ L * dim(H)`. It follows from first-order smoothness and a finite
partition function, using translation invariance rather than integration by
parts or a Hessian. -/
theorem integral_norm_sq_gradient_gibbs_le
    (U : H → ℝ) (L : ℝ≥0) (hdiff : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (hZ : gibbsPartition U ≠ ⊤) :
    (∫ x, ‖gradient U x‖ ^ 2 ∂gibbsMeasure U) ≤
      (L : ℝ) * (Module.finrank ℝ H : ℝ) := by
  have : IsProbabilityMeasure (gibbsMeasure U) := by
    constructor
    rw [gibbsMeasure, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
      setLIntegral_univ]
    exact ENNReal.inv_mul_cancel (ne_of_gt (gibbsPartition_pos U hdiff)) hZ
  let e := stdOrthonormalBasis ℝ H
  have hi (i : Fin (Module.finrank ℝ H)) :
      Integrable (fun x ↦ inner ℝ (gradient U x) (e i) ^ 2) (gibbsMeasure U) := by
    have hs := gibbs_score_subgaussian U L hdiff hLip hZ (e i)
    exact (memLp_two_iff_integrable_sq hs.aestronglyMeasurable).mp (hs.memLp 2)
  have hb (i : Fin (Module.finrank ℝ H)) :
      (∫ x, inner ℝ (gradient U x) (e i) ^ 2 ∂gibbsMeasure U) ≤ (L : ℝ) := by
    have h := integral_sq_le_of_subgaussian (gibbsMeasure U)
      (fun x ↦ inner ℝ (gradient U x) (e i)) (L * ‖e i‖₊ ^ 2)
      (gibbs_score_subgaussian U L hdiff hLip hZ (e i))
    simpa only [e.orthonormal.nnnorm_eq_one, one_pow, mul_one] using h
  calc
    _ = ∫ x, ∑ i : Fin (Module.finrank ℝ H), inner ℝ (gradient U x) (e i) ^ 2
        ∂gibbsMeasure U := by
      apply integral_congr_ae
      exact ae_of_all _ fun x ↦ (e.sum_sq_inner_left (gradient U x)).symm
    _ = ∑ i : Fin (Module.finrank ℝ H),
        ∫ x, inner ℝ (gradient U x) (e i) ^ 2 ∂gibbsMeasure U :=
      integral_finsetSum Finset.univ (fun i _ ↦ hi i)
    _ ≤ ∑ _ : Fin (Module.finrank ℝ H), (L : ℝ) :=
      Finset.sum_le_sum (fun i _ ↦ hb i)
    _ = _ := by simp [mul_comm]

/-- Square integrability of the actual Gibbs score, derived rather than assumed. -/
theorem memLp_gradient_gibbsMeasure
    (U : H → ℝ) (L : ℝ≥0) (hdiff : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (hZ : gibbsPartition U ≠ ⊤) :
    MemLp (gradient U) 2 (gibbsMeasure U) := by
  let e := stdOrthonormalBasis ℝ H
  have hi (i : Fin (Module.finrank ℝ H)) :
      Integrable (fun x ↦ inner ℝ (gradient U x) (e i) ^ 2) (gibbsMeasure U) := by
    have hs := gibbs_score_subgaussian U L hdiff hLip hZ (e i)
    exact (memLp_two_iff_integrable_sq hs.aestronglyMeasurable).mp (hs.memLp 2)
  apply (memLp_two_iff_integrable_sq_norm hLip.continuous.aestronglyMeasurable).mpr
  have hs := integrable_finsetSum Finset.univ (fun i _ ↦ hi i)
  convert hs using 1
  ext x
  exact (e.sum_sq_inner_left (gradient U x)).symm


/-- The sharp Gibbs score bound from precisely the strong-convexity and
first-order smoothness assumptions on the potential; normalization finiteness
is proved internally. -/
theorem integral_norm_sq_gradient_gibbs_le_of_strongConvex
    (U : H → ℝ) (m : ℝ) (L : ℝ≥0) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (hLip : LipschitzWith L (gradient U)) :
    (∫ x, ‖gradient U x‖ ^ 2 ∂gibbsMeasure U) ≤
      (L : ℝ) * (Module.finrank ℝ H : ℝ) :=
  integral_norm_sq_gradient_gibbs_le U L hdiff hLip
    (gibbsPartition_ne_top U m hm hdiff hsc)

end ULA
