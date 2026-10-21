import UnadjustedLangevin.MALACoupling
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space

set_option linter.style.header false

/-!
# Exact Gaussian displacement moments for frozen-drift ULA

The joint law is the actual independent product `μ.prod (stdGaussian E)`.
Only square integrability of the current gradient is needed for the exact
displacement moment; no second moment of the state itself is needed.

Reference: Vempala–Wibisono (2019), *Rapid Convergence of the Unadjusted
Langevin Algorithm: Isoperimetry Suffices*.
https://proceedings.neurips.cc/paper_files/paper/2019/file/65a99bb7a3115fdede20da98b08a370f-Paper.pdf
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ULA.LSI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The exact standard Gaussian second moment in an arbitrary finite-dimensional
real Hilbert space, including dimension zero. -/
theorem integral_norm_sq_stdGaussian :
    (∫ z : E, ‖z‖ ^ 2 ∂stdGaussian E) = (Module.finrank ℝ E : ℝ) := by
  let b := stdOrthonormalBasis ℝ E
  have hz : MemLp (fun z : E ↦ z) 2 (stdGaussian E) :=
    IsGaussian.memLp_id (stdGaussian E) 2 (by norm_num)
  have hcoord (i : Fin (Module.finrank ℝ E)) :
      Integrable (fun z : E ↦ (inner ℝ (b i) z) ^ 2) (stdGaussian E) :=
    (hz.const_inner (b i)).integrable_sq
  have hmom (i : Fin (Module.finrank ℝ E)) :
      (∫ z : E, (inner ℝ (b i) z) ^ 2 ∂stdGaussian E) = 1 := by
    have hv := variance_dual_stdGaussian (innerSL ℝ (b i))
    rw [variance_eq_integral (by fun_prop), integral_strongDual_stdGaussian] at hv
    simpa only [innerSL_apply_apply, sub_zero, innerSL_apply_norm,
      b.orthonormal.1 i, one_pow] using hv
  simp_rw [← b.sum_sq_inner_right]
  rw [integral_finsetSum _ (fun i _ ↦ hcoord i)]
  simp only [hmom, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]

/-- Exact second moment of an independent centered Gaussian affine perturbation. -/
theorem integral_norm_sq_affine_stdGaussian
    (μ : Measure E) [IsProbabilityMeasure μ] (g : E → E)
    (hg : MemLp g 2 μ) (a b : ℝ) :
    (∫ p : E × E, ‖a • g p.1 + b • p.2‖ ^ 2 ∂μ.prod (stdGaussian E)) =
      a ^ 2 * (∫ x, ‖g x‖ ^ 2 ∂μ) + b ^ 2 * (Module.finrank ℝ E : ℝ) := by
  have hz : MemLp (fun z : E ↦ z) 2 (stdGaussian E) :=
    IsGaussian.memLp_id (stdGaussian E) 2 (by norm_num)
  have hg1 : Integrable g μ := hg.integrable (by norm_num)
  have hz1 : Integrable (fun z : E ↦ z) (stdGaussian E) :=
    IsGaussian.integrable_id
  have hgsq : Integrable (fun p : E × E ↦ ‖g p.1‖ ^ 2)
      (μ.prod (stdGaussian E)) :=
    (hg.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).comp_fst _
  have hzsq : Integrable (fun p : E × E ↦ ‖p.2‖ ^ 2)
      (μ.prod (stdGaussian E)) :=
    (hz.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).comp_snd _
  have hcross : Integrable (fun p : E × E ↦ inner ℝ (g p.1) p.2)
      (μ.prod (stdGaussian E)) :=
    hg1.op_fst_snd (by fun_prop)
      ⟨1, by intro x y; simpa using norm_inner_le_norm (𝕜 := ℝ) x y⟩ hz1
  have hcross_zero : (∫ p : E × E, inner ℝ (g p.1) p.2
      ∂μ.prod (stdGaussian E)) = 0 := by
    have h := integral_prod_bilin (innerSL ℝ) hg1 hz1
    change (∫ p : E × E, inner ℝ (g p.1) p.2 ∂μ.prod (stdGaussian E)) =
      inner ℝ (∫ x, g x ∂μ) (∫ z : E, z ∂stdGaussian E) at h
    simpa only [integral_id_stdGaussian, inner_zero_right] using h
  have hexpand (p : E × E) :
      ‖a • g p.1 + b • p.2‖ ^ 2 =
        a ^ 2 * ‖g p.1‖ ^ 2 + (2 * a * b) * inner ℝ (g p.1) p.2 +
          b ^ 2 * ‖p.2‖ ^ 2 := by
    simp only [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_left, real_inner_smul_right]
    ring
  simp_rw [hexpand]
  have hfirst : Integrable (fun p : E × E ↦
      a ^ 2 * ‖g p.1‖ ^ 2 + (2 * a * b) * inner ℝ (g p.1) p.2)
      (μ.prod (stdGaussian E)) := (hgsq.const_mul _).add (hcross.const_mul _)
  have hfirst_moment : (∫ p : E × E, ‖g p.1‖ ^ 2 ∂μ.prod (stdGaussian E)) =
      ∫ x, ‖g x‖ ^ 2 ∂μ := by
    simpa only [probReal_univ, one_smul] using
      integral_fun_fst (μ := μ) (ν := stdGaussian E) (fun x ↦ ‖g x‖ ^ 2)
  have hnoise_moment : (∫ p : E × E, ‖p.2‖ ^ 2 ∂μ.prod (stdGaussian E)) =
      (Module.finrank ℝ E : ℝ) := by
    calc
      (∫ p : E × E, ‖p.2‖ ^ 2 ∂μ.prod (stdGaussian E)) =
          ∫ z : E, ‖z‖ ^ 2 ∂stdGaussian E := by
        simpa only [probReal_univ, one_smul] using
          integral_fun_snd (μ := μ) (ν := stdGaussian E) (fun z : E ↦ ‖z‖ ^ 2)
      _ = (Module.finrank ℝ E : ℝ) := integral_norm_sq_stdGaussian
  rw [integral_add hfirst (hzsq.const_mul (b ^ 2)),
    integral_add (hgsq.const_mul (a ^ 2)) (hcross.const_mul (2 * a * b))]
  simp only [integral_const_mul, hcross_zero, mul_zero, add_zero,
    hfirst_moment, hnoise_moment]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The initial position cancels out of the frozen-drift displacement. -/
theorem malaProposal_sub_initial (U : E → ℝ) (t : ℝ) (x z : E) :
    ULA.malaProposal U t x z - x =
      (-t) • gradient U x + Real.sqrt (2 * t) • z := by
  rw [neg_smul]
  simp only [ULA.malaProposal]
  abel

/-- The displacement of the actual independent-Gaussian interpolation is
square integrable whenever the initial gradient is square integrable. -/
theorem frozen_displacement_memLp
    (μ : Measure E) [IsProbabilityMeasure μ] (U : E → ℝ)
    (hgrad : MemLp (gradient U) 2 μ) (t : ℝ) :
    MemLp (fun p : E × E ↦ ULA.malaProposal U t p.1 p.2 - p.1) 2
      (μ.prod (stdGaussian E)) := by
  have hz : MemLp (fun z : E ↦ z) 2 (stdGaussian E) :=
    IsGaussian.memLp_id (stdGaussian E) 2 (by norm_num)
  have h := ((hgrad.comp_fst (stdGaussian E)).const_smul (-t)).add
    ((hz.comp_snd μ).const_smul (Real.sqrt (2 * t)))
  simpa only [malaProposal_sub_initial, Pi.add_apply, Pi.smul_apply] using! h

/-- Exact frozen-drift displacement energy, including the cancellation of
the drift-noise cross term by independence and the zero Gaussian mean. -/
theorem frozen_displacement_second_moment
    (μ : Measure E) [IsProbabilityMeasure μ] (U : E → ℝ)
    (hgrad : MemLp (gradient U) 2 μ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ p : E × E, ‖ULA.malaProposal U t p.1 p.2 - p.1‖ ^ 2
      ∂μ.prod (stdGaussian E)) =
      t ^ 2 * (∫ x, ‖gradient U x‖ ^ 2 ∂μ) +
        2 * t * (Module.finrank ℝ E : ℝ) := by
  simp_rw [malaProposal_sub_initial]
  rw [integral_norm_sq_affine_stdGaussian μ (gradient U) hgrad,
    neg_sq, Real.sq_sqrt (by positivity : 0 ≤ 2 * t)]

/-- The actual Gaussian interpolation's gradient error has finite energy and
is bounded by Lipschitzness times the exact displacement energy.

The current law need only be a probability law with integrable squared
gradient. No state moment, entropy estimate, convergence bound, or drift-error
bound is assumed. -/
theorem frozen_gradient_error_energy
    (μ : Measure E) [IsProbabilityMeasure μ] (U : E → ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U))
    (hgrad_int : Integrable (fun x ↦ ‖gradient U x‖ ^ 2) μ)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun p : E × E ↦
      ‖gradient U (ULA.malaProposal U t p.1 p.2) - gradient U p.1‖ ^ 2)
      (μ.prod (stdGaussian E)) ∧
      (∫ p : E × E,
        ‖gradient U (ULA.malaProposal U t p.1 p.2) - gradient U p.1‖ ^ 2
        ∂μ.prod (stdGaussian E)) ≤
        (L : ℝ) ^ 2 * (t ^ 2 * (∫ x, ‖gradient U x‖ ^ 2 ∂μ) +
          2 * t * (Module.finrank ℝ E : ℝ)) := by
  have hgrad : MemLp (gradient U) 2 μ :=
    (memLp_two_iff_integrable_sq_norm hLip.continuous.aestronglyMeasurable).mpr hgrad_int
  have hdisp_int := (frozen_displacement_memLp μ U hgrad t).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)
  have hpcont : Continuous (fun p : E × E ↦ ULA.malaProposal U t p.1 p.2) :=
    (continuous_fst.sub ((hLip.continuous.comp continuous_fst).const_smul t)).add
      (continuous_snd.const_smul (Real.sqrt (2 * t)))
  have herr_meas : AEStronglyMeasurable (fun p : E × E ↦
      ‖gradient U (ULA.malaProposal U t p.1 p.2) - gradient U p.1‖ ^ 2)
      (μ.prod (stdGaussian E)) :=
    (((hLip.continuous.comp hpcont).sub
      (hLip.continuous.comp continuous_fst)).norm.pow 2).aestronglyMeasurable
  have hbound (p : E × E) :
      ‖gradient U (ULA.malaProposal U t p.1 p.2) - gradient U p.1‖ ^ 2 ≤
        (L : ℝ) ^ 2 * ‖ULA.malaProposal U t p.1 p.2 - p.1‖ ^ 2 := by
    have hn : ‖gradient U (ULA.malaProposal U t p.1 p.2) - gradient U p.1‖ ≤
        (L : ℝ) * ‖ULA.malaProposal U t p.1 p.2 - p.1‖ := by
      simpa only [dist_eq_norm] using
        hLip.dist_le_mul (ULA.malaProposal U t p.1 p.2) p.1
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  have herr_int : Integrable (fun p : E × E ↦
      ‖gradient U (ULA.malaProposal U t p.1 p.2) - gradient U p.1‖ ^ 2)
      (μ.prod (stdGaussian E)) := by
    apply (hdisp_int.const_mul ((L : ℝ) ^ 2)).mono' herr_meas
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound p
  refine ⟨herr_int, ?_⟩
  have hi := integral_mono herr_int (hdisp_int.const_mul ((L : ℝ) ^ 2)) hbound
  simpa only [integral_const_mul, frozen_displacement_second_moment μ U hgrad t ht] using hi

end ULA.LSI
