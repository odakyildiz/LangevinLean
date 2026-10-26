import PBGSO.PaperTheorems
import PBGSO.Criteria
import ProximalLangevin.SplittingL2Energy

/-! # Weighted metric estimates for the separated PBGSO criteria
Cauchy--Schwarz and the Euclidean comparisons are proved from the supplied
symmetric positive quadratic weights and their lower/upper bounds.
-/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal RealInnerProductSpace InnerProductSpace BigOperators
namespace PBGSO

section Weighted
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Weighted Cauchy--Schwarz, derived from positivity of the quadratic form. -/
theorem weighted_cauchy_schwarz (W : E →L[ℝ] E)
    (hsym : ∀ x y, ⟪x, W y⟫_ℝ = ⟪W x, y⟫_ℝ)
    (hpos : ∀ x, 0 ≤ ⟪x, W x⟫_ℝ) (x y : E) :
    |⟪x, W y⟫_ℝ| ≤ Real.sqrt ⟪x, W x⟫_ℝ * Real.sqrt ⟪y, W y⟫_ℝ := by
  let A := ⟪x, W x⟫_ℝ
  let B := ⟪x, W y⟫_ℝ
  let C := ⟪y, W y⟫_ℝ
  have hA : 0 ≤ A := hpos x
  have hC : 0 ≤ C := hpos y
  have hsym' : ⟪y, W x⟫_ℝ = B := by
    calc
      ⟪y, W x⟫_ℝ = ⟪W x, y⟫_ℝ := real_inner_comm _ _
      _ = B := (hsym x y).symm
  have hsq : B ^ 2 ≤ A * C := by
    by_cases hc : C = 0
    · have hquad (t : ℝ) : 0 ≤ A + 2 * t * B := by
        have hp := hpos (x + t • y)
        simp only [map_add, map_smul, inner_add_left, inner_add_right,
          real_inner_smul_left, real_inner_smul_right, hsym'] at hp
        dsimp [A, B, C] at *
        rw [hc] at hp
        nlinarith
      have hb : B = 0 := by
        by_contra hb
        have hp := hquad (-(A + 1) / (2 * B))
        have he : A + 2 * (-(A + 1) / (2 * B)) * B = -1 := by field_simp; ring
        rw [he] at hp
        linarith
      rw [hb, hc]
      simp
    · have hcpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hc)
      have hp := hpos (C • x - B • y)
      simp only [map_sub, map_smul, inner_sub_left, inner_sub_right,
        real_inner_smul_left, real_inner_smul_right, hsym'] at hp
      have he : 0 ≤ C * (A * C - B ^ 2) := by
        dsimp [A, B, C] at *
        nlinarith only [hp]
      have hh := nonneg_of_mul_nonneg_right he hcpos
      linarith
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hC]
  exact hsq

/-- Spectral upper comparison turns weighted Cauchy--Schwarz into the exact
mixed metric/Euclidean inequality used by the paper. -/
theorem weighted_pairing_bound (W : E →L[ℝ] E) (upper : ℝ) (hu : 0 ≤ upper)
    (hsym : ∀ x y, ⟪x, W y⟫_ℝ = ⟪W x, y⟫_ℝ)
    (hpos : ∀ x, 0 ≤ ⟪x, W x⟫_ℝ)
    (hupper : ∀ y, ⟪y, W y⟫_ℝ ≤ upper * ‖y‖ ^ 2) (x y : E) :
    |⟪x, W y⟫_ℝ| ≤ Real.sqrt ⟪x, W x⟫_ℝ * Real.sqrt upper * ‖y‖ := by
  have hy : Real.sqrt ⟪y, W y⟫_ℝ ≤ Real.sqrt upper * ‖y‖ := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (hpos y), mul_pow, Real.sq_sqrt hu]
    exact hupper y
  exact (weighted_cauchy_schwarz W hsym hpos x y).trans
    (by have h := mul_le_mul_of_nonneg_left hy (Real.sqrt_nonneg ⟪x, W x⟫_ℝ); nlinarith)

end Weighted

namespace TwistedGeometry
variable {S Z : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [MeasurableSpace Z]
  (D : TwistedGeometry S Z)

/-- Exact metric pairing comparison for optimiser perturbations. -/
theorem optimizer_pairing_bound (s e : S) :
    |⟪s, D.optimizerWeight e⟫_ℝ| ≤
      Real.sqrt (D.optimizerSq s) * Real.sqrt D.upper * ‖e‖ :=
  weighted_pairing_bound D.optimizerWeight D.upper
    (D.lower_pos.le.trans D.lower_le_upper) D.optimizer_symmetric
    D.optimizerSq_nonneg D.optimizer_upper s e

/-- Exact metric pairing comparison for sampler perturbations. -/
theorem sampler_pairing_bound (z e : Z) :
    |⟪z, D.samplerWeight e⟫_ℝ| ≤
      Real.sqrt (D.samplerSq z) * Real.sqrt D.upper * ‖e‖ :=
  weighted_pairing_bound D.samplerWeight D.upper
    (D.lower_pos.le.trans D.lower_le_upper) D.sampler_symmetric
    D.samplerSq_nonneg D.sampler_upper z e

/-- Euclidean optimiser norm from its weighted energy. -/
theorem optimizer_norm_le (s : S) :
    ‖s‖ ≤ Real.sqrt (D.optimizerSq s) / Real.sqrt D.lower := by
  have h := Real.sqrt_le_sqrt (D.optimizer_lower s)
  rw [Real.sqrt_mul D.lower_pos.le, Real.sqrt_sq (norm_nonneg _)] at h
  apply (le_div_iff₀ (Real.sqrt_pos.mpr D.lower_pos)).mpr
  simpa only [TwistedGeometry.optimizerSq, mul_comm] using h

/-- Euclidean sampler norm from its weighted energy. -/
theorem sampler_norm_le (z : Z) :
    ‖z‖ ≤ Real.sqrt (D.samplerSq z) / Real.sqrt D.lower := by
  have h := Real.sqrt_le_sqrt (D.sampler_lower z)
  rw [Real.sqrt_mul D.lower_pos.le, Real.sqrt_sq (norm_nonneg _)] at h
  apply (le_div_iff₀ (Real.sqrt_pos.mpr D.lower_pos)).mpr
  simpa only [TwistedGeometry.samplerSq, mul_comm] using h

/-- The metric conversion factor is exactly the square root of the stated
condition number, rather than an unproved operator-norm assumption. -/
theorem sqrt_conditionNumber :
    Real.sqrt D.upper / Real.sqrt D.lower = Real.sqrt D.conditionNumber := by
  rw [conditionNumber, Real.sqrt_div (D.lower_pos.le.trans D.lower_le_upper)]

end TwistedGeometry
section Moments
variable {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- Square roots of integrable nonnegative quadratic energies have a finite
second moment. -/
theorem sqrt_energy_memLp (q : Ω → ℝ) (hq : AEStronglyMeasurable q Q)
    (hint : Integrable q Q) (hpos : ∀ ω, 0 ≤ q ω) :
    MemLp (fun ω ↦ Real.sqrt (q ω)) 2 Q := by
  apply (memLp_two_iff_integrable_sq (Real.continuous_sqrt.comp_aestronglyMeasurable hq)).mpr
  simpa only [Real.sq_sqrt (hpos _)] using hint

/-- Probability-space Cauchy--Schwarz for the actual quadratic coupling
energy. The integral bound is derived, rather than an input about a law. -/
theorem integral_sqrt_energy_le (q : Ω → ℝ) (hq : AEStronglyMeasurable q Q)
    (hint : Integrable q Q) (hpos : ∀ ω, 0 ≤ q ω) :
    (∫ ω, Real.sqrt (q ω) ∂Q) ≤ Real.sqrt (∫ ω, q ω ∂Q) := by
  let f := fun ω ↦ Real.sqrt (q ω)
  have hm : MemLp f 2 Q := sqrt_energy_memLp Q q hq hint hpos
  have hi := hm.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hOne : ENNReal.ofReal (∫ ω, ‖f ω‖ ∂Q) = eLpNorm f 1 Q := by
    rw [ofReal_integral_norm_eq_lintegral_enorm hi, eLpNorm_one_eq_lintegral_enorm hm.aestronglyMeasurable]
  have hle : eLpNorm f 1 Q ≤ eLpNorm f 2 Q :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hr := ENNReal.toReal_mono hm.eLpNorm_ne_top hle
  rw [← hOne, ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _)] at hr
  have hn := ProximalLangevin.lp_norm_sq_eq_integral Q (hm.toLp f)
  rw [Lp.norm_toLp] at hn
  have he : (∫ ω, ‖hm.toLp f ω‖ ^ 2 ∂Q) = ∫ ω, q ω ∂Q := by
    apply integral_congr_ae
    filter_upwards [hm.coeFn_toLp] with ω hω
    rw [hω]
    simp only [f, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hpos ω)]
  rw [he] at hn
  have hfpos : 0 ≤ ∫ ω, f ω ∂Q := integral_nonneg (fun ω ↦ Real.sqrt_nonneg _)
  have hr' : (∫ ω, f ω ∂Q) ≤ (eLpNorm f 2 Q).toReal := by
    simpa only [f, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hr
  apply Real.le_sqrt_of_sq_le
  nlinarith [ENNReal.toReal_nonneg (a := eLpNorm f 2 Q)]

end Moments

end PBGSO
