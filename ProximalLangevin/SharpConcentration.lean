import ProximalLangevin.Perturbation
import Mathlib.Analysis.Calculus.Deriv.Pow

set_option linter.style.header false

/-!
# Sharp Gibbs concentration under continuous strong convexity

This strengthens the existing dilation argument from `2 dim / q` to `dim / q`
using the sharp minimizer growth inequality. No differentiability of the
potential, integration by parts, or moment assumptions are required.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set ULA
open scoped ENNReal Topology
namespace ProximalLangevin
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

/-- The dilation inequality before taking the tangent limit. -/
theorem sharp_gibbs_mode_dilation_inequality
    (F : H → ℝ) (q : ℝ) (hq : 0 < q) (hc : Continuous F)
    (hsc : StrongConvexOn Set.univ q F) (z : H) (hz : ∀ x, F z ≤ F x)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    (∫ x, Real.exp (-F x) ∂volume) + q / 2 * (1 - r ^ 2) *
      (∫ x, ‖x - z‖ ^ 2 * Real.exp (-F x) ∂volume) ≤
    (r ^ Module.finrank ℝ H)⁻¹ * ∫ x, Real.exp (-F x) ∂volume := by
  let w := fun x ↦ Real.exp (-F x)
  let C := q / 2 * (1 - r ^ 2)
  have hi := integrable_exp_neg_of_continuous_strongConvex_mode F q hq hc hsc z hz
  have hmi := integrable_sq_dist_mul_exp_neg_of_continuous_strongConvex_mode F q hq hc hsc z hz
  have haff (x : H) : z + r • (x - z) = r • x + (1 - r) • z := by module
  have hip : Integrable (fun x ↦ w (z + r • (x - z))) volume := by
    have ht := (measurePreserving_add_right (volume : Measure H)
      ((1 - r) • z)).integrable_comp_of_integrable hi
    have hs := ht.comp_smul hr.ne'
    convert hs using 1
    funext x
    exact congrArg w (haff x)
  have htrans : (∫ x, w (z + r • (x - z)) ∂volume) =
      (r ^ Module.finrank ℝ H)⁻¹ * ∫ x, w x ∂volume := by
    have hs := Measure.integral_comp_smul_of_nonneg (volume : Measure H)
      (fun x ↦ w (x + (1 - r) • z)) r (hR := hr.le)
    rw [integral_add_right_eq_self] at hs
    convert hs using 1
    · apply integral_congr_ae
      exact ae_of_all _ fun x ↦ congrArg w (haff x)
  have hpoint (x : H) : w x + C * (‖x - z‖ ^ 2 * w x) ≤ w (z + r • (x - z)) := by
    have hs := hsc.2 (Set.mem_univ z) (Set.mem_univ x)
      (by linarith : 0 ≤ 1 - r) hr.le (by ring : 1 - r + r = 1)
    dsimp only at hs
    simp only [smul_eq_mul] at hs
    rw [norm_sub_rev z x] at hs
    have heq : (1 - r) • z + r • x = z + r • (x - z) := by module
    rw [heq] at hs
    have hb : F (z + r • (x - z)) ≤ F x - C * ‖x - z‖ ^ 2 := by
      have hg := strongConvex_minimum_growth F q hq.le hsc z hz x
      have hmin := mul_le_mul_of_nonneg_left hg (show 0 ≤ 1 - r by linarith)
      dsimp [C]
      nlinarith
    have he := Real.exp_le_exp.mpr (show -F x + C * ‖x - z‖ ^ 2 ≤
      -F (z + r • (x - z)) by linarith)
    rw [Real.exp_add] at he
    have hp := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (C * ‖x - z‖ ^ 2))
      (Real.exp_nonneg (-F x))
    dsimp [w] at *
    nlinarith
  calc
    _ = ∫ x, (w x + C * (‖x - z‖ ^ 2 * w x)) ∂volume := by
      rw [integral_add hi (hmi.const_mul C), integral_const_mul]
    _ ≤ ∫ x, w (z + r • (x - z)) ∂volume := integral_mono (hi.add (hmi.const_mul C)) hip hpoint
    _ = _ := htrans

/-- Taking the tangent limit of the dilation inequality gives the exact
dimension dependence, without differentiating the potential. -/
theorem sharp_integral_sq_dist_mul_exp_neg_le
    (F : H → ℝ) (q : ℝ) (hq : 0 < q) (hc : Continuous F)
    (hsc : StrongConvexOn Set.univ q F) (z : H) (hz : ∀ x, F z ≤ F x) :
    (∫ x, ‖x - z‖ ^ 2 * Real.exp (-F x) ∂volume) ≤
      ((Module.finrank ℝ H : ℝ) / q) * ∫ x, Real.exp (-F x) ∂volume := by
  let d := Module.finrank ℝ H
  let Z := ∫ x, Real.exp (-F x) ∂volume
  let M := ∫ x, ‖x - z‖ ^ 2 * Real.exp (-F x) ∂volume
  let C := q / 2
  let Φ : ℝ → ℝ := fun r ↦ r ^ d * (Z + C * (1 - r ^ 2) * M)
  have hΦ1 : Φ 1 = Z := by simp [Φ]
  have hΦ (r : ℝ) (hr : 0 < r) (hr1 : r < 1) : Φ r ≤ Z := by
    have h := sharp_gibbs_mode_dilation_inequality F q hq hc hsc z hz r hr hr1
    have hp : 0 < r ^ d := pow_pos hr d
    have hm := mul_le_mul_of_nonneg_left h hp.le
    change Φ r ≤ r ^ d * ((r ^ d)⁻¹ * Z) at hm
    rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul] at hm
    exact hm
  have hinner : HasDerivAt (fun r : ℝ ↦ Z + C * (1 - r ^ 2) * M) (-2 * C * M) 1 := by
    convert (hasDerivAt_const (1 : ℝ) Z).add
      (((hasDerivAt_const (1 : ℝ) 1).sub
        ((hasDerivAt_id (1 : ℝ)).pow 2)).const_mul C |>.mul_const M) using 1
    · rfl
    · simp only [id_eq]
      ring
  have hder : HasDerivAt Φ ((d : ℝ) * Z - 2 * C * M) 1 := by
    convert ((hasDerivAt_id (1 : ℝ)).pow d).mul hinner using 1
    · rfl
    · simp only [Pi.pow_apply, id_eq, one_pow, mul_one, sub_self, mul_zero, zero_mul, add_zero]
      ring
  have hnonneg : ∀ᶠ u : ℝ in 𝓝[<] 0,
      0 ≤ u⁻¹ * (Φ (1 + u) - Φ 1) := by
    have hnear : ∀ᶠ u : ℝ in 𝓝[<] 0, -1 < u :=
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (-1 : ℝ) < 0))
    filter_upwards [self_mem_nhdsWithin, hnear] with u hu hnear
    have hp := hΦ (1 + u) (by linarith) (by change u < 0 at hu; linarith)
    rw [← hΦ1] at hp
    exact mul_nonneg_of_nonpos_of_nonpos (inv_nonpos.mpr hu.le) (sub_nonpos.mpr hp)
  have hbound : 0 ≤ (d : ℝ) * Z - 2 * C * M := by
    have hs := hder.tendsto_slope_zero_left
    simp only [smul_eq_mul] at hs
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hs hnonneg
  change M ≤ ((d : ℝ) / q) * Z
  have hb : M ≤ (d : ℝ) * Z / q := by
    apply (le_div_iff₀ hq).mpr
    dsimp [C] at hbound
    nlinarith
  convert hb using 1
  ring

/-- A continuous `q`-strongly convex Gibbs potential concentrates around its
minimizer with sharp second moment at most `dim / q`. Every normalization and
integrability fact used in the conclusion is proved from the stated inputs. -/
theorem sharp_integral_sq_dist_gibbs_le
    (F : H → ℝ) (q : ℝ) (hq : 0 < q) (hc : Continuous F)
    (hsc : StrongConvexOn Set.univ q F) (z : H) (hz : ∀ x, F z ≤ F x) :
    (∫ x, ‖x - z‖ ^ 2 ∂gibbsMeasure F) ≤ (Module.finrank ℝ H : ℝ) / q := by
  let Z := ∫ x, Real.exp (-F x) ∂volume
  have hi := integrable_exp_neg_of_continuous_strongConvex_mode F q hq hc hsc z hz
  have hZ : 0 < Z := integral_exp_pos hi
  have hpart : gibbsPartition F = ENNReal.ofReal Z :=
    (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ ↦ Real.exp_nonneg _)).symm
  have hw : Measurable (gibbsWeight F) :=
    (Real.continuous_exp.comp hc.neg).measurable.ennreal_ofReal
  have heq : (∫ x, ‖x - z‖ ^ 2 ∂gibbsMeasure F) =
      Z⁻¹ * ∫ x, ‖x - z‖ ^ 2 * Real.exp (-F x) ∂volume := by
    rw [gibbsMeasure, hpart, integral_smul_measure,
      integral_withDensity_eq_integral_toReal_smul hw
        (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ.le, smul_eq_mul,
      gibbsWeight, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun x ↦ mul_comm _ _
  rw [heq]
  have hb := sharp_integral_sq_dist_mul_exp_neg_le F q hq hc hsc z hz
  calc
    _ ≤ Z⁻¹ * (((Module.finrank ℝ H : ℝ) / q) * Z) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hZ.le)
    _ = _ := by rw [mul_left_comm, inv_mul_cancel₀ hZ.ne', mul_one]

end ProximalLangevin
