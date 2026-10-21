import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Probability.Distributions.Gaussian.Real

set_option linter.style.header false

/-!
# Characteristic functions and Gaussian closedness in L²

At a fixed frequency, the characteristic function of a real random variable
is continuous in its L² class. The exponential is lifted by a Lipschitz map
vanishing at zero, and expectation is an L² inner product with the constant
one. Consequently centered Gaussian laws with their actual L² variances are
closed under arbitrary nontrivial-filter L² limits.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace ULA

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

private def centeredCharacteristic (t x : ℝ) : ℂ := circleMap (-1) 1 (t * x)

private theorem centeredCharacteristic_lipschitz (t : ℝ) :
    LipschitzWith ‖t‖₊ (centeredCharacteristic t) := by
  have hmul : LipschitzWith ‖t‖₊ (fun x : ℝ ↦ t * x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_eq_norm, ← mul_sub, norm_mul, coe_nnnorm]
    exact le_rfl
  have hunit : Real.nnabs (1 : ℝ) = 1 := by
    apply NNReal.eq
    norm_num
  change LipschitzWith ‖t‖₊ (fun x : ℝ ↦ circleMap (-1) 1 (t * x))
  simpa only [hunit, one_mul, Function.comp_def] using
    (lipschitzWith_circleMap (-1) 1).comp hmul

private theorem centeredCharacteristic_zero (t : ℝ) : centeredCharacteristic t 0 = 0 := by
  simp [centeredCharacteristic, circleMap]

private def characteristicLp (t : ℝ) (X : Lp ℝ 2 P) : Lp ℂ 2 P :=
  (centeredCharacteristic_lipschitz t).compLp (centeredCharacteristic_zero t) X +
    Lp.const 2 P 1

private theorem characteristicLp_coe (t : ℝ) (X : Lp ℝ 2 P) :
    characteristicLp P t X =ᵐ[P] fun ω ↦ Complex.exp (t * X ω * Complex.I) := by
  filter_upwards [Lp.coeFn_add
      ((centeredCharacteristic_lipschitz t).compLp (centeredCharacteristic_zero t) X)
      (Lp.const 2 P (1 : ℂ)),
    (centeredCharacteristic_lipschitz t).coeFn_compLp (centeredCharacteristic_zero t) X,
    Lp.coeFn_const (μ := P) (p := 2) (c := (1 : ℂ))] with ω hadd hcomp hone
  simp only [characteristicLp, hadd, Pi.add_apply, hcomp, hone, Function.comp_apply,
    Function.const_apply, centeredCharacteristic, circleMap, Complex.ofReal_one,
    one_mul, Complex.ofReal_mul]
  ring

private theorem charFun_map_eq_inner_characteristicLp (t : ℝ) (X : Lp ℝ 2 P) :
    charFun (P.map X) t = inner ℂ (Lp.const 2 P (1 : ℂ)) (characteristicLp P t X) := by
  rw [charFun_apply_real, integral_map (Lp.aestronglyMeasurable X).aemeasurable
    (by fun_prop), L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const (μ := P) (p := 2) (c := (1 : ℂ)),
    characteristicLp_coe P t X] with ω hone hchar
  simp [hchar, RCLike.inner_apply]

/-- The characteristic function at a fixed frequency depends continuously on
the real random variable in L². Its law is the actual pushforward measure. -/
theorem continuous_charFun_map_Lp (t : ℝ) :
    Continuous (fun X : Lp ℝ 2 P ↦ charFun (P.map X) t) := by
  have hc : Continuous (characteristicLp P t) :=
    ((centeredCharacteristic_lipschitz t).continuous_compLp
      (centeredCharacteristic_zero t)).add continuous_const
  have hi : Continuous (fun X : Lp ℝ 2 P ↦
      inner ℂ (Lp.const 2 P (1 : ℂ)) (characteristicLp P t X)) := continuous_const.inner hc
  simpa only [← charFun_map_eq_inner_characteristicLp] using hi

omit [IsProbabilityMeasure P] in
/-- The centered Gaussian characteristic function is continuous in the L²
norm supplying its variance. The nonnegative-real conversion is continuous. -/
theorem continuous_gaussianReal_charFun_Lp (t : ℝ) :
    Continuous (fun X : Lp ℝ 2 P ↦
      charFun (gaussianReal 0 ((‖X‖ ^ 2).toNNReal)) t) := by
  simp only [charFun_gaussianReal]
  fun_prop

/-- Centered Gaussian laws with their actual second moments are closed under
L² limits, for any nontrivial filter. Even eventual Gaussian laws suffice. -/
theorem hasLaw_gaussianReal_of_tendsto_Lp_eventually
    {ι : Type*} {l : Filter ι} [NeBot l] (X : ι → Lp ℝ 2 P) (Y : Lp ℝ 2 P)
    (hXY : Tendsto X l (𝓝 Y))
    (hGaussian : ∀ᶠ i in l, HasLaw (X i) (gaussianReal 0 ((‖X i‖ ^ 2).toNNReal)) P) :
    HasLaw Y (gaussianReal 0 ((‖Y‖ ^ 2).toNNReal)) P := by
  refine ⟨(Lp.aestronglyMeasurable Y).aemeasurable, Measure.ext_of_charFun ?_⟩
  funext t
  have hactual := ((continuous_charFun_map_Lp P t).tendsto Y).comp hXY
  have hgaussian := ((continuous_gaussianReal_charFun_Lp P t).tendsto Y).comp hXY
  have heq : (fun i ↦ charFun (P.map (X i)) t) =ᶠ[l]
      (fun i ↦ charFun (gaussianReal 0 ((‖X i‖ ^ 2).toNNReal)) t) := by
    filter_upwards [hGaussian] with i hi
    rw [hi.map_eq]
  exact tendsto_nhds_unique hactual (hgaussian.congr' heq.symm)

/-- The all-index version, convenient for finite-sum approximations to a
Gaussian Hilbert-space isometry. -/
theorem hasLaw_gaussianReal_of_tendsto_Lp
    {ι : Type*} {l : Filter ι} [NeBot l] (X : ι → Lp ℝ 2 P) (Y : Lp ℝ 2 P)
    (hXY : Tendsto X l (𝓝 Y))
    (hGaussian : ∀ i, HasLaw (X i) (gaussianReal 0 ((‖X i‖ ^ 2).toNNReal)) P) :
    HasLaw Y (gaussianReal 0 ((‖Y‖ ^ 2).toNNReal)) P :=
  hasLaw_gaussianReal_of_tendsto_Lp_eventually P X Y hXY (Eventually.of_forall hGaussian)

end ULA
