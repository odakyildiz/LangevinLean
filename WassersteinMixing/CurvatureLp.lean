import WassersteinMixing.Curvature
import UnadjustedLangevin.LpDrift
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space

/-! # The actual random Hessian as a bounded self-adjoint `L²` operator

The pointwise averaged Hessian is an essentially bounded operator field.
Hölder multiplication constructs its action on genuine square-integrable
random vectors and preserves adaptation to every sub-sigma-algebra.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory
open scoped ENNReal NNReal

namespace WassersteinMixing

variable {Ω H : Type*} [m0 : MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (Q : Measure Ω) (P : Parameters) (V : H → ℝ) (hV : PotentialAssumptions P V)

/-- The literal averaged Hessian between the two supplied actual states. -/
def averagedHessianField (X Y : Lp H 2 Q) (ω : Ω) : H →L[ℝ] H :=
  averagedHessian V (X ω) (Y ω)

include P hV in
/-- The actual random Hessian field is essentially bounded and measurable. -/
theorem averagedHessianField_memLp (X Y : Lp H 2 Q) :
    MemLp (averagedHessianField Q V X Y) ⊤ Q := by
  apply memLp_top_of_bound
    ((averagedHessian_continuous P V hV).comp_aestronglyMeasurable
      ((Lp.aestronglyMeasurable X).prodMk (Lp.aestronglyMeasurable Y))) P.beta
  exact Filter.Eventually.of_forall fun ω ↦ averagedHessian_norm_le P V hV _ _

/-- Hölder multiplication by the actual bounded random Hessian. -/
def randomCurvature (X Y : Lp H 2 Q) : Lp H 2 Q →L[ℝ] Lp H 2 Q :=
  (ContinuousLinearMap.id ℝ (H →L[ℝ] H)).holderL Q ⊤ 2 2
    ((averagedHessianField_memLp Q P V hV X Y).toLp
      (averagedHessianField Q V X Y))

/-- The lifted operator acts by the actual pointwise Hessian on representatives. -/
theorem randomCurvature_coe (X Y U : Lp H 2 Q) :
    randomCurvature Q P V hV X Y U =ᵐ[Q] fun ω ↦
      averagedHessian V (X ω) (Y ω) (U ω) := by
  have hh := (ContinuousLinearMap.id ℝ (H →L[ℝ] H)).coeFn_holder (r := 2)
    ((averagedHessianField_memLp Q P V hV X Y).toLp
      (averagedHessianField Q V X Y)) U
  filter_upwards [hh, (averagedHessianField_memLp Q P V hV X Y).coeFn_toLp]
    with ω hω hfield
  exact hω.trans (congrArg (fun A : H →L[ℝ] H ↦ A (U ω)) hfield)

/-- The actual random curvature has the sharp smoothness norm bound. -/
theorem randomCurvature_norm_le (X Y U : Lp H 2 Q) :
    ‖randomCurvature Q P V hV X Y U‖ ≤ P.beta * ‖U‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [randomCurvature_coe Q P V hV X Y U] with ω hω
  rw [hω]
  exact (averagedHessian V (X ω) (Y ω)).le_of_opNorm_le
    (averagedHessian_norm_le P V hV _ _) (U ω)

/-- Symmetry of the actual random curvature in the genuine `L²` inner product. -/
theorem randomCurvature_symmetric (X Y U W : Lp H 2 Q) :
    inner ℝ (randomCurvature Q P V hV X Y U) W =
      inner ℝ U (randomCurvature Q P V hV X Y W) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [randomCurvature_coe Q P V hV X Y U,
    randomCurvature_coe Q P V hV X Y W] with ω hU hW
  rw [hU, hW]
  exact averagedHessian_symmetric V hV.regularity _ _ _ _

/-- Strong convexity transfers to the actual random Hessian quadratic form. -/
theorem randomCurvature_lower (X Y U : Lp H 2 Q) :
    P.alpha * ‖U‖ ^ 2 ≤ inner ℝ U (randomCurvature Q P V hV X Y U) := by
  have hn : ‖U‖ ^ 2 = ∫ ω, ‖U ω‖ ^ 2 ∂Q := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ real_inner_self_eq_norm_sq _)
  rw [hn, ← integral_const_mul, L2.inner_def]
  apply integral_mono_ae (((Lp.memLp U).integrable_norm_pow (by norm_num)).const_mul P.alpha)
    (L2.integrable_inner _ _)
  filter_upwards [randomCurvature_coe Q P V hV X Y U] with ω hω
  rw [hω]
  exact averagedHessian_lower P V hV _ _ _

/-- Smoothness transfers to the actual random Hessian quadratic form. -/
theorem randomCurvature_upper (X Y U : Lp H 2 Q) :
    inner ℝ U (randomCurvature Q P V hV X Y U) ≤ P.beta * ‖U‖ ^ 2 := by
  have hi := real_inner_le_norm U (randomCurvature Q P V hV X Y U)
  have hn := randomCurvature_norm_le Q P V hV X Y U
  nlinarith [norm_nonneg U]

/-- The random Hessian is the exact lifted true-gradient secant operator. -/
theorem randomCurvature_secant [IsFiniteMeasure Q] (X Y : Lp H 2 Q) :
    randomCurvature Q P V hV X Y (X - Y) =
      ULA.lpDrift Q (gradient V) hV.gradientLipschitz X -
        ULA.lpDrift Q (gradient V) hV.gradientLipschitz Y := by
  apply Lp.ext
  filter_upwards [randomCurvature_coe Q P V hV X Y (X - Y), Lp.coeFn_sub X Y,
    Lp.coeFn_sub (ULA.lpDrift Q (gradient V) hV.gradientLipschitz X)
      (ULA.lpDrift Q (gradient V) hV.gradientLipschitz Y),
    ULA.lpDrift_coe Q (gradient V) hV.gradientLipschitz X,
    ULA.lpDrift_coe Q (gradient V) hV.gradientLipschitz Y] with ω hA hXY hsub hX hY
  rw [hA, hXY, hsub]
  simp only [Pi.sub_apply]
  rw [hX, hY]
  exact averagedHessian_secant V hV.regularity _ _

/-- The actual random Hessian preserves adaptation whenever the two current
states and the argument are measurable with respect to the current past. -/
theorem randomCurvature_adapted (m : MeasurableSpace Ω) (X Y U : Lp H 2 Q)
    (hX : AEStronglyMeasurable[m] X Q) (hY : AEStronglyMeasurable[m] Y Q)
    (hU : AEStronglyMeasurable[m] U Q) :
    AEStronglyMeasurable[m] (randomCurvature (m0 := m0) Q P V hV X Y U) Q := by
  have hfield := (averagedHessian_continuous P V hV).comp_aestronglyMeasurable (hX.prodMk hY)
  have hpoint := (ContinuousLinearMap.id ℝ (H →L[ℝ] H)).continuous₂.comp_aestronglyMeasurable
    (hfield.prodMk hU)
  exact hpoint.congr (randomCurvature_coe (m0 := m0) Q P V hV X Y U).symm

end WassersteinMixing
