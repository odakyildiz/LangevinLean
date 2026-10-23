import UnadjustedLangevin.LpDrift
import Mathlib.MeasureTheory.Function.Holder

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace KineticLangevin
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  (P : Measure Ω)

/-- A uniformly bounded measurable random linear operator acts continuously on actual L² variables. -/
def randomOperatorLp (A : Ω → E →L[ℝ] E) (hA : AEStronglyMeasurable A P)
    (M : ℝ) (hbound : ∀ᵐ ω ∂P,‖A ω‖≤M) : Lp E 2 P →L[ℝ] Lp E 2 P :=
  ((ContinuousLinearMap.id ℝ (E →L[ℝ] E)).holderL P ⊤ 2 2)
    ((memLp_top_of_bound hA M hbound).toLp A)

/-- This operator is the pointwise random operator on every actual representative. -/
theorem randomOperatorLp_coe (A : Ω → E →L[ℝ] E) (hA : AEStronglyMeasurable A P)
    (M : ℝ) (hbound : ∀ᵐ ω ∂P,‖A ω‖≤M) (X : Lp E 2 P) :
    randomOperatorLp P A hA M hbound X =ᵐ[P] fun ω ↦ A ω (X ω) := by
  filter_upwards [(ContinuousLinearMap.id ℝ (E →L[ℝ] E)).coeFn_holder (r := 2)
      ((memLp_top_of_bound hA M hbound).toLp A) X,
    (memLp_top_of_bound hA M hbound).coeFn_toLp] with ω hω hAω
  change (randomOperatorLp P A hA M hbound X) ω = _ at hω
  simpa only [ContinuousLinearMap.id_apply,hAω] using hω

/-- The random-operator action retains its deterministic operator bound. -/
theorem randomOperatorLp_apply_norm_le (A : Ω → E →L[ℝ] E) (hA : AEStronglyMeasurable A P)
    (M : ℝ) (hbound : ∀ᵐ ω ∂P,‖A ω‖≤M) (X : Lp E 2 P) :
    ‖randomOperatorLp P A hA M hbound X‖≤M*‖X‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [randomOperatorLp_coe P A hA M hbound X,hbound] with ω hω hMω
  rw [hω]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hMω (norm_nonneg _))

theorem randomOperatorLp_norm_le (A : Ω → E →L[ℝ] E) (hA : AEStronglyMeasurable A P)
    (M : ℝ) (hM : 0≤M) (hbound : ∀ᵐ ω ∂P,‖A ω‖≤M) :
    ‖randomOperatorLp P A hA M hbound‖≤M :=
  ContinuousLinearMap.opNorm_le_bound _ hM (randomOperatorLp_apply_norm_le P A hA M hbound)

end KineticLangevin
