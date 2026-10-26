import PBGSO.PastAverages
import PBGSO.MartingaleL2Limit

/-! # Adaptedness of actual past Bochner averages
The measurable L² subspace is preserved by integration, proved through
its actual continuous conditional projection. No projection identity for
a nonlinear coefficient or limiting adaptedness is assumed.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.AdaptedPastAverages
variable {Ω Z : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (F : Filtration ℝ≥0 mΩ)

theorem project_fixed (t : ℝ≥0) (X : Lp Z 2 Q)
    (hX : AEStronglyMeasurable[F t] X Q) :
    MartingaleL2Limit.project Q (F t) (F.le t) X = X := by
  apply Lp.ext
  exact (MartingaleL2Limit.project_coe Q (F t) (F.le t) X).trans
    (condExp_of_aestronglyMeasurable' (F.le t) hX ((Lp.memLp X).integrable (by norm_num)))

/-- The actual Bochner integral over a past time interval belongs to the
current measurable L² subspace, even for merely time-integrable data. -/
theorem integral_adapted (u : ℝ → Lp Z 2 Q) (a b : ℝ)
    (hab : a ≤ b) (hi : IntervalIntegrable u volume a b) (t : ℝ≥0)
    (hU : ∀ᵐ r ∂(volume : Measure ℝ).restrict (Ioc a b), AEStronglyMeasurable[F t] (u r) Q) :
    AEStronglyMeasurable[F t] ((∫ r in a..b, u r : Lp Z 2 Q) : Ω → Z) Q := by
  let P := MartingaleL2Limit.project (Z := Z) Q (F t) (F.le t)
  have hp : P (∫ r in a..b, u r) = ∫ r in a..b, u r := by
    rw [intervalIntegral.integral_of_le hab, ← P.integral_comp_comm hi.left]
    exact integral_congr_ae (hU.mono (fun r hr => project_fixed Q F t (u r) hr))
  have hm := aestronglyMeasurable_condExpL2 (E := Z) (𝕜 := ℝ) (F.le t) (∫ r in a..b, u r)
  change AEStronglyMeasurable[F t] (P (∫ r in a..b, u r)) Q at hm
  rw [hp] at hm
  exact hm

/-- Past adaptedness in the time-L² sense. It follows from actual adapted
coefficient values and filtration monotonicity, and is stable under time
null-set changes. -/
def PastAdapted (u : ℝ → Lp Z 2 Q) : Prop :=
  ∀ t : ℝ≥0, ∀ᵐ r : ℝ ∂(volume : Measure ℝ), r ≤ (t : ℝ) → AEStronglyMeasurable[F t] (u r) Q

/-- Moving past averages are actual current-past measurable random
variables. Only local Bochner integrability and past adaptedness are used. -/
theorem pastMean_adapted (u : ℝ → Lp Z 2 Q)
    (hu : LocallyIntegrable u (volume : Measure ℝ)) (hU : PastAdapted Q F u)
    (ε : ℝ) (hε : 0 ≤ ε) (t : ℝ≥0) :
    AEStronglyMeasurable[F t] ((PastAverages.pastMean (R := Lp Z 2 Q) u ε t) : Ω → Z) Q := by
  have hi : IntervalIntegrable u volume ((t : ℝ) - ε) t :=
    intervalIntegrable_iff.mpr ((hu.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)
  have had : ∀ᵐ r ∂(volume : Measure ℝ).restrict (Ioc ((t : ℝ) - ε) t),
      AEStronglyMeasurable[F t] (u r) Q := by
    filter_upwards [ae_restrict_of_ae (hU t), ae_restrict_mem measurableSet_Ioc] with r hr hmem
    exact hr hmem.2
  have hm := (integral_adapted Q F u _ _ (by linarith) hi t had).const_smul ε⁻¹
  exact hm.congr (Lp.coeFn_smul ε⁻¹ (∫ r in (t : ℝ) - ε..t, u r)).symm

/-- Actual nonnegative-time adaptedness, with zero coefficients before
initialization, implies the time-L² past-adaptedness property. -/
theorem pastAdapted_of_adapted (u : ℝ → Lp Z 2 Q)
    (hneg : ∀ r < 0, u r = 0)
    (hU : ∀ r : ℝ≥0, AEStronglyMeasurable[F r] (u r) Q) : PastAdapted Q F u := by
  intro t
  apply ae_of_all
  intro r hrt
  by_cases hr : 0 ≤ r
  · have hm := AEStronglyMeasurable.mono (F.mono (Real.toNNReal_le_iff_le_coe.mpr hrt)) (hU r.toNNReal)
    simpa only [Real.coe_toNNReal r hr] using hm
  · rw [hneg r (lt_of_not_ge hr)]
    exact aestronglyMeasurable_zero.congr (Lp.coeFn_zero Z 2 Q).symm

end PBGSO.AdaptedPastAverages
