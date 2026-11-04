import WassersteinMixing.ActualMarkovNoise
import Mathlib.Probability.ConditionalExpectation

/-! # Conditional averaging over an independent input

A measurable function of a past-measurable state and an independent random
input has conditional mean obtained by integrating only the independent input.
The statement applies to arbitrary measurable input spaces, including paths.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
namespace WassersteinMixing

/-- Restricting to a past event retains the independent input's original law,
while only the state marginal is restricted. -/
theorem independent_input_restrict_joint_map {Ω A B : Type*}
    (m : MeasurableSpace Ω) [m0 : MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (hm : m ≤ m0)
    (X : Ω → A) (Y : Ω → B) (hX : Measurable[m] X) (hY : Measurable Y)
    (hi : Indep ((inferInstance : MeasurableSpace B).comap Y) m Q)
    (s : Set Ω) (hs : MeasurableSet[m] s) :
    (Q.restrict s).map (fun ω ↦ (X ω, Y ω)) =
      ((Q.restrict s).map X).prod (Q.map Y) := by
  have hXa : Measurable X := hX.mono hm le_rfl
  apply Measure.ext_prod
  intro u v hu hv
  rw [Measure.map_apply (hXa.prodMk hY) (hu.prod hv),
    Measure.prod_prod, Measure.map_apply hXa hu, Measure.map_apply hY hv,
    Measure.restrict_apply ((hXa.prodMk hY) (hu.prod hv)),
    Measure.restrict_apply (hXa hu)]
  have he := (Indep_iff _ _ _).mp hi (Y ⁻¹' v) (X ⁻¹' u ∩ s) ⟨v, hv, rfl⟩ ((hX hu).inter hs)
  simpa only [Set.mk_preimage_prod, mul_comm, inter_assoc, inter_left_comm, inter_comm] using he

/-- Conditional averaging of a function of a measurable state and an input
independent of the whole conditioning sigma-algebra. -/
theorem condExp_independent_input_average {Ω A B H : Type*}
    (m : MeasurableSpace Ω) [m0 : MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (hm : m ≤ m0)
    (X : Ω → A) (Y : Ω → B) (hX : Measurable[m] X) (hY : Measurable Y)
    (hi : Indep ((inferInstance : MeasurableSpace B).comap Y) m Q)
    (F : A × B → H) (hF : StronglyMeasurable F)
    (hFi : Integrable (fun ω ↦ F (X ω, Y ω)) Q) :
    Q[(fun ω ↦ F (X ω, Y ω)) | m] =ᵐ[Q]
      fun ω ↦ ∫ y, F (X ω, y) ∂Q.map Y := by
  have hXa : Measurable X := hX.mono hm le_rfl
  let Havg : A → H := fun x ↦ ∫ y, F (x, y) ∂Q.map Y
  have hHsm : StronglyMeasurable Havg :=
    StronglyMeasurable.integral_prod_right (f := fun x y ↦ F (x, y)) (by
      simpa only [Function.uncurry_def] using hF)
  have hjoint : Q.map (fun ω ↦ (X ω, Y ω)) = (Q.map X).prod (Q.map Y) := by
    simpa only [Measure.restrict_univ] using
      independent_input_restrict_joint_map m Q hm X Y hX hY hi univ MeasurableSet.univ
  have hprod : Integrable F ((Q.map X).prod (Q.map Y)) := by
    rw [← hjoint]
    exact (integrable_map_measure hF.aestronglyMeasurable (hXa.prodMk hY).aemeasurable).mpr hFi
  have hHint : Integrable (fun ω ↦ Havg (X ω)) Q :=
    hprod.integral_prod_left.comp_aemeasurable hXa.aemeasurable
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hFi
  · intro s hs hμs
    exact hHint.integrableOn
  · intro s hs hμs
    have hmaps := independent_input_restrict_joint_map m Q hm X Y hX hY hi s hs
    have hprod_s : Integrable F (((Q.restrict s).map X).prod (Q.map Y)) := by
      rw [← hmaps]
      exact (integrable_map_measure hF.aestronglyMeasurable
        (hXa.prodMk hY).aemeasurable).mpr hFi.integrableOn
    calc
      (∫ ω in s, Havg (X ω) ∂Q) = ∫ x, Havg x ∂(Q.restrict s).map X :=
        (integral_map_of_stronglyMeasurable hXa hHsm).symm
      _ = ∫ z, F z ∂((Q.restrict s).map X).prod (Q.map Y) :=
        (integral_prod F hprod_s).symm
      _ = ∫ ω in s, F (X ω, Y ω) ∂Q := by
        rw [← hmaps]
        exact integral_map_of_stronglyMeasurable (hXa.prodMk hY) hF
  · exact (hHsm.comp_measurable hX).aestronglyMeasurable

/-- The preceding averaging principle with a merely almost-everywhere
past-measurable state, as needed for genuine `L²` representatives. The
conditional mean is measurable from that state alone. -/
theorem condExp_independent_input_state_measurable {Ω A B H : Type*}
    (m : MeasurableSpace Ω) [m0 : MeasurableSpace Ω]
    [NormedAddCommGroup A] [mA : MeasurableSpace A] [BorelSpace A]
    [MeasurableSpace B] [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (hm : m ≤ m0)
    (X : Ω → A) (Y : Ω → B) (hX : AEStronglyMeasurable[m] X Q) (hY : Measurable Y)
    (hi : Indep ((inferInstance : MeasurableSpace B).comap Y) m Q)
    (F : A × B → H) (hF : StronglyMeasurable F)
    (hFi : Integrable (fun ω ↦ F (X ω, Y ω)) Q) :
    AEStronglyMeasurable[mA.comap X] (Q[(fun ω ↦ F (X ω, Y ω)) | m]) Q := by
  let X' := hX.mk X
  have hX' : Measurable[m] X' := hX.stronglyMeasurable_mk.measurable
  have he : (fun ω ↦ F (X ω, Y ω)) =ᵐ[Q] (fun ω ↦ F (X' ω, Y ω)) := by
    filter_upwards [hX.ae_eq_mk] with ω hω
    rw [hω]
  have hFi' := hFi.congr he
  have hc := condExp_independent_input_average m Q hm X' Y hX' hY hi F hF hFi'
  let Havg : A → H := fun x ↦ ∫ y, F (x, y) ∂Q.map Y
  have hHsm : StronglyMeasurable Havg :=
    StronglyMeasurable.integral_prod_right (f := fun x y ↦ F (x, y)) (by
      simpa only [Function.uncurry_def] using hF)
  have hcomap : Measurable[mA.comap X] X := measurable_iff_comap_le.mpr le_rfl
  have hmeas : AEStronglyMeasurable[mA.comap X] (fun ω ↦ Havg (X ω)) Q :=
    (hHsm.comp_measurable hcomap).aestronglyMeasurable
  apply hmeas.congr
  have hc' := (condExp_congr_ae he).trans hc
  filter_upwards [hc', hX.ae_eq_mk] with ω hω hXω
  exact (congrArg Havg hXω).trans hω.symm

end WassersteinMixing
