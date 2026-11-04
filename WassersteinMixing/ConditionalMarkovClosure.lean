import WassersteinMixing.ConditionalIndependentAverage
import WassersteinMixing.BoundedComposition
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

/-! # Conditional Markov closure in the true `L²` space

Conditional averages of measurable functions of a state and independent
future input depend only on the state. This property is closed under strong
`L²` limits, allowing actual Euler approximations to establish the diffusion
Markov property.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace WassersteinMixing

variable {Ω A B H : Type*} (m : MeasurableSpace Ω) [m0 : MeasurableSpace Ω]
  [NormedAddCommGroup A] [mA : MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace B] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (hm : m ≤ m0)

/-- Conditional `L²` averaging of an actual state/fresh-input representation
is measurable from the state alone. -/
theorem condExpL2_independent_input_state_measurable
    (X : Ω → A) (Y : Ω → B) (hX : AEStronglyMeasurable[m] X Q) (hY : Measurable Y)
    (hi : Indep ((inferInstance : MeasurableSpace B).comap Y) m Q)
    (Z : Lp H 2 Q) (F : A × B → H) (hF : StronglyMeasurable F)
    (hZ : Z =ᵐ[Q] fun ω ↦ F (X ω, Y ω)) :
    AEStronglyMeasurable[mA.comap X] (condExpL2 H ℝ hm Z : Lp H 2 Q) Q := by
  have hFi : Integrable (fun ω ↦ F (X ω, Y ω)) Q :=
    ((Lp.memLp Z).integrable (by norm_num)).congr hZ
  have hmeas := condExp_independent_input_state_measurable m Q hm X Y hX hY hi F hF hFi
  have hcond : (condExpL2 H ℝ hm Z : Lp H 2 Q) =ᵐ[Q] Q[(fun ω ↦ F (X ω, Y ω)) | m] := by
    have he := (Lp.memLp Z).condExpL2_ae_eq_condExp (𝕜 := ℝ) hm
    rw [Lp.toLp_coeFn] at he
    exact he.trans (condExp_congr_ae hZ)
  exact hmeas.congr hcond.symm

omit [NormedAddCommGroup A] [BorelSpace A] [IsProbabilityMeasure Q] in
/-- The conditional-state property passes through strong `L²` limits. -/
theorem condExpL2_state_measurable_of_tendsto {I : Type*} {l : Filter I} [l.NeBot]
    (X : Ω → A) (hXa : Measurable X)
    (Z : I → Lp H 2 Q) (W : Lp H 2 Q) (hlim : Tendsto Z l (𝓝 W))
    (hZ : ∀ i, AEStronglyMeasurable[mA.comap X] (condExpL2 H ℝ hm (Z i) : Lp H 2 Q) Q) :
    AEStronglyMeasurable[mA.comap X] (condExpL2 H ℝ hm W : Lp H 2 Q) Q := by
  have hclosed : IsClosed {u : Lp H 2 Q | AEStronglyMeasurable[mA.comap X] u Q} :=
    isClosed_aestronglyMeasurable hXa.comap_le
  have ht : Tendsto (fun i ↦ (condExpL2 H ℝ hm (Z i) : Lp H 2 Q)) l
      (𝓝 (condExpL2 H ℝ hm W : Lp H 2 Q)) :=
    continuous_subtype_val.continuousAt.tendsto.comp
      ((condExpL2 H ℝ hm).continuous.continuousAt.tendsto.comp hlim)
  exact hclosed.mem_of_tendsto ht (Eventually.of_forall hZ)

end WassersteinMixing
