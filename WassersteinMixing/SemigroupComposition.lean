import WassersteinMixing.SemigroupGlobal
import WassersteinMixing.ActualAdapted
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

/-! # The observable algebra of the actual Markov composition law

The initial evaluation is measurable in every later actual Brownian past.
Consequently the actual conditional Markov identity implies composition of
the actual compressed operators, by the defining orthogonality identity of
conditional expectation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set

namespace WassersteinMixing.CanonicalSemigroup

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- An initial observable belongs to every later actual Brownian past. -/
theorem evaluation_zero_adapted_pastAt (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (a : ℝ) (f : Lp F 2 (ULA.gibbsMeasure V)) :
    AEStronglyMeasurable[ULA.lpLangevinPast (actualProbability P V)
      (initial P V hV) (actualBrownianNoise P V hV) a]
      (evaluation (𝕜 := ℝ) P V hV 0 f) (actualProbability P V) := by
  have hx : MeasurePreserving (state P V hV 0)
      (actualProbability P V) (ULA.gibbsMeasure V) :=
    ⟨(Lp.stronglyMeasurable _).measurable, state_law P V hV 0⟩
  have hi : AEStronglyMeasurable[ULA.lpLangevinPast (actualProbability P V)
      (initial P V hV) (actualBrownianNoise P V hV) a]
      (state P V hV 0) (actualProbability P V) := by
    rw [state_zero]
    exact ULA.lpLangevinPast_initial _ _ _ _
  have hf := (Lp.stronglyMeasurable f).comp_measurable hi.measurable_mk
  apply hf.aestronglyMeasurable.congr
  exact (hi.ae_eq_mk.fun_comp f).symm.trans (Lp.coeFn_compMeasurePreserving f hx).symm

/-- The conditional Markov identity gives the actual composition law.
This is the short algebraic step used after the concrete Brownian proof of
that conditional identity. -/
theorem op_add_of_markov (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (a t : ℝ)
    (hmarkov : ∀ f : Lp F 2 (ULA.gibbsMeasure V),
      (condExpL2 F ℝ (ULA.lpLangevinPast_le (actualProbability P V)
        (initial P V hV) (actualBrownianNoise P V hV) a)
        (evaluation (𝕜 := ℝ) P V hV (a + t) f) : Lp F 2 (actualProbability P V)) =
        evaluation (𝕜 := ℝ) P V hV a (op (𝕜 := ℝ) P V hV t f)) :
    op (𝕜 := ℝ) (F := F) P V hV (a + t) = op P V hV a ∘L op P V hV t := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro g
  change inner ℝ (op (𝕜 := ℝ) P V hV (a + t) f) g =
    inner ℝ (op (𝕜 := ℝ) P V hV a (op (𝕜 := ℝ) P V hV t f)) g
  dsimp only [op]
  rw [ObservableTransition.compression_inner, ObservableTransition.compression_inner]
  have h := inner_condExpL2_eq_inner_fun (𝕜 := ℝ)
    (ULA.lpLangevinPast_le (actualProbability P V) (initial P V hV)
      (actualBrownianNoise P V hV) a)
    (evaluation (𝕜 := ℝ) P V hV (a + t) f) (evaluation P V hV 0 g)
    (evaluation_zero_adapted_pastAt P V hV a g)
  rw [hmarkov f] at h
  exact h.symm

end WassersteinMixing.CanonicalSemigroup
