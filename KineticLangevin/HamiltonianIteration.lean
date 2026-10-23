import KineticLangevin.HamiltonianTests
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! # Iterated weak error and exact invariance of a limiting flow -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal ENNReal
namespace KineticLangevin
variable {H : Type*} [MeasurableSpace H]

/-- Telescoping bounded tests uses the fixed invariant initial measure at
every increment, so the weak error grows only linearly in the number of steps. -/
theorem correctedMeasure_iterate_weak_error (π : Measure H) [IsFiniteMeasure π]
    (V R : H → H) (hV : Measurable V) (hR : Measurable R)
    (a : H → ℝ) (ha : Measurable a) (ha0 : ∀ z, 0 ≤ a z) (ha1 : ∀ z, a z ≤ 1)
    (hstationary : (π.withDensity (fun z ↦ ENNReal.ofReal (a z))).map V +
      (π.withDensity (fun z ↦ ENNReal.ofReal (1-a z))).map R = π)
    (F : H → ℂ) (hF : Measurable F) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ z, ‖F z‖ ≤ C) (n : ℕ) :
    ‖(∫ z, F (V^[n] z) ∂π)-(∫ z, F z ∂π)‖ ≤
      (n : ℝ)*(2*C)*(∫ z, 1-a z ∂π) := by
  induction n with
  | zero => simp
  | succ n ih =>
      let G := F ∘ V^[n]
      have hG : Measurable G := hF.comp (hV.iterate n)
      have hGb (z : H) : ‖G z‖ ≤ C := hbound _
      have hs := correctedMeasure_weak_error π V R hV hR a ha ha0 ha1
        hstationary G hG C hC hGb
      have hs' : ‖(∫ z, F (V^[n+1] z) ∂π)-(∫ z, F (V^[n] z) ∂π)‖ ≤
          2*C*(∫ z, 1-a z ∂π) := by
        simpa only [G,Function.comp_def,Function.iterate_succ_apply] using hs
      calc
        _ ≤ ‖(∫ z, F (V^[n+1] z) ∂π)-(∫ z, F (V^[n] z) ∂π)‖ +
          ‖(∫ z, F (V^[n] z) ∂π)-(∫ z, F z ∂π)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 2*C*(∫ z, 1-a z ∂π)+(n : ℝ)*(2*C)*(∫ z, 1-a z ∂π) :=
          add_le_add hs' ih
        _ = _ := by push_cast; ring

section Limit
variable [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  [BorelSpace H] [SecondCountableTopology H]

/-- Pointwise convergence and vanishing bounded-test error identify the
actual limiting pushforward with the fixed finite measure. -/
theorem measure_map_eq_of_bounded_test_error_tendsto
    (π : Measure H) [IsFiniteMeasure π] (Y : H → H) (hY : Measurable Y)
    (Yn : ℕ → H → H) (hYn : ∀ n, Measurable (Yn n))
    (hconv : ∀ z, Tendsto (fun n ↦ Yn n z) atTop (𝓝 (Y z)))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hweak : ∀ (F : H → ℂ), Measurable F → (∀ z, ‖F z‖ ≤ 1) →
      ∀ᶠ n in atTop, ‖(∫ z, F (Yn n z) ∂π)-(∫ z, F z ∂π)‖ ≤ δ n) :
    π.map Y = π := by
  apply Measure.ext_of_charFunDual
  funext L
  let F : H → ℂ := fun z ↦ Complex.exp ((L z : ℂ)*Complex.I)
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hFb (z : H) : ‖F z‖ ≤ 1 := (Complex.norm_exp_ofReal_mul_I _).le
  have hactual : Tendsto (fun n ↦ ∫ z, F (Yn n z) ∂π) atTop
      (𝓝 (∫ z, F (Y z) ∂π)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ 1)
    · intro n
      exact (hF.measurable.comp (hYn n)).aestronglyMeasurable
    · exact integrable_const 1
    · intro n
      exact ae_of_all _ fun z ↦ hFb _
    · exact ae_of_all _ fun z ↦ hF.continuousAt.tendsto.comp (hconv z)
  have herr : Tendsto (fun n ↦ ‖(∫ z, F (Yn n z) ∂π)-(∫ z, F z ∂π)‖)
      atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _))
      (hweak F hF.measurable hFb) hδ
  have htarget : Tendsto (fun n ↦ ∫ z, F (Yn n z) ∂π) atTop
      (𝓝 (∫ z, F z ∂π)) := tendsto_iff_norm_sub_tendsto_zero.mpr herr
  have he := tendsto_nhds_unique hactual htarget
  rw [charFunDual_apply,charFunDual_apply,integral_map hY.aemeasurable (by fun_prop)]
  exact he

end Limit
end KineticLangevin
