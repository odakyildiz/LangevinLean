import KineticLangevin.LpDynamics
import UnadjustedLangevin.LpCharacteristic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! # Actual phase laws are continuous under L² phase convergence -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace KineticLangevin
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- Phase representatives are measurable functions on the actual source. -/
theorem measurable_lpPhaseCoe (S : Lp E 2 P × Lp E 2 P) :
    Measurable (lpPhaseCoe P S) :=
  (Lp.stronglyMeasurable S.1).measurable.prodMk (Lp.stronglyMeasurable S.2).measurable

/-- Every dual characteristic function of the actual phase law is
continuous in the pair of actual L² variables. -/
theorem continuous_charFunDual_map_lpPhase (L : (E×E) →L[ℝ] ℝ) :
    Continuous (fun S : Lp E 2 P × Lp E 2 P ↦ charFunDual (P.map (lpPhaseCoe P S)) L) := by
  let L1 := L.comp (ContinuousLinearMap.inl ℝ E E)
  let L2 := L.comp (ContinuousLinearMap.inr ℝ E E)
  let A := L1.compLpL 2 P
  let B := L2.compLpL 2 P
  let scalar : (Lp E 2 P × Lp E 2 P) → Lp ℝ 2 P := fun S ↦ A S.1+B S.2
  have hscalar (S : Lp E 2 P × Lp E 2 P) :
      scalar S =ᵐ[P] fun ω ↦ L (lpPhaseCoe P S ω) := by
    filter_upwards [Lp.coeFn_add (A S.1) (B S.2),
      ContinuousLinearMap.coeFn_compLpL L1 S.1,ContinuousLinearMap.coeFn_compLpL L2 S.2]
      with ω hsum h1 h2
    change (A S.1+B S.2 : Lp ℝ 2 P) ω = _
    simp only [Pi.add_apply] at hsum
    rw [hsum,h1,h2]
    change L (S.1 ω,0)+L (0,S.2 ω)=L (S.1 ω,S.2 ω)
    rw [← map_add]
    congr 1
    simp
  have he (S : Lp E 2 P × Lp E 2 P) :
      charFunDual (P.map (lpPhaseCoe P S)) L = charFun (P.map (scalar S)) 1 := by
    rw [charFunDual_eq_charFun_map_one,Measure.map_map L.continuous.measurable
      (measurable_lpPhaseCoe P S)]
    congr 1
    exact Measure.map_congr (hscalar S).symm
  have hc : Continuous scalar :=
    (A.continuous.comp continuous_fst).add (B.continuous.comp continuous_snd)
  have hh := (ULA.continuous_charFun_map_Lp P (1 : ℝ)).comp hc
  convert hh using 1
  funext S
  exact he S

/-- Vanishing bounded-test errors identify the stationary law of an actual
L² limit. The phase norm is the usual product norm, with no Hilbert-space
structure incorrectly imposed on that product. -/
theorem measure_map_lpPhase_eq_of_bounded_test_error
    (S : Lp E 2 P × Lp E 2 P) (Sn : ℕ → Lp E 2 P × Lp E 2 P)
    (hS : Tendsto Sn atTop (𝓝 S)) (π : Measure (E×E)) [IsFiniteMeasure π]
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hweak : ∀ (F : E×E → ℂ), Measurable F → (∀ z, ‖F z‖≤1) →
      ∀ᶠ n in atTop, ‖(∫ ω,F (lpPhaseCoe P (Sn n) ω) ∂P)-(∫ z,F z ∂π)‖≤δ n) :
    P.map (lpPhaseCoe P S)=π := by
  apply Measure.ext_of_charFunDual
  funext L
  let F : E×E → ℂ := fun z ↦ Complex.exp ((L z : ℂ)*Complex.I)
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hFb (z : E×E) : ‖F z‖≤1 := (Complex.norm_exp_ofReal_mul_I _).le
  have hbound : ∀ᶠ n in atTop,
      ‖charFunDual (P.map (lpPhaseCoe P (Sn n))) L-charFunDual π L‖≤δ n := by
    filter_upwards [hweak F hF hFb] with n hn
    change ‖(∫ z,F z ∂P.map (lpPhaseCoe P (Sn n)))-(∫ z,F z ∂π)‖≤δ n
    rw [integral_map (measurable_lpPhaseCoe P (Sn n)).aemeasurable hF.aestronglyMeasurable]
    exact hn
  have herr := squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _)) hbound hδ
  have htarget : Tendsto (fun n ↦ charFunDual (P.map (lpPhaseCoe P (Sn n))) L)
      atTop (𝓝 (charFunDual π L)) := tendsto_iff_norm_sub_tendsto_zero.mpr herr
  have hactual := ((continuous_charFunDual_map_lpPhase P L).tendsto S).comp hS
  exact tendsto_nhds_unique hactual htarget

end KineticLangevin
