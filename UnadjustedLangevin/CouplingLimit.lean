import UnadjustedLangevin.LpCharacteristic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

set_option linter.style.header false

/-! # Equality of a limiting law and an asymptotically coupled fixed law

Characteristic tests are Lipschitz. Couplings whose expected distance tends to
zero force characteristic-function convergence to their fixed second marginal.
An actual `L²` limit supplies the same limiting characteristic function, so the
limiting law is exactly that marginal.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace ULA

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

omit [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
/-- At a fixed frequency the real-Hilbert characteristic test is Lipschitz
with constant the norm of that frequency. -/
theorem characteristicTest_norm_sub_le (t x y : H) :
    ‖Complex.exp ((inner ℝ x t : ℂ) * Complex.I) -
      Complex.exp ((inner ℝ y t : ℂ) * Complex.I)‖ ≤ ‖t‖ * ‖x - y‖ := by
  have hunit : Real.nnabs (1 : ℝ) = 1 := by apply NNReal.eq; norm_num
  have hc := (lipschitzWith_circleMap (0 : ℂ) 1).norm_sub_le (inner ℝ x t) (inner ℝ y t)
  rw [hunit, NNReal.coe_one, one_mul] at hc
  simp only [circleMap, Complex.ofReal_one, one_mul, zero_add] at hc
  calc
    _ ≤ |inner ℝ x t - inner ℝ y t| := hc
    _ = |inner ℝ (x - y) t| := by rw [inner_sub_left]
    _ ≤ ‖x - y‖ * ‖t‖ := abs_real_inner_le_norm _ _
    _ = _ := mul_comm _ _

/-- Any actual coupling controls the difference between its marginal
characteristic functions by its ordinary expected distance. -/
theorem charFun_marginals_norm_sub_le
    (ρ : Measure (H × H)) [IsProbabilityMeasure ρ]
    (hint : Integrable (fun p : H × H ↦ ‖p.1 - p.2‖) ρ) (t : H) :
    ‖charFun (ρ.map Prod.fst) t - charFun (ρ.map Prod.snd) t‖ ≤
      ‖t‖ * ∫ p : H × H, ‖p.1 - p.2‖ ∂ρ := by
  have hf : Integrable (fun p : H × H ↦
      Complex.exp ((inner ℝ p.1 t : ℂ) * Complex.I)) ρ :=
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun p ↦
      (Complex.norm_exp_ofReal_mul_I (inner ℝ p.1 t)).le)
  have hg : Integrable (fun p : H × H ↦
      Complex.exp ((inner ℝ p.2 t : ℂ) * Complex.I)) ρ :=
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun p ↦
      (Complex.norm_exp_ofReal_mul_I (inner ℝ p.2 t)).le)
  rw [charFun_apply, charFun_apply,
    integral_map measurable_fst.aemeasurable (by fun_prop),
    integral_map measurable_snd.aemeasurable (by fun_prop), ← integral_sub hf hg]
  calc
    _ ≤ ∫ p : H × H, ‖Complex.exp ((inner ℝ p.1 t : ℂ) * Complex.I) -
        Complex.exp ((inner ℝ p.2 t : ℂ) * Complex.I)‖ ∂ρ := norm_integral_le_integral_norm _
    _ ≤ ∫ p : H × H, ‖t‖ * ‖p.1 - p.2‖ ∂ρ :=
      integral_mono (hf.sub hg).norm (hint.const_mul ‖t‖)
        (fun p ↦ characteristicTest_norm_sub_le t p.1 p.2)
    _ = _ := integral_const_mul _ _

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

omit [SecondCountableTopology H] in
/-- Characteristic functions of Hilbert-valued random variables are continuous
in their actual `L²` classes, at every fixed frequency. -/
theorem continuous_charFun_map_Lp_hilbert (t : H) :
    Continuous (fun X : Lp H 2 P ↦ charFun (P.map X) t) := by
  let L : H →L[ℝ] ℝ := innerSL ℝ t
  have heq (X : Lp H 2 P) :
      charFun (P.map X) t = charFun (P.map (L.compLp X)) (1 : ℝ) := by
    rw [charFun_map_eq_charFun_map_inner_one (Lp.aestronglyMeasurable X).aemeasurable t]
    congr 1
    apply Measure.map_congr
    filter_upwards [L.coeFn_compLp X] with ω hω
    simpa only [L, innerSL_apply_apply, real_inner_comm] using hω.symm
  have hc := (continuous_charFun_map_Lp P (1 : ℝ)).comp (L.compLpL 2 P).continuous
  convert hc using 1
  funext X
  exact heq X

variable [CompleteSpace H]

/-- If actual `L²` endpoint variables converge and their laws admit couplings
with a fixed probability law whose expected distances tend to zero, their
limit has exactly that fixed law. No density or optimal-transport premise is
needed. -/
theorem measure_map_Lp_eq_of_coupling_cost_tendsto
    {ι : Type*} {l : Filter ι} [NeBot l]
    (Xn : ι → Lp H 2 P) (X : Lp H 2 P)
    (π : Measure H) [IsProbabilityMeasure π]
    (ρ : ι → Measure (H × H)) [∀ i, IsProbabilityMeasure (ρ i)]
    (hX : Tendsto Xn l (𝓝 X))
    (hfst : ∀ i, (ρ i).map Prod.fst = P.map (Xn i))
    (hsnd : ∀ i, (ρ i).map Prod.snd = π)
    (hint : ∀ i, Integrable (fun p : H × H ↦ ‖p.1 - p.2‖) (ρ i))
    (hcost : Tendsto (fun i ↦ ∫ p : H × H, ‖p.1 - p.2‖ ∂ρ i) l (𝓝 0)) :
    P.map X = π := by
  apply Measure.ext_of_charFun
  funext t
  have hactual := ((continuous_charFun_map_Lp_hilbert P t).tendsto X).comp hX
  have hbound (i : ι) : ‖charFun (P.map (Xn i)) t - charFun π t‖ ≤
      ‖t‖ * ∫ p : H × H, ‖p.1 - p.2‖ ∂ρ i := by
    simpa only [hfst i, hsnd i] using charFun_marginals_norm_sub_le (ρ i) (hint i) t
  have hnorm : Tendsto (fun i ↦ ‖charFun (P.map (Xn i)) t - charFun π t‖) l (𝓝 0) := by
    apply squeeze_zero (fun _ ↦ norm_nonneg _) hbound
    simpa only [mul_zero] using hcost.const_mul ‖t‖
  have htarget : Tendsto (fun i ↦ charFun (P.map (Xn i)) t) l (𝓝 (charFun π t)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
  exact tendsto_nhds_unique hactual htarget

end ULA
