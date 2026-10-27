import AverageLMC.SquaredTransport
import UnadjustedLangevin.TransportMoments
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space

set_option linter.style.header false

/-! # Quadratic transport under a conditionally centered perturbation

Disintegration lifts every full-gradient output coupling to the original input
space. Independent centered index noise then has an exactly vanishing cross
term. Taking the coupling infimum gives the variance-addition estimate needed
by SGLD, without an optimal coupling hypothesis.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace AverageLMC

variable {Ω S I E : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [StandardBorelSpace E]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [StandardBorelSpace E] in
theorem eLpNorm_toReal_sq_eq_integral (P : Measure Ω) (f : Ω → E) (hf : MemLp f 2 P) :
    (eLpNorm f 2 P).toReal ^ 2 = ∫ ω, ‖f ω‖ ^ 2 ∂P := by
  calc
    _ = ‖hf.toLp f‖ ^ 2 := by rw [Lp.norm_toLp]
    _ = ∫ ω, inner ℝ (hf.toLp f ω) (hf.toLp f ω) ∂P := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with ω hω
      rw [hω, real_inner_self_eq_norm_sq]

/-- The actual variance-addition transport estimate for centered independent
index perturbations. Every distribution and lift is constructed in the proof. -/
theorem wasserstein2_sq_centered_perturbation
    (P : Measure S) [IsProbabilityMeasure P] (Q : Measure I) [IsProbabilityMeasure Q]
    (F : S → E) (hF : Measurable F) (hF2 : MemLp F 2 P)
    (D : S → I → E) (hD : Measurable (Function.uncurry D))
    (hD2 : MemLp (Function.uncurry D) 2 (P.prod Q))
    (hDi : ∀ s, Integrable (D s) Q) (hmean : ∀ s, ∫ i, D s i ∂Q = 0)
    (π : Measure E) [IsProbabilityMeasure π] (hπ : MemLp (fun x : E ↦ x) 2 π) :
    ULA.wasserstein2Real ((P.prod Q).map (fun q ↦ F q.1 + D q.1 q.2)) π ^ 2 ≤
      ULA.wasserstein2Real (P.map F) π ^ 2 +
        ∫ q : S × I, ‖D q.1 q.2‖ ^ 2 ∂P.prod Q := by
  let ν := (P.prod Q).map (fun q : S × I ↦ F q.1 + D q.1 q.2)
  have hFm : MemLp (fun x : E ↦ x) 2 (P.map F) := by
    exact (memLp_map_measure_iff (by fun_prop) hF.aemeasurable).mpr hF2
  have hplus : MemLp (fun q : S × I ↦ F q.1 + D q.1 q.2) 2 (P.prod Q) :=
    (hF2.comp_fst Q).add hD2
  have hν : MemLp (fun x : E ↦ x) 2 ν :=
    (memLp_map_measure_iff (by fun_prop) (by fun_prop)).mpr hplus
  have hfinite := ULA.wasserstein2_ne_top_of_memLp (P.map F) π hFm hπ
  have houtput := ULA.wasserstein2_ne_top_of_memLp ν π hν hπ
  suffices h : ULA.wasserstein2Real ν π ^ 2 ≤
      1 * ULA.wasserstein2Real (P.map F) π ^ 2 +
        ∫ q : S × I, ‖D q.1 q.2‖ ^ 2 ∂P.prod Q by simpa only [one_mul] using h
  apply wasserstein2_sq_bound_of_finite_couplings (P.map F) π ν π 1
    (∫ q : S × I, ‖D q.1 q.2‖ ^ 2 ∂P.prod Q) hfinite houtput
  intro c hc
  have := c.isProbabilityMeasure
  let R := liftedOutputCoupling P F hF c
  have hRfst : R.map Prod.fst = P := liftedOutputCoupling_fst P F hF c
  have hRout : R.map (fun q : S × E ↦ (F q.1, q.2)) = c.joint :=
    liftedOutputCoupling_output P F hF c
  have hRsnd : R.map Prod.snd = π := liftedOutputCoupling_snd P F hF c
  have hRI : (R.prod Q).map (fun q : (S × E) × I ↦ (q.1.1, q.2)) = P.prod Q := by
    have hm := (Measure.map_prod_map R Q measurable_fst measurable_id).symm
    rw [hRfst, Measure.map_id] at hm
    convert hm using 1
    apply congrArg (fun f : (S × E) × I → S × I ↦ (R.prod Q).map f)
    funext q
    rfl
  have hAc : MemLp (fun q : E × E ↦ q.1 - q.2) 2 c.joint :=
    lt_top_iff_ne_top.mpr hc
  have hAR : MemLp (fun q : S × E ↦ F q.1 - q.2) 2 R := by
    rw [← hRout] at hAc
    simpa only [Function.comp_def] using hAc.comp_of_map (by fun_prop)
  let A : (S × E) × I → E := fun q ↦ F q.1.1 - q.1.2
  let B : (S × E) × I → E := fun q ↦ D q.1.1 q.2
  have hA : MemLp A 2 (R.prod Q) := hAR.comp_fst Q
  have hB : MemLp B 2 (R.prod Q) := by
    rw [← hRI] at hD2
    simpa only [Function.comp_def, Function.uncurry_apply_pair] using
      hD2.comp_of_map (by fun_prop)
  have hAm : Measurable A := by dsimp [A]; fun_prop
  have hBm : Measurable B := by
    exact hD.comp (measurable_fst.fst.prodMk measurable_snd)
  have hcross : Integrable (fun q ↦ inner ℝ (A q) (B q)) (R.prod Q) :=
    (hA.norm.integrable_mul hB.norm).mono' (by fun_prop)
      (Filter.Eventually.of_forall fun q ↦ abs_real_inner_le_norm (A q) (B q))
  have hzero : (∫ q, inner ℝ (A q) (B q) ∂R.prod Q) = 0 := by
    rw [integral_prod _ hcross]
    have hz (r : S × E) : (∫ i, inner ℝ (F r.1 - r.2) (D r.1 i) ∂Q) = 0 := by
      have hi := (innerSL ℝ (F r.1 - r.2)).integral_comp_comm (hDi r.1)
      simpa only [innerSL_apply_apply, hmean, inner_zero_right] using hi
    simp only [A, B, hz, integral_zero]
  have hsumint := (hA.add hB).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hAint := hA.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hBint := hB.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have henergy : (∫ q, ‖A q + B q‖ ^ 2 ∂R.prod Q) =
      (∫ q, ‖A q‖ ^ 2 ∂R.prod Q) + (∫ q, ‖B q‖ ^ 2 ∂R.prod Q) := by
    simp_rw [norm_add_sq_real]
    rw [integral_add (f := fun q ↦ ‖A q‖ ^ 2 + 2 * inner ℝ (A q) (B q))
        (g := fun q ↦ ‖B q‖ ^ 2) (hAint.add (hcross.const_mul 2)) hBint,
      integral_add (f := fun q ↦ ‖A q‖ ^ 2)
        (g := fun q ↦ 2 * inner ℝ (A q) (B q)) hAint (hcross.const_mul 2),
      integral_const_mul, hzero, mul_zero, add_zero]
  have hAcost : (∫ q, ‖A q‖ ^ 2 ∂R.prod Q) = (ULA.couplingCost c.joint).toReal ^ 2 := by
    change (∫ q : (S × E) × I, ‖F q.1.1 - q.1.2‖ ^ 2 ∂R.prod Q) = _
    have hf := integral_fun_fst (μ := R) (ν := Q) (fun r : S × E ↦ ‖F r.1 - r.2‖ ^ 2)
    simp only [probReal_univ, one_smul] at hf
    rw [hf]
    have hi := integral_map (μ := R) (φ := fun q : S × E ↦ (F q.1, q.2))
      (by fun_prop) (by fun_prop : AEStronglyMeasurable (fun q : E × E ↦ ‖q.1 - q.2‖ ^ 2) (R.map (fun q : S × E ↦ (F q.1, q.2))))
    rw [hRout] at hi
    exact hi.symm.trans (eLpNorm_toReal_sq_eq_integral c.joint _ hAc).symm
  have hBcost : (∫ q, ‖B q‖ ^ 2 ∂R.prod Q) =
      ∫ q : S × I, ‖D q.1 q.2‖ ^ 2 ∂P.prod Q := by
    rw [← hRI, integral_map (by fun_prop) (by fun_prop)]
  have hXlaw : (R.prod Q).map (fun q : (S × E) × I ↦ F q.1.1 + D q.1.1 q.2) = ν := by
    dsimp only [ν]
    rw [← hRI, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hYlaw : (R.prod Q).map (fun q : (S × E) × I ↦ q.1.2) = π := by
    rw [← Function.comp_def, ← Measure.map_map measurable_snd measurable_fst,
      Measure.map_fst_prod]
    simpa only [measure_univ, one_smul] using hRsnd
  have hw := ULA.wasserstein2_le_random_cost_real (R.prod Q)
    (fun q : (S × E) × I ↦ F q.1.1 + D q.1.1 q.2)
    (fun q ↦ q.1.2) (by fun_prop) (by fun_prop)
    ((hA.add hB).ae_eq (Filter.Eventually.of_forall fun q ↦ by dsimp [A, B]; abel))
  rw [hXlaw, hYlaw] at hw
  have hs := (sq_le_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).mpr hw
  rw [eLpNorm_toReal_sq_eq_integral] at hs
  · have heq (q : (S × E) × I) :
        F q.1.1 + D q.1.1 q.2 - q.1.2 = A q + B q := by dsimp [A, B]; abel
    simp_rw [heq] at hs
    simpa only [henergy, hAcost, hBcost, one_mul, ULA.wasserstein2Real] using hs
  · exact (hA.add hB).ae_eq (Filter.Eventually.of_forall fun q ↦ by dsimp [A, B]; abel)

end AverageLMC
