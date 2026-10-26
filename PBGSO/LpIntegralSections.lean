import PBGSO.PastAverages
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-! # Actual sections of Bochner integrals in L²
Finite spatial test integrals are bounded linear maps. Fubini and uniqueness
from those tests identify integration of jointly measurable realizations,
including past translation averages without pointwise time regularity.
-/
noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.LpIntegralSections
variable {X R : Type*} [MeasurableSpace X] (ν : Measure X)
  [NormedAddCommGroup R] [InnerProductSpace ℝ R] [CompleteSpace R]

def indicatorCLM (s : Set X) (hs : MeasurableSet s) (hν : ν s ≠ ∞) :
    R →L[ℝ] Lp R 2 ν :=
  LinearMap.mkContinuous
    { toFun := indicatorConstLp 2 hs hν
      map_add' := fun _ _ => indicatorConstLp_add.symm
      map_smul' := by
        intro c a
        apply Lp.ext
        filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hν) (c := c • a),
          indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hν) (c := a),
          Lp.coeFn_smul c (indicatorConstLp 2 hs hν a)] with x hx hy hz
        simp only [RingHom.id_apply]
        rw [hx, hz]
        simp only [Pi.smul_apply, hy]
        by_cases hxs : x ∈ s <;> simp [hxs] }
    (ν.real s ^ (1 / (2 : ℝ))) (by
      intro a
      change ‖indicatorConstLp 2 hs hν a‖ ≤ _
      simpa only [ENNReal.toReal_ofNat, mul_comm] using
        (norm_indicatorConstLp_le (p := 2) (hs := hs) (hμs := hν) (c := a)))

def setIntegralCLM (s : Set X) (hs : MeasurableSet s) (hν : ν s ≠ ∞) :
    Lp R 2 ν →L[ℝ] R := (indicatorCLM ν s hs hν).adjoint

theorem setIntegralCLM_apply (s : Set X) (hs : MeasurableSet s) (hν : ν s ≠ ∞)
    (U : Lp R 2 ν) : setIntegralCLM ν s hs hν U = ∫ x in s, U x ∂ν := by
  apply ext_inner_left ℝ
  intro a
  rw [setIntegralCLM, ContinuousLinearMap.adjoint_inner_right]
  exact L2.inner_indicatorConstLp_eq_inner_setIntegral ℝ hs hν a U

theorem integral_norm_le (s : Set X) (hs : MeasurableSet s) (hν : ν s ≠ ∞)
    (U : Lp R 2 ν) :
    ∫ x in s, ‖U x‖ ∂ν ≤ ‖setIntegralCLM (R := ℝ) ν s hs hν‖ * ‖U‖ := by
  let V : Lp ℝ 2 ν := (Lp.memLp U).norm.toLp (fun x => ‖U x‖)
  have hV : ‖V‖ = ‖U‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm _ (Lp.aestronglyMeasurable U), Lp.norm_def]
  have hi : setIntegralCLM ν s hs hν V = ∫ x in s, ‖U x‖ ∂ν := by
    rw [setIntegralCLM_apply]
    exact integral_congr_ae (ae_restrict_of_ae (MemLp.coeFn_toLp (Lp.memLp U).norm))
  calc
    ∫ x in s, ‖U x‖ ∂ν ≤ ‖∫ x in s, ‖U x‖ ∂ν‖ := le_abs_self _
    _ ≤ ‖setIntegralCLM (R := ℝ) ν s hs hν‖ * ‖U‖ := by
      rw [← hi, ← hV]
      exact (setIntegralCLM (R := ℝ) ν s hs hν).le_opNorm V

section Sections
variable {T : Type*} [MeasurableSpace T] (μ : Measure T) [SFinite μ] [SigmaFinite ν]

/-- A jointly measurable realization of an L¹ family of L² variables is integrable
on every finite-measure spatial test set. -/
theorem integrable_restrict_prod (F : T → Lp R 2 ν) (hF : Integrable F μ)
    (g : T → X → R) (hg : AEStronglyMeasurable (Function.uncurry g) (μ.prod ν))
    (hsec : ∀ᵐ t ∂μ, g t =ᵐ[ν] F t)
    (s : Set X) (hs : MeasurableSet s) (hν : ν s ≠ ∞) :
    Integrable (Function.uncurry g) (μ.prod (ν.restrict s)) := by
  have hm : AEStronglyMeasurable (Function.uncurry g) (μ.prod (ν.restrict s)) :=
    hg.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [hsec] with t ht
    exact (integrableOn_Lp_of_measure_ne_top (F t) (by norm_num) hν).congr
      (ae_restrict_of_ae ht.symm)
  · apply (hF.norm.const_mul ‖setIntegralCLM (R := ℝ) ν s hs hν‖).mono'
      hm.norm.integral_prod_right'
    filter_upwards [hsec] with t ht
    have ht' : ∀ᵐ x ∂ν.restrict s, ‖g t x‖ = ‖F t x‖ := by
      filter_upwards [ae_restrict_of_ae ht] with x hx using congrArg norm hx
    simp only [Function.uncurry_apply_pair]
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _),
      integral_congr_ae ht']
    exact integral_norm_le ν s hs hν (F t)

/-- Bochner integration in L² agrees almost everywhere with integrating any
jointly measurable realization. All integrability statements follow from L¹(L²). -/
theorem integral_coe_ae (F : T → Lp R 2 ν) (hF : Integrable F μ)
    (g : T → X → R) (hg : AEStronglyMeasurable (Function.uncurry g) (μ.prod ν))
    (hsec : ∀ᵐ t ∂μ, g t =ᵐ[ν] F t) :
    (∫ t, F t ∂μ) =ᵐ[ν] (fun x => ∫ t, g t x ∂μ) := by
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro s hs hν
    exact integrableOn_Lp_of_measure_ne_top _ (by norm_num) hν.ne
  · intro s hs hν
    exact (integrable_restrict_prod ν μ F hF g hg hsec s hs hν.ne).integral_prod_right
  · intro s hs hν
    have hi := integrable_restrict_prod ν μ F hF g hg hsec s hs hν.ne
    calc
      (∫ x in s, (∫ t, F t ∂μ) x ∂ν) =
          setIntegralCLM ν s hs hν.ne (∫ t, F t ∂μ) :=
        (setIntegralCLM_apply ν s hs hν.ne _).symm
      _ = ∫ t, setIntegralCLM ν s hs hν.ne (F t) ∂μ :=
        ((setIntegralCLM ν s hs hν.ne).integral_comp_comm hF).symm
      _ = ∫ t, ∫ x in s, g t x ∂ν ∂μ := by
        apply integral_congr_ae
        filter_upwards [hsec] with t ht
        rw [setIntegralCLM_apply]
        exact integral_congr_ae (ae_restrict_of_ae ht.symm)
      _ = ∫ x in s, ∫ t, g t x ∂μ ∂ν := integral_integral_swap hi
end Sections

/-- The literal time-L² past average has the continuous moving-integral
representative. This statement assumes no pointwise time regularity of U. -/
theorem average_coe_ae (U : PastAverages.TimeLp (R := R)) (ε : ℝ) (hε : 0 < ε) :
    PastAverages.average U ε =ᵐ[volume] PastAverages.pastMean U ε := by
  have hi : Integrable (PastAverages.shift U) (volume.restrict (Ioc 0 ε)) :=
    ((PastAverages.shift_continuous U).intervalIntegrable 0 ε).1
  have hm : StronglyMeasurable (fun p : ℝ × ℝ => U (p.2 - p.1)) :=
    (Lp.stronglyMeasurable U).comp_measurable (measurable_snd.sub measurable_fst)
  have he := integral_coe_ae (volume : Measure ℝ) (volume.restrict (Ioc 0 ε))
    (PastAverages.shift U) hi (fun r t => U (t - r)) hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun r => (PastAverages.shift_coe U r).symm)
  have hsm := Lp.coeFn_smul ε⁻¹ (∫ r in Ioc 0 ε, PastAverages.shift U r)
  filter_upwards [he, hsm] with t ht hst
  change (ε⁻¹ • ∫ r in 0..ε, PastAverages.shift U r) t = _
  rw [intervalIntegral.integral_of_le hε.le, hst]
  simp only [Pi.smul_apply]
  rw [ht, ← intervalIntegral.integral_of_le hε.le,
    intervalIntegral.integral_comp_sub_left, sub_zero]
  rfl
end PBGSO.LpIntegralSections
