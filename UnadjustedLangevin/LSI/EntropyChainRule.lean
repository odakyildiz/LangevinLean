import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option linter.style.header false

/-! # A time-integrated chain rule without a common spatial majorant

Pointwise time differentiation and spacetime `L¹` of the derivative suffice
to commute spatial integration with the fundamental theorem of calculus.
The resulting integral path is absolutely continuous and has the expected
derivative almost everywhere. This is the form needed for bounded entropy
truncations: no bound on all time derivatives by one spatial function is used.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace ULA.LSI

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Spatial integration commutes with the time fundamental theorem under
joint `L¹` of the time derivative. Integrability at the terminal time follows
from integrability at the initial time and is not a separate hypothesis. -/
theorem integral_eq_initial_add_integral_of_spacetime_integrable
    (ν : Measure Ω) [SFinite ν] (f fdot : ℝ → Ω → ℝ)
    (a b : ℝ) (hab : a ≤ b) (hfa : Integrable (f a) ν)
    (hdot : Integrable (fun p : ℝ × Ω ↦ fdot p.1 p.2)
      ((volume.restrict (Ioc a b)).prod ν))
    (hderiv : ∀ᵐ x ∂ν, ∀ t ∈ Icc a b,
      HasDerivAt (fun u ↦ f u x) (fdot t x) t) :
    Integrable (f b) ν ∧
      (∫ x, f b x ∂ν) = (∫ x, f a x ∂ν) +
        ∫ t in a..b, ∫ x, fdot t x ∂ν := by
  have hinner : Integrable (fun x ↦ ∫ t in Ioc a b, fdot t x) ν :=
    hdot.integral_prod_right
  have hpoint : f b =ᵐ[ν] fun x ↦ f a x + ∫ t in Ioc a b, fdot t x := by
    filter_upwards [hdot.prod_left_ae, hderiv] with x hx hd
    have hinterval : IntervalIntegrable (fun t ↦ fdot t x) volume a b := by
      rw [intervalIntegrable_iff, uIoc_of_le hab]
      exact hx
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht ↦ hd t (by simpa only [uIcc_of_le hab] using ht)) hinterval
    rw [intervalIntegral.integral_of_le hab] at hFTC
    linarith
  refine ⟨(hfa.add hinner).congr hpoint.symm, ?_⟩
  rw [integral_congr_ae hpoint, integral_add hfa hinner,
    intervalIntegral.integral_of_le hab]
  congr 1
  exact (integral_integral_swap hdot).symm

/-- The full spatially integrated path is absolutely continuous on a time
interval when its pointwise time derivative belongs to spacetime `L¹`. -/
theorem absolutelyContinuous_integral_of_spacetime_integrable
    (ν : Measure Ω) [SFinite ν] (f fdot : ℝ → Ω → ℝ)
    (a b : ℝ) (hab : a ≤ b) (hfa : Integrable (f a) ν)
    (hdot : Integrable (fun p : ℝ × Ω ↦ fdot p.1 p.2)
      ((volume.restrict (Ioc a b)).prod ν))
    (hderiv : ∀ᵐ x ∂ν, ∀ t ∈ Icc a b,
      HasDerivAt (fun u ↦ f u x) (fdot t x) t) :
    (∀ t ∈ Icc a b, Integrable (f t) ν) ∧
      AbsolutelyContinuousOnInterval (fun t ↦ ∫ x, f t x ∂ν) a b := by
  have hFTC (t : ℝ) (ht : t ∈ Icc a b) :
      Integrable (f t) ν ∧
        (∫ x, f t x ∂ν) = (∫ x, f a x ∂ν) +
          ∫ u in a..t, ∫ x, fdot u x ∂ν := by
    have hrestrict : volume.restrict (Ioc a t) ≤ volume.restrict (Ioc a b) :=
      Measure.restrict_mono (Ioc_subset_Ioc_right ht.2) le_rfl
    apply integral_eq_initial_add_integral_of_spacetime_integrable ν f fdot a t ht.1 hfa
      (hdot.mono_measure (Measure.prod_mono hrestrict le_rfl))
    filter_upwards [hderiv] with x hx u hu
    exact hx u ⟨hu.1, hu.2.trans ht.2⟩
  refine ⟨fun t ht ↦ (hFTC t ht).1, ?_⟩
  have hq : IntervalIntegrable (fun t ↦ ∫ x, fdot t x ∂ν) volume a b := by
    rw [intervalIntegrable_iff, uIoc_of_le hab]
    exact hdot.integral_prod_left
  have hac := hq.absolutelyContinuousOnInterval_intervalIntegral
    (show a ∈ uIcc a b by rw [uIcc_of_le hab]; exact ⟨le_rfl, hab⟩)
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ ∫ x, f a x ∂ν) a b :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ ↦ ∫ x, f a x ∂ν)).contDiffOn
      |>.absolutelyContinuousOnInterval
  apply (hc.add hac).congr
  intro t ht
  exact (hFTC t (by simpa only [uIcc_of_le hab] using ht)).2.symm

/-- The a.e. derivative of the spatial integral is the spatial integral of
the pointwise time derivative, under spacetime `L¹`. This follows from Fubini,
FTC and Lebesgue differentiation rather than pointwise domination in time. -/
theorem integral_hasDerivAt_ae_of_spacetime_integrable
    (ν : Measure Ω) [SFinite ν] (f fdot : ℝ → Ω → ℝ)
    (a b : ℝ) (hab : a ≤ b) (hfa : Integrable (f a) ν)
    (hdot : Integrable (fun p : ℝ × Ω ↦ fdot p.1 p.2)
      ((volume.restrict (Ioc a b)).prod ν))
    (hderiv : ∀ᵐ x ∂ν, ∀ t ∈ Icc a b,
      HasDerivAt (fun u ↦ f u x) (fdot t x) t) :
    ∀ᵐ t ∂volume, t ∈ Ioo a b →
      HasDerivAt (fun u ↦ ∫ x, f u x ∂ν) (∫ x, fdot t x ∂ν) t := by
  have hFTC (t : ℝ) (ht : t ∈ Icc a b) :
      (∫ x, f t x ∂ν) = (∫ x, f a x ∂ν) +
        ∫ u in a..t, ∫ x, fdot u x ∂ν := by
    have hrestrict : volume.restrict (Ioc a t) ≤ volume.restrict (Ioc a b) :=
      Measure.restrict_mono (Ioc_subset_Ioc_right ht.2) le_rfl
    apply (integral_eq_initial_add_integral_of_spacetime_integrable ν f fdot a t ht.1 hfa
      (hdot.mono_measure (Measure.prod_mono hrestrict le_rfl)) ?_).2
    filter_upwards [hderiv] with x hx u hu
    exact hx u ⟨hu.1, hu.2.trans ht.2⟩
  have hq : IntervalIntegrable (fun t ↦ ∫ x, fdot t x ∂ν) volume a b := by
    rw [intervalIntegrable_iff, uIoc_of_le hab]
    exact hdot.integral_prod_left
  filter_upwards [hq.ae_hasDerivAt_integral] with t ht htIoo
  have hbase := ht (by rw [uIcc_of_le hab]; exact ⟨htIoo.1.le, htIoo.2.le⟩)
    a (by rw [uIcc_of_le hab]; exact ⟨le_rfl, hab⟩)
  have hplus : HasDerivAt
      (fun u ↦ (∫ x, f a x ∂ν) + ∫ v in a..u, ∫ x, fdot v x ∂ν)
      (∫ x, fdot t x ∂ν) t := by
    exact hbase.const_add (∫ x, f a x ∂ν)
  apply hplus.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds htIoo.1 htIoo.2] with u hu
  exact hFTC u ⟨hu.1.le, hu.2.le⟩

/-- A dominated sequence of truncated integral identities passes to its exact
limit. The limiting identity needs no assumption that its endpoint values or
derivative have already been identified by a differentiation theorem. -/
theorem integral_identity_of_dominated_limits
    (ν : Measure Ω) (A B : ℕ → ℝ) (A_lim B_lim : ℝ)
    (q : ℕ → Ω → ℝ) (q_lim : Ω → ℝ) (bound : Ω → ℝ)
    (hidentity : ∀ n, B n - A n = ∫ x, q n x ∂ν)
    (hA : Tendsto A atTop (𝓝 A_lim)) (hB : Tendsto B atTop (𝓝 B_lim))
    (hmeas : ∀ n, AEStronglyMeasurable (q n) ν)
    (hbound : Integrable bound ν)
    (hdom : ∀ n, ∀ᵐ x ∂ν, ‖q n x‖ ≤ bound x)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun n ↦ q n x) atTop (𝓝 (q_lim x))) :
    B_lim - A_lim = ∫ x, q_lim x ∂ν := by
  have hleft := hB.sub hA
  have hright := tendsto_integral_of_dominated_convergence bound hmeas hbound hdom hlim
  have heq : (fun n ↦ B n - A n) = fun n ↦ ∫ x, q n x ∂ν := funext hidentity
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

/-- An integrated entropy identity with an integrable flux gives exactly the
regularity used in the scalar comparison: absolute continuity and the flux as
the derivative almost everywhere in the open interval. -/
theorem regularity_of_integral_identity
    (H q : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hq : IntervalIntegrable q volume a b)
    (hidentity : ∀ t ∈ Icc a b, H t = H a + ∫ u in a..t, q u) :
    AbsolutelyContinuousOnInterval H a b ∧
      ∀ᵐ t ∂volume, t ∈ Ioo a b → HasDerivAt H (q t) t := by
  have hACq := hq.absolutelyContinuousOnInterval_intervalIntegral
    (show a ∈ uIcc a b by rw [uIcc_of_le hab]; exact ⟨le_rfl, hab⟩)
  have hACc : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ H a) a b :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ ↦ H a)).contDiffOn
      |>.absolutelyContinuousOnInterval
  refine ⟨(hACc.add hACq).congr ?_, ?_⟩
  · intro t ht
    exact (hidentity t (by simpa only [uIcc_of_le hab] using ht)).symm
  · filter_upwards [hq.ae_hasDerivAt_integral] with t ht htIoo
    have hbase := ht (by rw [uIcc_of_le hab]; exact ⟨htIoo.1.le, htIoo.2.le⟩)
      a (by rw [uIcc_of_le hab]; exact ⟨le_rfl, hab⟩)
    have hplus : HasDerivAt (fun u ↦ H a + ∫ v in a..u, q v) (q t) t :=
      hbase.const_add (H a)
    apply hplus.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds htIoo.1 htIoo.2] with u hu
    exact hidentity u ⟨hu.1.le, hu.2.le⟩

end ULA.LSI
