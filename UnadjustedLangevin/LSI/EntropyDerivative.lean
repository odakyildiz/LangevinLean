import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Differentiating the relative-entropy integrand

The relative-density form of the entropy calculation in Vempala--Wibisono
(2019), Lemma 3, starts from `∫ x, r t x * log (r t x) ∂ν`.
This file justifies its time derivative under explicit local domination,
measurability, integrability, positivity, and pointwise differentiability
hypotheses. A Fokker–Planck equation or integration-by-parts identity is not
assumed or proved here.

Reference: https://proceedings.neurips.cc/paper_files/paper/2019/file/65a99bb7a3115fdede20da98b08a370f-Paper.pdf
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace ULA.LSI

/-- The derivative of the positive relative-entropy integrand. -/
theorem hasDerivAt_mul_log {r : ℝ → ℝ} {rdot t : ℝ}
    (hr : HasDerivAt r rdot t) (hpos : 0 < r t) :
    HasDerivAt (fun s ↦ r s * Real.log (r s))
      (rdot * (Real.log (r t) + 1)) t := by
  have hcancel : r t * (rdot / r t) = rdot := by
    rw [mul_comm, div_mul_cancel₀ _ hpos.ne']
  simpa only [hcancel, mul_add, mul_one] using! hr.mul (hr.log hpos.ne')

/-- Local dominated differentiation of relative entropy in relative-density
coordinates. The derivative bound is uniform on a common neighborhood `s`
for almost every spatial point; all analytic requirements are explicit.

The conclusion includes integrability of the differentiated integrand. No
derivative of the integral itself is among the hypotheses. -/
theorem hasDerivAt_integral_mul_log_of_dominated
    {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {r rdot : ℝ → X → ℝ} {t : ℝ} {s : Set ℝ} {bound : X → ℝ}
    (hs : s ∈ 𝓝 t)
    (hmeas : ∀ᶠ u in 𝓝 t,
      AEStronglyMeasurable (fun x ↦ r u x * Real.log (r u x)) ν)
    (hint : Integrable (fun x ↦ r t x * Real.log (r t x)) ν)
    (hderiv_meas : AEStronglyMeasurable
      (fun x ↦ rdot t x * (Real.log (r t x) + 1)) ν)
    (hbound : ∀ᵐ x ∂ν, ∀ u ∈ s,
      ‖rdot u x * (Real.log (r u x) + 1)‖ ≤ bound x)
    (hbound_int : Integrable bound ν)
    (hpos : ∀ᵐ x ∂ν, ∀ u ∈ s, 0 < r u x)
    (hdiff : ∀ᵐ x ∂ν, ∀ u ∈ s,
      HasDerivAt (fun v ↦ r v x) (rdot u x) u) :
    Integrable (fun x ↦ rdot t x * (Real.log (r t x) + 1)) ν ∧
      HasDerivAt (fun u ↦ ∫ x, r u x * Real.log (r u x) ∂ν)
        (∫ x, rdot t x * (Real.log (r t x) + 1) ∂ν) t := by
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs hmeas hint hderiv_meas hbound hbound_int
  filter_upwards [hpos, hdiff] with x hxpos hxdiff
  intro u hu
  exact hasDerivAt_mul_log (hxdiff u hu) (hxpos u hu)

end ULA.LSI
