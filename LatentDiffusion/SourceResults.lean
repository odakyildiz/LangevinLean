import LatentDiffusion.Density
import LatentDiffusion.Flow
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option linter.style.header false

/-!
# Additional source results, on their explicit mathematical domains

These theorems reconstruct elementary steps used in the supplied manuscript.
They do not construct optimal transport plans, identify a Wasserstein metric
derivative, or justify differentiation or integration by parts on an unbounded
domain. Those continuum application steps remain separate obligations.

`cauchy_minimizing_sequence` corrects Supplement `lem:cauchy`: a Cauchy
sequence must also be a minimizing sequence. A complete ambient metric space
and lower semicontinuity then give an actual minimizer.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace LatentDiffusion.SourceResults

/-- Corrected Supplement `lem:cauchy`: completeness and lower semicontinuity
identify the limit of a Cauchy *minimizing* sequence as a minimizer.
No unrelated Cauchy sequence supplies this conclusion. -/
theorem cauchy_minimizing_sequence
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (F : X → ℝ) (Fstar : ℝ) (hF : LowerSemicontinuous F)
    (hstar : ∀ x, Fstar ≤ F x) (u : ℕ → X)
    (hu : CauchySeq u) (hvalue : Tendsto (fun n ↦ F (u n)) atTop (𝓝 Fstar)) :
    ∃ xstar, Tendsto u atTop (𝓝 xstar) ∧ F xstar = Fstar ∧
      ∀ x, F xstar ≤ F x := by
  obtain ⟨xstar, hx⟩ := cauchySeq_tendsto_of_complete hu
  have hlim : F xstar ≤ Fstar := by
    apply le_of_forall_lt_imp_le_of_dense
    intro c hc
    exact ge_of_tendsto hvalue ((hx.eventually (hF xstar c hc)).mono fun _ h ↦ h.le)
  have heq := le_antisymm hlim (hstar xstar)
  refine ⟨xstar, hx, heq, ?_⟩
  intro x
  rw [heq]
  exact hstar x

/-- The scalar derivative used in Supplement `app:lemma_1st_var` includes
the additive constant one. It disappears only on zero-total-mass directions. -/
theorem entropy_integrand_derivative (r U : ℝ) (hr : 0 < r) :
    HasDerivAt (fun s : ℝ ↦ s * (Real.log s + U)) (Real.log r + U + 1) r := by
  have hd := (hasDerivAt_id r).mul ((Real.hasDerivAt_log hr.ne').add_const U)
  convert hd using 1
  · ext s
    rfl
  · simp [hr.ne']

/-- Constants represent the same first variation on probability tangent
directions. This proves the precise reason the source may omit `+1`. -/
theorem first_variation_constant_cancels
    {Z : Type*} [MeasurableSpace Z] (ν : Measure Z) (g r : Z → ℝ)
    (hg : Integrable (fun z ↦ g z * r z) ν) (hr : Integrable r ν)
    (hzero : (∫ z, r z ∂ν) = 0) :
    (∫ z, (g z + 1) * r z ∂ν) = ∫ z, g z * r z ∂ν := by
  simp_rw [add_mul, one_mul]
  rw [integral_add hg hr, hzero, add_zero]

/-- The source's normalized product metric cancels the `1/M` from the
distributional first variation with the inverse metric's `M`.
The positivity of the data count is essential. -/
theorem normalized_product_metric_cancellation
    {V : Type*} [AddCommGroup V] [Module ℝ V] (M : ℕ) (hM : 0 < M) (v : V) :
    (M : ℝ) • ((M : ℝ)⁻¹ • v) = v := by
  rw [smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hM.ne'), one_smul]

/-- The first-order scalar consequence of the source's geodesic-convexity
inequality. This step is proved by taking the right derivative; the existence
and calculus of an actual Wasserstein geodesic is not a premise hidden here. -/
theorem geodesic_convexity_first_order
    (f : ℝ → ℝ) (fend derivative rho distance : ℝ)
    (hderiv : HasDerivWithinAt f derivative (Ici 0) 0)
    (hconv : ∀ s ∈ Icc (0 : ℝ) 1,
      f s ≤ (1 - s) * f 0 + s * fend - rho / 2 * s * (1 - s) * distance ^ 2) :
    derivative ≤ fend - f 0 - rho / 2 * distance ^ 2 := by
  have hright : Tendsto (slope f 0) (𝓝[>] 0) (𝓝 derivative) :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)).mp
      (hderiv.mono Ioi_subset_Ici_self)
  have hbound : ∀ᶠ s : ℝ in 𝓝[>] 0,
      slope f 0 s ≤ fend - f 0 - rho / 2 * (1 - s) * distance ^ 2 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with s hs hs1
    have hh := hconv s ⟨hs.le, hs1.le⟩
    rw [slope_def_field]
    simp only [sub_zero]
    apply (div_le_iff₀ hs).mpr
    calc
      f s - f 0 ≤ (1 - s) * f 0 + s * fend -
          rho / 2 * s * (1 - s) * distance ^ 2 - f 0 := sub_le_sub_right hh _
      _ = (fend - f 0 - rho / 2 * (1 - s) * distance ^ 2) * s := by ring
  have hlim : Tendsto (fun s : ℝ ↦ fend - f 0 - rho / 2 * (1 - s) * distance ^ 2)
      (𝓝[>] 0) (𝓝 (fend - f 0 - rho / 2 * distance ^ 2)) := by
    have hc : Continuous (fun s : ℝ ↦ fend - f 0 - rho / 2 * (1 - s) * distance ^ 2) := by
      fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto hright hlim hbound

/-- The source's Talagrand-type quadratic growth follows directly from strong
geodesic convexity at a minimizer. This proof needs no entropy dissipation.
The application must still establish the displayed convexity inequality for
its actual displacement interpolation and actual metric distance. -/
theorem geodesic_quadratic_growth
    (f : ℝ → ℝ) (fend rho distance : ℝ)
    (hmin : ∀ s ∈ Icc (0 : ℝ) 1, f 0 ≤ f s)
    (hconv : ∀ s ∈ Icc (0 : ℝ) 1,
      f s ≤ (1 - s) * f 0 + s * fend - rho / 2 * s * (1 - s) * distance ^ 2) :
    rho / 2 * distance ^ 2 ≤ fend - f 0 := by
  have hbound : ∀ᶠ s : ℝ in 𝓝[>] 0,
      rho / 2 * (1 - s) * distance ^ 2 ≤ fend - f 0 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with s hs hs1
    have hh := hconv s ⟨hs.le, hs1.le⟩
    have hm := hmin s ⟨hs.le, hs1.le⟩
    apply (mul_le_mul_iff_right₀ hs).mp
    nlinarith only [hh, hm]
  have hlim : Tendsto (fun s : ℝ ↦ rho / 2 * (1 - s) * distance ^ 2)
      (𝓝[>] 0) (𝓝 (rho / 2 * distance ^ 2)) := by
    have hc : Continuous (fun s : ℝ ↦ rho / 2 * (1 - s) * distance ^ 2) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto hlim hbound

/-- The actual tilted density in main-text `eq:ptildedef`. -/
def tiltedDensity {Z : Type*} (ρ R : Z → ℝ) (z : Z) : ℝ :=
  ρ z * Real.exp (-R z)

/-- The log-density free energy used by the paper, relative to a base measure. -/
def densityFreeEnergy {Z : Type*} [MeasurableSpace Z]
    (ν : Measure Z) (q ρ : Z → ℝ) : ℝ :=
  ∫ z, q z * Real.log (q z / ρ z) ∂ν

/-- Pointwise tilt identity, including zeros of the trial density. -/
theorem tilted_log_integrand {Z : Type*} (q ρ R : Z → ℝ)
    (hq : ∀ z, 0 ≤ q z) (hρ : ∀ z, 0 < ρ z) (z : Z) :
    q z * Real.log (q z / tiltedDensity ρ R z) =
      q z * Real.log (q z / ρ z) + q z * R z := by
  by_cases hz : q z = 0
  · simp [hz]
  · have hqz : 0 < q z := lt_of_le_of_ne (hq z) (Ne.symm hz)
    rw [tiltedDensity, Real.log_div hz (mul_ne_zero (hρ z).ne' (Real.exp_ne_zero _)),
      Real.log_mul (hρ z).ne' (Real.exp_ne_zero _), Real.log_exp,
      Real.log_div hz (hρ z).ne']
    ring

/-- Main-text free-energy decomposition after `eq:free-energy`, proved for
the actual base-density integral. Both integrable summands are explicit. -/
theorem tilted_freeEnergy_decomposition
    {Z : Type*} [MeasurableSpace Z] (ν : Measure Z) (q ρ R : Z → ℝ)
    (hq : ∀ z, 0 ≤ q z) (hρ : ∀ z, 0 < ρ z)
    (hfree : Integrable (fun z ↦ q z * Real.log (q z / ρ z)) ν)
    (hpenalty : Integrable (fun z ↦ q z * R z) ν) :
    Integrable (fun z ↦ q z * Real.log (q z / tiltedDensity ρ R z)) ν ∧
      densityFreeEnergy ν q (tiltedDensity ρ R) =
        densityFreeEnergy ν q ρ + ∫ z, q z * R z ∂ν := by
  unfold densityFreeEnergy
  simp_rw [tilted_log_integrand q ρ R hq hρ]
  exact ⟨hfree.add hpenalty, integral_add hfree hpenalty⟩

/-- Nonnegative KL regularization raises the density free energy. The KL
interpretation of `R` is independent of this integral inequality. -/
theorem tilted_freeEnergy_le
    {Z : Type*} [MeasurableSpace Z] (ν : Measure Z) (q ρ R : Z → ℝ)
    (hq : ∀ z, 0 ≤ q z) (hρ : ∀ z, 0 < ρ z) (hR : ∀ z, 0 ≤ R z)
    (hfree : Integrable (fun z ↦ q z * Real.log (q z / ρ z)) ν)
    (hpenalty : Integrable (fun z ↦ q z * R z) ν) :
    densityFreeEnergy ν q ρ ≤ densityFreeEnergy ν q (tiltedDensity ρ R) := by
  rw [(tilted_freeEnergy_decomposition ν q ρ R hq hρ hfree hpenalty).2]
  exact le_add_of_nonneg_right (integral_nonneg fun z ↦ mul_nonneg (hq z) (hR z))

/-- Integrability and evidence order follow from a nonnegative integrable
base density and a measurable nonnegative penalty, as used after main-text
`eq:ptildedef`. The tilted integral is not assumed integrable in advance. -/
theorem tilted_evidence_le
    {Z : Type*} [MeasurableSpace Z] (ν : Measure Z) (ρ R : Z → ℝ)
    (hρmeas : Measurable ρ) (hRmeas : Measurable R)
    (hρ : ∀ z, 0 ≤ ρ z) (hR : ∀ z, 0 ≤ R z) (hint : Integrable ρ ν) :
    Integrable (tiltedDensity ρ R) ν ∧
      (∫ z, tiltedDensity ρ R z ∂ν) ≤ ∫ z, ρ z ∂ν := by
  have hnonneg (z : Z) : 0 ≤ tiltedDensity ρ R z :=
    mul_nonneg (hρ z) (Real.exp_pos _).le
  have hle (z : Z) : tiltedDensity ρ R z ≤ ρ z := by
    apply mul_le_of_le_one_right (hρ z)
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hR z))
  have hmeas : Measurable (tiltedDensity ρ R) := hρmeas.mul (hRmeas.neg.exp)
  have htilt : Integrable (tiltedDensity ρ R) ν := by
    apply hint.mono' hmeas.aestronglyMeasurable
    exact ae_of_all _ fun z ↦ by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg z)] using hle z
  exact ⟨htilt, integral_mono htilt hint hle⟩

/-- Taking logs preserves the source's evidence comparison when the tilted
normalizer is positive. Its positivity must be established for the model. -/
theorem tilted_logEvidence_le
    {Z : Type*} [MeasurableSpace Z] (ν : Measure Z) (ρ R : Z → ℝ)
    (hρmeas : Measurable ρ) (hRmeas : Measurable R)
    (hρ : ∀ z, 0 ≤ ρ z) (hR : ∀ z, 0 ≤ R z) (hint : Integrable ρ ν)
    (hpositive : 0 < ∫ z, tiltedDensity ρ R z ∂ν) :
    Real.log (∫ z, tiltedDensity ρ R z ∂ν) ≤ Real.log (∫ z, ρ z ∂ν) :=
  Real.log_le_log hpositive (tilted_evidence_le ν ρ R hρmeas hRmeas hρ hR hint).2

/-- Exact finite uniform expectation over the diffusion time index. This is
the arithmetic mean on `Fin K`, so no sampling or asymptotic premise is used. -/
def uniformTimeMean {K : ℕ} (f : Fin K → ℝ) : ℝ :=
  (K : ℝ)⁻¹ * ∑ j, f j

/-- Supplement `app_eq:diffusion_likelihood` and
`app:one_sample_simplified_diffusion`: without inverse-inclusion scaling,
a uniformly selected summand estimates the average, rather than the sum. -/
theorem uniform_time_unscaled (K : ℕ) (hK : 0 < K) (c : ℝ) (L : Fin K → ℝ) :
    uniformTimeMean (fun j ↦ c + L j) = c + uniformTimeMean L := by
  unfold uniformTimeMean
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp [Nat.cast_ne_zero.mpr hK.ne']

/-- Corrected unbiased single-time estimator of a *summed* diffusion
objective: multiply the sampled summand by the number of time indices. -/
theorem uniform_time_corrected (K : ℕ) (hK : 0 < K) (c : ℝ) (L : Fin K → ℝ) :
    uniformTimeMean (fun j ↦ c + (K : ℝ) * L j) = c + ∑ j, L j := by
  unfold uniformTimeMean
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  field_simp [Nat.cast_ne_zero.mpr hK.ne']

end LatentDiffusion.SourceResults
