import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option linter.style.header false

/-!
# Dominated first variations of the actual density free-energy integral

Source: `papers/Latent_diffusion/supp_aistats.tex:188–199`,
Lemma `app:lemma_1st_var`.

The parameter result differentiates the actual integral, using pointwise
Fréchet derivatives and one integrable domination bound on a common parameter
neighborhood. The density result differentiates the actual integral along
`q + t r`, using positivity and integrable derivative domination on a common
interval. Neither result assumes the desired integral derivative.

These domination/integrability conditions are additional explicit analytic
hypotheses; the paper's A1 does not by itself establish them. The `+1` in the
ordinary entropy derivative disappears on zero-mass density perturbations.
No Wasserstein gradient, PDE integration by parts or flow construction is
claimed by this module.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace LatentDiffusion.SourceCalculus

variable {Z A : Type*} [MeasurableSpace Z]
  [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- The actual base-density free energy with potential `U = -log ρ`. -/
def densityFreeEnergy (ν : Measure Z) (q U : Z → ℝ) : ℝ :=
  ∫ z, q z * (Real.log (q z) + U z) ∂ν

/-- Parameter differentiation in source Lemma `app:lemma_1st_var`, with an
explicit weighted derivative bound that justifies differentiation under the
integral. The density is held fixed. In the source, use
`U(θ,φ,z) = L_D(θ,z) - log p_φ(x|z)` and split its derivative. -/
theorem parameter_freeEnergy_hasFDerivAt
    (ν : Measure Z) (q : Z → ℝ) (U : A → Z → ℝ)
    (DU : A → Z → A →L[ℝ] ℝ) (a₀ : A) (s : Set A) (bound : Z → ℝ)
    (hs : s ∈ 𝓝 a₀) (hq : Measurable q)
    (hU : ∀ᶠ a in 𝓝 a₀, Measurable (U a))
    (hbase : Integrable (fun z ↦ q z * (Real.log (q z) + U a₀ z)) ν)
    (hDU : AEStronglyMeasurable (fun z ↦ q z • DU a₀ z) ν)
    (hbound : ∀ᵐ z ∂ν, ∀ a ∈ s, |q z| * ‖DU a z‖ ≤ bound z)
    (hbound_int : Integrable bound ν)
    (hdiff : ∀ᵐ z ∂ν, ∀ a ∈ s, HasFDerivAt (fun b ↦ U b z) (DU a z) a) :
    HasFDerivAt (fun a ↦ densityFreeEnergy ν q (U a))
      (∫ z, q z • DU a₀ z ∂ν) a₀ := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun a z ↦ q z * (Real.log (q z) + U a z))
    (F' := fun a z ↦ q z • DU a z) hs
  · filter_upwards [hU] with a ha
    exact (hq.mul (hq.log.add ha)).aestronglyMeasurable
  · exact hbase
  · exact hDU
  · filter_upwards [hbound] with z hz a ha
    simpa only [norm_smul, Real.norm_eq_abs] using hz a ha
  · exact hbound_int
  · filter_upwards [hdiff] with z hz a ha
    exact ((hz a ha).const_add (Real.log (q z))).const_mul (q z)

/-- The ordinary pointwise derivative along an affine density perturbation.
This is used below inside a dominated differentiation theorem. -/
theorem density_integrand_hasDerivAt (q r U t : ℝ) (hpositive : 0 < q + t * r) :
    HasDerivAt (fun s ↦ (q + s * r) * (Real.log (q + s * r) + U))
      (r * (Real.log (q + t * r) + U + 1)) t := by
  have hq : HasDerivAt (fun s : ℝ ↦ q + s * r) r t := by
    simpa using ((hasDerivAt_id t).mul_const r).const_add q
  have hlog := (hq.log (ne_of_gt hpositive)).add_const U
  have hcancel : (q + t * r) * (r / (q + t * r)) = r := by
    rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hpositive)]
  convert hq.mul hlog using 1
  rw [hcancel]
  ring

/-- Genuine density-direction differentiation of the source free-energy
integral. Positivity and the domination bound hold on one common neighborhood
of zero, rather than point-dependent neighborhoods. -/
theorem density_freeEnergy_hasDerivAt
    (ν : Measure Z) (q r U : Z → ℝ) (s : Set ℝ) (bound : Z → ℝ)
    (hs : s ∈ 𝓝 (0 : ℝ)) (hq : Measurable q) (hr : Measurable r)
    (hU : Measurable U)
    (hbase : Integrable (fun z ↦ q z * (Real.log (q z) + U z)) ν)
    (hpositive : ∀ᵐ z ∂ν, ∀ t ∈ s, 0 < q z + t * r z)
    (hbound : ∀ᵐ z ∂ν, ∀ t ∈ s,
      |r z * (Real.log (q z + t * r z) + U z + 1)| ≤ bound z)
    (hbound_int : Integrable bound ν) :
    Integrable (fun z ↦ r z * (Real.log (q z) + U z + 1)) ν ∧
      HasDerivAt (fun t ↦ densityFreeEnergy ν (fun z ↦ q z + t * r z) U)
        (∫ z, r z * (Real.log (q z) + U z + 1) ∂ν) 0 := by
  have hmeas : ∀ t : ℝ,
      Measurable (fun z ↦ (q z + t * r z) * (Real.log (q z + t * r z) + U z)) :=
    fun t ↦ (hq.add (hr.const_mul t)).mul ((hq.add (hr.const_mul t)).log.add hU)
  have hdmeas : Measurable (fun z ↦ r z * (Real.log (q z) + U z + 1)) :=
    hr.mul ((hq.log.add hU).add_const 1)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t z ↦ (q z + t * r z) * (Real.log (q z + t * r z) + U z))
    (F' := fun t z ↦ r z * (Real.log (q z + t * r z) + U z + 1)) hs
    (Eventually.of_forall fun t ↦ (hmeas t).aestronglyMeasurable)
    (by simpa using hbase)
    (by simpa using hdmeas.aestronglyMeasurable (μ := ν))
    (by simpa only [Real.norm_eq_abs] using hbound) hbound_int
    (by
      filter_upwards [hpositive] with z hz t ht
      exact density_integrand_hasDerivAt (q z) (r z) (U z) t (hz t ht))
  simpa only [zero_mul, add_zero, densityFreeEnergy] using h

/-- On probability-density tangent directions the constant `+1` vanishes.
The conclusion is the source's density first variation, now for an actual
integral with all dominated-differentiation hypotheses exposed. -/
theorem density_firstVariation_of_zero_mass
    (ν : Measure Z) (q r U : Z → ℝ) (s : Set ℝ) (bound : Z → ℝ)
    (hs : s ∈ 𝓝 (0 : ℝ)) (hq : Measurable q) (hr : Measurable r)
    (hU : Measurable U)
    (hbase : Integrable (fun z ↦ q z * (Real.log (q z) + U z)) ν)
    (hpositive : ∀ᵐ z ∂ν, ∀ t ∈ s, 0 < q z + t * r z)
    (hbound : ∀ᵐ z ∂ν, ∀ t ∈ s,
      |r z * (Real.log (q z + t * r z) + U z + 1)| ≤ bound z)
    (hbound_int : Integrable bound ν)
    (hr_int : Integrable r ν) (hmass : (∫ z, r z ∂ν) = 0) :
    Integrable (fun z ↦ r z * (Real.log (q z) + U z)) ν ∧
      HasDerivAt (fun t ↦ densityFreeEnergy ν (fun z ↦ q z + t * r z) U)
        (∫ z, r z * (Real.log (q z) + U z) ∂ν) 0 := by
  obtain ⟨hint, hderiv⟩ := density_freeEnergy_hasDerivAt ν q r U s bound hs hq hr hU
    hbase hpositive hbound hbound_int
  have hweighted : Integrable (fun z ↦ r z * (Real.log (q z) + U z)) ν := by
    convert hint.sub hr_int using 1
    ext z
    change r z * (Real.log (q z) + U z) =
      r z * (Real.log (q z) + U z + 1) - r z
    ring
  refine ⟨hweighted, ?_⟩
  have heq : (∫ z, r z * (Real.log (q z) + U z + 1) ∂ν) =
      ∫ z, r z * (Real.log (q z) + U z) ∂ν := by
    calc
      _ = ∫ z, r z * (Real.log (q z) + U z) + r z ∂ν := by
        congr 1
        ext z
        ring
      _ = _ := by rw [integral_add hweighted hr_int, hmass, add_zero]
  rwa [heq] at hderiv

end LatentDiffusion.SourceCalculus
