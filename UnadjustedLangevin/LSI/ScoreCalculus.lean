import UnadjustedLangevin.LSI.FunctionalInequality
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Score calculus and the entropy test of the weak relative Fokker–Planck identity

For a smooth strictly positive relative density `r`, this file proves the
pointwise gradient identities for `log r` and `log r + 1`. It then tests an
explicit weak relative Fokker–Planck integration identity with `log r + 1`
to obtain the weighted squared-score integral.

The weak identity is required for all continuously differentiable tests whose
two integrands are integrable. This includes the necessary admissibility of
the noncompact entropy test; no boundary-decay or integration-by-parts fact is
inferred solely from smoothness.

Reference: Vempala–Wibisono (2019), *Rapid Convergence of the Unadjusted
Langevin Algorithm: Isoperimetry Suffices*.
https://proceedings.neurips.cc/paper_files/paper/2019/file/65a99bb7a3115fdede20da98b08a370f-Paper.pdf
-/

noncomputable section

open MeasureTheory

namespace ULA.LSI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- The score of a positive differentiable relative density. -/
theorem gradient_log_of_pos {r : E → ℝ} {x : E}
    (hdiff : DifferentiableAt ℝ r x) (hpos : 0 < r x) :
    gradient (fun y ↦ Real.log (r y)) x = (r x)⁻¹ • gradient r x := by
  simp only [gradient, fderiv.log hdiff hpos.ne', map_smul]

/-- Adding the normalization term `1` to the entropy test preserves its gradient. -/
theorem gradient_log_add_one_of_pos {r : E → ℝ} {x : E}
    (_hdiff : DifferentiableAt ℝ r x) (_hpos : 0 < r x) :
    gradient (fun y ↦ Real.log (r y) + 1) x =
      gradient (fun y ↦ Real.log (r y)) x := by
  simp only [gradient, fderiv_add_const]

/-- The Dirichlet integrand for the entropy test equals the density-weighted
squared score. -/
theorem inner_gradient_entropy_test {r : E → ℝ} {x : E}
    (hdiff : DifferentiableAt ℝ r x) (hpos : 0 < r x) :
    inner ℝ (gradient r x) (gradient (fun y ↦ Real.log (r y) + 1) x) =
      r x * ‖gradient (fun y ↦ Real.log (r y)) x‖ ^ 2 := by
  have hscore := gradient_log_of_pos hdiff hpos
  have hreverse : gradient r x =
      r x • gradient (fun y ↦ Real.log (r y)) x := by
    rw [hscore, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  rw [gradient_log_add_one_of_pos hdiff hpos, hreverse,
    real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- The entropy test in a weak relative Fokker–Planck identity with an
additional drift error. Both the weak identity for all admissible tests and
integrability of its three terms are explicit. The error sign is the sign
displayed in `hweak`.

This is the spatial calculation needed for a frozen-drift ULA interpolation;
it does not assert that a stochastic process has the stated weak equation. -/
theorem entropy_production_of_forced_weak_identity [MeasurableSpace E]
    (ν : Measure E) (r rdot : E → ℝ) (err : E → E)
    (hpos : ∀ x, 0 < r x) (hdiff : ContDiff ℝ 1 r)
    (hentropy_int : Integrable (fun x ↦ rdot x * (Real.log (r x) + 1)) ν)
    (hfisher_int : Integrable
      (fun x ↦ r x * ‖gradient (fun y ↦ Real.log (r y)) x‖ ^ 2) ν)
    (herror_int : Integrable
      (fun x ↦ r x * inner ℝ (err x) (gradient (fun y ↦ Real.log (r y)) x)) ν)
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ 1 ψ →
      Integrable (fun x ↦ rdot x * ψ x) ν →
      Integrable (fun x ↦ inner ℝ (gradient r x) (gradient ψ x)) ν →
      Integrable (fun x ↦ r x * inner ℝ (err x) (gradient ψ x)) ν →
      (∫ x, rdot x * ψ x ∂ν) =
        -(∫ x, inner ℝ (gradient r x) (gradient ψ x) ∂ν) +
          ∫ x, r x * inner ℝ (err x) (gradient ψ x) ∂ν) :
    (∫ x, rdot x * (Real.log (r x) + 1) ∂ν) =
      -(∫ x, r x * ‖gradient (fun y ↦ Real.log (r y)) x‖ ^ 2 ∂ν) +
        ∫ x, r x * inner ℝ (err x) (gradient (fun y ↦ Real.log (r y)) x) ∂ν := by
  have hgrad : ∀ x,
      inner ℝ (gradient r x) (gradient (fun y ↦ Real.log (r y) + 1) x) =
        r x * ‖gradient (fun y ↦ Real.log (r y)) x‖ ^ 2 := fun x ↦
    inner_gradient_entropy_test (hdiff.differentiable (by decide) x) (hpos x)
  have hscore : ∀ x, gradient (fun y ↦ Real.log (r y) + 1) x =
      gradient (fun y ↦ Real.log (r y)) x := fun x ↦
    gradient_log_add_one_of_pos (hdiff.differentiable (by decide) x) (hpos x)
  have htest : ContDiff ℝ 1 (fun x ↦ Real.log (r x) + 1) :=
    (hdiff.log (fun x ↦ (hpos x).ne')).add contDiff_const
  have hdirichlet_int : Integrable
      (fun x ↦ inner ℝ (gradient r x)
        (gradient (fun y ↦ Real.log (r y) + 1) x)) ν := by
    simpa only [hgrad] using hfisher_int
  have herror_test_int : Integrable
      (fun x ↦ r x * inner ℝ (err x)
        (gradient (fun y ↦ Real.log (r y) + 1) x)) ν := by
    simpa only [hscore] using herror_int
  have h := hweak (fun x ↦ Real.log (r x) + 1) htest
    hentropy_int hdirichlet_int herror_test_int
  simp only [hgrad] at h
  simpa only [hscore] using h

/-- Entropy production obtained by specializing the weak relative
Fokker–Planck identity to the continuously differentiable entropy test
`ψ = log r + 1`. The weak identity, including the admissibility of all
integrable continuously differentiable tests, is an explicit hypothesis;
the entropy-production identity itself is the conclusion. -/
theorem entropy_production_of_weak_identity [MeasurableSpace E]
    (ν : Measure E) (r rdot : E → ℝ)
    (hpos : ∀ x, 0 < r x) (hdiff : ContDiff ℝ 1 r)
    (hentropy_int : Integrable (fun x ↦ rdot x * (Real.log (r x) + 1)) ν)
    (hfisher_int : Integrable
      (fun x ↦ r x * ‖gradient (fun y ↦ Real.log (r y)) x‖ ^ 2) ν)
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ 1 ψ →
      Integrable (fun x ↦ rdot x * ψ x) ν →
      Integrable (fun x ↦ inner ℝ (gradient r x) (gradient ψ x)) ν →
      (∫ x, rdot x * ψ x ∂ν) =
        -(∫ x, inner ℝ (gradient r x) (gradient ψ x) ∂ν)) :
    (∫ x, rdot x * (Real.log (r x) + 1) ∂ν) =
      -(∫ x, r x * ‖gradient (fun y ↦ Real.log (r y)) x‖ ^ 2 ∂ν) := by
  have hgrad : ∀ x,
      inner ℝ (gradient r x) (gradient (fun y ↦ Real.log (r y) + 1) x) =
        r x * ‖gradient (fun y ↦ Real.log (r y)) x‖ ^ 2 := fun x ↦
    inner_gradient_entropy_test (hdiff.differentiable (by decide) x) (hpos x)
  have htest : ContDiff ℝ 1 (fun x ↦ Real.log (r x) + 1) :=
    (hdiff.log (fun x ↦ (hpos x).ne')).add contDiff_const
  have hdirichlet_int : Integrable
      (fun x ↦ inner ℝ (gradient r x)
        (gradient (fun y ↦ Real.log (r y) + 1) x)) ν := by
    simpa only [hgrad] using hfisher_int
  have h := hweak (fun x ↦ Real.log (r x) + 1) htest hentropy_int hdirichlet_int
  simpa only [hgrad] using h

end ULA.LSI
