import UnadjustedLangevin.Generator

set_option linter.style.header false

/-! # Gibbs Dirichlet identity, generator symmetry, and dissipativity

Ordinary integration by parts proves the Dirichlet identity for compactly
supported `C²` test functions. The potential needs only one derivative and a
Lipschitz gradient. No Hessian, diffusion invariance, or PDE uniqueness is used.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace ULA

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

omit [MeasurableSpace H] [BorelSpace H] in
/-- Differentiating a weighted test requires only one derivative of `U`. -/
theorem fderiv_exp_neg_mul_apply (U φ : H → ℝ)
    (hU : Differentiable ℝ U) (hφ : Differentiable ℝ φ) (x v : H) :
    fderiv ℝ (fun z ↦ Real.exp (-U z) * φ z) x v =
      Real.exp (-U x) * (fderiv ℝ φ x v - inner ℝ (gradient U x) v * φ x) := by
  have hd : HasFDerivAt (fun z ↦ Real.exp (-U z) * φ z)
      (Real.exp (-U x) • fderiv ℝ φ x +
        (φ x) • (Real.exp (-U x) • (-fderiv ℝ U x))) x := by
    exact ((hU x).hasFDerivAt.neg.exp).mul ((hφ x).hasFDerivAt)
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, neg_apply, smul_eq_mul, ← inner_gradient_left]
  ring

/-- Weighted directional Dirichlet integration by parts. -/
theorem integral_weighted_directional_dirichlet
    (U : H → ℝ) (L : ℝ≥0) (hU : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (φ ψ : H → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ)
    (hcφ : HasCompactSupport φ) (hcψ : HasCompactSupport ψ) (v : H) :
    (∫ x, Real.exp (-U x) * (φ x * directionalGenerator U ψ v x) ∂volume) =
      -(∫ x, Real.exp (-U x) * (fderiv ℝ φ x v * fderiv ℝ ψ x v) ∂volume) := by
  let a : H → ℝ := fun x ↦ Real.exp (-U x) * φ x
  let g : H → ℝ := fun x ↦ fderiv ℝ ψ x v
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hg : ContDiff ℝ 1 g :=
    (hψ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hw : Continuous (fun x ↦ Real.exp (-U x)) :=
    Real.continuous_exp.comp hU.continuous.neg
  have hDφ : Continuous (fun x ↦ fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDg : Continuous (fun x ↦ fderiv ℝ g x v) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hca : HasCompactSupport a := hcφ.mul_left
  have hcg : HasCompactSupport g := hcψ.fderiv_apply ℝ v
  have hDa : Continuous (fun x ↦ fderiv ℝ a x v) := by
    change Continuous (fun x ↦ fderiv ℝ (fun z ↦ Real.exp (-U z) * φ z) x v)
    simp_rw [fderiv_exp_neg_mul_apply U φ hU hφd]
    exact hw.mul (hDφ.sub ((hLip.continuous.inner continuous_const).mul hφ.continuous))
  have hia'g : Integrable (fun x ↦ fderiv ℝ a x v * g x) volume :=
    (hDa.mul hg.continuous).integrable_of_hasCompactSupport hcg.mul_left
  have hiag' : Integrable (fun x ↦ a x * fderiv ℝ g x v) volume :=
    ((hw.mul hφ.continuous).mul hDg).integrable_of_hasCompactSupport hca.mul_right
  have hiag : Integrable (fun x ↦ a x * g x) volume :=
    ((hw.mul hφ.continuous).mul hg.continuous).integrable_of_hasCompactSupport hca.mul_right
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hia'g hiag' hiag
    (fun x _ ↦ ((hU x).neg.exp).mul (hφd x))
    (fun x _ ↦ hg.differentiable (by norm_num) x)
  have hiL : Integrable
      (fun x ↦ Real.exp (-U x) * (φ x * directionalGenerator U ψ v x)) volume :=
    (hw.mul (hφ.continuous.mul (continuous_directionalGenerator U L hLip ψ hψ v)))
      |>.integrable_of_hasCompactSupport hcφ.mul_right.mul_left
  have hiD : Integrable
      (fun x ↦ Real.exp (-U x) * (fderiv ℝ φ x v * g x)) volume :=
    (hw.mul (hDφ.mul hg.continuous))
      |>.integrable_of_hasCompactSupport hcg.mul_left.mul_left
  have hsum : (∫ x, Real.exp (-U x) * (φ x * directionalGenerator U ψ v x) +
      Real.exp (-U x) * (fderiv ℝ φ x v * g x) ∂volume) = 0 := by
    calc
      _ = ∫ x, a x * fderiv ℝ g x v + fderiv ℝ a x v * g x ∂volume := by
        apply integral_congr_ae
        exact ae_of_all _ fun x ↦ by
          dsimp [a, g, directionalGenerator]
          rw [fderiv_exp_neg_mul_apply U φ hU hφd]
          ring
      _ = (∫ x, a x * fderiv ℝ g x v ∂volume) +
          ∫ x, fderiv ℝ a x v * g x ∂volume := integral_add hiag' hia'g
      _ = 0 := by rw [hibp]; ring
  rw [integral_add hiL hiD] at hsum
  exact eq_neg_iff_add_eq_zero.mpr hsum

/-- Directional Gibbs Dirichlet identity, with normalization handled explicitly. -/
theorem integral_directionalGenerator_dirichlet_gibbs
    (U : H → ℝ) (L : ℝ≥0) (hU : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (φ ψ : H → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ)
    (hcφ : HasCompactSupport φ) (hcψ : HasCompactSupport ψ) (v : H) :
    (∫ x, φ x * directionalGenerator U ψ v x ∂gibbsMeasure U) =
      -(∫ x, fderiv ℝ φ x v * fderiv ℝ ψ x v ∂gibbsMeasure U) := by
  rw [integral_gibbs_eq_weighted U hU, integral_gibbs_eq_weighted U hU,
    integral_weighted_directional_dirichlet U L hU hLip φ ψ hφ hψ hcφ hcψ v,
    mul_neg]

/-- Absolute integrability of the Dirichlet energy pairing. -/
theorem integrable_gradient_inner_gibbsMeasure
    (U : H → ℝ) (hU : Differentiable ℝ U) (φ ψ : H → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ)
    (hcφ : HasCompactSupport φ) :
    Integrable (fun x ↦ inner ℝ (gradient φ x) (gradient ψ x)) (gibbsMeasure U) := by
  let e := stdOrthonormalBasis ℝ H
  have hi (v : H) : Integrable (fun x ↦ fderiv ℝ φ x v * fderiv ℝ ψ x v)
      (gibbsMeasure U) :=
    integrable_gibbs_of_continuous_hasCompactSupport U hU _
      (((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
        ((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const))
      (hcφ.fderiv_apply ℝ v).mul_right
  have heq : (fun x ↦ inner ℝ (gradient φ x) (gradient ψ x)) =
      (fun x ↦ ∑ i : Fin (Module.finrank ℝ H), fderiv ℝ φ x (e i) *
        fderiv ℝ ψ x (e i)) := by
    funext x
    simp only [← inner_gradient_left]
    symm
    simpa only [real_inner_comm (gradient ψ x)] using
      e.sum_inner_mul_inner (gradient φ x) (gradient ψ x)
  rw [heq]
  exact integrable_finsetSum Finset.univ (fun i _ ↦ hi (e i))

/-- Absolute integrability of a compact test times the full generator. -/
theorem integrable_test_mul_langevinGenerator_gibbsMeasure
    (U : H → ℝ) (L : ℝ≥0) (hU : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (φ ψ : H → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ)
    (hcφ : HasCompactSupport φ) :
    Integrable (fun x ↦ φ x * langevinGenerator U ψ x) (gibbsMeasure U) := by
  have hi (v : H) : Integrable (fun x ↦ φ x * directionalGenerator U ψ v x)
      (gibbsMeasure U) :=
    integrable_gibbs_of_continuous_hasCompactSupport U hU _
      (hφ.continuous.mul (continuous_directionalGenerator U L hLip ψ hψ v))
      hcφ.mul_right
  simp only [langevinGenerator, Finset.mul_sum]
  exact integrable_finsetSum Finset.univ (fun i _ ↦ hi _)

/-- The Gibbs Dirichlet identity `∫ φ Lψ dπ = -∫ ⟪∇φ,∇ψ⟫ dπ`. -/
theorem integral_langevinGenerator_dirichlet_gibbs
    (U : H → ℝ) (L : ℝ≥0) (hU : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (φ ψ : H → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ)
    (hcφ : HasCompactSupport φ) (hcψ : HasCompactSupport ψ) :
    (∫ x, φ x * langevinGenerator U ψ x ∂gibbsMeasure U) =
      -(∫ x, inner ℝ (gradient φ x) (gradient ψ x) ∂gibbsMeasure U) := by
  let e := stdOrthonormalBasis ℝ H
  have hiL (v : H) : Integrable (fun x ↦ φ x * directionalGenerator U ψ v x)
      (gibbsMeasure U) :=
    integrable_gibbs_of_continuous_hasCompactSupport U hU _
      (hφ.continuous.mul (continuous_directionalGenerator U L hLip ψ hψ v))
      hcφ.mul_right
  have hiD (v : H) : Integrable (fun x ↦ fderiv ℝ φ x v * fderiv ℝ ψ x v)
      (gibbsMeasure U) :=
    integrable_gibbs_of_continuous_hasCompactSupport U hU _
      (((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
        ((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const))
      (hcφ.fderiv_apply ℝ v).mul_right
  simp_rw [langevinGenerator, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun i _ ↦ hiL _)]
  simp_rw [integral_directionalGenerator_dirichlet_gibbs U L hU hLip φ ψ hφ hψ hcφ hcψ]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum Finset.univ (fun i _ ↦ hiD (e i))]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun x ↦ by
    simp only [← inner_gradient_left]
    simpa only [real_inner_comm (gradient ψ x)] using
      e.sum_inner_mul_inner (gradient φ x) (gradient ψ x)

/-- The Langevin generator is symmetric on compactly supported `C²` tests. -/
theorem integral_langevinGenerator_symmetric_gibbs
    (U : H → ℝ) (L : ℝ≥0) (hU : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (φ ψ : H → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ)
    (hcφ : HasCompactSupport φ) (hcψ : HasCompactSupport ψ) :
    (∫ x, φ x * langevinGenerator U ψ x ∂gibbsMeasure U) =
      ∫ x, ψ x * langevinGenerator U φ x ∂gibbsMeasure U := by
  rw [integral_langevinGenerator_dirichlet_gibbs U L hU hLip φ ψ hφ hψ hcφ hcψ,
    integral_langevinGenerator_dirichlet_gibbs U L hU hLip ψ φ hψ hφ hcψ hcφ]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun x ↦ real_inner_comm _ _)

/-- The Dirichlet energy is exactly the negative generator quadratic form. -/
theorem integral_langevinGenerator_self_gibbs
    (U : H → ℝ) (L : ℝ≥0) (hU : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (φ : H → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hcφ : HasCompactSupport φ) :
    (∫ x, φ x * langevinGenerator U φ x ∂gibbsMeasure U) =
      -(∫ x, ‖gradient φ x‖ ^ 2 ∂gibbsMeasure U) := by
  simpa only [real_inner_self_eq_norm_sq] using
    integral_langevinGenerator_dirichlet_gibbs U L hU hLip φ φ hφ hφ hcφ hcφ

/-- Dissipativity of the Langevin generator under the Gibbs measure. -/
theorem integral_langevinGenerator_dissipative_gibbs
    (U : H → ℝ) (L : ℝ≥0) (hU : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (φ : H → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hcφ : HasCompactSupport φ) :
    (∫ x, φ x * langevinGenerator U φ x ∂gibbsMeasure U) ≤ 0 := by
  rw [integral_langevinGenerator_self_gibbs U L hU hLip φ hφ hcφ]
  exact neg_nonpos.mpr (integral_nonneg fun x ↦ sq_nonneg _)

end ULA
