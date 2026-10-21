import IPLA.Foundations
import UnadjustedLangevin.Generator

set_option linter.style.header false

/-! # The IPLA diffusion generator and its Gibbs integration identity

For the rescaled state `z = (θ,x¹/√N,…,xᴺ/√N)`, physical time has
generator `(∆ - ∇U_N · ∇)/N`. Both the target probability measure and
its infinitesimal invariance are derived from the original joint potential
`U y (pair θ x)`. No regularity is assumed separately for `U_N`.

The generator identity below and full Gibbs stationarity are both proved.
`UnadjustedLangevin.CanonicalULA` supplies the stationary integral reference.
-/

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal

namespace IPLA

/-- Generator in the physical IPLA time variable, acting on the rescaled state. -/
def diffusionGenerator {N dθ dx : ℕ} (U : Joint dθ dx → ℝ)
    (φ : State N dθ dx → ℝ) (z : State N dθ dx) : ℝ :=
  (N : ℝ)⁻¹ * ULA.langevinGenerator (potential U) φ z

/-- The exact Laplacian and drift formula for the IPLA generator. -/
theorem diffusionGenerator_eq {N dθ dx : ℕ} (U : Joint dθ dx → ℝ)
    (φ : State N dθ dx → ℝ) (hφ : ContDiff ℝ 2 φ) (z : State N dθ dx) :
    diffusionGenerator U φ z = (N : ℝ)⁻¹ *
      (Laplacian.laplacian φ z -
        inner ℝ (gradient (potential U) z) (gradient φ z)) := by
  rw [diffusionGenerator, ULA.langevinGenerator_eq_laplacian_sub_inner _ _ hφ]

/-- Gibbs infinitesimal invariance for IPLA under only the original joint
potential hypotheses. Integrability is a conclusion, so the zero integral
cannot result from Lean's default value for a nonintegrable function. -/
theorem gibbsTarget_infinitesimalInvariant
    {N dθ dx : ℕ} (hN : 0 < N) {Data : Type*}
    (U : Data → Joint dθ dx → ℝ) (y : Data) (m : ℝ) (L : ℝ≥0)
    (hm : 0 < m) (hdiff : Differentiable ℝ (U y))
    (hsc : StrongConvexOn Set.univ m (U y))
    (hLip : LipschitzWith L (gradient (U y))) :
    IsProbabilityMeasure (@gibbsTarget N dθ dx (U y)) ∧
      ∀ φ : State N dθ dx → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
        Integrable (diffusionGenerator (U y) φ) (gibbsTarget (U y)) ∧
          (∫ z, diffusionGenerator (U y) φ z ∂gibbsTarget (U y)) = 0 := by
  refine ⟨gibbsTarget_isProbability hN (U y) m hm hdiff hsc, ?_⟩
  intro φ hφ hc
  rw [gibbsTarget_eq_gibbsMeasure]
  constructor
  · exact (ULA.integrable_langevinGenerator_gibbsMeasure (potential (U y))
      ((N : ℝ≥0) * L) (potential_differentiable hdiff)
      (potential_gradient_lipschitz hdiff hLip) φ hφ hc).const_mul _
  · simp only [diffusionGenerator, integral_const_mul,
      ULA.integral_langevinGenerator_gibbs_eq_zero (potential (U y))
        ((N : ℝ≥0) * L) (potential_differentiable hdiff)
        (potential_gradient_lipschitz hdiff hLip) φ hφ hc, mul_zero]

end IPLA
