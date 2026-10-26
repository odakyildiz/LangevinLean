import PBGSO.BrownianProcess
import PBGSO.AdditiveJointBridge

/-! # The actual constant diffusion map and its Brownian scaling

Any finite family of sampler diffusion columns determines a continuous linear
map from Euclidean noise coordinates, including degenerate/augmented states.
The sqrt(2)-normalization used by `samplerBrownianInput` is derived explicitly;
matching a model's constant diffusion no longer needs a supplied matrix
identity. This identifies the actual additive L² input, not a general
state-dependent Itô integral.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace PBGSO

variable {I Z : Type*} [Fintype I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

/-- The linear diffusion operator built from its actual finite columns. -/
def diffusionColumnsCLM (σ : I → Z) : EuclideanSpace ℝ I →L[ℝ] Z :=
  ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (σ i)).comp (EuclideanSpace.proj i)

theorem diffusionColumnsCLM_apply (σ : I → Z) (x : EuclideanSpace ℝ I) :
    diffusionColumnsCLM σ x = ∑ i, x i • σ i := by
  simp [diffusionColumnsCLM]

@[simp] theorem diffusionColumnsCLM_basis (σ : I → Z) (i : I) :
    diffusionColumnsCLM σ (EuclideanSpace.basisFun I ℝ i) = σ i := by
  classical
  rw [diffusionColumnsCLM_apply, EuclideanSpace.basisFun_apply]
  simp

/-- The map accepted by the sqrt(2)-scaled Brownian input constructor. -/
def normalizedDiffusionCLM (σ : I → Z) : EuclideanSpace ℝ I →L[ℝ] Z :=
  (Real.sqrt 2)⁻¹ • diffusionColumnsCLM σ

/-- Its actual columns match the model coefficient after Brownian scaling. -/
theorem normalizedDiffusionCLM_basis (σ : I → Z) (i : I) :
    Real.sqrt 2 • normalizedDiffusionCLM σ (EuclideanSpace.basisFun I ℝ i) = σ i := by
  simp [normalizedDiffusionCLM, smul_smul, Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<2)]

section Brownian
variable {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)

/-- The normalized input is precisely σ applied to the unscaled Brownian
coordinate increment. There is no extra sqrt(2) in the resulting diffusion. -/
theorem samplerBrownianInput_normalized (σ : I → Z)
    (W : I → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) Q) (a t : ℝ) :
    samplerBrownianInput Q (normalizedDiffusionCLM σ) W hW a t =
      (diffusionColumnsCLM σ).compLp
        (ULA.brownianCoordinatesRealLp Q W hW (a + t) -
          ULA.brownianCoordinatesRealLp Q W hW a) := by
  change ((normalizedDiffusionCLM σ).compLpL 2 Q)
    (Real.sqrt 2 • _) = _
  rw [map_smul]
  simp only [normalizedDiffusionCLM, ContinuousLinearMap.smul_compLpL,
    smul_apply, smul_smul]
  rw [mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<2)), one_smul]
  rfl
end Brownian

section Model
variable {A G X : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [CompleteSpace Z]

/-- Every constant-diffusion compatible source model has the exact required
Brownian-column representation, constructed from any anchor states. -/
theorem additive_model_diffusion_columns
    (L : LipschitzDynamics A Z G) (M : Model A G Z X I)
    (H : AdditiveModelCompatibility L M) (a₀ a : A) (z₀ z : Z) (i : I) :
    M.diffusion (M.parameter a) z i =
      Real.sqrt 2 • normalizedDiffusionCLM (M.diffusion (M.parameter a₀) z₀)
        (EuclideanSpace.basisFun I ℝ i) := by
  rw [normalizedDiffusionCLM_basis]
  exact H.diffusion_constant a a₀ z z₀ i
end Model
end PBGSO
