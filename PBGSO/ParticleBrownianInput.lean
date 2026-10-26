import PBGSO.ParticleNoiseSpace
import PBGSO.ParticleAdditiveWeakRealization
import PBGSO.AdditiveCanonicalRealization
import PBGSO.BrownianProcess

/-! # Actual packed Brownian inputs for the particle implementations

Copying the one-sampler Brownian input on independent complete seeds equals
one explicit block-column Brownian input on the flattened particle/spatial
coordinate space. This is a proved equality of L² random variables, not an
assumed noise law or coefficient identity.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace PBGSO

section Coercion
variable {Ω I Z : Type*} [MeasurableSpace Ω] [Fintype I]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  (Q : Measure Ω)

/-- The actual Brownian input agrees with its finite coordinate formula. -/
theorem samplerBrownianInput_coe (K : EuclideanSpace ℝ I →L[ℝ] Z)
    (W : I → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) Q) (a t : ℝ) :
    samplerBrownianInput Q K W hW a t =ᵐ[Q]
      fun ω => K (Real.sqrt 2 •
        (ULA.brownianCoordinates W (a + t).toNNReal ω -
          ULA.brownianCoordinates W a.toNNReal ω)) := by
  filter_upwards [K.coeFn_compLp (ULA.brownianLangevinNoise Q W hW a t),
    Lp.coeFn_smul (Real.sqrt 2)
      (ULA.brownianCoordinatesRealLp Q W hW (a + t) - ULA.brownianCoordinatesRealLp Q W hW a),
    Lp.coeFn_sub (ULA.brownianCoordinatesRealLp Q W hW (a + t))
      (ULA.brownianCoordinatesRealLp Q W hW a),
    ULA.brownianCoordinatesLp_coe Q W hW (a + t).toNNReal,
    ULA.brownianCoordinatesLp_coe Q W hW a.toNNReal] with ω hK hs hd ht ha
  change (K.compLp (ULA.brownianLangevinNoise Q W hW a t)) ω = _
  rw [hK]
  simp only [ULA.brownianLangevinNoise]
  rw [hs]
  simp only [Pi.smul_apply]
  rw [hd]
  simp only [Pi.sub_apply, ULA.brownianCoordinatesRealLp]
  rw [ht, ha]

end Coercion

namespace ParticleBrownianInput
variable {A Z J : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z] [MeasurableSpace Z]
  [Fintype J]

/-- Extract one particle's spatial vector from the flattened noise vector. -/
def row (N : ℕ) (i : Fin N) : EuclideanSpace ℝ (Fin N × J) →L[ℝ] EuclideanSpace ℝ J :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : J => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j : J => EuclideanSpace.proj (i, j))

@[simp] theorem row_apply (N : ℕ) (i : Fin N) (x : EuclideanSpace ℝ (Fin N × J)) (j : J) :
    row N i x j = x (i, j) := rfl

/-- Actual block-column diffusion with exactly zero optimiser input. -/
def diffusion (N : ℕ) (K : EuclideanSpace ℝ J →L[ℝ] Z) :
    EuclideanSpace ℝ (Fin N × J) →L[ℝ] (A × (Fin N → Z)) :=
  (ContinuousLinearMap.inr ℝ A (Fin N → Z)).comp
    (ContinuousLinearMap.pi fun i : Fin N => K.comp (row N i))

@[simp] theorem diffusion_apply (N : ℕ) (K : EuclideanSpace ℝ J →L[ℝ] Z)
    (x : EuclideanSpace ℝ (Fin N × J)) :
    diffusion (A := A) N K x = (0, fun i => K (row N i x)) := rfl

variable (μ : Measure Z) [IsProbabilityMeasure μ] (N : ℕ)

/-- Actual Brownian coordinates on the product initial/noise seed space. -/
def coordinate (ij : Fin N × J) (t : ℝ≥0)
    (ω : Fin N → Z × ULA.CanonicalBrownian.VectorSample J) : ℝ :=
  ULA.CanonicalBrownian.coordinate ij.2 t (ω ij.1).2

theorem coordinate_isPreBrownian (ij : Fin N × J) :
    IsPreBrownianReal (coordinate (Z := Z) N ij) (ParticleNoiseSpace.probability (J := J) μ N) where
  hasLaw s := (ULA.CanonicalBrownian.coordinate_isPreBrownian ij).hasLaw s |>.comp
    (ParticleNoiseSpace.noise_preserving μ N).hasLaw

/-- The independently copied one-sampler input is exactly the flattened
block input used for the actual interacting particle construction. -/
theorem packed_input_eq (K : EuclideanSpace ℝ J →L[ℝ] Z) (a t : ℝ) :
    independentReferenceCLM (A := A) (Z := Z)
      (μ.prod (ULA.CanonicalBrownian.vectorProbability J)) N
      (0, AdditiveCanonical.input (ULA.CanonicalBrownian.vectorProbability J) μ
        (samplerBrownianInput (ULA.CanonicalBrownian.vectorProbability J) K
          ULA.CanonicalBrownian.coordinate ULA.CanonicalBrownian.coordinate_isPreBrownian a) t) =
      samplerBrownianInput (ParticleNoiseSpace.probability (J := J) μ N)
        (diffusion (A := A) N K) (coordinate (Z := Z) N)
        (coordinate_isPreBrownian μ N) a t := by
  let R := ULA.CanonicalBrownian.vectorProbability J
  let Q := μ.prod R
  let QN := IndependentCopies.seeds (J := Fin N) Q
  let W := ULA.CanonicalBrownian.coordinate (I := J)
  let hW := ULA.CanonicalBrownian.coordinate_isPreBrownian (I := J)
  let B := samplerBrownianInput R K W hW a
  have hB := samplerBrownianInput_coe R K W hW a t
  have hinput : AdditiveCanonical.input R μ B t =ᵐ[Q] fun p => K (Real.sqrt 2 •
      (ULA.brownianCoordinates W (a + t).toNNReal p.2 - ULA.brownianCoordinates W a.toNNReal p.2)) :=
    (lpPullback_coe (measurePreserving_snd (μ := μ) (ν := R)) _).trans
      ((measurePreserving_snd (μ := μ) (ν := R)).quasiMeasurePreserving.ae_eq_comp hB)
  have hall : ∀ᵐ ω ∂QN, ∀ i : Fin N, AdditiveCanonical.input R μ B t (ω i) =
      K (Real.sqrt 2 • (ULA.brownianCoordinates W (a + t).toNNReal (ω i).2 -
        ULA.brownianCoordinates W a.toNNReal (ω i).2)) := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : Fin N => Q) i).quasiMeasurePreserving.ae_eq_comp hinput
  change independentReferenceCLM (A := A) (Z := Z) Q N (0, AdditiveCanonical.input R μ B t) =
    samplerBrownianInput QN (diffusion (A := A) N K) (coordinate (Z := Z) N)
      (coordinate_isPreBrownian μ N) a t
  apply Lp.ext
  filter_upwards [independentReferenceCLM_coe (A := A) (Z := Z) Q N
      (0, AdditiveCanonical.input R μ B t), hall,
    samplerBrownianInput_coe QN (diffusion (A := A) N K) (coordinate (Z := Z) N)
      (coordinate_isPreBrownian μ N) a t] with ω hp hall hf
  rw [hp, hf, diffusion_apply]
  apply Prod.ext
  · rfl
  · funext i
    dsimp only
    rw [hall i]
    congr 1

end ParticleBrownianInput
end PBGSO
