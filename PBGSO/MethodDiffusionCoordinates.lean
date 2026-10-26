import PBGSO.ImplementationLpCoordinates
import PBGSO.ParticleBrownianInput
import PBGSO.MethodBrownianMatching

/-! # Physical diffusion in the actual implementation coordinates
The canonical Euclidean particle encoding turns the block-column sampler
input into precisely the kinetic or final-auxiliary HOL Brownian input.
These are equalities of actual L² variables on the same probability space.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace PBGSO.ImplementationDynamics
open Methods
variable {Ω A J : Type*} {N : ℕ} [MeasurableSpace Ω] [Fintype J]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]

/-- Physical kinetic diffusion: Brownian motion acts only on momentum. -/
def momentumPhysicalDiffusion (γ : ℝ) : EuclideanSpace ℝ J →L[ℝ]
    HypocoercivePhase (EuclideanSpace ℝ J) where
  toFun x := WithLp.toLp 2 (0, Real.sqrt γ • x)
  map_add' := by intros; apply WithLp.ofLp_injective 2; simp [smul_add]
  map_smul' := by intros; apply WithLp.ofLp_injective 2; simp [smul_smul, mul_comm]
  cont := by fun_prop

@[simp] theorem momentumPhysicalDiffusion_apply (γ : ℝ) (x : EuclideanSpace ℝ J) :
    momentumPhysicalDiffusion γ x = WithLp.toLp 2 (0, Real.sqrt γ • x) := rfl

/-- Physical HOL diffusion: only the last sampler auxiliary is forced. -/
def higherOrderPhysicalDiffusion (α : ℝ) : EuclideanSpace ℝ J →L[ℝ]
    HigherOrderSampler (EuclideanSpace ℝ J) where
  toFun x := WithLp.toLp 2 (0, WithLp.toLp 2 (0, Real.sqrt α • x))
  map_add' := by
    intros; apply WithLp.ofLp_injective 2
    apply Prod.ext
    · simp
    · apply WithLp.ofLp_injective 2; simp [smul_add]
  map_smul' := by
    intros; apply WithLp.ofLp_injective 2
    apply Prod.ext
    · simp
    · apply WithLp.ofLp_injective 2; simp [smul_smul, mul_comm]
  cont := by fun_prop

@[simp] theorem higherOrderPhysicalDiffusion_apply (α : ℝ) (x : EuclideanSpace ℝ J) :
    higherOrderPhysicalDiffusion α x =
      WithLp.toLp 2 (0, WithLp.toLp 2 (0, Real.sqrt α • x)) := rfl

variable (Q : Measure Ω)
  (D : ParticleForceData A (EuclideanSpace ℝ J) (EuclideanSpace ℝ (Fin N × J)) N)
  (hcloud : D.cloud = euclideanParticleEncoding N J)
include hcloud

/-- The inverse actual kinetic coordinates give exactly the physical
flattened input, with all optimiser and position components zero. -/
theorem momentumEncoded_diffusion (γ : ℝ) (x : EuclideanSpace ℝ (Fin N × J)) :
    (momentumEncodedStateEquiv D).symm
      (ParticleBrownianInput.diffusion (A := HypocoercivePhase A) N
        (momentumPhysicalDiffusion (J := J) γ) x) = ((0, Real.sqrt γ • x), (0, 0)) := by
  simp only [momentumEncodedStateEquiv_symm_apply, ParticleBrownianInput.diffusion_apply,
    momentumPhysicalDiffusion_apply]
  rw [hcloud]
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · apply PiLp.ext
      intro ij
      rcases ij with ⟨i,j⟩
      rfl
  · apply Prod.ext
    · rfl
    · apply PiLp.ext
      intro ij
      rcases ij with ⟨i,j⟩
      rfl

/-- The inverse actual HOL coordinates give only the final auxiliary input. -/
theorem higherOrderEncoded_diffusion (α : ℝ) (x : EuclideanSpace ℝ (Fin N × J)) :
    (higherOrderEncodedStateEquiv D).symm
      (ParticleBrownianInput.diffusion (A := A) N (higherOrderPhysicalDiffusion (J := J) α) x) =
      holBrownianIncrement (Θ := A) (Real.sqrt α • x) := by
  simp only [higherOrderEncodedStateEquiv_symm_apply, ParticleBrownianInput.diffusion_apply,
    higherOrderPhysicalDiffusion_apply, holBrownianIncrement]
  rw [hcloud]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply PiLp.ext; intro ij; rcases ij with ⟨i,j⟩; rfl
    · apply Prod.ext
      · apply PiLp.ext; intro ij; rcases ij with ⟨i,j⟩; rfl
      · apply PiLp.ext; intro ij; rcases ij with ⟨i,j⟩; rfl

variable (W : (Fin N × J) → ℝ≥0 → Ω → ℝ)
  (hW : ∀ i, IsPreBrownianReal (W i) Q)

/-- Exact physical kinetic Brownian input on the actual source space. -/
theorem momentumUnpackLp_brownian (γ a t : ℝ) :
    momentumUnpackLp Q D (samplerBrownianInput Q
      (ParticleBrownianInput.diffusion (A := HypocoercivePhase A) N
        (momentumPhysicalDiffusion (J := J) γ)) W hW a t) =
      ((0, Real.sqrt γ • ULA.brownianLangevinNoise Q W hW a t), (0, 0)) := by
  apply phase_eq_of_ae Q
  filter_upwards [momentumUnpackLp_coe Q D (samplerBrownianInput Q
      (ParticleBrownianInput.diffusion (A := HypocoercivePhase A) N
        (momentumPhysicalDiffusion (J := J) γ)) W hW a t),
    samplerBrownianInput_coe Q (ParticleBrownianInput.diffusion (A := HypocoercivePhase A) N
        (momentumPhysicalDiffusion (J := J) γ)) W hW a t,
    Lp.coeFn_smul (Real.sqrt γ) (ULA.brownianLangevinNoise Q W hW a t),
    brownianLangevinNoise_coe Q W hW a t,
    Lp.coeFn_zero A 2 Q,
    Lp.coeFn_zero (EuclideanSpace ℝ (Fin N × J)) 2 Q] with ω hu hb hs hn hzA hzX
  rw [hu, hb, momentumEncoded_diffusion D hcloud]
  change ((0, _), (0, 0)) = (( (0 : Lp A 2 Q) ω, _), ((0 : Lp A 2 Q) ω, _))
  simp only [Pi.smul_apply, Pi.zero_apply] at hs hzA hzX
  rw [hzA, hzX, hs, hn]

/-- Exact physical HOL Brownian input on the actual source space. -/
theorem higherOrderUnpackLp_brownian (α a t : ℝ) :
    higherOrderUnpackLp Q D (samplerBrownianInput Q
      (ParticleBrownianInput.diffusion (A := A) N (higherOrderPhysicalDiffusion (J := J) α)) W hW a t) =
      holBrownianIncrement (Θ := Lp A 2 Q)
        (Real.sqrt α • ULA.brownianLangevinNoise Q W hW a t) := by
  apply hol_eq_of_ae Q
  filter_upwards [higherOrderUnpackLp_coe Q D (samplerBrownianInput Q
      (ParticleBrownianInput.diffusion (A := A) N (higherOrderPhysicalDiffusion (J := J) α)) W hW a t),
    samplerBrownianInput_coe Q (ParticleBrownianInput.diffusion (A := A) N
      (higherOrderPhysicalDiffusion (J := J) α)) W hW a t,
    Lp.coeFn_smul (Real.sqrt α) (ULA.brownianLangevinNoise Q W hW a t),
    brownianLangevinNoise_coe Q W hW a t,
    Lp.coeFn_zero A 2 Q,
    Lp.coeFn_zero (EuclideanSpace ℝ (Fin N × J)) 2 Q] with ω hu hb hs hn hzA hzX
  rw [hu, hb, higherOrderEncoded_diffusion D hcloud]
  dsimp only [holBrownianIncrement, Prod.snd, Prod.fst]
  change (0, 0, 0, _) = ((0 : Lp A 2 Q) ω, (0 : Lp (EuclideanSpace ℝ (Fin N × J)) 2 Q) ω,
    (0 : Lp (EuclideanSpace ℝ (Fin N × J)) 2 Q) ω, _)
  simp only [Pi.smul_apply, Pi.zero_apply] at hs hzA hzX
  rw [hzA, hzX, hs, hn]

end PBGSO.ImplementationDynamics
