import PBGSO.HypocoerciveCriterion
import PBGSO.AdditiveJointBridge
import PBGSO.HigherOrderConsistency
import PBGSO.MethodParticles
import PBGSO.ParticleProcess

/-! # The proposed implementations as actual general models

The optimiser and sampler forces are independent primitive Lipschitz maps.
Both actual model coefficients and their primitive mean-field Lipschitz data
are constructed. Auxiliary variables use genuine Hilbert product norms; no
common potential or equality of optimiser and sampler dimensions is required.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory
open scoped NNReal
namespace PBGSO
namespace ImplementationDynamics

section Helpers
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A Hilbert product discrepancy is bounded by the sum of its coordinates. -/
theorem phase_difference_le (x x' : E) (y y' : F) :
    ‖WithLp.toLp 2 (x, y) - WithLp.toLp 2 (x', y')‖ ≤ ‖x - x'‖ + ‖y - y'‖ := by
  have he : WithLp.toLp 2 (x, y) - WithLp.toLp 2 (x', y') =
      WithLp.toLp 2 (x - x', (0 : F)) + WithLp.toLp 2 ((0 : E), y - y') := by
    apply WithLp.ofLp_injective 2
    simp
  rw [he]
  exact (norm_add_le _ _).trans_eq (by
    rw [WithLp.norm_toLp_fst, WithLp.norm_toLp_snd])

/-- The exact force/damping difference uses only norm and scalar arithmetic. -/
theorem damped_difference_le (γ : ℝ) (f g p q : E) :
    ‖(-f - γ • p) - (-g - γ • q)‖ ≤ ‖f - g‖ + ‖γ‖ * ‖p - q‖ := by
  have he : (-f - γ • p) - (-g - γ • q) = -(f - g) - γ • (p - q) := by module
  rw [he]
  simpa only [norm_neg, norm_smul] using norm_sub_le (-(f - g)) (γ • (p - q))
end Helpers

section Momentum
variable {A X I : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [Fintype I]
  (F : A → X → A) (G : A → X → X) (LF LG : ℝ≥0)
  (hF : ∀ a b x y, ‖F a x - F b y‖ ≤ (LF : ℝ) * (‖a - b‖ + ‖x - y‖))
  (hG : ∀ a b x y, ‖G a x - G b y‖ ≤ (LG : ℝ) * (‖a - b‖ + ‖x - y‖))
  (γ : ℝ)

/-- Actual M-MFPO primitive maps, with all Lipschitz constants derived from
F/G and friction. The optimiser state is (parameter,momentum). -/
def momentumDynamics : LipschitzDynamics (HypocoercivePhase A) (HypocoercivePhase X) A where
  observation := fun s z => F s.fst z.fst
  response := fun p => WithLp.toLp 2 (p.1.snd, -p.2 - γ • p.1.snd)
  sampler := fun s z => WithLp.toLp 2 (z.snd, -G s.fst z.fst - γ • z.snd)
  observationLip := LF
  responseLip := 2 + ‖γ‖₊
  samplerLip := 1 + LG + ‖γ‖₊
  observation_state := by
    intro s
    apply LipschitzWith.of_dist_le_mul
    intro z w
    have hb := hF s.fst s.fst z.fst w.fst
    simp only [dist_eq_norm, sub_self, norm_zero, zero_add] at hb ⊢
    exact hb.trans (mul_le_mul_of_nonneg_left (WithLp.norm_fst_le _ (z - w)) LF.coe_nonneg)
  observation_parameter := by
    intro s t z
    have hb := hF s.fst t.fst z.fst z.fst
    simp only [sub_self, norm_zero, add_zero] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (WithLp.norm_fst_le _ (s - t)) LF.coe_nonneg)
  response_lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    rw [dist_eq_norm, dist_eq_norm]
    have hv : ‖p.1.snd - q.1.snd‖ ≤ ‖p - q‖ :=
      (WithLp.norm_snd_le _ (p.1 - q.1)).trans (norm_fst_le (p - q))
    have hg : ‖p.2 - q.2‖ ≤ ‖p - q‖ := norm_snd_le (p - q)
    have hb := (phase_difference_le p.1.snd q.1.snd
      (-p.2 - γ • p.1.snd) (-q.2 - γ • q.1.snd)).trans
        (add_le_add (le_refl _) (damped_difference_le γ p.2 q.2 p.1.snd q.1.snd))
    change _ ≤ (2 + ‖γ‖) * ‖p - q‖
    nlinarith [mul_le_mul_of_nonneg_left hv (norm_nonneg γ)]
  sampler_state := by
    intro s
    apply LipschitzWith.of_dist_le_mul
    intro z w
    rw [dist_eq_norm, dist_eq_norm]
    have hv : ‖z.snd - w.snd‖ ≤ ‖z - w‖ := WithLp.norm_snd_le _ (z - w)
    have hx : ‖z.fst - w.fst‖ ≤ ‖z - w‖ := WithLp.norm_fst_le _ (z - w)
    have hg := hG s.fst s.fst z.fst w.fst
    simp only [sub_self, norm_zero, zero_add] at hg
    have hg' := hg.trans (mul_le_mul_of_nonneg_left hx LG.coe_nonneg)
    have hb := (phase_difference_le z.snd w.snd
      (-G s.fst z.fst - γ • z.snd) (-G s.fst w.fst - γ • w.snd)).trans
        (add_le_add (le_refl _) (damped_difference_le γ (G s.fst z.fst) (G s.fst w.fst)
          z.snd w.snd))
    change _ ≤ (1 + (LG : ℝ) + ‖γ‖) * ‖z - w‖
    nlinarith [mul_le_mul_of_nonneg_left hv (norm_nonneg γ)]
  sampler_parameter := by
    intro s t z
    have hg := hG s.fst t.fst z.fst z.fst
    simp only [sub_self, norm_zero, add_zero] at hg
    have hs : ‖s.fst - t.fst‖ ≤ ‖s - t‖ := WithLp.norm_fst_le _ (s - t)
    have hb := (phase_difference_le z.snd z.snd
      (-G s.fst z.fst - γ • z.snd) (-G t.fst z.fst - γ • z.snd)).trans
        (add_le_add (le_refl _) (damped_difference_le γ (G s.fst z.fst) (G t.fst z.fst)
          z.snd z.snd))
    simp only [sub_self, norm_zero, mul_zero, zero_add, add_zero] at hb
    change _ ≤ (1 + (LG : ℝ) + ‖γ‖) * ‖s - t‖
    have hgs := hg.trans (mul_le_mul_of_nonneg_left hs LG.coe_nonneg)
    nlinarith [norm_nonneg (s - t), mul_nonneg (norm_nonneg γ) (norm_nonneg (s - t))]

/-- These are exactly the general model coefficients, with no force or
state-coordinate compatibility premise. Constant diffusion columns are free. -/
theorem momentum_compatibility (σ : I → HypocoercivePhase X) :
    AdditiveModelCompatibility (momentumDynamics F G LF LG hF hG γ)
      (heavyBallModel γ F G σ) where
  observation := by intros; rfl
  response := by intros; rfl
  sampler := by intros; rfl
  diffusion_constant := by intros; rfl

/-- The source optimiser parameter projection is actually nonexpansive. -/
theorem momentum_parameter_lipschitz (σ : I → HypocoercivePhase X) :
    LipschitzWith 1 (heavyBallModel γ F G σ).parameter := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simpa [dist_eq_norm, heavyBallModel] using WithLp.norm_fst_le _ (s - t)
end Momentum

/-- The source higher-order sampler uses genuine Hilbert coordinates x,u,v. -/
abbrev HigherOrderSampler (X : Type*) := WithLp 2 (X × WithLp 2 (X × X))

section HigherOrder
variable {A X I : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [Fintype I]
  (F : A → X → A) (G : A → X → X) (LF LG : ℝ≥0)
  (hF : ∀ a b x y, ‖F a x - F b y‖ ≤ (LF : ℝ) * (‖a - b‖ + ‖x - y‖))
  (hG : ∀ a b x y, ‖G a x - G b y‖ ≤ (LG : ℝ) * (‖a - b‖ + ‖x - y‖))
  (α γ : ℝ)

/-- Actual three-coordinate higher-order sampler vector field. -/
def higherOrderSamplerField (a : A) (z : HigherOrderSampler X) : HigherOrderSampler X :=
  WithLp.toLp 2 (z.snd.fst,
    WithLp.toLp 2 (-G a z.fst + γ • z.snd.snd, -γ • z.snd.fst - α • z.snd.snd))

/-- An exact coordinate norm budget for the actual higher-order drift. -/
theorem higherOrderSamplerField_difference_le (a b : A) (z w : HigherOrderSampler X) :
    ‖higherOrderSamplerField G α γ a z - higherOrderSamplerField G α γ b w‖ ≤
      ‖G a z.fst - G b w.fst‖ + (1 + ‖γ‖) * ‖z.snd.fst - w.snd.fst‖ +
        (‖γ‖ + ‖α‖) * ‖z.snd.snd - w.snd.snd‖ := by
  have h1 := phase_difference_le z.snd.fst w.snd.fst
    (WithLp.toLp 2 (-G a z.fst + γ • z.snd.snd, -γ • z.snd.fst - α • z.snd.snd))
    (WithLp.toLp 2 (-G b w.fst + γ • w.snd.snd, -γ • w.snd.fst - α • w.snd.snd))
  have h2 := phase_difference_le (-G a z.fst + γ • z.snd.snd)
    (-G b w.fst + γ • w.snd.snd) (-γ • z.snd.fst - α • z.snd.snd)
    (-γ • w.snd.fst - α • w.snd.snd)
  have h3 := damped_difference_le (-γ) (G a z.fst) (G b w.fst) z.snd.snd w.snd.snd
  have h4 := damped_difference_le α (γ • z.snd.fst) (γ • w.snd.fst) z.snd.snd w.snd.snd
  simp only [neg_smul, sub_neg_eq_add, norm_neg] at h3
  simp only [← neg_smul, ← smul_sub, norm_smul] at h4
  dsimp only [higherOrderSamplerField]
  linarith

/-- The actual HOL optimiser/sampler model. Only the final sampler
auxiliary coordinate receives diffusion, and the optimiser force stays F. -/
def higherOrderModel (σ : I → X) : Model A A (HigherOrderSampler X) X I where
  parameter := id
  position := WithLp.fst
  observation := F
  optimizer := fun _ _ g => -g
  drift := higherOrderSamplerField G α γ
  diffusion := fun _ _ i => WithLp.toLp 2 (0, WithLp.toLp 2 (0, σ i))

/-- Primitive Lipschitz dynamics for the actual independent HOL forces. -/
def higherOrderDynamics : LipschitzDynamics A (HigherOrderSampler X) A where
  observation := fun a z => F a z.fst
  response := fun p => -p.2
  sampler := higherOrderSamplerField G α γ
  observationLip := LF
  responseLip := 1
  samplerLip := 1 + LG + 2 * ‖γ‖₊ + ‖α‖₊
  observation_state := by
    intro a
    apply LipschitzWith.of_dist_le_mul
    intro z w
    have hb := hF a a z.fst w.fst
    simp only [dist_eq_norm, sub_self, norm_zero, zero_add] at hb ⊢
    exact hb.trans (mul_le_mul_of_nonneg_left (WithLp.norm_fst_le _ (z - w)) LF.coe_nonneg)
  observation_parameter := by
    intro a b z
    simpa only [sub_self, norm_zero, add_zero] using hF a b z.fst z.fst
  response_lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    simpa only [dist_eq_norm, neg_sub_neg, norm_sub_rev, NNReal.coe_one, one_mul, Prod.snd_sub]
      using norm_snd_le (p - q)
  sampler_state := by
    intro a
    apply LipschitzWith.of_dist_le_mul
    intro z w
    rw [dist_eq_norm, dist_eq_norm]
    have hx : ‖z.fst - w.fst‖ ≤ ‖z - w‖ := WithLp.norm_fst_le _ (z - w)
    have hu : ‖z.snd.fst - w.snd.fst‖ ≤ ‖z - w‖ :=
      (WithLp.norm_fst_le _ ((z - w).snd)).trans (WithLp.norm_snd_le _ (z - w))
    have hv : ‖z.snd.snd - w.snd.snd‖ ≤ ‖z - w‖ :=
      (WithLp.norm_snd_le _ ((z - w).snd)).trans (WithLp.norm_snd_le _ (z - w))
    have hg := hG a a z.fst w.fst
    simp only [sub_self, norm_zero, zero_add] at hg
    have hgs := hg.trans (mul_le_mul_of_nonneg_left hx LG.coe_nonneg)
    have hb := higherOrderSamplerField_difference_le G α γ a a z w
    change _ ≤ (1 + (LG : ℝ) + 2 * ‖γ‖ + ‖α‖) * ‖z - w‖
    nlinarith [mul_le_mul_of_nonneg_left hu (norm_nonneg γ),
      mul_le_mul_of_nonneg_left hv (norm_nonneg γ),
      mul_le_mul_of_nonneg_left hv (norm_nonneg α)]
  sampler_parameter := by
    intro a b z
    have hb := higherOrderSamplerField_difference_le G α γ a b z z
    simp only [sub_self, norm_zero, mul_zero, add_zero] at hb
    have hg := hG a b z.fst z.fst
    simp only [sub_self, norm_zero, add_zero] at hg
    change _ ≤ (1 + (LG : ℝ) + 2 * ‖γ‖ + ‖α‖) * ‖a - b‖
    nlinarith [norm_nonneg (a - b), mul_nonneg (norm_nonneg γ) (norm_nonneg (a - b)),
      mul_nonneg (norm_nonneg α) (norm_nonneg (a - b))]

/-- HOL's general-model compatibility is proved from its actual coefficient
definitions; no common potential or compatibility equation is supplied. -/
theorem higherOrder_compatibility (σ : I → X) :
    AdditiveModelCompatibility (higherOrderDynamics F G LF LG hF hG α γ)
      (higherOrderModel F G α γ σ) where
  observation := by intros; rfl
  response := by intros; rfl
  sampler := by intros; rfl
  diffusion_constant := by intros; rfl

/-- The actual HOL optimiser coordinate is the parameter itself. -/
theorem higherOrder_parameter_lipschitz (σ : I → X) :
    LipschitzWith 1 (higherOrderModel F G α γ σ).parameter := LipschitzWith.id
end HigherOrder

section RawCoordinates
variable {A X I : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [Fintype I]

/-- Repack the raw momentum-position implementation into its actual complete
optimiser and individual Hilbert sampler coordinates. -/
def momentumParticleState {N : ℕ}
    (z : (A × (Fin N → X)) × (A × (Fin N → X))) :
    HypocoercivePhase A × (Fin N → HypocoercivePhase X) :=
  (WithLp.toLp 2 (z.2.1, z.1.1), fun i => WithLp.toLp 2 (z.2.2 i, z.1.2 i))

/-- The original kinetic integral drift is exactly the actual model's
empirical optimiser plus its individual sampler drifts. -/
theorem momentum_particle_drift (N : ℕ) (F : A → X → A) (G : A → X → X)
    (γ t : ℝ) (σ : I → HypocoercivePhase X)
    (z : (A × (Fin N → X)) × (A × (Fin N → X))) :
    momentumParticleState
      (-Methods.coupledForce (Methods.particleMeanForce F) (Methods.particleSamplerForce G) z.2 -
        γ • z.1, z.1) =
      ((heavyBallModel γ F G σ).particleField N t
        (momentumParticleState z).1 (momentumParticleState z).2,
       fun i => (heavyBallModel γ F G σ).drift
        ((heavyBallModel γ F G σ).parameter (momentumParticleState z).1)
        ((momentumParticleState z).2 i)) := by
  apply Prod.ext
  · apply WithLp.ofLp_injective 2
    rfl
  · funext i
    apply WithLp.ofLp_injective 2
    rfl

/-- Repack the raw HOL implementation into complete individual sampler
coordinates, keeping the optimiser coordinate unchanged. -/
def higherOrderParticleState {N : ℕ} (z : Methods.HOLState A (Fin N → X)) :
    A × (Fin N → HigherOrderSampler X) :=
  (z.1, fun i => WithLp.toLp 2 (z.2.1 i, WithLp.toLp 2 (z.2.2.1 i, z.2.2.2 i)))

/-- The raw HOL integral drift is the genuine empirical general-model drift. -/
theorem higherOrder_particle_drift (N : ℕ) (F : A → X → A) (G : A → X → X)
    (α γ t : ℝ) (σ : I → X) (z : Methods.HOLState A (Fin N → X)) :
    higherOrderParticleState
      (Methods.holDrift (Methods.particleMeanForce F) (Methods.particleSamplerForce G) α γ z) =
      ((higherOrderModel F G α γ σ).particleField N t
        (higherOrderParticleState z).1 (higherOrderParticleState z).2,
       fun i => (higherOrderModel F G α γ σ).drift
        ((higherOrderModel F G α γ σ).parameter (higherOrderParticleState z).1)
        ((higherOrderParticleState z).2 i)) := by
  apply Prod.ext
  · rfl
  · funext i
    apply WithLp.ofLp_injective 2
    rfl

end RawCoordinates

end ImplementationDynamics
end PBGSO
