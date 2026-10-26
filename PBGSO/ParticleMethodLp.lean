import PBGSO.GeneralProcess
import PBGSO.MethodParticles
import PBGSO.GaussianMethodBounds

/-!
# Pointwise L² lifting of the original finite-particle implementation forces

The optimiser is a random coordinate on the same probability space as every
particle. The cloud encoding is an explicit continuous linear equivalence;
it permits a Euclidean Gaussian cloud to represent the paper's particle array.
The empirical force and sampler force are constructed from the original `F`
and `G`. Their pointwise identification is proved, not postulated.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace PBGSO.Methods

section Pair
variable {Ω A C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  (Q : Measure Ω)

/-- Pair two random variables on their shared probability space, retaining
all dependence between the optimiser and the particle cloud. -/
def pairLp (a : Lp A 2 Q) (x : Lp C 2 Q) : Lp (A × C) 2 Q :=
  ((ContinuousLinearMap.inl ℝ A C).compLpL 2 Q) a +
    ((ContinuousLinearMap.inr ℝ A C).compLpL 2 Q) x

/-- The L² pairing is the actual pointwise pair almost everywhere. -/
theorem pairLp_coe (a : Lp A 2 Q) (x : Lp C 2 Q) :
    pairLp Q a x =ᵐ[Q] fun ω ↦ (a ω, x ω) := by
  filter_upwards [Lp.coeFn_add ((ContinuousLinearMap.inl ℝ A C).compLp a)
    ((ContinuousLinearMap.inr ℝ A C).compLp x),
    (ContinuousLinearMap.inl ℝ A C).coeFn_compLp a,
    (ContinuousLinearMap.inr ℝ A C).coeFn_compLp x] with ω ha h1 h2
  change (pairLp Q a x) ω = _
  rw [show pairLp Q a x = (ContinuousLinearMap.inl ℝ A C).compLp a +
    (ContinuousLinearMap.inr ℝ A C).compLp x from rfl, ha]
  simp only [Pi.add_apply]
  rw [h1, h2]
  simp

private theorem inlLp_norm_le (a : Lp A 2 Q) :
    ‖(ContinuousLinearMap.inl ℝ A C).compLp a‖ ≤ ‖a‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(ContinuousLinearMap.inl ℝ A C).coeFn_compLp a] with ω hω
  rw [hω]
  simp

private theorem inrLp_norm_le (x : Lp C 2 Q) :
    ‖(ContinuousLinearMap.inr ℝ A C).compLp x‖ ≤ ‖x‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(ContinuousLinearMap.inr ℝ A C).coeFn_compLp x] with ω hω
  rw [hω]
  simp

/-- The joint L² difference is controlled by the sum of marginal L² norms;
no independence between those marginals is used. -/
theorem pairLp_norm_sub_le (a b : Lp A 2 Q) (x y : Lp C 2 Q) :
    ‖pairLp Q a x - pairLp Q b y‖ ≤ ‖a - b‖ + ‖x - y‖ := by
  have he : pairLp Q a x - pairLp Q b y = pairLp Q (a - b) (x - y) := by
    unfold pairLp
    rw [map_sub, map_sub]
    module
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (inlLp_norm_le Q _) (inrLp_norm_le Q _))

/-- Evaluate a pair of L² coordinates on their shared sample. -/
def jointValue (s : Lp A 2 Q × Lp C 2 Q) (ω : Ω) : A × C := (s.1 ω, s.2 ω)

/-- Evaluate both momentum and position coordinates. -/
def phaseValue (z : (Lp A 2 Q × Lp C 2 Q) × (Lp A 2 Q × Lp C 2 Q))
    (ω : Ω) : (A × C) × (A × C) := (jointValue Q z.1 ω, jointValue Q z.2 ω)

theorem jointValue_add (s t : Lp A 2 Q × Lp C 2 Q) :
    ∀ᵐ ω ∂Q, jointValue Q (s + t) ω = jointValue Q s ω + jointValue Q t ω := by
  filter_upwards [Lp.coeFn_add s.1 t.1, Lp.coeFn_add s.2 t.2] with ω h1 h2
  exact Prod.ext h1 h2

theorem jointValue_sub (s t : Lp A 2 Q × Lp C 2 Q) :
    ∀ᵐ ω ∂Q, jointValue Q (s - t) ω = jointValue Q s ω - jointValue Q t ω := by
  filter_upwards [Lp.coeFn_sub s.1 t.1, Lp.coeFn_sub s.2 t.2] with ω h1 h2
  exact Prod.ext h1 h2

theorem jointValue_smul (r : ℝ) (s : Lp A 2 Q × Lp C 2 Q) :
    ∀ᵐ ω ∂Q, jointValue Q (r • s) ω = r • jointValue Q s ω := by
  filter_upwards [Lp.coeFn_smul r s.1, Lp.coeFn_smul r s.2] with ω h1 h2
  exact Prod.ext h1 h2

/-- OU stage correspondence is ordinary L² arithmetic; in particular a zero
optimiser innovation stays zero almost everywhere. -/
theorem ornsteinStep_Lp_coe (η σ : ℝ) (ξ : Lp A 2 Q × Lp C 2 Q)
    (z : (Lp A 2 Q × Lp C 2 Q) × (Lp A 2 Q × Lp C 2 Q)) :
    ∀ᵐ ω ∂Q,
      phaseValue Q (KineticLangevin.ornsteinStep η σ ξ z) ω =
        KineticLangevin.ornsteinStep η σ (jointValue Q ξ ω) (phaseValue Q z ω) := by
  filter_upwards [jointValue_add Q (η • z.1) (σ • ξ),
    jointValue_smul Q η z.1, jointValue_smul Q σ ξ] with ω ha hη hσ
  change (jointValue Q (η • z.1 + σ • ξ) ω, jointValue Q z.2 ω) = _
  rw [ha, hη, hσ]
  rfl

/-- The position drift stage has exactly the intended pointwise action. -/
theorem driftStep_Lp_coe (h : ℝ)
    (z : (Lp A 2 Q × Lp C 2 Q) × (Lp A 2 Q × Lp C 2 Q)) :
    ∀ᵐ ω ∂Q, phaseValue Q (KineticLangevin.driftStep h z) ω =
      KineticLangevin.driftStep h (phaseValue Q z ω) := by
  filter_upwards [jointValue_add Q z.2 (h • z.1), jointValue_smul Q h z.1] with ω ha hs
  change (jointValue Q z.1 ω, jointValue Q (z.2 + h • z.1) ω) = _
  rw [ha, hs]
  rfl

/-- Evaluate all four higher-order coordinates on one shared sample. -/
def holValue (z : HOLState (Lp A 2 Q) (Lp C 2 Q)) (ω : Ω) : HOLState A C :=
  (z.1 ω, z.2.1 ω, z.2.2.1 ω, z.2.2.2 ω)

/-- Finite L² affine arithmetic has its usual pointwise interpretation. -/
theorem linear5Lp_coe (r s t u v : ℝ) (a b c d e : Lp C 2 Q) :
    ∀ᵐ ω ∂Q, (r • a + s • b + t • c + u • d + v • e) ω =
      r • a ω + s • b ω + t • c ω + u • d ω + v • e ω := by
  filter_upwards [Lp.coeFn_add (r • a) (s • b),
    Lp.coeFn_add (r • a + s • b) (t • c),
    Lp.coeFn_add (r • a + s • b + t • c) (u • d),
    Lp.coeFn_add (r • a + s • b + t • c + u • d) (v • e),
    Lp.coeFn_smul r a, Lp.coeFn_smul s b, Lp.coeFn_smul t c,
    Lp.coeFn_smul u d, Lp.coeFn_smul v e] with ω h1 h2 h3 h4 ha hb hc hd he
  simp only [Pi.add_apply, Pi.smul_apply] at h1 h2 h3 h4 ha hb hc hd he
  rw [h4, h3, h2, h1, ha, hb, hc, hd, he]

end Pair

/-- Primitive raw finite-particle data, including an explicit cloud encoding.
The two forces need not derive from a joint potential. -/
structure ParticleForceData (A X C : Type*) (N : ℕ)
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup C] [NormedSpace ℝ C] where
  nonempty : 0 < N
  F : A → X → A
  G : A → X → X
  parameterLip : ℝ≥0
  samplerLip : ℝ≥0
  parameter_bound : ∀ a b x y,
    ‖F a x - F b y‖ ≤ (parameterLip : ℝ) * (‖a - b‖ + ‖x - y‖)
  sampler_bound : ∀ a b x y,
    ‖G a x - G b y‖ ≤ (samplerLip : ℝ) * (‖a - b‖ + ‖x - y‖)
  cloud : C ≃L[ℝ] (Fin N → X)

namespace ParticleForceData
variable {Ω A X C : Type*} {N : ℕ} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  (D : ParticleForceData A X C N)

/-- The actual empirical optimiser force in the supplied cloud coordinates. -/
def meanForce (s : A × C) : A := particleMeanForce D.F s.1 (D.cloud s.2)

/-- The actual per-particle sampler force, repacked in cloud coordinates. -/
def samplerForce (s : A × C) : C :=
  D.cloud.symm (particleSamplerForce D.G s.1 (D.cloud s.2))

/-- Explicit raw and lifted force constants, including the cloud coordinate
change. A product L² pairing will use these same constants. -/
def meanLip : ℝ≥0 := D.parameterLip * (1 + ‖D.cloud.toContinuousLinearMap‖₊)
def samplerForceLip : ℝ≥0 :=
  ‖D.cloud.symm.toContinuousLinearMap‖₊ * D.samplerLip *
    (1 + ‖D.cloud.toContinuousLinearMap‖₊)

/-- The empirical raw map is globally Lipschitz from the primitive force
assumption. No regularity of a numerical error sequence is assumed. -/
theorem meanForce_lipschitz : LipschitzWith D.meanLip D.meanForce := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [dist_eq_norm]
  have hm := particleMeanForce_lipschitz D.nonempty D.F (D.parameterLip : ℝ)
    D.parameterLip.coe_nonneg D.parameter_bound s.1 t.1 (D.cloud s.2) (D.cloud t.2)
  have he := D.cloud.toContinuousLinearMap.lipschitzWith.norm_sub_le s.2 t.2
  have hA : ‖s.1 - t.1‖ ≤ ‖s - t‖ := norm_fst_le (s - t)
  have hC : ‖s.2 - t.2‖ ≤ ‖s - t‖ := norm_snd_le (s - t)
  have henc := mul_le_mul_of_nonneg_left hC (norm_nonneg D.cloud.toContinuousLinearMap)
  change ‖particleMeanForce D.F s.1 (D.cloud s.2) -
    particleMeanForce D.F t.1 (D.cloud t.2)‖ ≤ _
  calc
    _ ≤ (D.parameterLip : ℝ) * (‖s.1 - t.1‖ + ‖D.cloud s.2 - D.cloud t.2‖) := hm
    _ ≤ (D.parameterLip : ℝ) *
        (‖s - t‖ + ‖D.cloud.toContinuousLinearMap‖ * ‖s - t‖) := by
      gcongr
      exact he.trans henc
    _ = _ := by simp [meanLip, NNReal.coe_mul, NNReal.coe_add]; ring

/-- The raw sampler map is globally Lipschitz with an explicit encoding cost. -/
theorem samplerForce_lipschitz : LipschitzWith D.samplerForceLip D.samplerForce := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [dist_eq_norm]
  have hg := particleSamplerForce_lipschitz D.G (D.samplerLip : ℝ)
    D.samplerLip.coe_nonneg D.sampler_bound s.1 t.1 (D.cloud s.2) (D.cloud t.2)
  have he := D.cloud.toContinuousLinearMap.lipschitzWith.norm_sub_le s.2 t.2
  have hi := D.cloud.symm.toContinuousLinearMap.lipschitzWith.norm_sub_le
    (particleSamplerForce D.G s.1 (D.cloud s.2))
    (particleSamplerForce D.G t.1 (D.cloud t.2))
  have hA : ‖s.1 - t.1‖ ≤ ‖s - t‖ := norm_fst_le (s - t)
  have hC : ‖s.2 - t.2‖ ≤ ‖s - t‖ := norm_snd_le (s - t)
  have henc := mul_le_mul_of_nonneg_left hC (norm_nonneg D.cloud.toContinuousLinearMap)
  calc
    _ ≤ ‖D.cloud.symm.toContinuousLinearMap‖ *
      ‖particleSamplerForce D.G s.1 (D.cloud s.2) -
        particleSamplerForce D.G t.1 (D.cloud t.2)‖ := hi
    _ ≤ ‖D.cloud.symm.toContinuousLinearMap‖ * ((D.samplerLip : ℝ) *
      (‖s - t‖ + ‖D.cloud.toContinuousLinearMap‖ * ‖s - t‖)) := by
      gcongr
      exact hg.trans (by gcongr; exact he.trans henc)
    _ = _ := by simp [samplerForceLip, NNReal.coe_mul, NNReal.coe_add]; ring

section Random
variable (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- Actual pointwise empirical force acting on the shared random optimiser
and random cloud. This is not an expectation over the sampling law. -/
def meanForceLp (a : Lp A 2 Q) (x : Lp C 2 Q) : Lp A 2 Q :=
  PBGSO.liftMap Q D.meanForce D.meanForce_lipschitz (pairLp Q a x)

/-- Actual pointwise sampler force in the same random coordinates. -/
def samplerForceLp (a : Lp A 2 Q) (x : Lp C 2 Q) : Lp C 2 Q :=
  PBGSO.liftMap Q D.samplerForce D.samplerForce_lipschitz (pairLp Q a x)

/-- The lifted optimiser force is the original finite empirical average
almost everywhere, using the same optimiser realisation for every particle. -/
theorem meanForceLp_coe (a : Lp A 2 Q) (x : Lp C 2 Q) :
    D.meanForceLp Q a x =ᵐ[Q] fun ω ↦
      (N : ℝ)⁻¹ • ∑ i, D.F (a ω) (D.cloud (x ω) i) := by
  filter_upwards [PBGSO.liftMap_coe Q D.meanForce D.meanForce_lipschitz (pairLp Q a x),
    pairLp_coe Q a x] with ω hf hp
  change (D.meanForceLp Q a x) ω = D.meanForce ((pairLp Q a x) ω) at hf
  rw [hf, hp]
  rfl

/-- Unpacking the lifted sampler force gives exactly the original force on
each particle, with the same shared random optimiser. -/
theorem samplerForceLp_coe (a : Lp A 2 Q) (x : Lp C 2 Q) :
    ∀ᵐ ω ∂Q, ∀ i : Fin N,
      D.cloud (D.samplerForceLp Q a x ω) i = D.G (a ω) (D.cloud (x ω) i) := by
  filter_upwards [PBGSO.liftMap_coe Q D.samplerForce D.samplerForce_lipschitz (pairLp Q a x),
    pairLp_coe Q a x] with ω hf hp
  change (D.samplerForceLp Q a x) ω = D.samplerForce ((pairLp Q a x) ω) at hf
  rw [hf, hp]
  simp [samplerForce, particleSamplerForce]

/-- Full cloud form of the same almost-everywhere sampler identification. -/
theorem samplerForceLp_coe_cloud (a : Lp A 2 Q) (x : Lp C 2 Q) :
    D.samplerForceLp Q a x =ᵐ[Q] fun ω ↦ D.samplerForce (a ω, x ω) := by
  filter_upwards [PBGSO.liftMap_coe Q D.samplerForce D.samplerForce_lipschitz (pairLp Q a x),
    pairLp_coe Q a x] with ω hf hp
  change (D.samplerForceLp Q a x) ω = D.samplerForce ((pairLp Q a x) ω) at hf
  rw [hf, hp]

/-- The actual random empirical force satisfies exactly the force assumption
used by the M-MFPO and HOL Gaussian-coordinate error theorems. -/
theorem meanForceLp_bound (a b : Lp A 2 Q) (x y : Lp C 2 Q) :
    ‖D.meanForceLp Q a x - D.meanForceLp Q b y‖ ≤
      (D.meanLip : ℝ) * (‖a - b‖ + ‖x - y‖) := by
  exact ((PBGSO.liftMap_lipschitz Q D.meanForce D.meanForce_lipschitz).norm_sub_le
    (pairLp Q a x) (pairLp Q b y)).trans
      (mul_le_mul_of_nonneg_left (pairLp_norm_sub_le Q a b x y) D.meanLip.coe_nonneg)

/-- The actual random coordinatewise sampler force satisfies the other
primitive force assumption of both Gaussian-coordinate error theorems. -/
theorem samplerForceLp_bound (a b : Lp A 2 Q) (x y : Lp C 2 Q) :
    ‖D.samplerForceLp Q a x - D.samplerForceLp Q b y‖ ≤
      (D.samplerForceLip : ℝ) * (‖a - b‖ + ‖x - y‖) := by
  exact ((PBGSO.liftMap_lipschitz Q D.samplerForce D.samplerForce_lipschitz).norm_sub_le
    (pairLp Q a x) (pairLp Q b y)).trans
      (mul_le_mul_of_nonneg_left (pairLp_norm_sub_le Q a b x y) D.samplerForceLip.coe_nonneg)

/-- Full raw force in encoded cloud coordinates. -/
def rawCoupledForce (q : A × C) : A × C := (D.meanForce q, D.samplerForce q)

/-- The complete coupled L² force is exactly the original raw force
samplewise, including the shared random optimiser. -/
theorem coupledForceLp_coe (q : Lp A 2 Q × Lp C 2 Q) :
    ∀ᵐ ω ∂Q,
      jointValue Q (coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) q) ω =
        D.rawCoupledForce (jointValue Q q ω) := by
  filter_upwards [D.meanForceLp_coe Q q.1 q.2,
    D.samplerForceLp_coe_cloud Q q.1 q.2] with ω hf hg
  exact Prod.ext hf hg

/-- The force kick acts pointwise by the original empirical optimiser and
coordinatewise sampler forces. -/
theorem kickStep_Lp_coe (h : ℝ)
    (z : (Lp A 2 Q × Lp C 2 Q) × (Lp A 2 Q × Lp C 2 Q)) :
    ∀ᵐ ω ∂Q,
      phaseValue Q (KineticLangevin.kickStep
        (coupledForce (D.meanForceLp Q) (D.samplerForceLp Q)) h z) ω =
      KineticLangevin.kickStep D.rawCoupledForce h (phaseValue Q z ω) := by
  let f := coupledForce (D.meanForceLp Q) (D.samplerForceLp Q)
  filter_upwards [jointValue_sub Q z.1 (h • f z.2),
    jointValue_smul Q h (f z.2), D.coupledForceLp_coe Q z.2] with ω hsub hs hf
  change (jointValue Q (z.1 - h • f z.2) ω, jointValue Q z.2 ω) = _
  rw [hsub, hs, hf]
  rfl

/-- The entire OBABO update on L² coordinates is the original raw update
almost everywhere. No pointwise update-identification assumption is used. -/
theorem obaboStep_Lp_coe (h η σ : ℝ)
    (z : (Lp A 2 Q × Lp C 2 Q) × (Lp A 2 Q × Lp C 2 Q))
    (ξ ξ' : Lp A 2 Q × Lp C 2 Q) :
    ∀ᵐ ω ∂Q,
      phaseValue Q (KineticLangevin.obaboStep
        (coupledForce (D.meanForceLp Q) (D.samplerForceLp Q)) h η σ z ξ ξ') ω =
      KineticLangevin.obaboStep D.rawCoupledForce h η σ
        (phaseValue Q z ω) (jointValue Q ξ ω) (jointValue Q ξ' ω) := by
  let f := coupledForce (D.meanForceLp Q) (D.samplerForceLp Q)
  let z0 := KineticLangevin.ornsteinStep η σ ξ z
  let z1 := KineticLangevin.kickStep f (h / 2) z0
  let z2 := KineticLangevin.driftStep h z1
  let z3 := KineticLangevin.kickStep f (h / 2) z2
  filter_upwards [ornsteinStep_Lp_coe Q η σ ξ z, D.kickStep_Lp_coe Q (h / 2) z0,
    driftStep_Lp_coe Q h z1, D.kickStep_Lp_coe Q (h / 2) z2,
    ornsteinStep_Lp_coe Q η σ ξ' z3] with ω h0 h1 h2 h3 h4
  change phaseValue Q (KineticLangevin.ornsteinStep η σ ξ' z3) ω = _
  rw [h4, h3, h2, h1, h0]
  rfl

/-- The complete HOL implementation, including the sequential random
parameter update and both original force lifts, acts by the raw update
almost everywhere. All four coordinates use the same sample. -/
theorem higherOrderStep_Lp_coe (α γ h : ℝ)
    (z : HOLState (Lp A 2 Q) (Lp C 2 Q)) (ξ : Lp C 2 Q × Lp C 2 Q × Lp C 2 Q) :
    ∀ᵐ ω ∂Q,
      holValue Q (higherOrderStep (D.meanForceLp Q) (D.samplerForceLp Q) α γ h z ξ) ω =
        higherOrderStep (fun a x ↦ D.meanForce (a, x))
          (fun a x ↦ D.samplerForce (a, x)) α γ h (holValue Q z ω)
          (ξ.1 ω, ξ.2.1 ω, ξ.2.2 ω) := by
  let θ := z.1 - h • D.meanForceLp Q z.1 z.2.1
  let Δ := h • D.samplerForceLp Q θ z.2.1
  let μ := holCoefficients α γ h
  have hθ : ∀ᵐ ω ∂Q, θ ω = z.1 ω - h • D.meanForce (z.1 ω, z.2.1 ω) := by
    filter_upwards [Lp.coeFn_sub z.1 (h • D.meanForceLp Q z.1 z.2.1),
      Lp.coeFn_smul h (D.meanForceLp Q z.1 z.2.1),
      D.meanForceLp_coe Q z.1 z.2.1] with ω hs hm hf
    change (z.1 - h • D.meanForceLp Q z.1 z.2.1) ω = _
    simp only [Pi.sub_apply, Pi.smul_apply] at hs hm
    rw [hs, hm, hf]
    rfl
  have hΔ : ∀ᵐ ω ∂Q, Δ ω = h • D.samplerForce (θ ω, z.2.1 ω) := by
    filter_upwards [Lp.coeFn_smul h (D.samplerForceLp Q θ z.2.1),
      D.samplerForceLp_coe_cloud Q θ z.2.1] with ω hs hg
    change (h • D.samplerForceLp Q θ z.2.1) ω = _
    simp only [Pi.smul_apply] at hs
    rw [hs, hg]
  have hx : ∀ᵐ ω ∂Q,
      (z.2.1 - (h / 2) • Δ + μ.μ12 • z.2.2.1 + μ.μ13 • z.2.2.2 + ξ.1) ω =
        z.2.1 ω + (-(h / 2)) • Δ ω + μ.μ12 • z.2.2.1 ω +
          μ.μ13 • z.2.2.2 ω + ξ.1 ω := by
    have he : z.2.1 - (h / 2) • Δ + μ.μ12 • z.2.2.1 + μ.μ13 • z.2.2.2 + ξ.1 =
        1 • z.2.1 + (-(h / 2)) • Δ + μ.μ12 • z.2.2.1 + μ.μ13 • z.2.2.2 + 1 • ξ.1 := by module
    rw [he]
    simpa only [one_smul] using linear5Lp_coe Q 1 (-(h / 2)) μ.μ12 μ.μ13 1
      z.2.1 Δ z.2.2.1 z.2.2.2 ξ.1
  have hu : ∀ᵐ ω ∂Q,
      (-Δ + μ.μ22 • z.2.2.1 + μ.μ23 • z.2.2.2 + ξ.2.1) ω =
        -Δ ω + μ.μ22 • z.2.2.1 ω + μ.μ23 • z.2.2.2 ω + ξ.2.1 ω := by
    have he : -Δ + μ.μ22 • z.2.2.1 + μ.μ23 • z.2.2.2 + ξ.2.1 =
        (-1 : ℝ) • Δ + μ.μ22 • z.2.2.1 + μ.μ23 • z.2.2.2 + 1 • ξ.2.1 + 0 • z.2.2.1 := by module
    rw [he]
    simpa only [neg_one_smul, one_smul, zero_smul, add_zero] using
      linear5Lp_coe Q (-1) μ.μ22 μ.μ23 1 0 Δ z.2.2.1 z.2.2.2 ξ.2.1 z.2.2.1
  have hv : ∀ᵐ ω ∂Q,
      (μ.μ31 • Δ + μ.μ32 • z.2.2.1 + μ.μ33 • z.2.2.2 + ξ.2.2) ω =
        μ.μ31 • Δ ω + μ.μ32 • z.2.2.1 ω + μ.μ33 • z.2.2.2 ω + ξ.2.2 ω := by
    have he : μ.μ31 • Δ + μ.μ32 • z.2.2.1 + μ.μ33 • z.2.2.2 + ξ.2.2 =
        μ.μ31 • Δ + μ.μ32 • z.2.2.1 + μ.μ33 • z.2.2.2 + 1 • ξ.2.2 + 0 • z.2.2.1 := by module
    rw [he]
    simpa only [one_smul, zero_smul, add_zero] using
      linear5Lp_coe Q μ.μ31 μ.μ32 μ.μ33 1 0 Δ z.2.2.1 z.2.2.2 ξ.2.2 z.2.2.1
  filter_upwards [hθ, hΔ, hx, hu, hv] with ω ht hd hxx huu hvv
  change (θ ω,
    (z.2.1 - (h / 2) • Δ + μ.μ12 • z.2.2.1 + μ.μ13 • z.2.2.2 + ξ.1) ω,
    (-Δ + μ.μ22 • z.2.2.1 + μ.μ23 • z.2.2.2 + ξ.2.1) ω,
    (μ.μ31 • Δ + μ.μ32 • z.2.2.1 + μ.μ33 • z.2.2.2 + ξ.2.2) ω) = _
  rw [hxx, huu, hvv, hd, ht]
  dsimp [higherOrderStep, holQuadratureStep, holResponse, holValue, μ]
  congr 1
  congr 1
  module

end Random
end ParticleForceData
/-- Explicit Euclidean cloud encoding: a flattened `(particle, coordinate)`
array is curried into the paper's collection of particle vectors. -/
def euclideanParticleEncoding (N : ℕ) (I : Type*) [Fintype I] :
    EuclideanSpace ℝ (Fin N × I) ≃L[ℝ] (Fin N → EuclideanSpace ℝ I) :=
  ((WithLp.linearEquiv 2 ℝ (Fin N × I → ℝ)).trans
    ((LinearEquiv.curry ℝ ℝ (Fin N) I).trans
      (LinearEquiv.piCongrRight (fun _ : Fin N ↦
        (WithLp.linearEquiv 2 ℝ (I → ℝ)).symm)))).toContinuousLinearEquiv

/-- The constructed encoding reads exactly the intended particle coordinate. -/
@[simp] theorem euclideanParticleEncoding_apply (N : ℕ) (I : Type*) [Fintype I]
    (x : EuclideanSpace ℝ (Fin N × I)) (i : Fin N) (j : I) :
    euclideanParticleEncoding N I x i j = x (i, j) := rfl

/-- Encoding inverse simply repacks the original particle coordinates. -/
@[simp] theorem euclideanParticleEncoding_symm_apply (N : ℕ) (I : Type*) [Fintype I]
    (x : Fin N → EuclideanSpace ℝ I) (i : Fin N) (j : I) :
    (euclideanParticleEncoding N I).symm x (i, j) = x i j := rfl

section ParticleMomentumRate
variable {Ω A X I : Type*} {N : ℕ} [MeasurableSpace Ω] [Fintype I]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  (W : I → ℝ≥0 → Ω → ℝ) (hW : ∀ i, ProbabilityTheory.IsPreBrownianReal (W i) Q)
  (D : ParticleForceData A X (EuclideanSpace ℝ I) N)

/-- M-MFPO Gaussian finite-horizon bound for the proved pointwise lifts of
actual finite-particle empirical and sampler forces. The shared optimiser
and all its momenta are random variables on `Q`; no force-lift premise remains. -/
theorem m_mfpo_particle_lp_gaussian_finite_bound
    (γ h R P F : ℝ) (hγ : 0 ≤ γ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hR : 0 ≤ R) (hP : 0 ≤ P) (hforce : 0 ≤ F)
    (hpaths : iIndepFun
      (fun i ω (j : ℕ) ↦ W i ((j : ℝ≥0) * (h / 2).toNNReal) ω) Q)
    (p q : ℕ → ℝ → (Lp A 2 Q) × Lp (EuclideanSpace ℝ I) 2 Q) (n : ℕ)
    (hpInt : ∀ k, k < n → IntervalIntegrable (p k) volume 0 h)
    (hfInt : ∀ k, k < n → IntervalIntegrable
      (fun t ↦ coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) (q k t) + γ • p k t) volume 0 h)
    (hp : ∀ k, k < n → p k h = p k 0 -
      (∫ t in 0..h, coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) (q k t) + γ • p k t) +
      momentumGaussianIncrement (Θ := Lp A 2 Q) Q W hW γ h k)
    (hq : ∀ k, k < n → q k h = q k 0 + (∫ t in 0..h, p k t))
    (hcompat : ∀ k, k < n → p (k + 1) 0 = p k h ∧ q (k + 1) 0 = q k h)
    (hmod : ∀ k, k < n → ∀ t, t ∈ Set.Icc 0 h →
      ‖p k t - p k 0‖ ≤ R * Real.sqrt t ∧ ‖q k t - q k 0‖ ≤ R * Real.sqrt t)
    (hpbound : ∀ k, k < n → ‖p k 0‖ ≤ P)
    (hfbound : ∀ k, k < n → ‖coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) (q k 0)‖ ≤ F)
    (z : ((Lp A 2 Q) × Lp (EuclideanSpace ℝ I) 2 Q) × ((Lp A 2 Q) × Lp (EuclideanSpace ℝ I) 2 Q)) :
    phaseError
      (trajectory (fun s r ↦ KineticLangevin.obaboStep (coupledForce (D.meanForceLp Q) (D.samplerForceLp Q)) h
        (Real.exp (-γ * h / 2)) (Real.sqrt (1 - Real.exp (-γ * h))) s r.1 r.2)
        (momentumGaussianNoise (Θ := Lp A 2 Q) Q W hW h) z n) (p n 0, q n 0) ≤
      Real.exp (momentumStabilityConstant (coupledLipschitzConstant (D.meanLip : ℝ) (D.samplerForceLip : ℝ)) * h * n) *
        (phaseError z (p 0 0, q 0 0) +
          (momentumLocalConsistencyConstant (coupledLipschitzConstant (D.meanLip : ℝ) (D.samplerForceLip : ℝ)) γ P F
              (Real.sqrt (Fintype.card I : ℝ)) +
            Real.sqrt γ * Real.sqrt (Fintype.card I : ℝ) +
            (3 / 2 : ℝ) * γ * Real.sqrt γ * Real.sqrt (Fintype.card I : ℝ) +
            (2 / 3 : ℝ) * (coupledLipschitzConstant (D.meanLip : ℝ) (D.samplerForceLip : ℝ) + γ + 1) * R) *
              (n * h) * Real.sqrt h) := by
  exact m_mfpo_gaussian_finite_bound (Θ := Lp A 2 Q) Q W hW
    (D.meanForceLp Q) (D.samplerForceLp Q) (D.meanLip : ℝ) (D.samplerForceLip : ℝ)
    γ h R P F D.meanLip.coe_nonneg D.samplerForceLip.coe_nonneg hγ hh hh1 hR hP hforce
    hpaths (D.meanForceLp_bound Q) (D.samplerForceLp_bound Q)
    p q n hpInt hfInt hp hq hcompat hmod hpbound hfbound z

end ParticleMomentumRate

section ParticleHOLRate
variable {A X : Type*} {N : ℕ}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  (I : Type*) [Fintype I] [DecidableEq I]
  (D : ParticleForceData A X (EuclideanSpace ℝ I) N)

/-- HOL-MYPGD Gaussian finite-horizon bound for the actual finite-particle
force lifts, including a shared random optimiser. The smoothed sampler force
may differ from the original optimiser force. No force-lift assumption remains. -/
theorem hol_mypgd_particle_lp_gaussian_finite_bound
    (α γ Fθ FG U V C : ℝ) (h : ℝ≥0)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hh : 0 < (h : ℝ)) (hh1 : (h : ℝ) ≤ 1)
    (hFθ : 0 ≤ Fθ) (hFG : 0 ≤ FG)
    (hU0 : 0 ≤ U) (hV0 : 0 ≤ V) (hC : 0 ≤ C)
    (r : ℕ → ℝ → HOLState (Lp A 2 (ULA.CanonicalBrownian.vectorProbability I)) (HOLGaussianSpace I)) (n : ℕ)
    (hInt : ∀ k, k < n → IntervalIntegrable (fun t ↦ holDrift (D.meanForceLp (ULA.CanonicalBrownian.vectorProbability I)) (D.samplerForceLp (ULA.CanonicalBrownian.vectorProbability I)) α γ (r k t)) volume 0 h)
    (heq : ∀ k, k < n → r k h = r k 0 + (∫ t in 0..h, holDrift (D.meanForceLp (ULA.CanonicalBrownian.vectorProbability I)) (D.samplerForceLp (ULA.CanonicalBrownian.vectorProbability I)) α γ (r k t)) +
      holBrownianIncrement (higherOrderGaussianIncrement I α γ h k))
    (hcompat : ∀ k, k < n → r (k + 1) 0 = r k h)
    (hmod : ∀ k, k < n → ∀ t, t ∈ Set.Icc 0 (h : ℝ) →
      ‖holDrift (D.meanForceLp (ULA.CanonicalBrownian.vectorProbability I)) (D.samplerForceLp (ULA.CanonicalBrownian.vectorProbability I)) α γ (r k t) - holDrift (D.meanForceLp (ULA.CanonicalBrownian.vectorProbability I)) (D.samplerForceLp (ULA.CanonicalBrownian.vectorProbability I)) α γ (r k 0)‖ ≤ C * Real.sqrt t)
    (hFbound : ∀ k, k < n → ‖(D.meanForceLp (ULA.CanonicalBrownian.vectorProbability I)) (r k 0).1 (r k 0).2.1‖ ≤ Fθ)
    (hGbound : ∀ k, k < n →
      ‖(D.samplerForceLp (ULA.CanonicalBrownian.vectorProbability I)) ((r k 0).1 - (h : ℝ) • (D.meanForceLp (ULA.CanonicalBrownian.vectorProbability I)) (r k 0).1 (r k 0).2.1) (r k 0).2.1‖ ≤ FG)
    (hU : ∀ k, k < n → ‖(r k 0).2.2.1‖ ≤ U)
    (hV : ∀ k, k < n → ‖(r k 0).2.2.2‖ ≤ V)
    (z : HOLState (Lp A 2 (ULA.CanonicalBrownian.vectorProbability I)) (HOLGaussianSpace I)) :
    holError (trajectory (higherOrderStep (D.meanForceLp (ULA.CanonicalBrownian.vectorProbability I)) (D.samplerForceLp (ULA.CanonicalBrownian.vectorProbability I)) α γ h)
      (higherOrderGaussianNoise I α γ h) z n) (r n 0) ≤
      Real.exp (holStabilityConstant α γ (D.meanLip : ℝ) (D.samplerForceLip : ℝ) * (h : ℝ) * n) *
        (holError z (r 0 0) +
          (holLocalConsistencyConstant (holRemainderConstants α γ) (D.samplerForceLip : ℝ) Fθ FG U V +
            Real.sqrt (Fintype.card I : ℝ) * holScalarNoiseConstant α γ +
            (8 / 3 : ℝ) * C) * (n * (h : ℝ)) * Real.sqrt (h : ℝ)) := by
  exact hol_mypgd_gaussian_finite_bound (Θ := Lp A 2 (ULA.CanonicalBrownian.vectorProbability I)) I
    (D.meanForceLp (ULA.CanonicalBrownian.vectorProbability I))
    (D.samplerForceLp (ULA.CanonicalBrownian.vectorProbability I))
    (D.meanLip : ℝ) (D.samplerForceLip : ℝ) α γ Fθ FG U V C h
    hα hγ hh hh1 D.meanLip.coe_nonneg D.samplerForceLip.coe_nonneg hFθ hFG hU0 hV0 hC
    (D.meanForceLp_bound (ULA.CanonicalBrownian.vectorProbability I))
    (D.samplerForceLp_bound (ULA.CanonicalBrownian.vectorProbability I))
    r n hInt heq hcompat hmod hFbound hGbound hU hV z

end ParticleHOLRate

end PBGSO.Methods
