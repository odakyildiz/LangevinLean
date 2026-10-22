import ProximalLangevin.Algorithms
import ProximalLangevin.Moreau
import ProximalLangevin.SharpIPLA

set_option linter.style.header false

/-!
# A proved finite-time theorem for the actual MYIPLA recursion

The scalar potential used in this module is `g₁ + e`. When `e` is the
Moreau envelope, its differentiability, convexity, residual gradient and
smoothness follow from the proximal minimization theorems. The stochastic
bound is proved by identifying the displayed MYIPLA recursion with the
existing Gaussian IPLA chain; no error estimate is supplied as a hypothesis.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal

namespace ProximalLangevin

/-- The pair potential of MYIPLA, with only its nonsmooth part regularized. -/
def smoothedPotential {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (g₁ g₂ : E → ℝ) (η : ℝ) (x : E) : ℝ :=
  g₁ x + moreau g₂ η x

/-- Smoothing adds the inverse smoothing scale to the smooth gradient bound. -/
def smoothingLipschitz (L₁ : ℝ≥0) (η : ℝ) : ℝ≥0 := L₁ + η.toNNReal⁻¹

theorem smoothingLipschitz_coe (L₁ : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    (smoothingLipschitz L₁ η : ℝ) = (L₁ : ℝ) + η⁻¹ := by
  simp [smoothingLipschitz, Real.toNNReal_of_nonneg hη.le]

/-- Adding a convex envelope preserves the strong convexity of the smooth part. -/
theorem smoothed_strongConvex {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g₁ e : E → ℝ} {m : ℝ}
    (hsc : StrongConvexOn univ m g₁) (he : ConvexOn ℝ univ e) :
    StrongConvexOn univ m (fun x ↦ g₁ x + e x) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h₁ := hsc.2 hx hy ha hb hab
  have h₂ := he.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h₁ h₂ ⊢
  linarith

/-- The gradient Lipschitz constants of the smooth part and envelope add. -/
theorem smoothed_gradient_lipschitz {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    {g₁ e : E → ℝ} {L₁ L₂ : ℝ≥0}
    (hg₁ : Differentiable ℝ g₁) (he : Differentiable ℝ e)
    (h₁ : LipschitzWith L₁ (gradient g₁)) (h₂ : LipschitzWith L₂ (gradient e)) :
    LipschitzWith (L₁ + L₂) (gradient (fun x ↦ g₁ x + e x)) := by
  have hsum : gradient (fun x ↦ g₁ x + e x) = fun x ↦ gradient g₁ x + gradient e x :=
    funext (gradient_add_of_differentiable hg₁ he)
  rw [hsum]
  exact h₁.add h₂

/-- The law of the expanded MYIPLA recursion, for arbitrary supplied maps. -/
def myiplaLaws {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    {N dθ dx : ℕ} (g₁ : IPLA.Joint dθ dx → ℝ)
    (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx) (η γ : ℝ)
    (initial : Ω → IPLA.State N dθ dx) (noise : ℕ → Ω → IPLA.State N dθ dx)
    (n : ℕ) : Measure (IPLA.State N dθ dx) :=
  Q.map (fun ω ↦ myiplaChain g₁ P η γ (initial ω) (fun k ↦ noise k ω) n)

/-- Pointwise equivalence identifies the actual MYIPLA law with the IPLA law. -/
theorem myiplaLaws_eq_iplaLaws {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] {N dθ dx : ℕ} (hN : 0 < N)
    {g₁ e : IPLA.Joint dθ dx → ℝ} (hg₁ : Differentiable ℝ g₁)
    (he : Differentiable ℝ e) (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx)
    {η : ℝ} (hη : η ≠ 0)
    (hgrad : ∀ x, gradient e x = η⁻¹ • (x - P x)) (γ : ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient (fun x ↦ g₁ x + e x)))
    (initial : Lp (IPLA.State N dθ dx) 2 Q)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 Q) (n : ℕ) :
    myiplaLaws Q g₁ P η γ initial (fun k ↦ noise k) n =
      IPLA.laws Q (fun x ↦ g₁ x + e x) γ L (hg₁.add he) hLip initial noise n := by
  rw [IPLA.laws_eq_scaledChain]
  unfold myiplaLaws
  congr 1
  funext ω
  exact myiplaChain_eq_scaledChain hN hg₁ he P hη hgrad γ _ _ n

/-- Every projected MYIPLA error has a finite second moment whenever the
initialization and innovations are in `L²`. This is derived from the actual
chain, without Gaussianity, equilibrium, or an error bound assumption. -/
theorem myiplaLaws_parameter_memLp {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] {N dθ dx : ℕ} (hN : 0 < N)
    {g₁ e : IPLA.Joint dθ dx → ℝ} (hg₁ : Differentiable ℝ g₁)
    (he : Differentiable ℝ e) (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx)
    {η : ℝ} (hη : η ≠ 0)
    (hgrad : ∀ x, gradient e x = η⁻¹ • (x - P x)) (γ : ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient (fun x ↦ g₁ x + e x)))
    (initial : Lp (IPLA.State N dθ dx) 2 Q)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 Q) (n : ℕ)
    (θ : EuclideanSpace ℝ (Fin dθ)) :
    MemLp (fun z ↦ IPLA.parameterCLM z - θ) 2
      (myiplaLaws Q g₁ P η γ initial (fun k ↦ noise k) n) := by
  rw [myiplaLaws_eq_iplaLaws Q hN hg₁ he P hη hgrad γ L hLip]
  let chain := IPLA.lpChain Q (IPLA.potential (fun x ↦ g₁ x + e x)) (γ / N)
    (IPLA.potential_gradient_lipschitz (hg₁.add he) hLip) initial noise n
  change MemLp (fun z ↦ IPLA.parameterCLM z - θ) 2 (Q.map chain)
  apply (memLp_map_measure_iff (by fun_prop)
    (Lp.aestronglyMeasurable chain).aemeasurable).mpr
  exact ((Lp.memLp chain).continuousLinearMap_comp IPLA.parameterCLM).sub (memLp_const θ)

/-- An explicit finite-time RMS parameter bound for MYIPLA around the
maximizer of its smoothed marginal likelihood. All Gaussian-law hypotheses
describe the algorithm's actual innovations. The dependence on the smoothing
scale is explicit through `L₁ + η⁻¹`. -/
theorem myipla_parameter_rms_smoothed
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (N dθ dx : ℕ) (hN : 0 < N)
    {g₁ e : IPLA.Joint dθ dx → ℝ} (m η γ : ℝ) (L₁ : ℝ≥0)
    (hg₁ : Differentiable ℝ g₁) (hsc : StrongConvexOn univ m g₁)
    (hLip₁ : LipschitzWith L₁ (gradient g₁))
    (he : Differentiable ℝ e) (heconv : ConvexOn ℝ univ e)
    (hLipe : LipschitzWith η.toNNReal⁻¹ (gradient e))
    (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx)
    (hgrad : ∀ x, gradient e x = η⁻¹ • (x - P x))
    (hm : 0 < m) (hη : 0 < η) (hγ : 0 < γ)
    (hsmall : γ ≤ 2 / (m + (smoothingLipschitz L₁ η : ℝ)))
    (θStar : EuclideanSpace ℝ (Fin dθ))
    (hMaximizer : IPLA.IsMarginalMaximizer (fun x ↦ g₁ x + e x) θStar)
    (initial : Lp (IPLA.State N dθ dx) 2 Q)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 Q)
    (hGaussian : IPLA.GaussianInnovations Q initial noise) (n : ℕ) :
    Real.sqrt (∫ z, ‖IPLA.parameterCLM z - θStar‖ ^ 2
      ∂(myiplaLaws Q g₁ P η γ initial (fun k ↦ noise k) n)) ≤
      Real.sqrt ((dθ : ℝ) / ((N : ℝ) * m)) +
      (1 - m * γ) ^ n * ULA.wasserstein2Real (Q.map initial)
        (IPLA.gibbsTarget (fun x ↦ g₁ x + e x)) +
      (33 / 20 : ℝ) * ((smoothingLipschitz L₁ η : ℝ) / m) *
        Real.sqrt ((dx : ℝ) + (dθ : ℝ) / (N : ℝ)) * Real.sqrt γ := by
  have hLip : LipschitzWith (smoothingLipschitz L₁ η)
      (gradient (fun x ↦ g₁ x + e x)) :=
    smoothed_gradient_lipschitz hg₁ he hLip₁ hLipe
  rw [myiplaLaws_eq_iplaLaws Q hN hg₁ he P hη.ne' hgrad γ _ hLip]
  exact sharp_ipla_parameter_rms Q N dθ dx hN (fun x ↦ g₁ x + e x)
    m γ (smoothingLipschitz L₁ η) (hg₁.add he)
    (smoothed_strongConvex hsc heconv) hLip hm hγ hsmall θStar hMaximizer
    initial noise hGaussian n

/-- MYIPLA with the actual proximity minimizer and its actual Moreau envelope.
Every analytic envelope property used by the stochastic theorem is derived
from convexity and a lower bound on `g₂`. In particular, no residual-gradient
identity, stationarity result, concentration bound, or convergence estimate
is an additional hypothesis of this theorem. -/
theorem moreau_myipla_parameter_rms
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (N dθ dx : ℕ) (hN : 0 < N)
    {g₁ g₂ : IPLA.Joint dθ dx → ℝ} (m η γ : ℝ) (L₁ : ℝ≥0)
    (hg₁ : Differentiable ℝ g₁) (hsc : StrongConvexOn univ m g₁)
    (hLip₁ : LipschitzWith L₁ (gradient g₁))
    (hg₂ : ConvexOn ℝ univ g₂) (hb : ∃ b : ℝ, ∀ z, b ≤ g₂ z)
    (hm : 0 < m) (hη : 0 < η) (hγ : 0 < γ)
    (hsmall : γ ≤ 2 / (m + (smoothingLipschitz L₁ η : ℝ)))
    (θStar : EuclideanSpace ℝ (Fin dθ))
    (hMaximizer : IPLA.IsMarginalMaximizer (smoothedPotential g₁ g₂ η) θStar)
    (initial : Lp (IPLA.State N dθ dx) 2 Q)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 Q)
    (hGaussian : IPLA.GaussianInnovations Q initial noise) (n : ℕ) :
    Real.sqrt (∫ z, ‖IPLA.parameterCLM z - θStar‖ ^ 2
      ∂(myiplaLaws Q g₁ (prox g₂ η) η γ initial (fun k ↦ noise k) n)) ≤
      Real.sqrt ((dθ : ℝ) / ((N : ℝ) * m)) +
      (1 - m * γ) ^ n * ULA.wasserstein2Real (Q.map initial)
        (IPLA.gibbsTarget (smoothedPotential g₁ g₂ η)) +
      (33 / 20 : ℝ) * ((smoothingLipschitz L₁ η : ℝ) / m) *
        Real.sqrt ((dx : ℝ) + (dθ : ℝ) / (N : ℝ)) * Real.sqrt γ := by
  have hgrad : ∀ x, gradient (moreau g₂ η) x = η⁻¹ • (x - prox g₂ η x) := by
    intro x
    exact gradient_moreau hg₂ hb hη x
  have hgeq : gradient (moreau g₂ η) = residual g₂ η :=
    funext (gradient_moreau hg₂ hb hη)
  have hLipe : LipschitzWith η.toNNReal⁻¹ (gradient (moreau g₂ η)) := by
    rw [hgeq]
    simpa only [Real.toNNReal_inv] using residual_lipschitz hg₂ hb hη
  exact myipla_parameter_rms_smoothed Q N dθ dx hN m η γ L₁ hg₁ hsc hLip₁
    (moreau_differentiable hg₂ hb hη) (moreau_convex hg₂ hb hη) hLipe
    (prox g₂ η) hgrad hm hη hγ hsmall θStar hMaximizer initial noise hGaussian n

/-- Finite moments for MYIPLA with its genuine Moreau/proximal construction. -/
theorem moreau_myipla_parameter_memLp
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    {N dθ dx : ℕ} (hN : 0 < N)
    {g₁ g₂ : IPLA.Joint dθ dx → ℝ} (η γ : ℝ) (L₁ : ℝ≥0)
    (hg₁ : Differentiable ℝ g₁) (hLip₁ : LipschitzWith L₁ (gradient g₁))
    (hg₂ : ConvexOn ℝ univ g₂) (hb : ∃ b : ℝ, ∀ z, b ≤ g₂ z) (hη : 0 < η)
    (initial : Lp (IPLA.State N dθ dx) 2 Q)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 Q) (n : ℕ)
    (θ : EuclideanSpace ℝ (Fin dθ)) :
    MemLp (fun z ↦ IPLA.parameterCLM z - θ) 2
      (myiplaLaws Q g₁ (prox g₂ η) η γ initial (fun k ↦ noise k) n) := by
  have he := moreau_differentiable hg₂ hb hη
  have hgeq : gradient (moreau g₂ η) = residual g₂ η :=
    funext (gradient_moreau hg₂ hb hη)
  have hLipe : LipschitzWith η.toNNReal⁻¹ (gradient (moreau g₂ η)) := by
    rw [hgeq]
    simpa only [Real.toNNReal_inv] using residual_lipschitz hg₂ hb hη
  exact myiplaLaws_parameter_memLp Q hN hg₁ he (prox g₂ η) hη.ne'
    (gradient_moreau hg₂ hb hη) γ (smoothingLipschitz L₁ η)
    (smoothed_gradient_lipschitz hg₁ he hLip₁ hLipe) initial noise n θ

/-- The actual MYIPLA output is a probability law. Measurability follows
from the identified `L²` recursion, rather than being assumed for the map. -/
theorem moreau_myipla_isProbability
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    {N dθ dx : ℕ} (hN : 0 < N)
    {g₁ g₂ : IPLA.Joint dθ dx → ℝ} (η γ : ℝ) (L₁ : ℝ≥0)
    (hg₁ : Differentiable ℝ g₁) (hLip₁ : LipschitzWith L₁ (gradient g₁))
    (hg₂ : ConvexOn ℝ univ g₂) (hb : ∃ b : ℝ, ∀ z, b ≤ g₂ z) (hη : 0 < η)
    (initial : Lp (IPLA.State N dθ dx) 2 Q)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 Q) (n : ℕ) :
    IsProbabilityMeasure (myiplaLaws Q g₁ (prox g₂ η) η γ initial (fun k ↦ noise k) n) := by
  have he := moreau_differentiable hg₂ hb hη
  have hgeq : gradient (moreau g₂ η) = residual g₂ η :=
    funext (gradient_moreau hg₂ hb hη)
  have hLipe : LipschitzWith η.toNNReal⁻¹ (gradient (moreau g₂ η)) := by
    rw [hgeq]
    simpa only [Real.toNNReal_inv] using residual_lipschitz hg₂ hb hη
  have hLip := smoothed_gradient_lipschitz hg₁ he hLip₁ hLipe
  rw [myiplaLaws_eq_iplaLaws Q hN hg₁ he (prox g₂ η) hη.ne'
    (gradient_moreau hg₂ hb hη) γ _ hLip]
  unfold IPLA.laws
  constructor
  rw [Measure.map_apply_of_aemeasurable (Lp.aestronglyMeasurable _).aemeasurable
    MeasurableSet.univ, Set.preimage_univ, measure_univ]

end ProximalLangevin
