import ProximalLangevin.MYIPLA
import ProximalLangevin.Perturbation
import ProximalLangevin.ProjectionCenter

set_option linter.style.header false


/-!
# Nonasymptotic comparison with the original nonsmooth statistical model

The exact Moreau value gap gives a finite square-root smoothing estimate for
the actual marginal maximizers. This replaces the paper's Taylor-based linear
asymptotic estimate; it neither asserts the same order nor assumes an
asymptotic remainder can be integrated.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProximalLangevin

/-- The true smoothed pair potential is a one-sided uniform approximation of
the original pair potential, with the sharp Lipschitz Moreau value gap. -/
theorem smoothedPotential_gap {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (g₁ g₂ : E → ℝ) (hg₂ : ConvexOn ℝ univ g₂)
    (hb : ∃ b : ℝ, ∀ z, b ≤ g₂ z) {η : ℝ} (hη : 0 < η)
    {K : ℝ≥0} (hK : LipschitzWith K g₂) (z : E) :
    smoothedPotential g₁ g₂ η z ≤ g₁ z + g₂ z ∧
      g₁ z + g₂ z ≤ smoothedPotential g₁ g₂ η z + η * (K : ℝ) ^ 2 / 2 := by
  have h := moreau_gap_of_lipschitz hg₂ hb hη hK z
  dsimp [smoothedPotential]
  constructor <;> linarith

/-- The original nonsmooth model has an actual marginal maximizer under the
primitive MYIPLA assumptions; no maximizer existence assumption is hidden. -/
theorem moreau_original_maximizer_exists {dθ dx : ℕ}
    (g₁ g₂ : IPLA.Joint dθ dx → ℝ) (m η : ℝ)
    (hg₁ : Differentiable ℝ g₁) (hsc : StrongConvexOn univ m g₁)
    (hg₂ : ConvexOn ℝ univ g₂) (hb : ∃ b : ℝ, ∀ z, b ≤ g₂ z)
    (hm : 0 < m) (hη : 0 < η) {K : ℝ≥0} (hK : LipschitzWith K g₂) :
    ∃ θ, IPLA.IsMarginalMaximizer (fun z ↦ g₁ z + g₂ z) θ := by
  exact exists_original_marginalMaximizer (fun z ↦ g₁ z + g₂ z)
    (smoothedPotential g₁ g₂ η) m hm (hg₁.continuous.add hK.continuous)
    (hg₁.add (moreau_differentiable hg₂ hb hη))
    (smoothed_strongConvex hsc (moreau_convex hg₂ hb hη))
    (fun z ↦ (smoothedPotential_gap g₁ g₂ hg₂ hb hη hK z).1)

/-- A genuine finite smoothing-bias bound for marginal maximizers. It holds
without twice differentiability, a fibrewise Hessian premise, or Taylor
remainders: squared displacement is at most `η*K²/m`. -/
theorem moreau_marginal_center_distance {dθ dx : ℕ}
    (g₁ g₂ : IPLA.Joint dθ dx → ℝ) (m η : ℝ)
    (hg₁ : Differentiable ℝ g₁) (hsc : StrongConvexOn univ m g₁)
    (hg₂ : ConvexOn ℝ univ g₂) (hb : ∃ b : ℝ, ∀ z, b ≤ g₂ z)
    (hm : 0 < m) (hη : 0 < η) {K : ℝ≥0} (hK : LipschitzWith K g₂)
    (θU θη : EuclideanSpace ℝ (Fin dθ))
    (hmaxU : IPLA.IsMarginalMaximizer (fun z ↦ g₁ z + g₂ z) θU)
    (hmaxη : IPLA.IsMarginalMaximizer (smoothedPotential g₁ g₂ η) θη) :
    ‖θU - θη‖ ≤ Real.sqrt (η * (K : ℝ) ^ 2 / m) := by
  have h := marginal_center_distance (fun z ↦ g₁ z + g₂ z)
    (smoothedPotential g₁ g₂ η) (η * (K : ℝ) ^ 2 / 2) m hm
    (hg₁.continuous.add hK.continuous)
    (hg₁.add (moreau_differentiable hg₂ hb hη))
    (smoothed_strongConvex hsc (moreau_convex hg₂ hb hη))
    (smoothedPotential_gap g₁ g₂ hg₂ hb hη hK) θU θη hmaxU hmaxη
  convert h using 1
  congr 1
  ring

/-- A fully proved finite-time theorem for the actual MYIPLA iterates and the
original nonsmooth model's marginal maximizer. This is a finite replacement
for the Taylor-based statement in v3 Theorem 4.1: the smoothing bias is
`sqrt (η*K²/m)`, and the discretization constant explicitly depends on `η`.
There are no interpolation, entropy-production, or convergence hypotheses. -/
theorem moreau_myipla_parameter_rms_original
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (N dθ dx : ℕ) (hN : 0 < N)
    {g₁ g₂ : IPLA.Joint dθ dx → ℝ} (m η γ : ℝ) (L₁ K : ℝ≥0)
    (hg₁ : Differentiable ℝ g₁) (hsc : StrongConvexOn univ m g₁)
    (hLip₁ : LipschitzWith L₁ (gradient g₁))
    (hg₂ : ConvexOn ℝ univ g₂) (hb : ∃ b : ℝ, ∀ z, b ≤ g₂ z)
    (hK : LipschitzWith K g₂) (hm : 0 < m) (hη : 0 < η) (hγ : 0 < γ)
    (hsmall : γ ≤ 2 / (m + (smoothingLipschitz L₁ η : ℝ)))
    (θU θη : EuclideanSpace ℝ (Fin dθ))
    (hmaxU : IPLA.IsMarginalMaximizer (fun z ↦ g₁ z + g₂ z) θU)
    (hmaxη : IPLA.IsMarginalMaximizer (smoothedPotential g₁ g₂ η) θη)
    (initial : Lp (IPLA.State N dθ dx) 2 Q)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 Q)
    (hGaussian : IPLA.GaussianInnovations Q initial noise) (n : ℕ) :
    Real.sqrt (∫ z, ‖IPLA.parameterCLM z - θU‖ ^ 2
      ∂(myiplaLaws Q g₁ (prox g₂ η) η γ initial (fun k ↦ noise k) n)) ≤
      Real.sqrt (η * (K : ℝ) ^ 2 / m) +
      Real.sqrt ((dθ : ℝ) / ((N : ℝ) * m)) +
      (1 - m * γ) ^ n * ULA.wasserstein2Real (Q.map initial)
        (IPLA.gibbsTarget (smoothedPotential g₁ g₂ η)) +
      (33 / 20 : ℝ) * ((smoothingLipschitz L₁ η : ℝ) / m) *
        Real.sqrt ((dx : ℝ) + (dθ : ℝ) / (N : ℝ)) * Real.sqrt γ := by
  let ρ := myiplaLaws Q g₁ (prox g₂ η) η γ initial (fun k ↦ noise k) n
  have : IsProbabilityMeasure ρ :=
    moreau_myipla_isProbability Q hN η γ L₁ hg₁ hLip₁ hg₂ hb hη initial noise n
  have hmem := moreau_myipla_parameter_memLp Q hN η γ L₁ hg₁ hLip₁ hg₂ hb hη
    initial noise n θη
  have hmove := sqrt_integral_center_le ρ (@IPLA.parameterCLM N dθ dx) θU θη
    hmem.eLpNorm_ne_top
  have hdist := moreau_marginal_center_distance g₁ g₂ m η hg₁ hsc hg₂ hb hm hη hK
    θU θη hmaxU hmaxη
  rw [norm_sub_rev θη θU] at hmove
  have hbound := moreau_myipla_parameter_rms Q N dθ dx hN m η γ L₁ hg₁ hsc hLip₁
    hg₂ hb hm hη hγ hsmall θη hmaxη initial noise hGaussian n
  dsimp [ρ] at hmove
  linarith

end ProximalLangevin
