import ProximalLangevin.Algorithms
import ProximalLangevin.StrongMoreau
import ProximalLangevin.SharpIPLA

set_option linter.style.header false


/-!
# PIPULA under a genuine strong-convexity assumption

The full nonsmooth potential is strongly convex. Its actual Moreau envelope
has modulus `m / (1 + m*γ)`, and PIPULA is exactly Gaussian IPLA for that
envelope with time step `γ`. The admissible-step condition is proved rather
than supplied. This is a corrected sufficient-assumption theorem; it is not
the paper's B1 statement and makes no claim about an original marginal center.
-/


noncomputable section
open MeasureTheory Set
open scoped NNReal

namespace ProximalLangevin

/-- Strong convexity after smoothing the entire potential. -/
def fullSmoothingModulus (m γ : ℝ) : ℝ := m / (1 + m * γ)

theorem fullSmoothingModulus_pos {m γ : ℝ} (hm : 0 < m) (hγ : 0 < γ) :
    0 < fullSmoothingModulus m γ := div_pos hm (by positivity)

/-- With smoothing equal to the time step, the envelope always meets the
proved Gaussian ULA step restriction. -/
theorem pipula_admissible_step {m γ : ℝ} (hm : 0 < m) (hγ : 0 < γ) :
    γ ≤ 2 / (fullSmoothingModulus m γ + γ⁻¹) := by
  have hd : 0 < 1 + m * γ := by positivity
  have hmod : 0 < fullSmoothingModulus m γ := fullSmoothingModulus_pos hm hγ
  have ht : γ * fullSmoothingModulus m γ ≤ 1 := by
    unfold fullSmoothingModulus
    rw [← mul_div_assoc, div_le_iff₀ hd]
    nlinarith
  rw [le_div_iff₀ (by positivity : 0 < fullSmoothingModulus m γ + γ⁻¹)]
  simpa only [mul_add, mul_inv_cancel₀ hγ.ne'] using (by linarith :
    γ * fullSmoothingModulus m γ + 1 ≤ 2)

/-- The probability law defined by the paper's pairwise PIPULA recursion. -/
def pipulaLaws {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    {N dθ dx : ℕ} (U : IPLA.Joint dθ dx → ℝ) (γ : ℝ)
    (initial : Ω → IPLA.State N dθ dx) (noise : ℕ → Ω → IPLA.State N dθ dx)
    (n : ℕ) : Measure (IPLA.State N dθ dx) :=
  Q.map (fun ω ↦ pipulaChain (prox U γ) γ (initial ω) (fun k ↦ noise k ω) n)

/-- Exact equality between the displayed PIPULA law and IPLA for the genuine
full Moreau envelope. -/
theorem pipulaLaws_eq_iplaLaws {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] {N dθ dx : ℕ} (hN : 0 < N)
    {U : IPLA.Joint dθ dx → ℝ} (hf : ConvexOn ℝ univ U)
    (hb : ∃ b : ℝ, ∀ z, b ≤ U z) {γ : ℝ} (hγ : 0 < γ)
    (initial : Lp (IPLA.State N dθ dx) 2 Q)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 Q) (n : ℕ) :
    pipulaLaws Q U γ initial (fun k ↦ noise k) n =
      IPLA.laws Q (moreau U γ) γ (γ⁻¹).toNNReal
        (moreau_differentiable hf hb hγ)
        (by simpa only [funext (gradient_moreau hf hb hγ)] using
          residual_lipschitz hf hb hγ) initial noise n := by
  rw [IPLA.laws_eq_scaledChain]
  unfold pipulaLaws
  congr 1
  funext ω
  rw [pipulaChain_eq_myiplaChain _ hγ.ne']
  simpa only [zero_add] using myiplaChain_eq_scaledChain hN (differentiable_const (0 : ℝ))
    (moreau_differentiable hf hb hγ) (prox U γ) hγ.ne'
    (gradient_moreau hf hb hγ) γ (initial ω) (fun k ↦ noise k ω) n

/-- A complete finite-time bound for PIPULA around the maximizer of the
smoothed marginal. The original potential may be nonsmooth and need not be
globally Lipschitz. All envelope properties, the time-step restriction,
normalization, finite transport moments, and equilibrium concentration are
proved from the displayed assumptions and the actual Gaussian innovations. -/
theorem pipula_parameter_rms_smoothed
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (N dθ dx : ℕ) (hN : 0 < N) {U : IPLA.Joint dθ dx → ℝ}
    (m γ : ℝ) (hm : 0 < m) (hγ : 0 < γ)
    (hsc : StrongConvexOn univ m U) (hb : ∃ b : ℝ, ∀ z, b ≤ U z)
    (θStar : EuclideanSpace ℝ (Fin dθ))
    (hmax : IPLA.IsMarginalMaximizer (moreau U γ) θStar)
    (initial : Lp (IPLA.State N dθ dx) 2 Q)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 Q)
    (hGaussian : IPLA.GaussianInnovations Q initial noise) (n : ℕ) :
    Real.sqrt (∫ z, ‖IPLA.parameterCLM z - θStar‖ ^ 2
      ∂pipulaLaws Q U γ initial (fun k ↦ noise k) n) ≤
      Real.sqrt ((dθ : ℝ) / ((N : ℝ) * fullSmoothingModulus m γ)) +
      (1 - fullSmoothingModulus m γ * γ) ^ n * ULA.wasserstein2Real
        (Q.map initial) (IPLA.gibbsTarget (moreau U γ)) +
      (33 / 20 : ℝ) * (γ⁻¹ / fullSmoothingModulus m γ) *
        Real.sqrt ((dx : ℝ) + (dθ : ℝ) / (N : ℝ)) * Real.sqrt γ := by
  have hf : ConvexOn ℝ univ U := hsc.convexOn (fun r ↦ by positivity)
  have he := moreau_differentiable hf hb hγ
  have heq : gradient (moreau U γ) = residual U γ :=
    funext (gradient_moreau hf hb hγ)
  have hLip : LipschitzWith (γ⁻¹).toNNReal (gradient (moreau U γ)) := by
    rw [heq]
    exact residual_lipschitz hf hb hγ
  have hco : ((γ⁻¹).toNNReal : ℝ) = γ⁻¹ := by
    simp [Real.toNNReal_of_nonneg (inv_nonneg.mpr hγ.le)]
  rw [pipulaLaws_eq_iplaLaws Q hN hf hb hγ]
  have hs : γ ≤ 2 / (fullSmoothingModulus m γ + ((γ⁻¹).toNNReal : ℝ)) := by
    rw [hco]
    exact pipula_admissible_step hm hγ
  simpa only [hco] using sharp_ipla_parameter_rms Q N dθ dx hN (moreau U γ)
    (fullSmoothingModulus m γ) γ (γ⁻¹).toNNReal he
    (moreau_strongConvex hm.le hsc hb hγ) hLip
    (fullSmoothingModulus_pos hm hγ) hγ hs θStar hmax initial noise hGaussian n

end ProximalLangevin
