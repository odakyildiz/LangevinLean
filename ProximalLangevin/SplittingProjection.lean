import ProximalLangevin.SplittingLaw
import ProximalLangevin.Theorem
import UnadjustedLangevin.TransportMoments

set_option linter.style.header false

/-!
# Finite output moments and comparison with the original parameter center

These statements concern the actual PIPGLA recursion. The transport comparison
is a triangle inequality, independently of the later proof of a transport rate.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace ProximalLangevin

section Moments
variable {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    {N dθ dx : ℕ} (hN : 0 < N)
    {g₁ g₂ : IPLA.Joint dθ dx → ℝ} (lam γ : ℝ) (L₁ : ℝ≥0)
    (hg₁ : Differentiable ℝ g₁) (hLip : LipschitzWith L₁ (gradient g₁))
    (hg₂ : ConvexOn ℝ univ g₂) (hb : ∃ b : ℝ, ∀ z, b ≤ g₂ z)
    (hlam : 0 < lam)

include hN hg₁ hLip hg₂ hb hlam

/-- Every actual output law has a finite state second moment, without
Gaussianity or a convergence assumption. -/
theorem pipglaLaws_state_memLp (initial : Lp (IPLA.State N dθ dx) 2 Q)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 Q) (n : ℕ) :
    MemLp (fun z : IPLA.State N dθ dx => z) 2
      (pipglaLaws Q g₁ (prox g₂ lam) γ initial (fun k => noise k) n) := by
  rw [pipglaLaws_eq_lpLaw Q hN lam γ L₁ hg₁ hLip hg₂ hb hlam initial noise n]
  let X := lpPipglaChain Q hN lam γ L₁ hg₁ hLip hg₂ hb hlam initial noise n
  apply (memLp_map_measure_iff (by fun_prop)
    (Lp.aestronglyMeasurable X).aemeasurable).mpr
  exact Lp.memLp X

/-- The actual parameter error has finite second moment about every center. -/
theorem pipglaLaws_parameter_memLp (initial : Lp (IPLA.State N dθ dx) 2 Q)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 Q) (n : ℕ)
    (θ : EuclideanSpace ℝ (Fin dθ)) :
    MemLp (fun z => IPLA.parameterCLM z - θ) 2
      (pipglaLaws Q g₁ (prox g₂ lam) γ initial (fun k => noise k) n) := by
  have : IsProbabilityMeasure
      (pipglaLaws Q g₁ (prox g₂ lam) γ initial (fun k => noise k) n) :=
    pipglaLaws_isProbability Q hN lam γ L₁ hg₁ hLip hg₂ hb hlam initial noise n
  have h := pipglaLaws_state_memLp Q hN lam γ L₁ hg₁ hLip hg₂ hb hlam initial noise n
  exact (h.continuousLinearMap_comp IPLA.parameterCLM).sub (memLp_const θ)

end Moments

/-- A rigorous original-center comparison for the actual PIPGLA law. The
remaining transport term is its genuine Wasserstein distance to the smoothed
Gibbs target; this statement alone is not a convergence rate. -/
theorem pipgla_parameter_rms_original_le_transport
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    {N dθ dx : ℕ} (hN : 0 < N)
    {g₁ g₂ : IPLA.Joint dθ dx → ℝ} (m η lam γ : ℝ) (L₁ K : ℝ≥0)
    (hg₁ : Differentiable ℝ g₁) (hsc : StrongConvexOn univ m g₁)
    (hLip : LipschitzWith L₁ (gradient g₁))
    (hg₂ : ConvexOn ℝ univ g₂) (hb : ∃ b : ℝ, ∀ z, b ≤ g₂ z)
    (hK : LipschitzWith K g₂) (hm : 0 < m) (hη : 0 < η) (hlam : 0 < lam)
    (θU θη : EuclideanSpace ℝ (Fin dθ))
    (hmaxU : IPLA.IsMarginalMaximizer (fun z => g₁ z + g₂ z) θU)
    (hmaxη : IPLA.IsMarginalMaximizer (smoothedPotential g₁ g₂ η) θη)
    (initial : Lp (IPLA.State N dθ dx) 2 Q)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 Q) (n : ℕ) :
    Real.sqrt (∫ z, ‖IPLA.parameterCLM z - θU‖ ^ 2
      ∂(pipglaLaws Q g₁ (prox g₂ lam) γ initial (fun k => noise k) n)) ≤
      Real.sqrt (η * (K : ℝ) ^ 2 / m) +
      Real.sqrt ((dθ : ℝ) / ((N : ℝ) * m)) +
      ULA.wasserstein2Real
        (pipglaLaws Q g₁ (prox g₂ lam) γ initial (fun k => noise k) n)
        (IPLA.gibbsTarget (smoothedPotential g₁ g₂ η)) := by
  let V := smoothedPotential g₁ g₂ η
  let ρ := pipglaLaws Q g₁ (prox g₂ lam) γ initial (fun k => noise k) n
  have hV : Differentiable ℝ V := hg₁.add (moreau_differentiable hg₂ hb hη)
  have hscV : StrongConvexOn univ m V :=
    smoothed_strongConvex hsc (moreau_convex hg₂ hb hη)
  have : IsProbabilityMeasure ρ :=
    pipglaLaws_isProbability Q hN lam γ L₁ hg₁ hLip hg₂ hb hlam initial noise n
  have : IsProbabilityMeasure (@IPLA.gibbsTarget N dθ dx V) :=
    IPLA.gibbsTarget_isProbability hN V m hm hV hscV
  have hfinite : ULA.wasserstein2 ρ (IPLA.gibbsTarget V) ≠ ⊤ :=
    ULA.wasserstein2_ne_top_of_memLp _ _
      (pipglaLaws_state_memLp Q hN lam γ L₁ hg₁ hLip hg₂ hb hlam initial noise n)
      (IPLA.gibbsTarget_memLp hN V m hm hV hscV)
  have hc := sharp_gibbsTarget_parameter_concentration hN V m hm hV hscV θη hmaxη
  have hp := IPLA.projectedRMSReal_le_wasserstein2Real_add
    (@IPLA.parameterCLM N dθ dx) IPLA.norm_parameterCLM_le_one θη
    (Real.sqrt ((dθ : ℝ) / ((N : ℝ) * m))) (Real.sqrt_nonneg _) hfinite hc
  have hmem := pipglaLaws_parameter_memLp Q hN lam γ L₁ hg₁ hLip hg₂ hb hlam
    initial noise n θη
  rw [IPLA.projectedRMSReal_eq_sqrt_integral _ _ _ hmem.eLpNorm_ne_top] at hp
  have hmove := sqrt_integral_center_le ρ (@IPLA.parameterCLM N dθ dx) θU θη
    hmem.eLpNorm_ne_top
  rw [norm_sub_rev θη θU] at hmove
  have hdist := moreau_marginal_center_distance g₁ g₂ m η hg₁ hsc hg₂ hb hm hη hK
    θU θη hmaxU hmaxη
  dsimp [ρ, V] at hp hmove
  linarith

end ProximalLangevin
