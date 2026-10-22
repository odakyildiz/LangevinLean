import ProximalLangevin.MYPGD
import ProximalLangevin.MYPGDAlgorithm
import ProximalLangevin.Theorem

set_option linter.style.header false

/-! # A finite-time original-center theorem for the actual MYPGD algorithm

The comparison with full-noise MYIPLA is proved for the actual Gaussian
recursions. The additional finite-particle radius comes from exactly the
parameter noise removed by MYPGD. This is an explicit conservative replacement
for the paper's mean-field bound, with no propagation-of-chaos premise.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace ProximalLangevin

section ActualComparison
variable {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    {N dθ dx : ℕ} (hN : 0 < N) {g₁ g₂ : IPLA.Joint dθ dx → ℝ}
    (m η γ : ℝ) (L₁ : ℝ≥0)
    (hg₁ : Differentiable ℝ g₁) (hsc : StrongConvexOn univ m g₁)
    (hLip : LipschitzWith L₁ (gradient g₁))
    (hg₂ : ConvexOn ℝ univ g₂) (hb : ∃ b, ∀ z, b ≤ g₂ z)
    (hm : 0 < m) (hmL : m ≤ (smoothingLipschitz L₁ η : ℝ))
    (hη : 0 < η) (hγ : 0 < γ)
    (hsmall : γ ≤ 2 / (m + (smoothingLipschitz L₁ η : ℝ)))
    (initial : Lp (IPLA.State N dθ dx) 2 Q)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 Q)
    (hGaussian : IPLA.GaussianInnovations Q initial noise)

include hN hg₁ hsc hLip hg₂ hb hm hmL hη hγ hsmall hGaussian

/-- The actual MYPGD and MYIPLA laws have the proved finite transport bound.
Their common full Gaussian input is used only to identify the two different
Markov transitions; the MYPGD output has latent-only noise. -/
theorem mypgd_myipla_actual_transport_sq (n : ℕ) :
    ULA.wasserstein2
      (mypgdLaws Q g₁ (prox g₂ η) η γ initial (fun k => noise k) n)
      (myiplaLaws Q g₁ (prox g₂ η) η γ initial (fun k => noise k) n) ≠ ⊤ ∧
    ULA.wasserstein2Real
      (mypgdLaws Q g₁ (prox g₂ η) η γ initial (fun k => noise k) n)
      (myiplaLaws Q g₁ (prox g₂ η) η γ initial (fun k => noise k) n) ^ 2 ≤
      2 * (dθ : ℝ) / ((N : ℝ) * m) := by
  have hμ : MemLp (fun x : IPLA.State N dθ dx => x) 2 (Q.map initial) :=
    (memLp_map_measure_iff (by fun_prop)
      (Lp.aestronglyMeasurable initial).aemeasurable).mpr (Lp.memLp initial)
  have h := mypgd_myipla_markov_transport_sq hN m η γ L₁ hg₁ hsc hLip hg₂ hb
    hm hmL hη hγ hsmall (Q.map initial) hμ n
  rw [mypgdLaws_eq_markovLaws Q hN hg₁ hLip hg₂ hb hη γ initial noise hGaussian n,
    myiplaLaws_eq_markovLaws Q hN hg₁ hLip hg₂ hb hη γ initial noise hGaussian n]
  exact h

/-- Any parameter RMS for actual MYPGD is bounded by the corresponding
actual MYIPLA RMS plus an explicit finite-particle noise-removal radius. -/
theorem mypgd_parameter_rms_le_myipla (n : ℕ) (θ : EuclideanSpace ℝ (Fin dθ)) :
    Real.sqrt (∫ z, ‖IPLA.parameterCLM z - θ‖ ^ 2
      ∂(mypgdLaws Q g₁ (prox g₂ η) η γ initial (fun k => noise k) n)) ≤
      Real.sqrt (2 * (dθ : ℝ) / ((N : ℝ) * m)) +
      Real.sqrt (∫ z, ‖IPLA.parameterCLM z - θ‖ ^ 2
        ∂(myiplaLaws Q g₁ (prox g₂ η) η γ initial (fun k => noise k) n)) := by
  let μ := mypgdLaws Q g₁ (prox g₂ η) η γ initial (fun k => noise k) n
  let ν := myiplaLaws Q g₁ (prox g₂ η) η γ initial (fun k => noise k) n
  have htransport := mypgd_myipla_actual_transport_sq Q hN m η γ L₁ hg₁ hsc hLip hg₂ hb
    hm hmL hη hγ hsmall initial noise hGaussian n
  have hν : IPLA.projectedRMS ν (@IPLA.parameterCLM N dθ dx) θ ≠ ⊤ :=
    (moreau_myipla_parameter_memLp Q hN η γ L₁ hg₁ hLip hg₂ hb hη initial noise n θ).eLpNorm_ne_top
  let r := IPLA.projectedRMSReal ν (@IPLA.parameterCLM N dθ dx) θ
  have hr : 0 ≤ r := ENNReal.toReal_nonneg
  have hc : IPLA.projectedRMS ν (@IPLA.parameterCLM N dθ dx) θ ≤ ENNReal.ofReal r :=
    le_of_eq (ENNReal.ofReal_toReal hν).symm
  have hμ := IPLA.projectedRMS_ne_top (@IPLA.parameterCLM N dθ dx)
    IPLA.norm_parameterCLM_le_one θ r htransport.1 hc
  have hp := IPLA.projectedRMSReal_le_wasserstein2Real_add (@IPLA.parameterCLM N dθ dx)
    IPLA.norm_parameterCLM_le_one θ r hr htransport.1 hc
  rw [IPLA.projectedRMSReal_eq_sqrt_integral μ _ _ hμ] at hp
  have hr' : r = Real.sqrt (∫ z, ‖IPLA.parameterCLM z - θ‖ ^ 2 ∂ν) :=
    IPLA.projectedRMSReal_eq_sqrt_integral ν _ _ hν
  rw [hr'] at hp
  have hW := Real.sqrt_le_sqrt htransport.2
  have hW0 : 0 ≤ ULA.wasserstein2Real μ ν := ENNReal.toReal_nonneg
  rw [Real.sqrt_sq hW0] at hW
  linarith

end ActualComparison

/-- Fully proved finite-time original-center control for the actual MYPGD
Gaussian recursion. The extra `sqrt (2*dθ/(N*m))` is a conservative derived
comparison radius, not the source's unformalized mean-field constant. -/
theorem moreau_mypgd_parameter_rms_original
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (N dθ dx : ℕ) (hN : 0 < N)
    {g₁ g₂ : IPLA.Joint dθ dx → ℝ} (m η γ : ℝ) (L₁ K : ℝ≥0)
    (hg₁ : Differentiable ℝ g₁) (hsc : StrongConvexOn univ m g₁)
    (hLip : LipschitzWith L₁ (gradient g₁))
    (hg₂ : ConvexOn ℝ univ g₂) (hb : ∃ b, ∀ z, b ≤ g₂ z)
    (hK : LipschitzWith K g₂) (hm : 0 < m)
    (hmL : m ≤ (smoothingLipschitz L₁ η : ℝ)) (hη : 0 < η) (hγ : 0 < γ)
    (hsmall : γ ≤ 2 / (m + (smoothingLipschitz L₁ η : ℝ)))
    (θU θη : EuclideanSpace ℝ (Fin dθ))
    (hmaxU : IPLA.IsMarginalMaximizer (fun z => g₁ z + g₂ z) θU)
    (hmaxη : IPLA.IsMarginalMaximizer (smoothedPotential g₁ g₂ η) θη)
    (initial : Lp (IPLA.State N dθ dx) 2 Q)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 Q)
    (hGaussian : IPLA.GaussianInnovations Q initial noise) (n : ℕ) :
    Real.sqrt (∫ z, ‖IPLA.parameterCLM z - θU‖ ^ 2
      ∂(mypgdLaws Q g₁ (prox g₂ η) η γ initial (fun k => noise k) n)) ≤
      Real.sqrt (2 * (dθ : ℝ) / ((N : ℝ) * m)) +
      Real.sqrt (η * (K : ℝ) ^ 2 / m) +
      Real.sqrt ((dθ : ℝ) / ((N : ℝ) * m)) +
      (1 - m * γ) ^ n * ULA.wasserstein2Real (Q.map initial)
        (IPLA.gibbsTarget (smoothedPotential g₁ g₂ η)) +
      (33 / 20 : ℝ) * ((smoothingLipschitz L₁ η : ℝ) / m) *
        Real.sqrt ((dx : ℝ) + (dθ : ℝ) / (N : ℝ)) * Real.sqrt γ := by
  have hcompare := mypgd_parameter_rms_le_myipla Q hN m η γ L₁ hg₁ hsc hLip hg₂ hb
    hm hmL hη hγ hsmall initial noise hGaussian n θU
  have hbound := moreau_myipla_parameter_rms_original Q N dθ dx hN m η γ L₁ K
    hg₁ hsc hLip hg₂ hb hK hm hη hγ hsmall θU θη hmaxU hmaxη initial noise hGaussian n
  linarith

end ProximalLangevin
