import ProximalLangevin.SplittingEndpoint
import ProximalLangevin.SplittingProjection
import ProximalLangevin.ProxParameter

set_option linter.style.header false

/-!
# An original-model bound for the actual PIPGLA recursion

The equal-step stochastic coupling is combined with a pathwise proximal-
parameter comparison and the finite marginal-center perturbation theorem.
The conclusion is a proved replacement with explicit constants, not the
paper's printed heat-flow bound.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace ProximalLangevin

/-- Actual PIPGLA parameter RMS values at two positive proximal parameters
are separated by the proved pathwise parameter-sensitivity floor. -/
theorem pipgla_parameter_rms_prox_comparison
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    {N dθ dx : ℕ} (hN : 0 < N)
    {g₁ g₂ : IPLA.Joint dθ dx → ℝ} (m γ lam eta : ℝ) (L₁ K : ℝ≥0)
    (hg₁ : Differentiable ℝ g₁) (hsc : StrongConvexOn univ m g₁)
    (hLip : LipschitzWith L₁ (gradient g₁))
    (hg₂ : ConvexOn ℝ univ g₂) (hb : ∃ b, ∀ z, b ≤ g₂ z)
    (hK : LipschitzWith K g₂) (hm : 0 < m) (hmL : m ≤ (L₁ : ℝ))
    (hγ : 0 < γ) (hlam : 0 < lam) (heta : 0 < eta)
    (hsmall : γ ≤ 2 / (m + (L₁ : ℝ)))
    (initial : Lp (IPLA.State N dθ dx) 2 Q)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 Q) (n : ℕ)
    (θ : EuclideanSpace ℝ (Fin dθ)) :
    Real.sqrt (∫ z, ‖IPLA.parameterCLM z - θ‖ ^ 2
      ∂(pipglaLaws Q g₁ (prox g₂ lam) γ initial (fun k => noise k) n)) ≤
      Real.sqrt (∫ z, ‖IPLA.parameterCLM z - θ‖ ^ 2
        ∂(pipglaLaws Q g₁ (prox g₂ eta) γ initial (fun k => noise k) n)) +
      (K : ℝ) * |lam - eta| / (m * γ) := by
  let X := lpPipglaChain Q hN lam γ L₁ hg₁ hLip hg₂ hb hlam initial noise n
  let Y := lpPipglaChain Q hN eta γ L₁ hg₁ hLip hg₂ hb heta initial noise n
  let c := (K : ℝ) * |lam - eta| / (m * γ)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hpoint : ∀ᵐ ω ∂Q, ‖(X - Y) ω‖ ≤ c := by
    filter_upwards [Lp.coeFn_sub X Y,
      lpPipglaChain_coe Q hN lam γ L₁ hg₁ hLip hg₂ hb hlam initial noise n,
      lpPipglaChain_coe Q hN eta γ L₁ hg₁ hLip hg₂ hb heta initial noise n]
      with ω hsub hx hy
    rw [hsub]
    change ‖X ω - Y ω‖ ≤ c
    rw [hx, hy]
    simpa only [sub_self, norm_zero, mul_zero, zero_add] using
      pipglaChain_parameter_comparison_bound hN m γ lam eta L₁ K hg₁ hsc hLip
        hg₂ hb hK hm hmL hγ hlam heta hsmall (initial ω) (initial ω)
        (fun k => noise k ω) n
  have hXY : ‖X - Y‖ ≤ c := by
    simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hc hpoint
  let A := IPLA.parameterCLM.compLp X - Lp.const 2 Q θ
  let B := IPLA.parameterCLM.compLp Y - Lp.const 2 Q θ
  have hAB : A - B = IPLA.parameterCLM.compLp (X - Y) := by
    dsimp [A, B]
    rw [sub_sub_sub_cancel_right]
    exact (map_sub (IPLA.parameterCLM.compLpL 2 Q) X Y).symm
  have hn : ‖A‖ ≤ ‖B‖ + c := by
    have hproj := IPLA.parameterCLM.norm_compLp_le (X - Y)
    have hproj' : ‖IPLA.parameterCLM.compLp (X - Y)‖ ≤ ‖X - Y‖ := by
      exact hproj.trans (by simpa using (mul_le_mul_of_nonneg_right
        (@IPLA.norm_parameterCLM_le_one N dθ dx) (norm_nonneg (X - Y))))
    have ht := norm_le_norm_sub_add A B
    rw [hAB] at ht
    linarith
  have hnorm (a : ℝ) (ha : 0 < a) :
      let Z := lpPipglaChain Q hN a γ L₁ hg₁ hLip hg₂ hb ha initial noise n
      Real.sqrt (∫ z, ‖IPLA.parameterCLM z - θ‖ ^ 2
        ∂(pipglaLaws Q g₁ (prox g₂ a) γ initial (fun k => noise k) n)) =
        ‖IPLA.parameterCLM.compLp Z - Lp.const 2 Q θ‖ := by
    intro Z
    rw [pipglaLaws_eq_lpLaw Q hN a γ L₁ hg₁ hLip hg₂ hb ha initial noise n]
    rw [integral_map (Lp.aestronglyMeasurable Z).aemeasurable (by fun_prop)]
    have heq : (∫ ω, ‖IPLA.parameterCLM (Z ω) - θ‖ ^ 2 ∂Q) =
        ‖IPLA.parameterCLM.compLp Z - Lp.const 2 Q θ‖ ^ 2 := by
      rw [lp_norm_sq_eq_integral Q]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (IPLA.parameterCLM.compLp Z) (Lp.const 2 Q θ),
        IPLA.parameterCLM.coeFn_compLp Z, Lp.coeFn_const (μ := Q) (p := 2) (c := θ)]
        with ω hsub hp ht
      simp only [hsub, hp, ht, Pi.sub_apply, Function.const_apply]
    rw [heq, Real.sqrt_sq (norm_nonneg _)]
  rw [hnorm lam hlam, hnorm eta heta]
  exact hn

/-- A genuine finite-time original-center theorem for PIPGLA, for any positive
proximal parameter. In the paper's corridor the additional sensitivity term
is `O(γ)`; the derived transport and center-bias terms are `O(sqrt γ)`.
All stationarity, moment, Brownian, and law-recurrence obligations are proved
in the imported endpoints rather than assumed here. -/
theorem pipgla_parameter_rms_original
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    {N dθ dx : ℕ} (hN : 0 < N) {g₁ g₂ : IPLA.Joint dθ dx → ℝ}
    (m γ lam : ℝ) (L₁ K : ℝ≥0)
    (hg₁ : Differentiable ℝ g₁) (hsc : StrongConvexOn univ m g₁)
    (hLip : LipschitzWith L₁ (gradient g₁))
    (hg₂ : ConvexOn ℝ univ g₂) (hb : ∃ b, ∀ z, b ≤ g₂ z)
    (hK : LipschitzWith K g₂) (hm : 0 < m) (hmL : m ≤ (L₁ : ℝ))
    (hγ : 0 < γ) (hlam : 0 < lam) (hsmall : γ ≤ 2 / (m + (L₁ : ℝ)))
    (θU θγ : EuclideanSpace ℝ (Fin dθ))
    (hmaxU : IPLA.IsMarginalMaximizer (fun z => g₁ z + g₂ z) θU)
    (hmaxγ : IPLA.IsMarginalMaximizer (smoothedPotential g₁ g₂ γ) θγ)
    (initial : Lp (IPLA.State N dθ dx) 2 Q)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 Q)
    (hGaussian : IPLA.GaussianInnovations Q initial noise) (n : ℕ) :
    Real.sqrt (∫ z, ‖IPLA.parameterCLM z - θU‖ ^ 2
      ∂(pipglaLaws Q g₁ (prox g₂ lam) γ initial (fun k => noise k) n)) ≤
      (K : ℝ) * |lam - γ| / (m * γ) +
      Real.sqrt (γ * (K : ℝ) ^ 2 / m) +
      Real.sqrt ((dθ : ℝ) / ((N : ℝ) * m)) +
      Real.sqrt ((1 - m * γ) ^ n *
        ULA.wasserstein2Real (Q.map initial)
          (IPLA.gibbsTarget (smoothedPotential g₁ g₂ γ)) ^ 2 +
        (γ / N) * pipglaTransportConstant N dθ dx m L₁ K) := by
  have hcompare := pipgla_parameter_rms_prox_comparison Q hN m γ lam γ L₁ K
    hg₁ hsc hLip hg₂ hb hK hm hmL hγ hlam hγ hsmall initial noise n θU
  have htriangle := pipgla_parameter_rms_original_le_transport Q hN m γ γ γ L₁ K
    hg₁ hsc hLip hg₂ hb hK hm hγ hγ θU θγ hmaxU hmaxγ initial noise n
  have htransport := (pipgla_equal_step_transport_sq Q hN m γ L₁ K hg₁ hsc hLip
    hg₂ hb hK hm hmL hγ hsmall initial noise hGaussian n).2
  have hsqrt := Real.sqrt_le_sqrt htransport
  have hWnonneg : 0 ≤ ULA.wasserstein2Real
      (pipglaLaws Q g₁ (prox g₂ γ) γ initial (fun k => noise k) n)
      (IPLA.gibbsTarget (smoothedPotential g₁ g₂ γ)) := ENNReal.toReal_nonneg
  rw [Real.sqrt_sq hWnonneg] at hsqrt
  linarith

end ProximalLangevin
