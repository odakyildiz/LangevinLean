import ProximalLangevin.SharpConcentration
import IPLA.Theorem

set_option linter.style.header false

/-!
# Sharp parameter concentration for a smooth interacting particle chain

The transport argument is the existing proved Gaussian ULA argument. The
new sharp continuous-Gibbs dilation theorem gives the parameter radius
`sqrt (dθ / (N*m))` used by the third version of the proximal paper.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProximalLangevin

/-- Sharp equilibrium second moment of the actual powered marginal density. -/
theorem sharp_marginalTarget_secondMoment_le {N dθ dx : ℕ} (hN : 0 < N)
    (U : IPLA.Joint dθ dx → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U)
    (θStar : EuclideanSpace ℝ (Fin dθ)) (hmax : IPLA.IsMarginalMaximizer U θStar) :
    (∫ θ, ‖θ - θStar‖ ^ 2 ∂IPLA.marginalTarget N U) ≤
      (dθ : ℝ) / ((N : ℝ) * m) := by
  have hmode := IPLA.marginalMaximizer_minimizes_potential U m hm hdiff hsc θStar hmax
  have h := sharp_integral_sq_dist_gibbs_le
    (fun θ ↦ (N : ℝ) * IPLA.marginalPotential U θ) ((N : ℝ) * m)
    (mul_pos (by exact_mod_cast hN) hm)
    (continuous_const.mul (IPLA.marginalPotential_continuous U m hm hdiff hsc))
    (IPLA.scaled_marginalPotential_strongConvex U m hm hdiff hsc) θStar
    (fun θ ↦ mul_le_mul_of_nonneg_left (hmode θ) (Nat.cast_nonneg N))
  rw [← IPLA.marginalTarget_eq_gibbsMeasure U m hm hdiff hsc] at h
  simpa only [finrank_euclideanSpace, Fintype.card_fin] using h

/-- The exact parameter-marginal identity transfers sharp concentration to
the full lifted Gibbs measure. -/
theorem sharp_gibbsTarget_parameter_secondMoment_le {N dθ dx : ℕ} (hN : 0 < N)
    (U : IPLA.Joint dθ dx → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U)
    (θStar : EuclideanSpace ℝ (Fin dθ)) (hmax : IPLA.IsMarginalMaximizer U θStar) :
    (∫ z : IPLA.State N dθ dx, ‖IPLA.parameterCLM z - θStar‖ ^ 2
      ∂IPLA.gibbsTarget U) ≤ (dθ : ℝ) / ((N : ℝ) * m) := by
  have h := sharp_marginalTarget_secondMoment_le hN U m hm hdiff hsc θStar hmax
  rw [← IPLA.gibbsTarget_parameter_marginal hN U m hm hdiff hsc,
    integral_map IPLA.parameterCLM.continuous.measurable.aemeasurable (by fun_prop)] at h
  exact h

/-- The parameter RMS radius with the sharp dimension constant. -/
theorem sharp_gibbsTarget_parameter_concentration {N dθ dx : ℕ} (hN : 0 < N)
    (U : IPLA.Joint dθ dx → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U)
    (θStar : EuclideanSpace ℝ (Fin dθ)) (hmax : IPLA.IsMarginalMaximizer U θStar) :
    IPLA.projectedRMS (@IPLA.gibbsTarget N dθ dx U) IPLA.parameterCLM θStar ≤
      ENNReal.ofReal (Real.sqrt ((dθ : ℝ) / ((N : ℝ) * m))) := by
  have : IsProbabilityMeasure (ULA.gibbsMeasure (@IPLA.potential N dθ dx U)) :=
    ULA.isProbabilityMeasure_gibbsMeasure (IPLA.potential U) ((N : ℝ) * m)
      (mul_pos (by exact_mod_cast hN) hm)
      (IPLA.potential_differentiable hdiff) (IPLA.potential_strongConvex hsc)
  have hi := (ULA.memLp_id_gibbsMeasure (@IPLA.potential N dθ dx U) ((N : ℝ) * m)
    (mul_pos (by exact_mod_cast hN) hm)
    (IPLA.potential_differentiable hdiff)
    (IPLA.potential_strongConvex hsc)).continuousLinearMap_comp
      (@IPLA.parameterCLM N dθ dx)
  apply IPLA.projectedRMS_le_of_secondMoment _ _ _ _ (Real.sqrt_nonneg _)
    (hi.sub (memLp_const θStar))
  rw [Real.sq_sqrt (by positivity : 0 ≤ (dθ : ℝ) / ((N : ℝ) * m))]
  exact sharp_gibbsTarget_parameter_secondMoment_le hN U m hm hdiff hsc θStar hmax

private theorem sharp_ipla_parameter_rms_nonempty
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (N dθ dx : ℕ) [Nonempty (Fin dθ ⊕ (Fin N × Fin dx))] (hN : 0 < N)
    (U : IPLA.Joint dθ dx → ℝ) (m γ : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U)
    (hLip : LipschitzWith L (gradient U)) (hm : 0 < m)
    (hγ : 0 < γ) (hsmall : γ ≤ 2 / (m + (L : ℝ)))
    (θStar : EuclideanSpace ℝ (Fin dθ)) (hmax : IPLA.IsMarginalMaximizer U θStar)
    (initial : Lp (IPLA.State N dθ dx) 2 Q)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 Q)
    (hGaussian : IPLA.GaussianInnovations Q initial noise) (n : ℕ) :
    Real.sqrt (∫ z, ‖IPLA.parameterCLM z - θStar‖ ^ 2
      ∂IPLA.laws Q U γ L hdiff hLip initial noise n) ≤
      Real.sqrt ((dθ : ℝ) / ((N : ℝ) * m)) +
      (1 - m * γ) ^ n * ULA.wasserstein2Real (Q.map initial) (IPLA.gibbsTarget U) +
      (33 / 20 : ℝ) * ((L : ℝ) / m) *
        Real.sqrt ((dx : ℝ) + (dθ : ℝ) / (N : ℝ)) * Real.sqrt γ := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have : IsProbabilityMeasure (@IPLA.gibbsTarget N dθ dx U) :=
    IPLA.gibbsTarget_isProbability hN U m hm hdiff hsc
  have hfinite := ULA.Hilbert.gaussianULA_initial_transport_finite Q
    (@IPLA.potential N dθ dx U) ((N : ℝ) * m) (mul_pos hn hm)
    (IPLA.potential_differentiable hdiff) (IPLA.potential_strongConvex hsc) initial
  have hs : γ / (N : ℝ) ≤ 2 / ((N : ℝ) * m + (((N : ℝ≥0) * L : ℝ≥0) : ℝ)) := by
    simpa using (IPLA.scaled_step_iff N hN m (L : ℝ) γ).mpr hsmall
  have htransport := ULA.Hilbert.dalalyan_of_gaussian_innovations Q
    (@IPLA.potential N dθ dx U) ((N : ℝ) * m) (γ / N) ((N : ℝ≥0) * L)
    (mul_pos hn hm) (IPLA.potential_differentiable hdiff)
    (IPLA.potential_strongConvex hsc) (IPLA.potential_gradient_lipschitz hdiff hLip)
    (div_pos hγ hn) hs initial noise hGaussian.coordinateLaw hGaussian.independent
    hGaussian.independentInitial n
  change ULA.wasserstein2Real (IPLA.laws Q U γ L hdiff hLip initial noise n)
    (ULA.gibbsMeasure (IPLA.potential U)) ≤ _ at htransport
  have houtput := ULA.Hilbert.dalalyan_output_finite (@IPLA.potential N dθ dx U)
    ((N : ℝ) * m) (γ / N) ((N : ℝ≥0) * L) (mul_pos hn hm)
    (IPLA.potential_differentiable hdiff) (IPLA.potential_strongConvex hsc)
    (IPLA.potential_gradient_lipschitz hdiff hLip) (div_pos hγ hn) (Q.map initial) hfinite n
  have hlaw := IPLA.laws_eq_ulaLawStep Q U γ L hdiff hLip initial noise hGaussian n
  rw [← hlaw] at houtput
  rw [← IPLA.gibbsTarget_eq_gibbsMeasure U] at htransport houtput
  have hfactor : (N : ℝ) * m * (γ / N) = m * γ := by field_simp
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, NNReal.coe_mul,
    NNReal.coe_natCast, hfactor] at htransport
  rw [IPLA.scaled_bias_eq N dθ dx hN m (L : ℝ) γ hγ.le] at htransport
  have hc := sharp_gibbsTarget_parameter_concentration hN U m hm hdiff hsc θStar hmax
  have hp := IPLA.projectedRMSReal_le_wasserstein2Real_add
    (@IPLA.parameterCLM N dθ dx) IPLA.norm_parameterCLM_le_one θStar
    (Real.sqrt ((dθ : ℝ) / ((N : ℝ) * m))) (Real.sqrt_nonneg _) houtput hc
  have hmoment := IPLA.projectedRMS_ne_top (@IPLA.parameterCLM N dθ dx)
    IPLA.norm_parameterCLM_le_one θStar _ houtput hc
  rw [IPLA.projectedRMSReal_eq_sqrt_integral _ _ _ hmoment] at hp
  linarith

/-- A complete actual Gaussian IPLA parameter bound with sharp concentration.
This theorem includes zero parameter/latent dimensions. -/
theorem sharp_ipla_parameter_rms
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (N dθ dx : ℕ) (hN : 0 < N) (U : IPLA.Joint dθ dx → ℝ)
    (m γ : ℝ) (L : ℝ≥0) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn univ m U) (hLip : LipschitzWith L (gradient U))
    (hm : 0 < m) (hγ : 0 < γ) (hsmall : γ ≤ 2 / (m + (L : ℝ)))
    (θStar : EuclideanSpace ℝ (Fin dθ)) (hmax : IPLA.IsMarginalMaximizer U θStar)
    (initial : Lp (IPLA.State N dθ dx) 2 Q)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 Q)
    (hGaussian : IPLA.GaussianInnovations Q initial noise) (n : ℕ) :
    Real.sqrt (∫ z, ‖IPLA.parameterCLM z - θStar‖ ^ 2
      ∂IPLA.laws Q U γ L hdiff hLip initial noise n) ≤
      Real.sqrt ((dθ : ℝ) / ((N : ℝ) * m)) +
      (1 - m * γ) ^ n * ULA.wasserstein2Real (Q.map initial) (IPLA.gibbsTarget U) +
      (33 / 20 : ℝ) * ((L : ℝ) / m) *
        Real.sqrt ((dx : ℝ) + (dθ : ℝ) / (N : ℝ)) * Real.sqrt γ := by
  classical
  by_cases hi : Nonempty (Fin dθ ⊕ (Fin N × Fin dx))
  · let : Nonempty (Fin dθ ⊕ (Fin N × Fin dx)) := hi
    exact sharp_ipla_parameter_rms_nonempty Q N dθ dx hN U m γ L hdiff hsc hLip hm
      hγ hsmall θStar hmax initial noise hGaussian n
  · have hθ : dθ = 0 := Nat.eq_zero_of_not_pos (fun hp ↦ hi ⟨Sum.inl ⟨0, hp⟩⟩)
    have hx : dx = 0 := Nat.eq_zero_of_not_pos
      (fun hp ↦ hi ⟨Sum.inr (⟨0, hN⟩, ⟨0, hp⟩)⟩)
    subst dθ
    subst dx
    have : IsProbabilityMeasure (@IPLA.gibbsTarget N 0 0 U) :=
      IPLA.gibbsTarget_isProbability hN U m hm hdiff hsc
    simpa only [Nat.cast_zero, mul_zero] using
      IPLA.zero_dimensions_bound (Q.map initial) (IPLA.gibbsTarget U)
        (IPLA.laws Q U γ L hdiff hLip initial noise n) m γ L θStar n

end ProximalLangevin
