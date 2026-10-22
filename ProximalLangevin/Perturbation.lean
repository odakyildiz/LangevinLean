import IPLA.StrongLogConcavity
import UnadjustedLangevin.GibbsConcentration

set_option linter.style.header false


/-!
# Nonasymptotic stability under a uniform potential perturbation

This argument supplies a finite smoothing bias without a Taylor expansion of
the proximal map or an unproved interchange of an asymptotic remainder and an
integral. The original potential need not be differentiable. Its statistical
center is its actual latent marginal maximizer.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ProximalLangevin

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A global minimizer of a strongly convex function has the sharp quadratic
growth bound, even when the function is not differentiable. -/
theorem strongConvex_minimum_growth (F : H → ℝ) (m : ℝ) (hm : 0 ≤ m)
    (hsc : StrongConvexOn Set.univ m F) (z : H)
    (hz : ∀ x, F z ≤ F x) (x : H) :
    F z + m / 2 * ‖x - z‖ ^ 2 ≤ F x := by
  let A := m / 2 * ‖x - z‖ ^ 2
  let G := F x - F z
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hG : 0 ≤ G := sub_nonneg.mpr (hz x)
  suffices A ≤ G by dsimp [A, G] at this; linarith
  by_contra h
  have hGA : G < A := lt_of_not_ge h
  have hAp : 0 < A := lt_of_le_of_lt hG hGA
  let b := (A - G) / (2 * A)
  have hb : 0 < b := div_pos (sub_pos.mpr hGA) (by positivity)
  have hb1 : b ≤ 1 / 2 := by
    dsimp [b]
    apply (div_le_iff₀ (by positivity : 0 < 2 * A)).mpr
    linarith
  have hs := hsc.2 (mem_univ z) (mem_univ x)
    (show 0 ≤ 1 - b by linarith) hb.le (by ring : 1 - b + b = 1)
  have hmin := hz ((1 - b) • z + b • x)
  dsimp only at hs
  simp only [smul_eq_mul, norm_sub_rev z x] at hs
  have hg : (1 - b) * A ≤ G := by
    dsimp [A, G]
    nlinarith
  have heq : b * (2 * A) = A - G := by
    dsimp [b]
    exact div_mul_cancel₀ _ (by positivity : 2 * A ≠ 0)
  nlinarith

/-- A one-sided uniform perturbation transfers directly to the actual
extended-valued latent integrals. No real conversion or normalization is used. -/
theorem marginalDensity_sandwich {dθ dx : ℕ}
    (U V : IPLA.Joint dθ dx → ℝ) (δ : ℝ)
    (hgap : ∀ z, V z ≤ U z ∧ U z ≤ V z + δ)
    (θ : EuclideanSpace ℝ (Fin dθ)) :
    IPLA.marginalDensity U θ ≤ IPLA.marginalDensity V θ ∧
      IPLA.marginalDensity V θ ≤
        ENNReal.ofReal (Real.exp δ) * IPLA.marginalDensity U θ := by
  constructor
  · apply lintegral_mono
    intro x
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg (hgap _).1))
  · unfold IPLA.marginalDensity
    rw [← lintegral_const_mul' _ _]
    · apply lintegral_mono
      intro x
      dsimp only
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [(hgap (IPLA.pair θ x)).2]))
    · exact ENNReal.ofReal_ne_top

/-- The two negative log marginal likelihoods differ by at most the same
uniform potential gap. Integrability of the nonsmooth original weight is
derived by domination by the smooth strongly convex comparison potential. -/
theorem marginalPotential_sandwich {dθ dx : ℕ}
    (U V : IPLA.Joint dθ dx → ℝ) (δ m : ℝ) (hm : 0 < m)
    (hU : Continuous U) (hV : Differentiable ℝ V)
    (hsc : StrongConvexOn Set.univ m V)
    (hgap : ∀ z, V z ≤ U z ∧ U z ≤ V z + δ)
    (θ : EuclideanSpace ℝ (Fin dθ)) :
    IPLA.marginalPotential V θ ≤ IPLA.marginalPotential U θ ∧
      IPLA.marginalPotential U θ ≤ IPLA.marginalPotential V θ + δ := by
  have hiV := IPLA.integrable_marginal_weight V m hm hV hsc θ
  have hiU : Integrable (fun x ↦ Real.exp (-U (IPLA.pair θ x))) volume := by
    apply hiV.mono'
    · exact (Real.continuous_exp.comp
        (hU.comp (IPLA.continuous_pair.comp
          (continuous_const.prodMk continuous_id))).neg).aestronglyMeasurable
    · exact ae_of_all _ fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (neg_le_neg (hgap _).1)
  have hpU : 0 < IPLA.marginalIntegral U θ := integral_exp_pos hiU
  have hpV := IPLA.marginalIntegral_pos V m hm hV hsc θ
  have hUV : IPLA.marginalIntegral U θ ≤ IPLA.marginalIntegral V θ := by
    exact integral_mono hiU hiV (fun x ↦ Real.exp_le_exp.mpr (neg_le_neg (hgap _).1))
  have hVU : IPLA.marginalIntegral V θ ≤ Real.exp δ * IPLA.marginalIntegral U θ := by
    change (∫ x, Real.exp (-V (IPLA.pair θ x)) ∂volume) ≤
      Real.exp δ * (∫ x, Real.exp (-U (IPLA.pair θ x)) ∂volume)
    rw [← integral_const_mul]
    apply integral_mono hiV (hiU.const_mul _)
    intro x
    dsimp only
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [(hgap (IPLA.pair θ x)).2])
  constructor
  · exact neg_le_neg (Real.log_le_log hpU hUV)
  · have hh := Real.log_le_log hpV hVU
    rw [Real.log_mul (Real.exp_ne_zero _) hpU.ne', Real.log_exp] at hh
    dsimp [IPLA.marginalPotential]
    linarith

/-- A continuous nonsmooth original potential has finite latent integrals
when it dominates the smooth strongly convex comparison potential. -/
theorem integrable_original_marginal {dθ dx : ℕ}
    (U V : IPLA.Joint dθ dx → ℝ) (m : ℝ) (hm : 0 < m)
    (hU : Continuous U) (hV : Differentiable ℝ V)
    (hsc : StrongConvexOn Set.univ m V) (hgap : ∀ z, V z ≤ U z)
    (θ : EuclideanSpace ℝ (Fin dθ)) :
    Integrable (fun x ↦ Real.exp (-U (IPLA.pair θ x))) volume := by
  apply (IPLA.integrable_marginal_weight V m hm hV hsc θ).mono'
  · exact (Real.continuous_exp.comp
      (hU.comp (IPLA.continuous_pair.comp
        (continuous_const.prodMk continuous_id))).neg).aestronglyMeasurable
  · exact ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (neg_le_neg (hgap _))

/-- The original marginal is continuous by a Gaussian dominated convergence
argument, even though its joint potential may be nonsmooth. -/
theorem continuous_original_marginal {dθ dx : ℕ}
    (U V : IPLA.Joint dθ dx → ℝ) (m : ℝ) (hm : 0 < m)
    (hU : Continuous U) (hV : Differentiable ℝ V)
    (hsc : StrongConvexOn Set.univ m V) (hgap : ∀ z, V z ≤ U z) :
    Continuous (IPLA.marginalIntegral U) := by
  apply continuous_of_dominated
    (bound := fun x : EuclideanSpace ℝ (Fin dx) ↦
      Real.exp (‖gradient V 0‖ ^ 2 / m - V 0) * Real.exp (-(m / 4) * ‖x‖ ^ 2))
  · exact fun θ ↦ (integrable_original_marginal U V m hm hU hV hsc hgap θ).aestronglyMeasurable
  · intro θ
    apply ae_of_all
    intro x
    have hUV : ‖Real.exp (-U (IPLA.pair θ x))‖ ≤
        ‖Real.exp (-V (IPLA.pair θ x))‖ := by
      simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (neg_le_neg (hgap _))
    exact hUV.trans (IPLA.marginal_weight_uniform_bound V m hm hV hsc θ x)
  · exact (ULA.integrable_exp_neg_mul_norm_sq
      (H := EuclideanSpace ℝ (Fin dx)) (m / 4) (by positivity)).const_mul _
  · apply ae_of_all
    intro x
    exact Real.continuous_exp.comp
      (hU.comp (IPLA.continuous_pair.comp (continuous_id.prodMk continuous_const))).neg

/-- A maximizer of the actual nonsmooth marginal exists; existence is not an
extra statistical premise added to the Moreau comparison argument. -/
theorem exists_original_marginalMaximizer {dθ dx : ℕ}
    (U V : IPLA.Joint dθ dx → ℝ) (m : ℝ) (hm : 0 < m)
    (hU : Continuous U) (hV : Differentiable ℝ V)
    (hsc : StrongConvexOn Set.univ m V) (hgap : ∀ z, V z ≤ U z) :
    ∃ θ : EuclideanSpace ℝ (Fin dθ), IPLA.IsMarginalMaximizer U θ := by
  have hi := integrable_original_marginal U V m hm hU hV hsc hgap
  have hp : 0 < IPLA.marginalIntegral U (0 : EuclideanSpace ℝ (Fin dθ)) :=
    integral_exp_pos (hi 0)
  have ht : Filter.Tendsto (IPLA.marginalIntegral U) (Filter.cocompact _) (nhds 0) := by
    apply squeeze_zero (fun θ ↦ integral_nonneg (fun _ ↦ Real.exp_nonneg _))
      (fun θ ↦ integral_mono (hi θ) (IPLA.integrable_marginal_weight V m hm hV hsc θ)
        (fun x ↦ Real.exp_le_exp.mpr (neg_le_neg (hgap _))))
    exact IPLA.tendsto_marginal_integral_cocompact V m hm hV hsc
  have he := ht.eventually_lt_const hp
  obtain ⟨θ, hθ⟩ := (continuous_original_marginal U V m hm hU hV hsc hgap).exists_forall_ge'
    0 (he.mono fun _ h ↦ h.le)
  refine ⟨θ, fun θ' ↦ ?_⟩
  have heq (a : EuclideanSpace ℝ (Fin dθ)) :
      IPLA.marginalDensity U a = ENNReal.ofReal (IPLA.marginalIntegral U a) :=
    (ofReal_integral_eq_lintegral_ofReal (hi a)
      (ae_of_all _ fun _ ↦ Real.exp_nonneg _)).symm
  rw [heq θ, heq θ']
  exact ENNReal.ofReal_le_ofReal (hθ θ')

/-- Marginal maximization for the actual nonsmooth model is equivalent to
minimization of its finite negative log marginal likelihood. -/
theorem original_maximizer_minimizes {dθ dx : ℕ}
    (U V : IPLA.Joint dθ dx → ℝ) (m : ℝ) (hm : 0 < m)
    (hU : Continuous U) (hV : Differentiable ℝ V)
    (hsc : StrongConvexOn Set.univ m V) (hgap : ∀ z, V z ≤ U z)
    (θStar : EuclideanSpace ℝ (Fin dθ))
    (hmax : IPLA.IsMarginalMaximizer U θStar) :
    ∀ θ, IPLA.marginalPotential U θStar ≤ IPLA.marginalPotential U θ := by
  have hi := integrable_original_marginal U V m hm hU hV hsc hgap
  have he (θ : EuclideanSpace ℝ (Fin dθ)) :
      IPLA.marginalDensity U θ = ENNReal.ofReal (IPLA.marginalIntegral U θ) :=
    (ofReal_integral_eq_lintegral_ofReal (hi θ)
      (ae_of_all _ fun _ ↦ Real.exp_nonneg _)).symm
  have hp (θ : EuclideanSpace ℝ (Fin dθ)) : 0 < IPLA.marginalIntegral U θ :=
    integral_exp_pos (hi θ)
  intro θ
  have h := hmax θ
  rw [he θ, he θStar] at h
  have hr := (ENNReal.ofReal_le_ofReal_iff (hp θStar).le).mp h
  exact neg_le_neg (Real.log_le_log (hp θ) hr)

/-- A fully nonasymptotic marginal-center perturbation bound. Only the
comparison model is assumed smooth. The centers maximize the actual marginal
integrals; they are not joint modes. -/
theorem marginal_center_distance_sq {dθ dx : ℕ}
    (U V : IPLA.Joint dθ dx → ℝ) (δ m : ℝ) (hm : 0 < m)
    (hU : Continuous U) (hV : Differentiable ℝ V)
    (hsc : StrongConvexOn Set.univ m V)
    (hgap : ∀ z, V z ≤ U z ∧ U z ≤ V z + δ)
    (θU θV : EuclideanSpace ℝ (Fin dθ))
    (hmaxU : IPLA.IsMarginalMaximizer U θU)
    (hmaxV : IPLA.IsMarginalMaximizer V θV) :
    ‖θU - θV‖ ^ 2 ≤ 2 * δ / m := by
  have hminU := original_maximizer_minimizes U V m hm hU hV hsc
    (fun z ↦ (hgap z).1) θU hmaxU
  have hminV := IPLA.marginalMaximizer_minimizes_potential V m hm hV hsc θV hmaxV
  have hgrowth := strongConvex_minimum_growth (IPLA.marginalPotential V) m hm.le
    (IPLA.marginalPotential_strongConvex V m hm hV hsc) θV hminV θU
  have h1 := (marginalPotential_sandwich U V δ m hm hU hV hsc hgap θU).1
  have h2 := (marginalPotential_sandwich U V δ m hm hU hV hsc hgap θV).2
  have h3 := hminU θV
  apply (le_div_iff₀ hm).mpr
  nlinarith

/-- The square-root form of the uniform-gap marginal-center estimate. -/
theorem marginal_center_distance {dθ dx : ℕ}
    (U V : IPLA.Joint dθ dx → ℝ) (δ m : ℝ) (hm : 0 < m)
    (hU : Continuous U) (hV : Differentiable ℝ V)
    (hsc : StrongConvexOn Set.univ m V)
    (hgap : ∀ z, V z ≤ U z ∧ U z ≤ V z + δ)
    (θU θV : EuclideanSpace ℝ (Fin dθ))
    (hmaxU : IPLA.IsMarginalMaximizer U θU)
    (hmaxV : IPLA.IsMarginalMaximizer V θV) :
    ‖θU - θV‖ ≤ Real.sqrt (2 * δ / m) := by
  have hsq := marginal_center_distance_sq U V δ m hm hU hV hsc hgap θU θV hmaxU hmaxV
  have hnonneg : 0 ≤ 2 * δ / m := (sq_nonneg ‖θU - θV‖).trans hsq
  exact (Real.le_sqrt (norm_nonneg _) hnonneg).mpr hsq

end ProximalLangevin
