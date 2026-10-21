import IPLA.MarginalConcentration
import IPLA.PrekopaTensorization

set_option linter.style.header false

/-! # Strong log-concavity of the actual IPLA marginal

The proved Prékopa--Leindler inequality is applied to the latent slices of the
original jointly strongly convex potential. Marginal strong convexity is a
conclusion of the theorem, never an added input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace IPLA

/-- The real latent partition. Positivity and finiteness were proved from the
joint assumptions in `MarginalConcentration.lean`. -/
def marginalIntegral {dθ dx : ℕ} (U : Joint dθ dx → ℝ) (θ : EuclideanSpace ℝ (Fin dθ)) : ℝ :=
  ∫ x, Real.exp (-U (pair θ x)) ∂volume

/-- The actual marginal negative log-likelihood, with the observations fixed. -/
def marginalPotential {dθ dx : ℕ} (U : Joint dθ dx → ℝ) (θ : EuclideanSpace ℝ (Fin dθ)) : ℝ :=
  -Real.log (marginalIntegral U θ)

theorem marginalIntegral_pos {dθ dx : ℕ} (U : Joint dθ dx → ℝ)
    (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) (θ : EuclideanSpace ℝ (Fin dθ)) :
    0 < marginalIntegral U θ :=
  integral_exp_pos (integrable_marginal_weight U m hm hdiff hsc θ)

theorem marginalPotential_continuous {dθ dx : ℕ} (U : Joint dθ dx → ℝ)
    (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) : Continuous (marginalPotential U) := by
  exact ((continuous_marginal_integral U m hm hdiff hsc).log
    (fun θ ↦ (marginalIntegral_pos U m hm hdiff hsc θ).ne')).neg

/-- The statistical marginal maximizer minimizes the actual negative
log-likelihood. All real conversions use proved positive finite partitions. -/
theorem marginalMaximizer_minimizes_potential {dθ dx : ℕ} (U : Joint dθ dx → ℝ)
    (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) (θStar : EuclideanSpace ℝ (Fin dθ))
    (hmax : IsMarginalMaximizer U θStar) :
    ∀ θ, marginalPotential U θStar ≤ marginalPotential U θ := by
  intro θ
  have h := hmax θ
  rw [marginalDensity_eq_ofReal_integral U m hm hdiff hsc θ,
    marginalDensity_eq_ofReal_integral U m hm hdiff hsc θStar] at h
  have hr := (ENNReal.ofReal_le_ofReal_iff
    (marginalIntegral_pos U m hm hdiff hsc θStar).le).mp h
  exact neg_le_neg (Real.log_le_log (marginalIntegral_pos U m hm hdiff hsc θ) hr)

/-- A latent slice written in ordinary product coordinates for applying the
finite-dimensional Prékopa--Leindler theorem. -/
def latentWeight {dθ dx : ℕ} (U : Joint dθ dx → ℝ) (θ : EuclideanSpace ℝ (Fin dθ))
    (x : Prekopa.Coordinates dx) : ℝ :=
  Real.exp (-U (pair θ (WithLp.toLp 2 x)))

theorem latentWeight_gaussian {dθ dx : ℕ} (U : Joint dθ dx → ℝ)
    (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) (θ : EuclideanSpace ℝ (Fin dθ)) :
    Prekopa.GaussianWeight dx (latentWeight U θ) := by
  refine ⟨?_, fun _ ↦ Real.exp_pos _,
    Real.exp (‖gradient U 0‖ ^ 2 / m - U 0), m / 4, Real.exp_pos _, by positivity, ?_⟩
  · exact Real.continuous_exp.comp (hdiff.continuous.comp
      (continuous_pair.comp (continuous_const.prodMk (PiLp.continuous_toLp 2 _)))).neg
  · intro x
    have h := marginal_weight_uniform_bound U m hm hdiff hsc θ (WithLp.toLp 2 x)
    simpa only [latentWeight, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      EuclideanSpace.real_norm_sq_eq, PiLp.toLp_apply] using h

theorem integral_latentWeight {dθ dx : ℕ} (U : Joint dθ dx → ℝ)
    (θ : EuclideanSpace ℝ (Fin dθ)) :
    (∫ x, latentWeight U θ x ∂volume) = marginalIntegral U θ := by
  exact (PiLp.volume_preserving_toLp (Fin dx)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin dx → ℝ)).measurableEmbedding
    (fun x ↦ Real.exp (-U (pair θ x)))

@[simp] theorem pair_sub {dθ dx : ℕ} (θ θ' : EuclideanSpace ℝ (Fin dθ))
    (x x' : EuclideanSpace ℝ (Fin dx)) :
    pair θ x - pair θ' x' = pair (θ - θ') (x - x') := by
  ext i
  cases i <;> simp [pair]

theorem pair_affine {dθ dx : ℕ} (θ θ' : EuclideanSpace ℝ (Fin dθ))
    (x x' : EuclideanSpace ℝ (Fin dx)) (a b : ℝ) :
    pair (a • θ + b • θ') (a • x + b • x') = a • pair θ x + b • pair θ' x' := by
  ext i
  cases i <;> simp [pair]

/-- Integrating out the latent variables preserves precisely the original
strong-convexity constant. This is the derived Prékopa theorem for IPLA. -/
theorem marginalPotential_strongConvex {dθ dx : ℕ} (U : Joint dθ dx → ℝ)
    (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) :
    StrongConvexOn Set.univ m (marginalPotential U) := by
  refine ⟨convex_univ, ?_⟩
  intro θ hθ θ' hθ' a b ha hb hab
  have hb1 : b ≤ 1 := by linarith
  have haeq : 1 - b = a := by linarith
  let θr := a • θ + b • θ'
  let c := a * b * (m / 2 * ‖θ - θ'‖ ^ 2)
  have hf := latentWeight_gaussian U m hm hdiff hsc θ
  have hg := latentWeight_gaussian U m hm hdiff hsc θ'
  have hh := (latentWeight_gaussian U m hm hdiff hsc θr).const_mul
    (Real.exp (-c)) (Real.exp_pos _)
  have hpoint (x y : Prekopa.Coordinates dx) :
      Real.exp ((1 - b) * Real.log (latentWeight U θ x) +
        b * Real.log (latentWeight U θ' y)) ≤
      Real.exp (-c) * latentWeight U θr (fun i ↦ (1 - b) * x i + b * y i) := by
    simp only [latentWeight, Real.log_exp, haeq, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    let x' : EuclideanSpace ℝ (Fin dx) := WithLp.toLp 2 x
    let y' : EuclideanSpace ℝ (Fin dx) := WithLp.toLp 2 y
    have hs := hsc.2 (Set.mem_univ (pair θ x')) (Set.mem_univ (pair θ' y')) ha hb hab
    have he : (WithLp.toLp 2 (fun i ↦ a * x i + b * y i) : EuclideanSpace ℝ (Fin dx)) =
        a • x' + b • y' := by ext i; rfl
    rw [← pair_affine, pair_sub] at hs
    dsimp only at hs
    rw [norm_pair_sq] at hs
    have hnonneg : 0 ≤ a * b * (m / 2 * ‖x' - y'‖ ^ 2) := by positivity
    dsimp [c, θr, x', y'] at hs hnonneg ⊢
    rw [he]
    nlinarith
  have hpl := Prekopa.prekopa_leindler hf hg hh b hb hb1 hpoint
  rw [integral_const_mul, integral_latentWeight, integral_latentWeight,
    integral_latentWeight] at hpl
  have hz : 0 < marginalIntegral U θr := (latentWeight_gaussian U m hm hdiff hsc θr).integral_pos
    |>.trans_eq (integral_latentWeight U θr)
  have hlog := Real.log_le_log (Real.exp_pos _) hpl
  rw [Real.log_exp, Real.log_mul (Real.exp_ne_zero _) hz.ne', Real.log_exp, haeq] at hlog
  change -Real.log (marginalIntegral U θr) ≤
    a * (-Real.log (marginalIntegral U θ)) + b * (-Real.log (marginalIntegral U θ')) - _
  dsimp [c] at hlog
  linarith

/-- Joint strong convexity implies uniqueness of the marginal maximizer. -/
theorem marginalMaximizer_unique {dθ dx : ℕ} (U : Joint dθ dx → ℝ)
    (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) (θ θ' : EuclideanSpace ℝ (Fin dθ))
    (hθ : IsMarginalMaximizer U θ) (hθ' : IsMarginalMaximizer U θ') : θ = θ' := by
  have hs := (marginalPotential_strongConvex U m hm hdiff hsc).strictConvexOn hm
  exact hs.eq_of_isMinOn
    (fun x _ ↦ marginalMaximizer_minimizes_potential U m hm hdiff hsc θ hθ x)
    (fun x _ ↦ marginalMaximizer_minimizes_potential U m hm hdiff hsc θ' hθ' x)
    (Set.mem_univ _) (Set.mem_univ _)

/-- The marginal maximizer exists uniquely under exactly the original joint
potential assumptions. -/
theorem existsUnique_marginalMaximizer {dθ dx : ℕ} (U : Joint dθ dx → ℝ)
    (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) :
    ∃! θ : EuclideanSpace ℝ (Fin dθ), IsMarginalMaximizer U θ := by
  obtain ⟨θ, hθ⟩ := exists_marginalMaximizer U m hm hdiff hsc
  exact ⟨θ, hθ, fun θ' hθ' ↦ marginalMaximizer_unique U m hm hdiff hsc θ' θ hθ' hθ⟩

end IPLA
