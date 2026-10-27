import IPLA.StrongLogConcavity
import LatentDiffusion.Flow

/-! Actual heterogeneous latent marginals: existence and uniqueness from joint
strong convexity, using the proved finite-dimensional Prékopa theorem. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace LatentDiffusion

variable {dθ dz M : ℕ}

def averageMarginalPotential (U : Fin M → IPLA.Joint dθ dz → ℝ)
    (θ : EuclideanSpace ℝ (Fin dθ)) : ℝ :=
  (M : ℝ)⁻¹ * ∑ i, IPLA.marginalPotential (U i) θ

theorem averageMarginalPotential_strongConvex
    (U : Fin M → IPLA.Joint dθ dz → ℝ) (hM : 0 < M)
    (rho : ℝ) (hrho : 0 < rho) (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn univ rho (U i)) :
    StrongConvexOn univ rho (averageMarginalPotential U) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    (IPLA.marginalPotential_strongConvex (U i) rho hrho (hdiff i) (hsc i)).2 hx hy ha hb hab)
  have hmp : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hh := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hmp.le)
  simp only [smul_eq_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  dsimp [averageMarginalPotential]
  convert hh using 1
  field_simp

theorem marginalPotential_coercive (U : IPLA.Joint dθ dz → ℝ)
    (rho : ℝ) (hrho : 0 < rho) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn univ rho U) :
    Tendsto (IPLA.marginalPotential U) (cocompact _) atTop := by
  have ht : Tendsto (IPLA.marginalIntegral U) (cocompact _) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨IPLA.tendsto_marginal_integral_cocompact U rho hrho hdiff hsc,
      Eventually.of_forall (fun θ => IPLA.marginalIntegral_pos U rho hrho hdiff hsc θ)⟩
  exact tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp ht)

theorem averageMarginalPotential_coercive
    (U : Fin M → IPLA.Joint dθ dz → ℝ) (hM : 0 < M)
    (rho : ℝ) (hrho : 0 < rho) (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn univ rho (U i)) :
    Tendsto (averageMarginalPotential U) (cocompact _) atTop := by
  apply tendsto_atTop.2
  intro b
  have hh : ∀ᶠ θ in cocompact (EuclideanSpace ℝ (Fin dθ)),
      ∀ i, b ≤ IPLA.marginalPotential (U i) θ := by
    rw [eventually_all]
    intro i
    exact (marginalPotential_coercive (U i) rho hrho (hdiff i) (hsc i)).eventually
      (eventually_ge_atTop b)
  filter_upwards [hh] with θ hθ
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hθ i)
  have hp : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hh := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hp.le)
  simpa [averageMarginalPotential, hp.ne', ← mul_assoc] using hh

theorem existsUnique_averageMarginalMinimizer
    (U : Fin M → IPLA.Joint dθ dz → ℝ) (hM : 0 < M)
    (rho : ℝ) (hrho : 0 < rho) (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn univ rho (U i)) :
    ∃! θ, ∀ θ', averageMarginalPotential U θ ≤ averageMarginalPotential U θ' := by
  have hc : Continuous (averageMarginalPotential U) := continuous_const.mul
    (continuous_finsetSum _ (fun i _ =>
      IPLA.marginalPotential_continuous (U i) rho hrho (hdiff i) (hsc i)))
  obtain ⟨θ, hθ⟩ := hc.exists_forall_le
    (averageMarginalPotential_coercive U hM rho hrho hdiff hsc)
  refine ⟨θ, hθ, ?_⟩
  intro θ' hθ'
  exact (averageMarginalPotential_strongConvex U hM rho hrho hdiff hsc).strictConvexOn hrho
    |>.eq_of_isMinOn (fun x _ => hθ' x) (fun x _ => hθ x) (mem_univ _) (mem_univ _)
/-- Unique joint variational optimizer, whenever the supplied normalized
posterior family has the actual average log evidence of the datum potentials.
The posterior normalization itself remains the responsibility of that family. -/
theorem existsUnique_variationalOptimizer
    {Z : Type*} [MeasurableSpace Z]
    (U : Fin M → IPLA.Joint dθ dz → ℝ) (hM : 0 < M)
    (rho : ℝ) (hrho : 0 < rho) (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn univ rho (U i))
    (P : PosteriorFamily (EuclideanSpace ℝ (Fin dθ)) Z M)
    (hlog : ∀ θ, P.logEvidence θ = -averageMarginalPotential U θ) :
    ∃! p : EuclideanSpace ℝ (Fin dθ) × (Fin M → ProbabilityMeasure Z),
      P.IsGlobalMin p.1 p.2 := by
  obtain ⟨θ, hθ, hu⟩ := existsUnique_averageMarginalMinimizer U hM rho hrho hdiff hsc
  refine ⟨(θ, P.posterior θ), ?_, ?_⟩
  · apply (P.global_minimizers_iff hM θ _).mpr
    refine ⟨?_, rfl⟩
    intro b
    rw [hlog, hlog]
    exact neg_le_neg (hθ b)
  · rintro ⟨b, q⟩ hq
    obtain ⟨hb, rfl⟩ := (P.global_minimizers_iff hM b q).mp hq
    have he : b = θ := hu b (fun c => by
      have h := hb c
      rw [hlog, hlog] at h
      linarith)
    subst b
    rfl
/-- Sharp quadratic growth at a minimizer needs no differentiability: take
the interpolation parameter to zero in the strong-convexity inequality. -/
theorem strongConvex_quadratic_growth
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (F : H → ℝ) (rho : ℝ) (hsc : StrongConvexOn univ rho F)
    (z : H) (hz : ∀ x, F z ≤ F x) (x : H) :
    rho / 2 * ‖x - z‖ ^ 2 ≤ F x - F z := by
  have hb : ∀ᶠ s : ℝ in 𝓝[>] 0,
      rho / 2 * (1 - s) * ‖x - z‖ ^ 2 ≤ F x - F z := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with s hs hs1
    have hsp : 0 < s := hs
    have hh := hsc.2 (mem_univ z) (mem_univ x)
      (show 0 ≤ 1 - s by linarith) hsp.le (show 1 - s + s = 1 by ring)
    have hm := hz ((1 - s) • z + s • x)
    simp only [smul_eq_mul] at hh
    rw [norm_sub_rev z x] at hh
    apply (mul_le_mul_iff_right₀ hsp).mp
    nlinarith
  have ht : Tendsto (fun s : ℝ => rho / 2 * (1 - s) * ‖x - z‖ ^ 2)
      (𝓝[>] 0) (𝓝 (rho / 2 * ‖x - z‖ ^ 2)) := by
    have hc : Continuous (fun s : ℝ => rho / 2 * (1 - s) * ‖x - z‖ ^ 2) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto ht hb

/-- Simultaneous sharp parameter and posterior control by actual free-energy
excess, without any differentiability premise for the marginal potential. -/
theorem parameter_posterior_control
    {Z : Type*} [MeasurableSpace Z]
    (U : Fin M → IPLA.Joint dθ dz → ℝ) (hM : 0 < M)
    (rho : ℝ) (hrho : 0 < rho) (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn univ rho (U i))
    (P : PosteriorFamily (EuclideanSpace ℝ (Fin dθ)) Z M)
    (hlog : ∀ θ, P.logEvidence θ = -averageMarginalPotential U θ)
    (θstar θ : EuclideanSpace ℝ (Fin dθ))
    (hmin : ∀ b, averageMarginalPotential U θstar ≤ averageMarginalPotential U b)
    (q : Fin M → ProbabilityMeasure Z) :
    rho / 2 * ‖θ - θstar‖ ^ 2 +
      (M : ℝ)⁻¹ * ∑ i, (InformationTheory.klDiv (q i : Measure Z)
        (P.posterior θ i : Measure Z)).toReal ≤
    P.freeEnergy θ q - P.freeEnergy θstar (P.posterior θstar) := by
  have hh := strongConvex_quadratic_growth (averageMarginalPotential U) rho
    (averageMarginalPotential_strongConvex U hM rho hrho hdiff hsc) θstar hmin θ
  rw [P.posterior_freeEnergy]
  unfold PosteriorFamily.freeEnergy
  rw [hlog, hlog]
  linarith
/-- The source parameter convergence rate, with sharp prefactor, derived
from primitive marginal convexity and the explicit entropy-calculus bridges.
In particular quadratic growth is proved, not supplied as a Talagrand premise. -/
theorem parameter_decay_of_firstOrder
    {Z : Type*} [MeasurableSpace Z]
    (U : Fin M → IPLA.Joint dθ dz → ℝ) (hM : 0 < M)
    (rho : ℝ) (hrho : 0 < rho) (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn univ rho (U i))
    (P : PosteriorFamily (EuclideanSpace ℝ (Fin dθ)) Z M)
    (hlog : ∀ θ, P.logEvidence θ = -averageMarginalPotential U θ)
    (θstar : EuclideanSpace ℝ (Fin dθ))
    (hmin : ∀ b, averageMarginalPotential U θstar ≤ averageMarginalPotential U b)
    (a : ℝ → EuclideanSpace ℝ (Fin dθ))
    (q : ℝ → Fin M → ProbabilityMeasure Z) (T : ℝ) (I r : ℝ → ℝ)
    (hadm : ∀ t ∈ Icc 0 T, P.Admissible (a t) (q t))
    (hcont : ContinuousOn (fun t => P.freeEnergy (a t) (q t) -
      P.freeEnergy θstar (P.posterior θstar)) (Icc 0 T))
    (hdiss : ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => P.freeEnergy (a s) (q s) -
        P.freeEnergy θstar (P.posterior θstar)) (-I t) (Ici t) t)
    (hI : ∀ t ∈ Ico 0 T, 0 ≤ I t)
    (hfirst : ∀ t ∈ Ico 0 T,
      P.freeEnergy (a t) (q t) - P.freeEnergy θstar (P.posterior θstar) ≤
        Real.sqrt (I t) * r t - rho / 2 * (r t) ^ 2)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖a t - θstar‖ ≤
      Real.sqrt (2 * (P.freeEnergy (a 0) (q 0) -
        P.freeEnergy θstar (P.posterior θstar)) / rho) * Real.exp (-rho * t) := by
  let gap := P.freeEnergy (a 0) (q 0) - P.freeEnergy θstar (P.posterior θstar)
  have hg : 0 ≤ gap := by
    have hb := P.lower_bound (a 0) (q 0)
    have hm := hmin (a 0)
    rw [hlog] at hb
    dsimp [gap]
    rw [P.posterior_freeEnergy, hlog]
    linarith
  have hc := parameter_posterior_control U hM rho hrho hdiff hsc P hlog
    θstar (a t) hmin (q t)
  have hk : 0 ≤ (M : ℝ)⁻¹ * ∑ i, (InformationTheory.klDiv (q t i : Measure Z)
      (P.posterior (a t) i : Measure Z)).toReal :=
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))
  have he := (P.freeEnergy_decay_of_firstOrder a q _ rho T I r hrho
    hadm hcont hdiss hI hfirst t ht).2
  have hs : ‖a t - θstar‖ ^ 2 ≤ (2 * gap / rho) * Real.exp (-2 * rho * t) := by
    have hb : ‖a t - θstar‖ ^ 2 * rho ≤ 2 * gap * Real.exp (-2 * rho * t) := by
      dsimp [gap]
      nlinarith [he]
    calc
      _ ≤ (2 * gap * Real.exp (-2 * rho * t)) / rho := (le_div_iff₀ hrho).mpr hb
      _ = _ := by ring
  have hgp : 0 ≤ 2 * gap / rho := div_nonneg (by positivity) hrho.le
  have hsq : (Real.sqrt (2 * gap / rho) * Real.exp (-rho * t)) ^ 2 =
      (2 * gap / rho) * Real.exp (-2 * rho * t) := by
    rw [mul_pow, Real.sq_sqrt hgp, pow_two, ← Real.exp_add]
    congr 2
    ring
  have hp : 0 ≤ Real.sqrt (2 * gap / rho) * Real.exp (-rho * t) := by positivity
  change ‖a t - θstar‖ ≤ Real.sqrt (2 * gap / rho) * Real.exp (-rho * t)
  nlinarith [sq_nonneg (‖a t - θstar‖ - Real.sqrt (2 * gap / rho) * Real.exp (-rho * t))]
/-- One-sided uniform evidence bias costs only `delta`, and an approximate
optimization tolerance costs `epsilon`, in objective excess. -/
theorem tilted_objective_bias
    {A : Type*} (ell tilted : A → ℝ) (delta epsilon : ℝ)
    (hgap : ∀ x, 0 ≤ ell x - tilted x ∧ ell x - tilted x ≤ delta)
    (star approx : A) (happrox : ∀ x, tilted x ≤ tilted approx + epsilon) :
    ell star - ell approx ≤ delta + epsilon := by
  have hs := (hgap star).2
  have ha := (hgap approx).1
  have ho := happrox star
  linarith

/-- Model-bias robustness: one-sided evidence error `delta` and optimization
error `epsilon` give parameter error at most sqrt(2(delta+epsilon)/rho).
The target is the original evidence maximizer, not the tilted maximizer. -/
theorem tilted_parameter_bias
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ell tilted : H → ℝ) (rho delta epsilon : ℝ) (hrho : 0 < rho)
    (hdelta : 0 ≤ delta) (hepsilon : 0 ≤ epsilon)
    (hsc : StrongConvexOn univ rho (fun x => -ell x))
    (hgap : ∀ x, 0 ≤ ell x - tilted x ∧ ell x - tilted x ≤ delta)
    (star approx : H) (hstar : ∀ x, ell x ≤ ell star)
    (happrox : ∀ x, tilted x ≤ tilted approx + epsilon) :
    ‖approx - star‖ ≤ Real.sqrt (2 * (delta + epsilon) / rho) := by
  have hg := strongConvex_quadratic_growth (fun x => -ell x) rho hsc star
    (fun x => neg_le_neg (hstar x)) approx
  have hb := tilted_objective_bias ell tilted delta epsilon hgap star approx happrox
  have hs : ‖approx - star‖ ^ 2 ≤ 2 * (delta + epsilon) / rho := by
    apply (le_div_iff₀ hrho).mpr
    nlinarith
  have hp : 0 ≤ 2 * (delta + epsilon) / rho := by positivity
  have hr := Real.sq_sqrt hp
  have hn := Real.sqrt_nonneg (2 * (delta + epsilon) / rho)
  nlinarith [norm_nonneg (approx - star)]
end LatentDiffusion
