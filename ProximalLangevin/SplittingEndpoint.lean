import ProximalLangevin.SplittingCanonical
import ProximalLangevin.SplittingGaussianLaw
import ProximalLangevin.ParticleSmoothing
import ProximalLangevin.SplittingRate
import UnadjustedLangevin.Recurrence

set_option linter.style.header false

/-! # Actual finite-time convergence of the equal-step PIPGLA algorithm

The law recurrence is proved by fresh canonical stationary couplings, followed
by the infimum over actual initial couplings. The resulting squared error floor
is linear in the time step and uses bounds uniform over the Moreau scale.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal RealInnerProductSpace
namespace ProximalLangevin
open ULA

section Generic
variable {ι : Type*} [Fintype ι]
    {f₁ f e : EuclideanSpace ℝ ι → ℝ}
    {T : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {L₁ Le Kf Ke LT K : ℝ≥0}
    (hf₁ : Differentiable ℝ f₁) (he : Differentiable ℝ e)
    (m h : ℝ) (hm : 0 < m) (hh : 0 < h)
    (hsc : StrongConvexOn univ m f₁)
    (hLip₁ : LipschitzWith L₁ (gradient f₁)) (hmL : m ≤ (L₁ : ℝ))
    (hsmall : h ≤ 2 / (m + (L₁ : ℝ)))
    (heconv : ConvexOn ℝ univ e) (hegrad : LipschitzWith Le (gradient e))
    (heLip : LipschitzWith Ke e) (hfLip : LipschitzWith Kf f)
    (hbounded : ∀ x, ‖gradient e x‖ ≤ (K : ℝ))
    (hT : LipschitzWith LT T)
    (henergy : ∀ x y, ‖T x - y‖ ^ 2 ≤
      ‖x - y‖ ^ 2 - 2 * h * (f x - f y) + h ^ 2 * (K : ℝ) ^ 2)
    (delta : ℝ) (hgap : ∀ x, e x ≤ f x ∧ f x ≤ e x + delta)

include hm hh hmL hsmall
private theorem step_product_le_one : m * h ≤ 1 := by
  have hp := (le_div_iff₀ (by positivity : 0 < m + (L₁ : ℝ))).mp hsmall
  nlinarith [mul_le_mul_of_nonneg_right hmL hh.le]

include hf₁ he hm hh hsc hLip₁ hmL hsmall heconv hegrad heLip hfLip hbounded hT henergy hgap

/-- The squared transport recurrence for one actual independent Gaussian
transition, with canonical stationarity and the coupling infimum discharged. -/
theorem splitting_markov_step_sq_bound
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hfinite : wasserstein2 μ (gibbsMeasure (fun x => f₁ x + e x)) ≠ ⊤) :
    let G := Real.sqrt (2 * (L₁ : ℝ) ^ 2 * ((Module.finrank ℝ (EuclideanSpace ℝ ι) : ℝ) / m) +
      2 * (K : ℝ) ^ 2) + (K : ℝ)
    let noise := Real.sqrt (2 * (Fintype.card ι : ℝ))
    wasserstein2 (markovStep (splittingUpdate f₁ T h) (stdGaussian (EuclideanSpace ℝ ι)) μ)
      (gibbsMeasure (fun x => f₁ x + e x)) ≠ ⊤ ∧
    wasserstein2Real (markovStep (splittingUpdate f₁ T h) (stdGaussian (EuclideanSpace ℝ ι)) μ)
      (gibbsMeasure (fun x => f₁ x + e x)) ^ 2 ≤
      (1 - m * h) * wasserstein2Real μ (gibbsMeasure (fun x => f₁ x + e x)) ^ 2 +
        splittingCouplingForcing m h (L₁ : ℝ) G noise (K : ℝ) delta := by
  have hcouple := splitting_markov_step_coupling_bound hf₁ he m h hm hh hsc hLip₁ hmL hsmall
    heconv hegrad heLip hfLip hbounded hT henergy delta hgap μ
  obtain ⟨c, hc⟩ := exists_finiteCost_coupling μ (gibbsMeasure (fun x => f₁ x + e x)) hfinite
  refine ⟨(hcouple c (ne_of_lt hc)).1, ?_⟩
  apply wasserstein2_sq_bound_of_finite_couplings _ _ _ _ (1 - m * h) _
    (by linarith [step_product_le_one m h hm hh hmL hsmall])
    (by
      have hδ : 0 ≤ delta := by
        have hh := hgap 0
        linarith
      unfold splittingCouplingForcing
      positivity) hfinite
  intro p hp
  exact (hcouple p hp).2

/-- Fully derived convergence for the actual iterated Gaussian splitting laws.
The coefficient is uniform in the smoothing scale whenever the value gap is
at most `h*K²/2`. -/
theorem splitting_markov_laws_sq_bound
    (hdelta : delta ≤ h * (K : ℝ) ^ 2 / 2)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hfinite : wasserstein2 μ (gibbsMeasure (fun x => f₁ x + e x)) ≠ ⊤) (n : ℕ) :
    let G := Real.sqrt (2 * (L₁ : ℝ) ^ 2 * ((Module.finrank ℝ (EuclideanSpace ℝ ι) : ℝ) / m) +
      2 * (K : ℝ) ^ 2) + (K : ℝ)
    let noise := Real.sqrt (2 * (Fintype.card ι : ℝ))
    wasserstein2 (markovLaws (splittingUpdate f₁ T h) (stdGaussian (EuclideanSpace ℝ ι)) μ n)
      (gibbsMeasure (fun x => f₁ x + e x)) ≠ ⊤ ∧
    wasserstein2Real (markovLaws (splittingUpdate f₁ T h) (stdGaussian (EuclideanSpace ℝ ι)) μ n)
      (gibbsMeasure (fun x => f₁ x + e x)) ^ 2 ≤
      (1 - m * h) ^ n * wasserstein2Real μ (gibbsMeasure (fun x => f₁ x + e x)) ^ 2 +
        h * splittingRMSConstant m (L₁ : ℝ) G noise (K : ℝ) := by
  let π := gibbsMeasure (fun x => f₁ x + e x)
  let F := splittingUpdate f₁ T h
  let η := stdGaussian (EuclideanSpace ℝ ι)
  let laws := markovLaws F η μ
  have hF : Measurable (Function.uncurry F) := splittingUpdate_measurable hLip₁ hT h
  have hprob (k : ℕ) : IsProbabilityMeasure (laws k) := markovLaws_isProbability F hF μ η k
  have hfinite' (k : ℕ) : wasserstein2 (laws k) π ≠ ⊤ := by
    induction k with
    | zero => exact hfinite
    | succ k ih =>
      have := hprob k
      exact (splitting_markov_step_sq_bound hf₁ he m h hm hh hsc hLip₁ hmL hsmall heconv
        hegrad heLip hfLip hbounded hT henergy delta hgap (laws k) ih).1
  let G := Real.sqrt (2 * (L₁ : ℝ) ^ 2 *
    ((Module.finrank ℝ (EuclideanSpace ℝ ι) : ℝ) / m) + 2 * (K : ℝ) ^ 2) + (K : ℝ)
  let noise := Real.sqrt (2 * (Fintype.card ι : ℝ))
  let C := splittingRMSConstant m (L₁ : ℝ) G noise (K : ℝ)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hnoise : 0 ≤ noise := Real.sqrt_nonneg _
  have hC : 0 ≤ C := splittingRMSConstant_nonneg hm hG K.coe_nonneg
  have hmh := step_product_le_one m h hm hh hmL hsmall
  have hhsmall : h ≤ 1 / m := (le_div_iff₀ hm).mpr (by nlinarith)
  have hforcing := splittingCouplingForcing_le (L := (L₁ : ℝ)) hm hh hhsmall hG hnoise
    K.coe_nonneg hdelta
  have hstep (k : ℕ) : wasserstein2Real (laws (k + 1)) π ^ 2 ≤
      (1 - m * h) * wasserstein2Real (laws k) π ^ 2 + m * h ^ 2 * C := by
    have := hprob k
    have hb := (splitting_markov_step_sq_bound hf₁ he m h hm hh hsc hLip₁ hmL hsmall heconv
      hegrad heLip hfLip hbounded hT henergy delta hgap (laws k) (hfinite' k)).2
    exact hb.trans (add_le_add_right hforcing _)
  have hb := affine_recurrence_bound (fun k => wasserstein2Real (laws k) π ^ 2)
    (1 - m * h) (m * h ^ 2 * C) (by linarith) (by nlinarith [mul_pos hm hh])
    (by positivity) hstep n
  have heq : m * h ^ 2 * C / (1 - (1 - m * h)) = h * C := by
    field_simp
    ring
  rw [heq] at hb
  exact ⟨hfinite' n, hb⟩

end Generic

/-- Smoothing-uniform moment bound in the scaled particle coordinates. -/
def pipglaReferenceG (N dθ dx : ℕ) (m : ℝ) (L₁ K : ℝ≥0) : ℝ :=
  Real.sqrt (2 * ((N : ℝ) * (L₁ : ℝ)) ^ 2 *
    ((dθ + N * dx : ℕ) / ((N : ℝ) * m)) + 2 * ((N : ℝ) * (K : ℝ)) ^ 2) +
    (N : ℝ) * (K : ℝ)

/-- A finite explicit coefficient for the equal-step PIPGLA transport floor. -/
def pipglaTransportConstant (N dθ dx : ℕ) (m : ℝ) (L₁ K : ℝ≥0) : ℝ :=
  splittingRMSConstant ((N : ℝ) * m) ((N : ℝ) * (L₁ : ℝ))
    (pipglaReferenceG N dθ dx m L₁ K) (Real.sqrt (2 * (dθ + N * dx : ℕ)))
    ((N : ℝ) * (K : ℝ))

/-- The explicit transport coefficient is nonnegative in the intended regime. -/
theorem pipglaTransportConstant_nonneg {N dθ dx : ℕ} (hN : 0 < N)
    {m : ℝ} (hm : 0 < m) (L₁ K : ℝ≥0) :
    0 ≤ pipglaTransportConstant N dθ dx m L₁ K := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  exact splittingRMSConstant_nonneg (mul_pos hn hm)
    (by dsimp [pipglaReferenceG]; positivity) (by positivity)

/-- The actual PIPGLA Gaussian recursion, with equal proximal and forward
steps, converges to within a proved `O(sqrt γ)` transport radius of the true
smooth reference Gibbs law. No invariant-law or convergence hypothesis is
assumed. -/
theorem pipgla_equal_step_transport_sq
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    {N dθ dx : ℕ} (hN : 0 < N) {g₁ g₂ : IPLA.Joint dθ dx → ℝ}
    (m γ : ℝ) (L₁ K : ℝ≥0)
    (hg₁ : Differentiable ℝ g₁) (hsc : StrongConvexOn univ m g₁)
    (hLip : LipschitzWith L₁ (gradient g₁))
    (hg₂ : ConvexOn ℝ univ g₂) (hb : ∃ b, ∀ z, b ≤ g₂ z)
    (hK : LipschitzWith K g₂) (hm : 0 < m) (hmL : m ≤ (L₁ : ℝ))
    (hγ : 0 < γ) (hsmall : γ ≤ 2 / (m + (L₁ : ℝ)))
    (initial : Lp (IPLA.State N dθ dx) 2 Q)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 Q)
    (hGaussian : IPLA.GaussianInnovations Q initial noise) (n : ℕ) :
    let π := @IPLA.gibbsTarget N dθ dx (smoothedPotential g₁ g₂ γ)
    wasserstein2 (pipglaLaws Q g₁ (prox g₂ γ) γ initial (fun k => noise k) n) π ≠ ⊤ ∧
    wasserstein2Real (pipglaLaws Q g₁ (prox g₂ γ) γ initial (fun k => noise k) n) π ^ 2 ≤
      (1 - m * γ) ^ n * wasserstein2Real (Q.map initial) π ^ 2 +
        (γ / N) * pipglaTransportConstant N dθ dx m L₁ K := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  let f₁ := @IPLA.potential N dθ dx g₁
  let f := @IPLA.potential N dθ dx g₂
  let e := @IPLA.potential N dθ dx (moreau g₂ γ)
  let T := @pairwiseMap N dθ dx (prox g₂ γ)
  have he : Differentiable ℝ e := IPLA.potential_differentiable (moreau_differentiable hg₂ hb hγ)
  have heconv : ConvexOn ℝ univ e := by
    have hs := IPLA.potential_strongConvex (N := N)
      (strongConvexOn_zero.mpr (moreau_convex hg₂ hb hγ))
    simpa only [mul_zero, strongConvexOn_zero] using hs
  have hres : gradient (moreau g₂ γ) = residual g₂ γ := funext (gradient_moreau hg₂ hb hγ)
  have hmoreauLip : LipschitzWith γ⁻¹.toNNReal (gradient (moreau g₂ γ)) := by
    rw [hres]
    exact residual_lipschitz hg₂ hb hγ
  have hegrad := IPLA.potential_gradient_lipschitz (N := N)
    (moreau_differentiable hg₂ hb hγ) hmoreauLip
  have heLip := potential_moreau_lipschitz hN hg₂ hb hγ hK
  have hfLip := potential_lipschitz hN hK
  have hbound (z : IPLA.State N dθ dx) : ‖gradient e z‖ ≤ (((N : ℝ≥0) * K : ℝ≥0) : ℝ) := by
    simpa using potential_moreau_gradient_norm_le hN hg₂ hb hγ hK z
  have henergy (x y : IPLA.State N dθ dx) : ‖T x - y‖ ^ 2 ≤
      ‖x - y‖ ^ 2 - 2 * (γ / N) * (f x - f y) +
        (γ / N) ^ 2 * (((N : ℝ≥0) * K : ℝ≥0) : ℝ) ^ 2 := by
    have he := pairwise_prox_energy_le_lipschitz hN hg₂ hb hγ hK x y
    have hscale : (γ / (N : ℝ)) ^ 2 * ((N : ℝ) * (K : ℝ)) ^ 2 =
        γ ^ 2 * (K : ℝ) ^ 2 := by field_simp
    simpa only [T, f, NNReal.coe_mul, NNReal.coe_natCast, hscale, mul_div_assoc] using he
  let δ := (N : ℝ) * γ * (K : ℝ) ^ 2 / 2
  have hgap (z : IPLA.State N dθ dx) : e z ≤ f z ∧ f z ≤ e z + δ := by
    have hh := potential_moreau_gap hg₂ hb hγ hK z
    exact ⟨by linarith [hh.1], by dsimp [δ]; linarith [hh.2]⟩
  have hδ : δ ≤ (γ / N) * (((N : ℝ≥0) * K : ℝ≥0) : ℝ) ^ 2 / 2 := by
    dsimp [δ]
    simp only [NNReal.coe_natCast]
    apply le_of_eq
    field_simp
  have hF : (fun z => f₁ z + e z) = @IPLA.potential N dθ dx (smoothedPotential g₁ g₂ γ) :=
    (potential_smoothed_decomposition g₁ g₂ γ).symm
  have hfinite : wasserstein2 (Q.map initial) (gibbsMeasure (fun z => f₁ z + e z)) ≠ ⊤ := by
    rw [hF]
    have hdiff : Differentiable ℝ (@IPLA.potential N dθ dx (smoothedPotential g₁ g₂ γ)) :=
      IPLA.potential_differentiable (hg₁.add (moreau_differentiable hg₂ hb hγ))
    have hstrong : StrongConvexOn univ ((N : ℝ) * m)
        (@IPLA.potential N dθ dx (smoothedPotential g₁ g₂ γ)) :=
      IPLA.potential_strongConvex (smoothed_strongConvex hsc (moreau_convex hg₂ hb hγ))
    have : IsProbabilityMeasure (gibbsMeasure
        (@IPLA.potential N dθ dx (smoothedPotential g₁ g₂ γ))) :=
      isProbabilityMeasure_gibbsMeasure _ ((N : ℝ) * m) (mul_pos hn hm) hdiff hstrong
    have hμ : MemLp (fun x : IPLA.State N dθ dx => x) 2 (Q.map initial) :=
      (memLp_map_measure_iff (by fun_prop)
        (Lp.aestronglyMeasurable initial).aemeasurable).mpr (Lp.memLp initial)
    exact wasserstein2_ne_top_of_memLp _ _ hμ
      (memLp_id_gibbsMeasure _ ((N : ℝ) * m) (mul_pos hn hm) hdiff hstrong)
  have : IsProbabilityMeasure (Q.map initial) := inferInstance
  have hb' := splitting_markov_laws_sq_bound (IPLA.potential_differentiable hg₁) he
    ((N : ℝ) * m) (γ / N) (mul_pos hn hm) (div_pos hγ hn)
    (IPLA.potential_strongConvex hsc) (IPLA.potential_gradient_lipschitz hg₁ hLip)
    (by simpa using mul_le_mul_of_nonneg_left hmL hn.le)
    ((IPLA.scaled_step_iff N hN m (L₁ : ℝ) γ).mpr hsmall)
    heconv hegrad heLip hfLip hbound (pairwiseMap_prox_lipschitz hN hg₂ hb hγ)
    henergy δ hgap hδ (Q.map initial) hfinite n
  have hupdate : splittingUpdate f₁ T (γ / N) = pipglaUpdate g₁ (prox g₂ γ) γ := by
    funext x z
    change T (x - (γ / N) • gradient f₁ x + Real.sqrt (2 * (γ / N)) • z) =
      T (x - (γ / N) • gradient f₁ x + Real.sqrt (2 * γ / N) • z)
    rw [show 2 * (γ / (N : ℝ)) = 2 * γ / N by ring]
  rw [hF, hupdate, ← chainLaw_eq_markovLaws _ (pipglaUpdate_measurable hN hg₁ hLip hg₂ hb hγ γ)
    (Q.map initial) (stdGaussian (IPLA.State N dθ dx)) n,
    ← pipglaLaws_eq_canonicalGaussian Q hN hg₁ hLip hg₂ hb hγ γ initial noise hGaussian n] at hb'
  have hfactor : (N : ℝ) * m * (γ / N) = m * γ := by field_simp
  simpa only [IPLA.gibbsTarget_eq_gibbsMeasure, hfactor, NNReal.coe_mul, NNReal.coe_natCast,
    IPLA.finrank_state, Fintype.card_sum, Fintype.card_fin, Fintype.card_prod,
    pipglaTransportConstant, pipglaReferenceG] using hb'

end ProximalLangevin
