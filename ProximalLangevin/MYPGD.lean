import ProximalLangevin.MYPGDTransport
import ProximalLangevin.MYIPLA

set_option linter.style.header false

/-! # A derived finite-particle MYPGD comparison theorem

MYPGD and MYIPLA use identical latent Gaussian noise, while the parameter
noise is present only in MYIPLA. This proves an explicit finite-particle
comparison for their actual Markov laws, without a mean-field assumption.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace ProximalLangevin
open ULA

section Generic
variable {N dθ dx : ℕ} {D : IPLA.State N dθ dx → IPLA.State N dθ dx}
    {r : ℝ≥0} (hD : LipschitzWith r D) (a : ℝ)

include hD

/-- The finite-moment independent Gaussian transition satisfies the derived
squared transport recurrence. -/
theorem latent_full_markov_sq
    (μ ν : Measure (IPLA.State N dθ dx)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp (fun x => x) 2 μ) (hν : MemLp (fun x => x) 2 ν) :
    wasserstein2
      (markovStep (latentGaussianUpdate D a) (stdGaussian _) μ)
      (markovStep (fullGaussianUpdate D a) (stdGaussian _) ν) ≠ ⊤ ∧
    wasserstein2Real
      (markovStep (latentGaussianUpdate D a) (stdGaussian _) μ)
      (markovStep (fullGaussianUpdate D a) (stdGaussian _) ν)^2 ≤
      (r : ℝ)^2*wasserstein2Real μ ν^2+a^2*(dθ : ℝ) := by
  have hf := wasserstein2_ne_top_of_memLp μ ν hμ hν
  obtain ⟨c, _⟩ := exists_finiteCost_coupling μ ν hf
  refine ⟨(latent_full_markov_coupling_sq hD a μ ν hμ hν c).1, ?_⟩
  apply wasserstein2_sq_bound_of_finite_couplings _ _ _ _ ((r : ℝ)^2) (a^2*(dθ : ℝ))
    (sq_nonneg _) (by positivity) hf
  intro c _hc
  exact (latent_full_markov_coupling_sq hD a μ ν hμ hν c).2

/-- The actual iterated independent-Gaussian laws differ by at most the
explicit noise-removal floor. No error recurrence is assumed. -/
theorem latent_full_markov_laws_sq (hr : (r : ℝ) < 1)
    (μ : Measure (IPLA.State N dθ dx)) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun x => x) 2 μ) (n : ℕ) :
    wasserstein2
      (markovLaws (latentGaussianUpdate D a) (stdGaussian _) μ n)
      (markovLaws (fullGaussianUpdate D a) (stdGaussian _) μ n) ≠ ⊤ ∧
    wasserstein2Real
      (markovLaws (latentGaussianUpdate D a) (stdGaussian _) μ n)
      (markovLaws (fullGaussianUpdate D a) (stdGaussian _) μ n)^2 ≤
      a^2*(dθ : ℝ)/(1-(r : ℝ)^2) := by
  let M := markovLaws (latentGaussianUpdate D a) (stdGaussian (IPLA.State N dθ dx)) μ
  let I := markovLaws (fullGaussianUpdate D a) (stdGaussian (IPLA.State N dθ dx)) μ
  have hMp (k : ℕ) : IsProbabilityMeasure (M k) :=
    markovLaws_isProbability _ (latentGaussianUpdate_measurable hD a) μ _ k
  have hIp (k : ℕ) : IsProbabilityMeasure (I k) :=
    markovLaws_isProbability _ (fullGaussianUpdate_measurable hD a) μ _ k
  have hMm (k : ℕ) : MemLp (fun x => x) 2 (M k) := by
    induction k with
    | zero => exact hμ
    | succ k ih =>
      have := hMp k
      exact latentGaussianStep_memLp hD a (M k) ih
  have hIm (k : ℕ) : MemLp (fun x => x) 2 (I k) := by
    induction k with
    | zero => exact hμ
    | succ k ih =>
      have := hIp k
      exact fullGaussianStep_memLp hD a (I k) ih
  have hfinite (k : ℕ) : wasserstein2 (M k) (I k) ≠ ⊤ := by
    have := hMp k
    have := hIp k
    exact wasserstein2_ne_top_of_memLp _ _ (hMm k) (hIm k)
  have hstep (k : ℕ) : wasserstein2Real (M (k+1)) (I (k+1))^2 ≤
      (r : ℝ)^2*wasserstein2Real (M k) (I k)^2+a^2*(dθ : ℝ) := by
    have := hMp k
    have := hIp k
    exact (latent_full_markov_sq hD a (M k) (I k) (hMm k) (hIm k)).2
  have hself : wasserstein2 μ μ = 0 := by
    have hb := wasserstein2_le_random_cost μ (fun x => x) (fun x => x)
      measurable_id measurable_id
    have hid : (fun x : IPLA.State N dθ dx => x) = id := rfl
    have hz : (fun x : IPLA.State N dθ dx => x-x) = 0 := by ext x; simp
    rw [hid] at hb
    change wasserstein2 (μ.map id) (μ.map id) ≤ _ at hb
    rw [Measure.map_id, hz, eLpNorm_zero] at hb
    exact le_antisymm hb bot_le
  have hr2 : (r : ℝ)^2 < 1 := by nlinarith [r.coe_nonneg]
  have hb := affine_recurrence_bound (fun k => wasserstein2Real (M k) (I k)^2)
    ((r : ℝ)^2) (a^2*(dθ : ℝ)) (sq_nonneg _) hr2 (by positivity) hstep n
  have hzero : wasserstein2Real (M 0) (I 0) = 0 := by
    change (wasserstein2 μ μ).toReal = 0
    rw [hself, ENNReal.toReal_zero]
  rw [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_add] at hb
  exact ⟨hfinite n, hb⟩

end Generic

/-- The smooth Euler map used by both MYPGD and MYIPLA. -/
def mypgdDriftMap {N dθ dx : ℕ} (g₁ g₂ : IPLA.Joint dθ dx → ℝ) (η γ : ℝ)
    (z : IPLA.State N dθ dx) : IPLA.State N dθ dx :=
  z-(γ/N) • gradient (@IPLA.potential N dθ dx (smoothedPotential g₁ g₂ η)) z

/-- Genuine MYPGD/MYIPLA comparison with a uniform finite-particle floor.
This bound concerns the actual Gaussian Markov transitions. It is a proved
replacement for, rather than an assertion of, the source's mean-field estimate. -/
theorem mypgd_myipla_markov_transport_sq
    {N dθ dx : ℕ} (hN : 0 < N) {g₁ g₂ : IPLA.Joint dθ dx → ℝ}
    (m η γ : ℝ) (L₁ : ℝ≥0)
    (hg₁ : Differentiable ℝ g₁) (hsc : StrongConvexOn univ m g₁)
    (hLip : LipschitzWith L₁ (gradient g₁))
    (hg₂ : ConvexOn ℝ univ g₂) (hb : ∃ b, ∀ z, b ≤ g₂ z)
    (hm : 0 < m) (hmL : m ≤ (smoothingLipschitz L₁ η : ℝ))
    (hη : 0 < η) (hγ : 0 < γ)
    (hsmall : γ ≤ 2/(m+(smoothingLipschitz L₁ η : ℝ)))
    (μ : Measure (IPLA.State N dθ dx)) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun x => x) 2 μ) (n : ℕ) :
    let D := @mypgdDriftMap N dθ dx g₁ g₂ η γ
    let a := Real.sqrt (2*γ/N)
    wasserstein2 (markovLaws (latentGaussianUpdate D a) (stdGaussian _) μ n)
      (markovLaws (fullGaussianUpdate D a) (stdGaussian _) μ n) ≠ ⊤ ∧
    wasserstein2Real (markovLaws (latentGaussianUpdate D a) (stdGaussian _) μ n)
      (markovLaws (fullGaussianUpdate D a) (stdGaussian _) μ n)^2 ≤
      2*(dθ : ℝ)/((N : ℝ)*m) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  let L := smoothingLipschitz L₁ η
  have hdiff : Differentiable ℝ (smoothedPotential g₁ g₂ η) :=
    hg₁.add (moreau_differentiable hg₂ hb hη)
  have hstrong := smoothed_strongConvex hsc (moreau_convex hg₂ hb hη)
  have hres : gradient (moreau g₂ η) = residual g₂ η := funext (gradient_moreau hg₂ hb hη)
  have hgrad : LipschitzWith L (gradient (smoothedPotential g₁ g₂ η)) := by
    apply smoothed_gradient_lipschitz hg₁ (moreau_differentiable hg₂ hb hη) hLip
    simpa only [hres, smoothingLipschitz, Real.toNNReal_inv] using
      residual_lipschitz hg₂ hb hη
  have hprod : m*γ ≤ 1 := by
    have hp := (le_div_iff₀ (by positivity : 0 < m+(L : ℝ))).mp hsmall
    nlinarith [mul_le_mul_of_nonneg_right hmL hγ.le]
  have hr0 : 0 ≤ 1-m*γ := by linarith
  have hr1 : 1-m*γ < 1 := by nlinarith [mul_pos hm hγ]
  let r : ℝ≥0 := ⟨1-m*γ, hr0⟩
  have hD : LipschitzWith r (@mypgdDriftMap N dθ dx g₁ g₂ η γ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hc := strong_smooth_gradient_step_contract
      (@IPLA.potential N dθ dx (smoothedPotential g₁ g₂ η))
      ((N : ℝ)*m) (γ/N) ((N : ℝ≥0)*L)
      (IPLA.potential_differentiable hdiff) (IPLA.potential_strongConvex hstrong)
      (IPLA.potential_gradient_lipschitz hdiff hgrad)
      (by simpa using mul_le_mul_of_nonneg_left hmL hn.le)
      (by simp only [NNReal.coe_mul, NNReal.coe_natCast]; positivity)
      (by positivity) ((IPLA.scaled_step_iff N hN m (L : ℝ) γ).mpr hsmall) x y
    have hfactor : (N : ℝ)*m*(γ/N)=m*γ := by field_simp
    rw [hfactor] at hc
    change ‖(x-(γ/N) • gradient (IPLA.potential (smoothedPotential g₁ g₂ η)) x) -
      (y-(γ/N) • gradient (IPLA.potential (smoothedPotential g₁ g₂ η)) y)‖ ≤
      (1-m*γ)*‖x-y‖
    exact hc
  have hb' := latent_full_markov_laws_sq hD (Real.sqrt (2*γ/N)) hr1 μ hμ n
  refine ⟨hb'.1, hb'.2.trans ?_⟩
  change (Real.sqrt (2*γ/N))^2*(dθ : ℝ)/(1-(1-m*γ)^2) ≤ _
  rw [Real.sq_sqrt (by positivity)]
  have hbound : m*γ ≤ (1-(1-m*γ)^2) := by
    nlinarith [mul_nonneg (mul_nonneg hm.le hγ.le) (sub_nonneg.mpr hprod)]
  calc
    (2*γ/N)*(dθ : ℝ)/(1-(1-m*γ)^2) ≤ (2*γ/N)*(dθ : ℝ)/(m*γ) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hm hγ) hbound
    _ = 2*(dθ : ℝ)/((N : ℝ)*m) := by field_simp

end ProximalLangevin
