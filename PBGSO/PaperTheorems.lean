import PBGSO.Framework
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Quantitative comparison arguments for PBGSO

The model and joint monotonicity definition retain general optimiser maps,
augmented sampler states, and multiplicative noise. The comparison theorems
below prove the deterministic analytic step of the paper's arguments from
explicit energy derivative hypotheses. Identifying such derivatives with
coupled stochastic laws requires a separate Itô/martingale argument; that
argument is not silently included in these hypotheses or claimed here.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators RealInnerProductSpace InnerProductSpace Topology

namespace PBGSO

section Geometry
variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [MeasurableSpace Z] [Fintype I]

/-- Explicit positive-definite quadratic weights and their spectral bounds.
No symmetry or definiteness is inferred from an arbitrary matrix. -/
structure TwistedGeometry (S Z : Type*)
    [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] where
  optimizerWeight : S →L[ℝ] S
  samplerWeight : Z →L[ℝ] Z
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_le_upper : lower ≤ upper
  optimizer_symmetric : ∀ x y,
    ⟪x, optimizerWeight y⟫_ℝ = ⟪optimizerWeight x, y⟫_ℝ
  sampler_symmetric : ∀ x y,
    ⟪x, samplerWeight y⟫_ℝ = ⟪samplerWeight x, y⟫_ℝ
  optimizer_lower : ∀ s, lower * ‖s‖ ^ 2 ≤ ⟪s, optimizerWeight s⟫_ℝ
  optimizer_upper : ∀ s, ⟪s, optimizerWeight s⟫_ℝ ≤ upper * ‖s‖ ^ 2
  sampler_lower : ∀ z, lower * ‖z‖ ^ 2 ≤ ⟪z, samplerWeight z⟫_ℝ
  sampler_upper : ∀ z, ⟪z, samplerWeight z⟫_ℝ ≤ upper * ‖z‖ ^ 2

namespace TwistedGeometry
variable (D : TwistedGeometry S Z)

def optimizerSq (s : S) : ℝ := ⟪s, D.optimizerWeight s⟫_ℝ
def samplerSq (z : Z) : ℝ := ⟪z, D.samplerWeight z⟫_ℝ
def conditionNumber : ℝ := D.upper / D.lower

theorem conditionNumber_ge_one : 1 ≤ D.conditionNumber := by
  exact (le_div_iff₀ D.lower_pos).mpr (by simpa using D.lower_le_upper)

theorem optimizerSq_nonneg (s : S) : 0 ≤ D.optimizerSq s :=
  (mul_nonneg D.lower_pos.le (sq_nonneg _)).trans (D.optimizer_lower s)

theorem samplerSq_nonneg (z : Z) : 0 ≤ D.samplerSq z :=
  (mul_nonneg D.lower_pos.le (sq_nonneg _)).trans (D.sampler_lower z)

end TwistedGeometry

/-- The two marginals are specified by genuine pushforwards. -/
def IsCoupling (Λ : Measure (Z × Z)) (ν ν' : Measure Z) : Prop :=
  Λ.map Prod.fst = ν ∧ Λ.map Prod.snd = ν'

/-- The sampler contribution to the twisted quadratic coupling energy.
The sum is the weighted Hilbert--Schmidt diffusion correction. -/
def samplerCouplingWork (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    (s s' : S) (zz : Z × Z) : ℝ :=
  ⟪zz.1 - zz.2, D.samplerWeight
      (M.drift (M.parameter s) zz.1 - M.drift (M.parameter s') zz.2)⟫_ℝ +
    (1 / 2 : ℝ) * ∑ i,
      D.samplerSq (M.diffusion (M.parameter s) zz.1 i -
        M.diffusion (M.parameter s') zz.2 i)

/-- The exact twisted joint strong monotonicity assumption in the paper,
including the Hilbert--Schmidt diffusion correction represented by its
finite sum of squared column norms. The gradient integrability premises
exclude accidental use of undefined Bochner expectations. -/
def TwistedJointMonotonicity (M : Model S Θ Z X I)
    (D : TwistedGeometry S Z) (ρ : ℝ) : Prop :=
  ∀ t, 0 ≤ t → ∀ s s' ν ν' (Λ : Measure (Z × Z)),
    IsCoupling Λ ν ν' →
    IsProbabilityMeasure ν → IsProbabilityMeasure ν' →
    HasFiniteSecondMoment ν → HasFiniteSecondMoment ν' →
    Integrable (fun z => M.observation (M.parameter s) (M.position z)) ν →
    Integrable (fun z => M.observation (M.parameter s') (M.position z)) ν' →
    Integrable (samplerCouplingWork M D s s') Λ →
    Integrable (fun zz => D.samplerSq (zz.1 - zz.2)) Λ →
    ⟪s - s', D.optimizerWeight
      (M.optimizerField t s ν - M.optimizerField t s' ν')⟫_ℝ +
      (∫ zz, samplerCouplingWork M D s s' zz ∂Λ) ≤
      -ρ * (D.optimizerSq (s - s') +
        ∫ zz, D.samplerSq (zz.1 - zz.2) ∂Λ)

end Geometry

/-- Grönwall proves the squared-energy decay from a right derivative
inequality. This theorem applies to any energy, including an expectation
once differentiation under the stochastic integral has been justified. -/
theorem energy_decay {E E' : ℝ → ℝ} {ρ T : ℝ}
    (hcont : ContinuousOn E (Icc 0 T))
    (hder : ∀ t ∈ Ico 0 T, HasDerivWithinAt E (E' t) (Ici t) t)
    (hdiss : ∀ t ∈ Ico 0 T, E' t ≤ -2 * ρ * E t)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    E t ≤ E 0 * Real.exp (-2 * ρ * t) := by
  have h := le_gronwallBound_of_liminf_deriv_right_le (K := -2 * ρ) (ε := 0) hcont
    (fun r hr c hc => (hder r hr).liminf_right_slope_le hc)
    (le_refl (E 0)) (fun r hr => by simpa using hdiss r hr) t ht
  simpa only [gronwallBound_ε0, sub_zero] using h

/-- The square-root comparison needed for the finite-particle theorem.
It is proved from the *squared* energy inequality and zero initial error.
No differentiability of `sqrt E` at its zeros is assumed: the proof uses
`sqrt (E + ε²)` and then sends `ε` to zero by an order argument. -/
theorem forced_energy_bound {E E' : ℝ → ℝ} {ρ c T : ℝ}
    (hρ : 0 < ρ) (hc : 0 ≤ c)
    (hcont : ContinuousOn E (Icc 0 T))
    (hder : ∀ t ∈ Ico 0 T, HasDerivWithinAt E (E' t) (Ici t) t)
    (hE : ∀ t ∈ Icc 0 T, 0 ≤ E t) (hzero : E 0 = 0)
    (hdiss : ∀ t ∈ Ico 0 T,
      E' t ≤ -2 * ρ * E t + 2 * c * Real.sqrt (E t))
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    Real.sqrt (E t) ≤ c / ρ * (1 - Real.exp (-ρ * t)) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let u : ℝ → ℝ := fun r => Real.sqrt (E r + ε ^ 2)
  let u' : ℝ → ℝ := fun r => E' r / (2 * u r)
  have hT : 0 ≤ T := ht.1.trans ht.2
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hup : ∀ r ∈ Icc 0 T, 0 < u r := by
    intro r hr
    exact Real.sqrt_pos.mpr (by nlinarith [hE r hr])
  have husq : ∀ r ∈ Icc 0 T, u r ^ 2 = E r + ε ^ 2 := by
    intro r hr
    exact Real.sq_sqrt (by nlinarith [hE r hr])
  have hεu : ∀ r ∈ Icc 0 T, ε ≤ u r := by
    intro r hr
    nlinarith [husq r hr, hE r hr, (hup r hr).le]
  have hsqrt : ∀ r ∈ Icc 0 T, Real.sqrt (E r) ≤ u r := by
    intro r hr
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hucont : ContinuousOn u (Icc 0 T) :=
    Real.continuous_sqrt.comp_continuousOn (hcont.add continuousOn_const)
  have huder : ∀ r ∈ Ico 0 T, HasDerivWithinAt u (u' r) (Ici r) r := by
    intro r hr
    have hr' : r ∈ Icc 0 T := ⟨hr.1, hr.2.le⟩
    simpa only [u, u', add_zero] using
      ((hder r hr).add_const (ε ^ 2)).sqrt
        (ne_of_gt (by nlinarith [hE r hr'] : 0 < E r + ε ^ 2))
  have hubound : ∀ r ∈ Ico 0 T, u' r ≤ -ρ * u r + (c + ρ * ε) := by
    intro r hr
    have hr' : r ∈ Icc 0 T := ⟨hr.1, hr.2.le⟩
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (hup r hr'))).mpr
    have hm := mul_le_mul_of_nonneg_left (hsqrt r hr') (by positivity : 0 ≤ 2 * c)
    have hreg := mul_nonneg (by positivity : 0 ≤ 2 * ρ * ε)
      (sub_nonneg.mpr (hεu r hr'))
    have heq := husq r hr'
    have hd := hdiss r hr
    nlinarith
  have hgr := le_gronwallBound_of_liminf_deriv_right_le hucont
    (fun r hr a ha => (huder r hr).liminf_right_slope_le ha)
    (le_refl (u 0)) hubound t ht
  rw [gronwallBound_of_K_ne_0 (neg_ne_zero.mpr hρ.ne'), sub_zero] at hgr
  have hu0 : u 0 = ε := by
    simp only [u, hzero, zero_add, Real.sqrt_sq hε.le]
  rw [hu0] at hgr
  have heq : ε * Real.exp (-ρ * t) +
      (c + ρ * ε) / -ρ * (Real.exp (-ρ * t) - 1) =
      c / ρ * (1 - Real.exp (-ρ * t)) + ε := by
    field_simp
    <;> ring
  exact (hsqrt t ht).trans (heq ▸ hgr)

/-- The condition-number factor follows from the two quadratic norm
comparisons; the estimate is on the root mean square distance. -/
theorem distance_decay_of_energy {E E' d : ℝ → ℝ} {ρ T lower upper : ℝ}
    (hlower : 0 < lower) (hupper : 0 ≤ upper)
    (hcont : ContinuousOn E (Icc 0 T))
    (hder : ∀ t ∈ Ico 0 T, HasDerivWithinAt E (E' t) (Ici t) t)
    (hdiss : ∀ t ∈ Ico 0 T, E' t ≤ -2 * ρ * E t)
    (hd : ∀ t ∈ Icc 0 T, 0 ≤ d t)
    (hcomp : ∀ t ∈ Icc 0 T, lower * d t ^ 2 ≤ E t)
    (hinit : E 0 ≤ upper * d 0 ^ 2)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    d t ≤ Real.sqrt (upper / lower) * Real.exp (-ρ * t) * d 0 := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hd0 := hd 0 h0
  have hdec := energy_decay hcont hder hdiss t ht
  have hs : d t ^ 2 ≤ (upper / lower) * Real.exp (-2 * ρ * t) * d 0 ^ 2 := by
    apply (mul_le_mul_iff_of_pos_left hlower).mp
    have hi := mul_le_mul_of_nonneg_right hinit (Real.exp_pos (-2 * ρ * t)).le
    calc
      lower * d t ^ 2 ≤ E t := hcomp t ht
      _ ≤ (upper * d 0 ^ 2) * Real.exp (-2 * ρ * t) := hdec.trans hi
      _ = lower * ((upper / lower) * Real.exp (-2 * ρ * t) * d 0 ^ 2) := by
        field_simp
        <;> ring
  apply (sq_le_sq₀ (hd t ht) (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hupper hlower.le)]
  have hexp : Real.exp (-ρ * t) ^ 2 = Real.exp (-2 * ρ * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  exact hs

/-- The diagonal-dominance sufficient condition in Appendix A. It controls
the optimiser--sampler cross term as part of one joint quadratic form. -/
theorem small_gain_diagonal_form {α β C δ ρ u v : ℝ}
    (hC : 0 ≤ C)
    (hα : ρ + δ + C / 2 ≤ α) (hβ : ρ + δ + C / 2 ≤ β) :
    -α * u ^ 2 - β * v ^ 2 + C * u * v + δ * (u ^ 2 + v ^ 2) ≤
      -ρ * (u ^ 2 + v ^ 2) := by
  have ha := mul_nonneg (sub_nonneg.mpr hα) (sq_nonneg u)
  have hb := mul_nonneg (sub_nonneg.mpr hβ) (sq_nonneg v)
  have hc := mul_nonneg hC (sq_nonneg (u - v))
  nlinarith

/-- A sharp completion-of-squares criterion for the 2×2 small-gain matrix.
It can be used with any certified lower eigenvalue `ρ`. -/
theorem small_gain_schur {α β C ρ u v : ℝ}
    (hα : 0 < α - ρ)
    (hdet : C ^ 2 ≤ 4 * (α - ρ) * (β - ρ)) :
    -α * u ^ 2 - β * v ^ 2 + C * u * v ≤ -ρ * (u ^ 2 + v ^ 2) := by
  have hs := sq_nonneg (2 * (α - ρ) * u - C * v)
  have hd := mul_nonneg (sub_nonneg.mpr hdet) (sq_nonneg v)
  have h : 0 ≤ (α - ρ) *
      (α * u ^ 2 + β * v ^ 2 - C * u * v - ρ * (u ^ 2 + v ^ 2)) := by
    nlinarith
  have h' := (mul_nonneg_iff_of_pos_left hα).mp h
  linarith

/-- Combining particle interaction and mean-field relaxation gives the
paper's parameter bound; the triangle premise is explicitly separate. -/
theorem parameter_error_of_components {error interaction relaxation κ ρ V L N t d0 : ℝ}
    (htriangle : error ≤ interaction + relaxation)
    (hinteraction : interaction ≤ (L / ρ) * Real.sqrt (κ * V / N) *
      (1 - Real.exp (-ρ * t)))
    (hrelaxation : relaxation ≤ Real.sqrt κ * Real.exp (-ρ * t) * d0) :
    error ≤ Real.sqrt κ * Real.exp (-ρ * t) * d0 +
      (L / ρ) * Real.sqrt (κ * V / N) * (1 - Real.exp (-ρ * t)) := by
  linarith

/-- The exponential relaxation factor tends to zero at every positive
contractivity rate. -/
theorem relaxation_tendsto_zero {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun t : ℝ => Real.exp (-ρ * t)) atTop (𝓝 0) := by
  have hmul : Tendsto (fun t : ℝ => ρ * t) atTop atTop :=
    tendsto_id.const_mul_atTop hρ
  simpa only [Function.comp_def, neg_mul] using
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul

/-- A finite distance between two stationary solutions is zero if the
same contraction estimate holds for every nonnegative elapsed time. -/
theorem stationary_distance_zero {d C ρ : ℝ} (hd : 0 ≤ d) (hρ : 0 < ρ)
    (hcontract : ∀ t, 0 ≤ t → d ≤ C * Real.exp (-ρ * t) * d) : d = 0 := by
  have hlim : Tendsto (fun t : ℝ => C * Real.exp (-ρ * t) * d) atTop (𝓝 0) := by
    simpa using ((relaxation_tendsto_zero hρ).const_mul C).mul_const d
  have hle : d ≤ 0 := ge_of_tendsto hlim
    ((eventually_ge_atTop (0 : ℝ)).mono fun t ht => hcontract t ht)
  exact le_antisymm hle hd

/-- The explicit right-hand side of the paper's parameter estimate has the
stated long-time sampling floor. No discretisation term is included. -/
theorem parameter_bound_long_time_limit (κ L V N d0 : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun t : ℝ => Real.sqrt κ * Real.exp (-ρ * t) * d0 +
      (L / ρ) * Real.sqrt (κ * V / N) * (1 - Real.exp (-ρ * t)))
      atTop (𝓝 ((L / ρ) * Real.sqrt (κ * V / N))) := by
  have h := relaxation_tendsto_zero hρ
  simpa using ((h.const_mul (Real.sqrt κ)).mul_const d0).add
    (((tendsto_const_nhds (x := (1 : ℝ))).sub h).const_mul
      ((L / ρ) * Real.sqrt (κ * V / N)))

/-- The sampling floor vanishes as the number of particles tends to
infinity, with all geometry and variance constants fixed. -/
theorem particle_floor_tendsto_zero (κ L ρ V : ℝ) :
    Tendsto (fun N : ℕ => (L / ρ) * Real.sqrt (κ * V / (N : ℝ)))
      atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => κ * V / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (κ * V)
  simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp h).const_mul (L / ρ)

end PBGSO
