import IPLA.ULAAdapter
import IPLA.Foundations
import IPLA.LSI.Scaling
import UnadjustedLangevin.LSI.InterpolationData

set_option linter.style.header false

/-!
# Conditional log-Sobolev bounds for the actual Gaussian IPLA laws

IPLA is ULA for the actual lifted potential `U_N`, with step `γ / N`,
gradient Lipschitz constant `N * L`, and dimension `dθ + N * dx`.
The log-Sobolev assumption below concerns the lifted Gibbs target itself.
No implication from a pair-potential LSI to a lifted-target LSI is asserted.

The interpolation data retain the explicit analytic density, weak-equation,
drift-error, and gradient-moment obligations of the shared ULA result. The
finite KL guard is proved before using its real value. These conclusions
control relative entropy; they do not give parameter concentration about an
optimizer without an additional concentration argument.

Reference: Vempala–Wibisono (2019), *Rapid Convergence of the Unadjusted
Langevin Algorithm: Isoperimetry Suffices*, Theorem 2.
https://proceedings.neurips.cc/paper_files/paper/2019/file/65a99bb7a3115fdede20da98b08a370f-Paper.pdf
-/

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal

namespace IPLA.LSI

/-- The canonical Markov laws of IPLA, using its proved lifted-ULA transition. -/
def particleLaws {N dθ dx : ℕ} (U : Joint dθ dx → ℝ) (γ : ℝ)
    (μ : Measure (State N dθ dx)) (k : ℕ) : Measure (State N dθ dx) :=
  ULA.LSI.ulaLaws (@potential N dθ dx U) (γ / N) μ k

@[simp]
theorem particleLaws_zero {N dθ dx : ℕ} (U : Joint dθ dx → ℝ) (γ : ℝ)
    (μ : Measure (State N dθ dx)) : particleLaws U γ μ 0 = μ := rfl

/-- The actual lifted IPLA transition preserves probability mass. -/
theorem particleLaws_isProbability
    {N dθ dx : ℕ} (U : Joint dθ dx → ℝ) (γ : ℝ)
    (μ : Measure (State N dθ dx)) [IsProbabilityMeasure μ] (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U)) (k : ℕ) :
    IsProbabilityMeasure (particleLaws U γ μ k) :=
  ULA.LSI.ulaLaws_isProbability (@potential N dθ dx U) (γ / N) μ ((N : ℝ≥0) * L)
    (potential_gradient_lipschitz hdiff hLip) k

/-- These Markov laws agree with the existing noise-driven Gaussian IPLA
implementation, including its scalar coordinate laws and independence. -/
theorem particleLaws_eq_laws
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N dθ dx : ℕ} (U : Joint dθ dx → ℝ) (γ : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (initial : Lp (State N dθ dx) 2 P) (noise : ℕ → Lp (State N dθ dx) 2 P)
    (hGaussian : GaussianInnovations P initial noise) (k : ℕ) :
    particleLaws U γ (P.map initial) k =
      laws P U γ L hdiff hLip initial noise k := by
  simpa only [particleLaws, ULA.LSI.ulaLaws] using
    (IPLA.laws_eq_ulaLawStep P U γ L hdiff hLip initial noise hGaussian k).symm

/-- The identified regular interpolation gives finite actual IPLA relative
entropy. Target normalization follows from the lifted LSI assumption. -/
theorem particle_kl_finite
    {N dθ dx : ℕ} (U : Joint dθ dx → ℝ) (β γ : ℝ) (L : ℝ≥0)
    (μ : Measure (State N dθ dx)) (hγ : 0 ≤ γ)
    (hLSI : ULA.LSI.IsLogSobolev (@gibbsTarget N dθ dx U) β)
    (data : ULA.LSI.RegularInterpolationData (@potential N dθ dx U) β (γ / N)
      ((N : ℝ≥0) * L) μ) (k : ℕ) :
    InformationTheory.klDiv (particleLaws U γ μ k) (gibbsTarget U) ≠ ⊤ := by
  have : IsProbabilityMeasure (ULA.gibbsMeasure (@potential N dθ dx U)) := hLSI.1
  exact data.kl_finite (div_nonneg hγ (by positivity)) k

/-- The one-step entropy recurrence is derived from the regular weak
interpolation equation. The forcing is `6 * γ² * D * L²` in the full state. -/
theorem particle_kl_one_step
    {N dθ dx : ℕ} (hN : 0 < N) (U : Joint dθ dx → ℝ)
    (β γ : ℝ) (L : ℝ≥0) (μ : Measure (State N dθ dx)) [IsProbabilityMeasure μ]
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hβ : 0 < β) (hβL : β ≤ (N : ℝ) * (L : ℝ)) (hγ : 0 < γ)
    (hsmall : γ ≤ β / (4 * (N : ℝ) * (L : ℝ) ^ 2))
    (hLSI : ULA.LSI.IsLogSobolev (@gibbsTarget N dθ dx U) β)
    (data : ULA.LSI.RegularInterpolationData (@potential N dθ dx U) β (γ / N)
      ((N : ℝ≥0) * L) μ) (k : ℕ) :
    (InformationTheory.klDiv (particleLaws U γ μ (k + 1)) (gibbsTarget U)).toReal ≤
      Real.exp (-β * γ / N) *
        (InformationTheory.klDiv (particleLaws U γ μ k) (gibbsTarget U)).toReal +
          6 * γ ^ 2 * (dθ + N * dx : ℕ) * (L : ℝ) ^ 2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 < (L : ℝ) :=
    (mul_pos_iff_of_pos_left hn).mp (lt_of_lt_of_le hβ hβL)
  have hs : γ / (N : ℝ) ≤ β / (4 * ((N : ℝ) * (L : ℝ)) ^ 2) :=
    (lifted_lsi_step_iff N hN β (L : ℝ) γ hL).mpr hsmall
  have hLs : 0 < (((N : ℝ≥0) * L : ℝ≥0) : ℝ) := by
    simpa only [NNReal.coe_mul, NNReal.coe_natCast] using mul_pos hn hL
  have hβLs : β ≤ (((N : ℝ≥0) * L : ℝ≥0) : ℝ) := by
    simpa only [NNReal.coe_mul, NNReal.coe_natCast] using hβL
  have hscaled : γ / (N : ℝ) ≤ β / (4 * (((N : ℝ≥0) * L : ℝ≥0) : ℝ) ^ 2) := by
    simpa only [NNReal.coe_mul, NNReal.coe_natCast] using hs
  have hb := data.one_step hβ (div_pos hγ hn) hLs hβLs hscaled
    (potential_differentiable hdiff) (potential_gradient_lipschitz hdiff hLip) hLSI k
  have hrate : -β * (γ / (N : ℝ)) = -β * γ / N := by ring
  change (InformationTheory.klDiv (particleLaws U γ μ (k + 1)) (gibbsTarget U)).toReal ≤ _ at hb
  simpa only [NNReal.coe_mul, NNReal.coe_natCast, finrank_state,
    lifted_entropy_forcing_eq N hN, hrate] using! hb

/-- The actual one-step recurrence per particle has the intensive dimension
`dx + dθ / N`. -/
theorem particle_kl_one_step_normalized
    {N dθ dx : ℕ} (hN : 0 < N) (U : Joint dθ dx → ℝ)
    (β γ : ℝ) (L : ℝ≥0) (μ : Measure (State N dθ dx)) [IsProbabilityMeasure μ]
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hβ : 0 < β) (hβL : β ≤ (N : ℝ) * (L : ℝ)) (hγ : 0 < γ)
    (hsmall : γ ≤ β / (4 * (N : ℝ) * (L : ℝ) ^ 2))
    (hLSI : ULA.LSI.IsLogSobolev (@gibbsTarget N dθ dx U) β)
    (data : ULA.LSI.RegularInterpolationData (@potential N dθ dx U) β (γ / N)
      ((N : ℝ≥0) * L) μ) (k : ℕ) :
    (InformationTheory.klDiv (particleLaws U γ μ (k + 1)) (gibbsTarget U)).toReal / N ≤
      Real.exp (-β * γ / N) *
        ((InformationTheory.klDiv (particleLaws U γ μ k) (gibbsTarget U)).toReal / N) +
          (6 * γ ^ 2 * (L : ℝ) ^ 2) * ((dx : ℝ) + (dθ : ℝ) / N) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hb := (div_le_div_iff_of_pos_right hn).mpr
    (particle_kl_one_step hN U β γ L μ hdiff hLip hβ hβL hγ hsmall hLSI data k)
  have heq :
      (Real.exp (-β * γ / N) *
        (InformationTheory.klDiv (particleLaws U γ μ k) (gibbsTarget U)).toReal +
          6 * γ ^ 2 * (dθ + N * dx : ℕ) * (L : ℝ) ^ 2) / N =
      Real.exp (-β * γ / N) *
        ((InformationTheory.klDiv (particleLaws U γ μ k) (gibbsTarget U)).toReal / N) +
          (6 * γ ^ 2 * (L : ℝ) ^ 2) * ((dx : ℝ) + (dθ : ℝ) / N) := by
    rw [add_div, normalized_entropy_forcing_eq N dθ dx hN]
    ring
  rwa [heq] at hb

/-- The shared ULA entropy argument in IPLA coordinates. The LSI constant
`β` belongs to the full lifted target; in particular it is not assumed to
equal `N` times a pair-target constant. -/
theorem particle_kl_bound
    {N dθ dx : ℕ} (hN : 0 < N) (U : Joint dθ dx → ℝ)
    (β γ : ℝ) (L : ℝ≥0) (μ : Measure (State N dθ dx)) [IsProbabilityMeasure μ]
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hβ : 0 < β) (hβL : β ≤ (N : ℝ) * (L : ℝ)) (hγ : 0 < γ)
    (hsmall : γ ≤ β / (4 * (N : ℝ) * (L : ℝ) ^ 2))
    (hLSI : ULA.LSI.IsLogSobolev (@gibbsTarget N dθ dx U) β)
    (data : ULA.LSI.RegularInterpolationData (@potential N dθ dx U) β (γ / N)
      ((N : ℝ≥0) * L) μ) (k : ℕ) :
    (InformationTheory.klDiv (particleLaws U γ μ k) (gibbsTarget U)).toReal ≤
      Real.exp (-β * γ * k / N) *
        (InformationTheory.klDiv μ (gibbsTarget U)).toReal +
          8 * γ * N * (dθ + N * dx : ℕ) * (L : ℝ) ^ 2 / β := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 < (L : ℝ) :=
    (mul_pos_iff_of_pos_left hn).mp (lt_of_lt_of_le hβ hβL)
  have hs : γ / (N : ℝ) ≤ β / (4 * ((N : ℝ) * (L : ℝ)) ^ 2) :=
    (lifted_lsi_step_iff N hN β (L : ℝ) γ hL).mpr hsmall
  have hLs : 0 < (((N : ℝ≥0) * L : ℝ≥0) : ℝ) := by
    simpa only [NNReal.coe_mul, NNReal.coe_natCast] using mul_pos hn hL
  have hβLs : β ≤ (((N : ℝ≥0) * L : ℝ≥0) : ℝ) := by
    simpa only [NNReal.coe_mul, NNReal.coe_natCast] using hβL
  have hscaled : γ / (N : ℝ) ≤ β / (4 * (((N : ℝ≥0) * L : ℝ≥0) : ℝ) ^ 2) := by
    simpa only [NNReal.coe_mul, NNReal.coe_natCast] using hs
  have hb := data.kl_bound hβ (div_pos hγ hn) hLs hβLs hscaled
    (potential_differentiable hdiff) (potential_gradient_lipschitz hdiff hLip) hLSI k
  change (InformationTheory.klDiv (particleLaws U γ μ k) (gibbsTarget U)).toReal ≤ _ at hb
  simpa only [NNReal.coe_mul, NNReal.coe_natCast, finrank_state,
    lifted_entropy_rate_eq, lifted_entropy_bias_eq N hN] using! hb

/-- Dividing the full-state relative entropy by the particle number gives
its natural per-particle normalization. -/
theorem particle_kl_bound_normalized
    {N dθ dx : ℕ} (hN : 0 < N) (U : Joint dθ dx → ℝ)
    (β γ : ℝ) (L : ℝ≥0) (μ : Measure (State N dθ dx)) [IsProbabilityMeasure μ]
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hβ : 0 < β) (hβL : β ≤ (N : ℝ) * (L : ℝ)) (hγ : 0 < γ)
    (hsmall : γ ≤ β / (4 * (N : ℝ) * (L : ℝ) ^ 2))
    (hLSI : ULA.LSI.IsLogSobolev (@gibbsTarget N dθ dx U) β)
    (data : ULA.LSI.RegularInterpolationData (@potential N dθ dx U) β (γ / N)
      ((N : ℝ≥0) * L) μ) (k : ℕ) :
    (InformationTheory.klDiv (particleLaws U γ μ k) (gibbsTarget U)).toReal / N ≤
      Real.exp (-β * γ * k / N) *
        ((InformationTheory.klDiv μ (gibbsTarget U)).toReal / N) +
          8 * γ * (dθ + N * dx : ℕ) * (L : ℝ) ^ 2 / β := by
  exact normalize_entropy_bound N hN β γ (L : ℝ) (dθ + N * dx : ℕ)
    (InformationTheory.klDiv (particleLaws U γ μ k) (gibbsTarget U)).toReal
    (InformationTheory.klDiv μ (gibbsTarget U)).toReal (Real.exp (-β * γ * k / N))
    (particle_kl_bound hN U β γ L μ hdiff hLip hβ hβL hγ hsmall hLSI data k)

/-- If the lifted target actually has LSI constant `N * α`, the rate is
independent of `N` and the normalized dimension is `dx + dθ / N`.
This is a specialization of a supplied lifted-target LSI, rather than a
tensorization assertion about the original pair model. -/
theorem particle_kl_bound_of_linear_lsi
    {N dθ dx : ℕ} (hN : 0 < N) (U : Joint dθ dx → ℝ)
    (α γ : ℝ) (L : ℝ≥0) (μ : Measure (State N dθ dx)) [IsProbabilityMeasure μ]
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hα : 0 < α) (hαL : α ≤ (L : ℝ)) (hγ : 0 < γ)
    (hsmall : γ ≤ α / (4 * (L : ℝ) ^ 2))
    (hLSI : ULA.LSI.IsLogSobolev (@gibbsTarget N dθ dx U) ((N : ℝ) * α))
    (data : ULA.LSI.RegularInterpolationData (@potential N dθ dx U) ((N : ℝ) * α)
      (γ / N) ((N : ℝ≥0) * L) μ) (k : ℕ) :
    (InformationTheory.klDiv (particleLaws U γ μ k) (gibbsTarget U)).toReal / N ≤
      Real.exp (-α * γ * k) *
        ((InformationTheory.klDiv μ (gibbsTarget U)).toReal / N) +
          (8 * γ * (L : ℝ) ^ 2 / α) * ((dx : ℝ) + (dθ : ℝ) / N) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 < (L : ℝ) := lt_of_lt_of_le hα hαL
  have hs : γ ≤ (N : ℝ) * α / (4 * (N : ℝ) * (L : ℝ) ^ 2) := by
    exact (linear_lsi_step_iff N hN α (L : ℝ) γ hL).mpr hsmall
  have hb := particle_kl_bound_normalized hN U ((N : ℝ) * α) γ L μ hdiff hLip
    (mul_pos hn hα) (linear_lsi_compatibility N hN α (L : ℝ) hαL) hγ hs hLSI data k
  simpa only [linear_entropy_rate_eq N hN,
    linear_normalized_entropy_bias_eq N dθ dx hN] using hb

/-- The normalized bound for the original independent-Gaussian IPLA
implementation. It is obtained by identifying its laws with `particleLaws`. -/
theorem gaussian_ipla_kl_bound_normalized
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N dθ dx : ℕ} (hN : 0 < N) (U : Joint dθ dx → ℝ)
    (β γ : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hβ : 0 < β) (hβL : β ≤ (N : ℝ) * (L : ℝ)) (hγ : 0 < γ)
    (hsmall : γ ≤ β / (4 * (N : ℝ) * (L : ℝ) ^ 2))
    (hLSI : ULA.LSI.IsLogSobolev (@gibbsTarget N dθ dx U) β)
    (initial : Lp (State N dθ dx) 2 P) (noise : ℕ → Lp (State N dθ dx) 2 P)
    (hGaussian : GaussianInnovations P initial noise)
    (data : ULA.LSI.RegularInterpolationData (@potential N dθ dx U) β (γ / N)
      ((N : ℝ≥0) * L) (P.map initial)) (k : ℕ) :
    (InformationTheory.klDiv (laws P U γ L hdiff hLip initial noise k)
      (gibbsTarget U)).toReal / N ≤
      Real.exp (-β * γ * k / N) *
        ((InformationTheory.klDiv (P.map initial) (gibbsTarget U)).toReal / N) +
          8 * γ * (dθ + N * dx : ℕ) * (L : ℝ) ^ 2 / β := by
  simpa only [particleLaws_eq_laws P U γ L hdiff hLip initial noise hGaussian k] using
    particle_kl_bound_normalized hN U β γ L (P.map initial) hdiff hLip
      hβ hβL hγ hsmall hLSI data k

/-- The `N * α` lifted-LSI specialization for the actual Gaussian IPLA
implementation, with every algorithm-law assumption retained. -/
theorem gaussian_ipla_kl_bound_of_linear_lsi
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N dθ dx : ℕ} (hN : 0 < N) (U : Joint dθ dx → ℝ)
    (α γ : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hα : 0 < α) (hαL : α ≤ (L : ℝ)) (hγ : 0 < γ)
    (hsmall : γ ≤ α / (4 * (L : ℝ) ^ 2))
    (hLSI : ULA.LSI.IsLogSobolev (@gibbsTarget N dθ dx U) ((N : ℝ) * α))
    (initial : Lp (State N dθ dx) 2 P) (noise : ℕ → Lp (State N dθ dx) 2 P)
    (hGaussian : GaussianInnovations P initial noise)
    (data : ULA.LSI.RegularInterpolationData (@potential N dθ dx U) ((N : ℝ) * α)
      (γ / N) ((N : ℝ≥0) * L) (P.map initial)) (k : ℕ) :
    (InformationTheory.klDiv (laws P U γ L hdiff hLip initial noise k)
      (gibbsTarget U)).toReal / N ≤
      Real.exp (-α * γ * k) *
        ((InformationTheory.klDiv (P.map initial) (gibbsTarget U)).toReal / N) +
          (8 * γ * (L : ℝ) ^ 2 / α) * ((dx : ℝ) + (dθ : ℝ) / N) := by
  simpa only [particleLaws_eq_laws P U γ L hdiff hLip initial noise hGaussian k] using
    particle_kl_bound_of_linear_lsi hN U α γ L (P.map initial) hdiff hLip
      hα hαL hγ hsmall hLSI data k

end IPLA.LSI
