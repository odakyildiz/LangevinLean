import UnadjustedLangevin.LSI.ScoreCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bounding the drift error in entropy production

The Young inequality used in the ULA interpolation argument gives
`⟪err, score⟫ ≤ (1 / 4) * ‖score‖² + ‖err‖²`. After integration against
the positive relative density, this retains three quarters of the Fisher
information in the entropy-production upper bound.

The bounds are proved from the weak equation and the energy integrals.
Neither a drift-error estimate nor an entropy differential inequality is
assumed. Measurability and integrability requirements are explicit.

Reference: Vempala–Wibisono (2019), *Rapid Convergence of the Unadjusted
Langevin Algorithm: Isoperimetry Suffices*.
https://proceedings.neurips.cc/paper_files/paper/2019/file/65a99bb7a3115fdede20da98b08a370f-Paper.pdf
-/

noncomputable section

open MeasureTheory

namespace ULA.LSI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Young's inequality with the coefficient used to absorb one quarter of
the Fisher information. -/
theorem inner_le_quarter_norm_sq_add_norm_sq (e score : E) :
    inner ℝ e score ≤ (1 / 4 : ℝ) * ‖score‖ ^ 2 + ‖e‖ ^ 2 := by
  have h := real_inner_le_norm e score
  nlinarith [sq_nonneg (‖e‖ - ‖score‖ / 2)]

/-- The same bound for the absolute inner product, used to establish
integrability from the two energy integrals. -/
theorem abs_inner_le_quarter_norm_sq_add_norm_sq (e score : E) :
    |inner ℝ e score| ≤ (1 / 4 : ℝ) * ‖score‖ ^ 2 + ‖e‖ ^ 2 := by
  have h := abs_real_inner_le_norm e score
  nlinarith [sq_nonneg (‖e‖ - ‖score‖ / 2)]

/-- The drift-score cross term is integrable when it is measurable and both
density-weighted energy integrals are finite. -/
theorem integrable_weighted_inner_of_energy
    {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (r : X → ℝ) (err score : X → E) (hr : ∀ x, 0 ≤ r x)
    (hmeas : AEStronglyMeasurable
      (fun x ↦ r x * inner ℝ (err x) (score x)) ν)
    (hscore_int : Integrable (fun x ↦ r x * ‖score x‖ ^ 2) ν)
    (herror_int : Integrable (fun x ↦ r x * ‖err x‖ ^ 2) ν) :
    Integrable (fun x ↦ r x * inner ℝ (err x) (score x)) ν := by
  apply ((hscore_int.const_mul (1 / 4 : ℝ)).add herror_int).mono' hmeas
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hr x)]
  calc
    r x * |inner ℝ (err x) (score x)| ≤
        r x * ((1 / 4 : ℝ) * ‖score x‖ ^ 2 + ‖err x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (abs_inner_le_quarter_norm_sq_add_norm_sq (err x) (score x)) (hr x)
    _ = (1 / 4 : ℝ) * (r x * ‖score x‖ ^ 2) + r x * ‖err x‖ ^ 2 := by ring

/-- Integrated weighted Young inequality. This holds for any nonnegative
weight and does not require it to define a probability density. -/
theorem integral_weighted_inner_le_quarter_fisher_add_energy
    {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (r : X → ℝ) (err score : X → E) (hr : ∀ x, 0 ≤ r x)
    (hcross_int : Integrable (fun x ↦ r x * inner ℝ (err x) (score x)) ν)
    (hscore_int : Integrable (fun x ↦ r x * ‖score x‖ ^ 2) ν)
    (herror_int : Integrable (fun x ↦ r x * ‖err x‖ ^ 2) ν) :
    (∫ x, r x * inner ℝ (err x) (score x) ∂ν) ≤
      (1 / 4 : ℝ) * (∫ x, r x * ‖score x‖ ^ 2 ∂ν) +
        ∫ x, r x * ‖err x‖ ^ 2 ∂ν := by
  have hle := integral_mono hcross_int
    ((hscore_int.const_mul (1 / 4 : ℝ)).add herror_int) (fun x ↦ ?_)
  · simpa only [Pi.add_apply,
      integral_add (hscore_int.const_mul (1 / 4 : ℝ)) herror_int,
      integral_const_mul] using hle
  calc
    r x * inner ℝ (err x) (score x) ≤
        r x * ((1 / 4 : ℝ) * ‖score x‖ ^ 2 + ‖err x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (inner_le_quarter_norm_sq_add_norm_sq (err x) (score x)) (hr x)
    _ = (1 / 4 : ℝ) * (r x * ‖score x‖ ^ 2) + r x * ‖err x‖ ^ 2 := by ring

/-- The weak relative Fokker–Planck equation with a drift error gives the
entropy-production upper bound `-(3 / 4) * Fisher + errorEnergy`.
Integrability of the cross term is derived from measurability and the two
energy integrals, rather than assumed as an extra energy bound. -/
theorem entropy_production_le_of_forced_weak_identity
    [CompleteSpace E] [MeasurableSpace E]
    (ν : Measure E) (r rdot : E → ℝ) (err : E → E)
    (hpos : ∀ x, 0 < r x) (hdiff : ContDiff ℝ 1 r)
    (hentropy_int : Integrable (fun x ↦ rdot x * (Real.log (r x) + 1)) ν)
    (hfisher_int : Integrable
      (fun x ↦ r x * ‖gradient (fun y ↦ Real.log (r y)) x‖ ^ 2) ν)
    (henergy_int : Integrable (fun x ↦ r x * ‖err x‖ ^ 2) ν)
    (herror_meas : AEStronglyMeasurable
      (fun x ↦ r x * inner ℝ (err x) (gradient (fun y ↦ Real.log (r y)) x)) ν)
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ 1 ψ →
      Integrable (fun x ↦ rdot x * ψ x) ν →
      Integrable (fun x ↦ inner ℝ (gradient r x) (gradient ψ x)) ν →
      Integrable (fun x ↦ r x * inner ℝ (err x) (gradient ψ x)) ν →
      (∫ x, rdot x * ψ x ∂ν) =
        -(∫ x, inner ℝ (gradient r x) (gradient ψ x) ∂ν) +
          ∫ x, r x * inner ℝ (err x) (gradient ψ x) ∂ν) :
    (∫ x, rdot x * (Real.log (r x) + 1) ∂ν) ≤
      -(3 / 4 : ℝ) * (∫ x, r x * ‖gradient (fun y ↦ Real.log (r y)) x‖ ^ 2 ∂ν) +
        ∫ x, r x * ‖err x‖ ^ 2 ∂ν := by
  have herror_int := integrable_weighted_inner_of_energy ν r err
    (gradient (fun y ↦ Real.log (r y))) (fun x ↦ (hpos x).le)
    herror_meas hfisher_int henergy_int
  rw [entropy_production_of_forced_weak_identity ν r rdot err hpos hdiff
    hentropy_int hfisher_int herror_int hweak]
  have hle := integral_weighted_inner_le_quarter_fisher_add_energy ν r err
    (gradient (fun y ↦ Real.log (r y))) (fun x ↦ (hpos x).le)
    herror_int hfisher_int henergy_int
  linarith

end ULA.LSI
