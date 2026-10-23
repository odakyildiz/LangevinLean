import UnadjustedLangevin.LangevinIntegral

/-! # Constructing the kinetic integral equation

The drift is a concrete Lipschitz vector field on velocity-position pairs.
The finite-horizon existence theorem invokes the project's proved Picard
construction; no kinetic reference process or integral identity is postulated.
The input is any continuous additive path in velocity, so the theorem applies
pathwise to continuous Brownian trajectories and in L² to continuous L² noise.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal

namespace KineticLangevin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The negative kinetic drift, in the sign convention of the Picard theorem. -/
def kineticNegativeDrift (g : E → E) (γ u : ℝ) (s : E × E) : E × E :=
  (γ • s.1 + u • g s.2, -s.1)

/-- A global Lipschitz constant for the actual kinetic phase-space drift.
The maximum norm of the product is convenient for existence only. -/
theorem kineticNegativeDrift_lipschitz (g : E → E) (L γ u : ℝ≥0)
    (hg : LipschitzWith L g) :
    LipschitzWith (γ + u * L + 1) (kineticNegativeDrift g γ u) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [dist_eq_norm]
  change max ‖(γ : ℝ) • s.1 + (u : ℝ) • g s.2 - ((γ : ℝ) • t.1 + (u : ℝ) • g t.2)‖
      ‖-s.1 - -t.1‖ ≤ _
  rw [max_le_iff]
  have hv : ‖s.1 - t.1‖ ≤ ‖s - t‖ := by simpa using (norm_fst_le (s - t))
  have hx : ‖s.2 - t.2‖ ≤ ‖s - t‖ := by simpa using (norm_snd_le (s - t))
  have hgrad : ‖g s.2 - g t.2‖ ≤ (L : ℝ) * ‖s - t‖ :=
    (hg.norm_sub_le _ _).trans (mul_le_mul_of_nonneg_left hx L.coe_nonneg)
  constructor
  · have he : (γ : ℝ) • s.1 + (u : ℝ) • g s.2 - ((γ : ℝ) • t.1 + (u : ℝ) • g t.2) =
        (γ : ℝ) • (s.1 - t.1) + (u : ℝ) • (g s.2 - g t.2) := by module
    rw [he]
    have htriangle := norm_add_le ((γ : ℝ) • (s.1 - t.1)) ((u : ℝ) • (g s.2 - g t.2))
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg γ.coe_nonneg,
      abs_of_nonneg u.coe_nonneg] at htriangle
    have hγv := mul_le_mul_of_nonneg_left hv γ.coe_nonneg
    have hug := mul_le_mul_of_nonneg_left hgrad u.coe_nonneg
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_one, dist_eq_norm]
    nlinarith [norm_nonneg (s - t)]
  · simp only [neg_sub_neg, norm_sub_rev]
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_one, dist_eq_norm]
    have hnonneg : 0 ≤ ((γ : ℝ) + (u : ℝ) * (L : ℝ)) * ‖s - t‖ := by positivity
    nlinarith

/-- The actual kinetic integral equation exists on every finite horizon,
from a Lipschitz force and continuous velocity noise.  In particular, the
position receives no direct additive noise. -/
theorem exists_kinetic_integral [CompleteSpace E]
    (g : E → E) (L γ u : ℝ≥0) (hg : LipschitzWith L g)
    (initial : E × E) (B : ℝ → E) (hB : Continuous B) (hB0 : B 0 = 0)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ Y : ℝ → E × E, Continuous Y ∧ Y 0 = initial ∧
      ∀ t ∈ Icc 0 T,
        Y t - initial = -(∫ s in 0..t, kineticNegativeDrift g γ u (Y s)) +
          (B t, 0) := by
  exact ULA.exists_langevin_integral (kineticNegativeDrift g γ u) (γ + u * L + 1)
    (kineticNegativeDrift_lipschitz g L γ u hg) initial (fun t ↦ (B t, 0))
    (hB.prodMk continuous_const) (by simp [hB0]) T hT

end KineticLangevin
