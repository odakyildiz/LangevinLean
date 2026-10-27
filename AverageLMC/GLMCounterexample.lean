import AverageLMC.GLMObstruction
import AverageLMC.GaussianObstruction
import Mathlib.MeasureTheory.Constructions.Pi

set_option linter.style.header false

/-! # The isotropic GLM table cannot hold uniformly in dimension

The design below has exactly `n = p` independent standard Gaussian rows.
The potential is an actual sum of convex smooth one-dimensional components.
The event asserts an operator-norm Lipschitz bound for its explicit Hessian.
Such an event has probability strictly below one half for all sufficiently
large dimensions, contradicting the isotropic `M₂ ≤ C n` table entry.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace AverageLMC

/-- Square isotropic Gaussian design, represented by its independent rows. -/
abbrev GaussianDesign (p : ℕ) := Fin p → EuclideanSpace ℝ (Fin p)

/-- The actual product law of the paper's `n = p`, identity-covariance design. -/
def gaussianDesignLaw (p : ℕ) : Measure (GaussianDesign p) :=
  Measure.pi (fun _ : Fin p ↦ stdGaussian (EuclideanSpace ℝ (Fin p)))

instance gaussianDesignLaw_probability (p : ℕ) :
    IsProbabilityMeasure (gaussianDesignLaw p) := by
  unfold gaussianDesignLaw
  infer_instance

/-- Each design row has precisely the standard Gaussian law. -/
theorem gaussianDesign_row_law (p : ℕ) (i : Fin p) :
    HasLaw (fun X : GaussianDesign p ↦ X i)
      (stdGaussian (EuclideanSpace ℝ (Fin p))) (gaussianDesignLaw p) :=
  (measurePreserving_eval (fun _ : Fin p ↦
    stdGaussian (EuclideanSpace ℝ (Fin p))) i).hasLaw

/-- Rows are independent under the constructed design law. -/
theorem gaussianDesign_rows_independent (p : ℕ) :
    iIndepFun (fun i (X : GaussianDesign p) ↦ X i) (gaussianDesignLaw p) :=
  iIndepFun_pi (fun _ ↦ measurable_id.aemeasurable)

/-- The single Hessian upper bound required by the isotropic GLM table.
It uses the actual derivative of the actual gradient of the finite-sum
potential. The explicit rank-one Hessian is a proved identity, not a premise. -/
def glmHessianBoundEvent (p : ℕ) (i : Fin p) (C : ℝ) : Set (GaussianDesign p) :=
  {X | ∀ x y : EuclideanSpace ℝ (Fin p),
    ‖fderiv ℝ (gradient (counterexamplePotential X i)) x -
      fderiv ℝ (gradient (counterexamplePotential X i)) y‖ ≤ C * (p : ℝ) * ‖x - y‖}

/-- The claimed isotropic Hessian estimate has probability below one half
for this actual independent Gaussian design, in every large enough dimension. -/
theorem glmHessianBound_probability_lt_half (p : ℕ) (i : Fin p) (C : ℝ)
    (hC : 0 ≤ C) (hp : 16 < p) (hlarge : 8 * C ^ 2 < (p : ℝ)) :
    gaussianDesignLaw p (glmHessianBoundEvent p i C) < (1 / 2 : ℝ≥0∞) := by
  have hsub : glmHessianBoundEvent p i C ⊆
      {X : GaussianDesign p | ‖X i‖ ^ 3 ≤ C * (p : ℝ)} := by
    intro X hX
    exact counterexamplePotential_hessian_lipschitz_lower X i
      (mul_nonneg hC (Nat.cast_nonneg _)) hX
  have hrow := (gaussianDesign_row_law p i).measure_eq
    (p := fun z : EuclideanSpace ℝ (Fin p) ↦ ‖z‖ ^ 3 ≤ C * (p : ℝ))
    (by measurability)
  exact ((measure_mono hsub).trans_eq hrow).trans_lt
    (stdGaussian_cube_bound_fails p C hC hp hlarge)

/-- No constant depending only on the fixed component bound can make the
printed `M₂ ≤ C n` event have probability one half in all positive dimensions. -/
theorem no_uniform_glmHessian_bound :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℕ) (hp : 0 < p),
      (1 / 2 : ℝ≥0∞) ≤ gaussianDesignLaw p
        (glmHessianBoundEvent p ⟨0, hp⟩ C) := by
  rintro ⟨C, hC, hbound⟩
  obtain ⟨p, hp⟩ := exists_nat_gt (max 16 (8 * C ^ 2))
  have hp16 : 16 < p := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hp)
  have hpC : 8 * C ^ 2 < (p : ℝ) := lt_of_le_of_lt (le_max_right _ _) hp
  have hp0 : 0 < p := by omega
  exact (glmHessianBound_probability_lt_half p ⟨0, hp0⟩ C hC hp16 hpC).not_ge
    (hbound p hp0)

end AverageLMC
