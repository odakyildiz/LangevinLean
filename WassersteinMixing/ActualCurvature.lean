import WassersteinMixing.ActualLocalError
import WassersteinMixing.CurvatureLp

/-! # The actual synchronous error with its genuine averaged Hessian

Every numerical local-error and curvature field is derived from the original
potential and the actual stationary Brownian/Gaussian ULA construction.
-/

noncomputable section
open MeasureTheory

namespace WassersteinMixing

variable (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V)

/-- The literal random averaged Hessian between the two actual current states. -/
def actualCurvature (n : ℕ) :
    Lp (E P.dimension) 2 (actualProbability P V) →L[ℝ]
      Lp (E P.dimension) 2 (actualProbability P V) :=
  randomCurvature (actualProbability P V) P V hV
    (actualReference P V hV n) (actualChain P V hV n)

/-- The actual error recursion, now with the genuinely constructed Hessian. -/
theorem actual_curvature_error_step (n : ℕ) :
    actualReference P V hV (n + 1) - actualChain P V hV (n + 1) =
      (actualReference P V hV n - actualChain P V hV n) -
        P.step • actualCurvature P V hV n (actualReference P V hV n - actualChain P V hV n) +
          actualDefect P V hV n := by
  let := actualProbability_isProbability P V hV
  have hs := randomCurvature_secant (actualProbability P V) P V hV
    (actualReference P V hV n) (actualChain P V hV n)
  change actualCurvature P V hV n (actualReference P V hV n - actualChain P V hV n) =
    actualScore P V hV n - ULA.lpDrift (actualProbability P V) (gradient V)
      hV.gradientLipschitz (actualChain P V hV n) at hs
  rw [hs]
  exact actual_error_step P V hV n

theorem actualCurvature_symmetric (n : ℕ)
    (u v : Lp (E P.dimension) 2 (actualProbability P V)) :
    inner ℝ (actualCurvature P V hV n u) v = inner ℝ u (actualCurvature P V hV n v) :=
  randomCurvature_symmetric _ P V hV _ _ u v

theorem actualCurvature_lower (n : ℕ) (u : Lp (E P.dimension) 2 (actualProbability P V)) :
    P.alpha * ‖u‖ ^ 2 ≤ inner ℝ u (actualCurvature P V hV n u) :=
  randomCurvature_lower _ P V hV _ _ u

theorem actualCurvature_upper (n : ℕ) (u : Lp (E P.dimension) 2 (actualProbability P V)) :
    inner ℝ u (actualCurvature P V hV n u) ≤ P.beta * ‖u‖ ^ 2 :=
  randomCurvature_upper _ P V hV _ _ u

/-- Measurability of the actual two current states suffices for preservation
of the same past by the genuine random Hessian operator. -/
theorem actualCurvature_adapted (m : MeasurableSpace (ActualSpace P)) (n : ℕ)
    (u : Lp (E P.dimension) 2 (actualProbability P V))
    (hX : AEStronglyMeasurable[m] (actualReference P V hV n) (actualProbability P V))
    (hY : AEStronglyMeasurable[m] (actualChain P V hV n) (actualProbability P V))
    (hu : AEStronglyMeasurable[m] u (actualProbability P V)) :
    AEStronglyMeasurable[m] (actualCurvature P V hV n u) (actualProbability P V) := by
  exact randomCurvature_adapted (m0 := Prod.instMeasurableSpace) (actualProbability P V) P V hV m
    _ _ _ hX hY hu

end WassersteinMixing
