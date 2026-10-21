import UnadjustedLangevin.MALACoupling
import Mathlib.InformationTheory.KullbackLeibler.Basic

set_option linter.style.header false

/-! # ULA laws and their frozen-drift interpolation

`interpolationLaw U μ t` is the pushforward of `μ × N(0, I)` under
`(x, z) ↦ x - t ∇U(x) + √(2t) z`. For `t ≥ 0`, it is the frozen-drift
interpolation used in the one-step entropy argument. Its endpoints agree
with the actual independent-Gaussian ULA transition on measures.

These definitions and probability results require no convexity assumption.
They do not assert differentiability of the laws or entropy, nor derive an
entropy-production identity or a convergence bound from LSI alone.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ULA.LSI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E]

/-- The actual frozen-drift interpolation law, with an independent standard
Gaussian innovation. Only nonnegative `t` has the interpolation interpretation. -/
def interpolationLaw (U : E → ℝ) (μ : Measure E) (t : ℝ) : Measure E :=
  ULA.ulaLawStep U t μ

/-- The actual ULA laws obtained by iterating its independent-noise transition. -/
def ulaLaws (U : E → ℝ) (h : ℝ) (μ : Measure E) (k : ℕ) : Measure E :=
  (ULA.ulaLawStep U h)^[k] μ

/-- The frozen-drift interpolation starts at its supplied initial law.
No regularity of the potential is needed for this zero-time identity. -/
@[simp]
theorem interpolationLaw_zero (U : E → ℝ) (μ : Measure E) :
    interpolationLaw U μ 0 = μ := by
  simp [interpolationLaw, ULA.ulaLawStep, ULA.malaProposal]

@[simp]
theorem ulaLaws_zero (U : E → ℝ) (h : ℝ) (μ : Measure E) :
    ulaLaws U h μ 0 = μ := rfl

/-- Successive laws use precisely the original ULA transition. -/
theorem ulaLaws_succ (U : E → ℝ) (h : ℝ) (μ : Measure E) (k : ℕ) :
    ulaLaws U h μ (k + 1) = ULA.ulaLawStep U h (ulaLaws U h μ k) := by
  exact Function.iterate_succ_apply' (ULA.ulaLawStep U h) k μ

/-- At time `h`, the interpolation from the current ULA law is the next law. -/
theorem interpolationLaw_endpoint (U : E → ℝ) (h : ℝ) (μ : Measure E) (k : ℕ) :
    interpolationLaw U (ulaLaws U h μ k) h = ulaLaws U h μ (k + 1) := by
  exact (ulaLaws_succ U h μ k).symm

variable [BorelSpace E]

/-- The measurable frozen-drift Gaussian update preserves probability mass.
Lipschitzness supplies the measurability used by the pushforward calculation. -/
theorem interpolationLaw_isProbability (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U)) (t : ℝ) :
    IsProbabilityMeasure (interpolationLaw U μ t) := by
  constructor
  rw [interpolationLaw, ULA.ulaLawStep,
    Measure.map_apply (ULA.malaProposal_measurable U t L hLip) MeasurableSet.univ,
    Set.preimage_univ, measure_univ]

/-- Every iterated ULA law is a probability measure. -/
theorem ulaLaws_isProbability (U : E → ℝ) (h : ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U)) (k : ℕ) :
    IsProbabilityMeasure (ulaLaws U h μ k) := by
  induction k with
  | zero => exact inferInstanceAs (IsProbabilityMeasure μ)
  | succ k ih =>
    have := ih
    rw [ulaLaws_succ]
    exact interpolationLaw_isProbability U (ulaLaws U h μ k) L hLip h

/-- The real KL value for the actual ULA law. Any real entropy estimate must
retain a separate proof that the underlying extended KL divergence is finite. -/
def ulaEntropy (U : E → ℝ) (h : ℝ) (μ ν : Measure E) (k : ℕ) : ℝ :=
  (InformationTheory.klDiv (ulaLaws U h μ k) ν).toReal

omit [BorelSpace E] in
@[simp]
theorem ulaEntropy_zero (U : E → ℝ) (h : ℝ) (μ ν : Measure E) :
    ulaEntropy U h μ ν 0 = (InformationTheory.klDiv μ ν).toReal := rfl

end ULA.LSI
