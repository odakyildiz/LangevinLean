import UnadjustedLangevin.ULAStep
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-! # The actual noise-driven ULA chain

The noise is supplied explicitly. When it consists of independent standard
Gaussian vectors this definition is the unadjusted Langevin algorithm.
The algebraic coupling results apply to every common noise sequence.
-/

noncomputable section

open scoped NNReal

namespace ULA

/-- ULA iterates, with the initial condition and every noise vector visible. -/
def ulaChain {d : ℕ} (U : E d → ℝ) (h : ℝ) (initial : E d)
    (noise : ℕ → E d) : ℕ → E d
  | 0 => initial
  | n + 1 => ulaUpdate U h (ulaChain U h initial noise n) (noise n)

@[simp] theorem ulaChain_zero {d : ℕ} (U : E d → ℝ) (h : ℝ)
    (initial : E d) (noise : ℕ → E d) : ulaChain U h initial noise 0 = initial := rfl

@[simp] theorem ulaChain_succ {d : ℕ} (U : E d → ℝ) (h : ℝ)
    (initial : E d) (noise : ℕ → E d) (n : ℕ) :
    ulaChain U h initial noise (n + 1) =
      ulaUpdate U h (ulaChain U h initial noise n) (noise n) := rfl

/-- Measurable initial data and noises give measurable iterates. -/
theorem ulaChain_measurable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (U : E d → ℝ) (h : ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U))
    (initial : Ω → E d) (noise : ℕ → Ω → E d)
    (hinitial : Measurable initial) (hnoise : ∀ n, Measurable (noise n)) (n : ℕ) :
    Measurable (fun ω ↦ ulaChain U h (initial ω) (fun k ↦ noise k ω) n) := by
  have hg : Measurable (gradient U) := hLip.continuous.measurable
  induction n with
  | zero => exact hinitial
  | succ n ih =>
      simp only [ulaChain_succ, ulaUpdate]
      exact (ih.sub ((hg.comp ih).const_smul h)).add
        ((hnoise n).const_smul (Real.sqrt (2 * h)))

end ULA
