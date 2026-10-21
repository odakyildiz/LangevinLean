import UnadjustedLangevin.HilbertDalalyan

-- This project does not prescribe Mathlib copyright headers.
set_option linter.style.header false

/-! # Euclidean specialization of the shared Dalalyan theorem

The analytic proof is shared with arbitrary Hilbert-space presentations in
`ULA.Hilbert`. This module preserves the earlier `E d` theorem signatures
using specializations, without repeating the local-error or coupling proof.
The remaining inputs are explicit: a stationary reference, its score moment bound, and its
square-root noise increment bound. `UnadjustedLangevin/CanonicalULA.lean`
constructs these inputs and proves the unconditional Gaussian ULA theorem.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace ULA

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- Exactly the continuous-reference inputs to Dalalyan's coupling argument.
All norms are L² norms, so `scoreBound` and `noiseBound` are moment bounds.
`noise` is not asserted to be Gaussian by this structure. -/
abbrev L2Reference (U : E d → ℝ) (h : ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U)) (noise : ℕ → Lp (E d) 2 P)
    (π : Measure (E d)) :=
  Hilbert.L2Reference P d U h L hLip noise π

/-- The historical Euclidean recursion is the shared Hilbert-space recursion. -/
@[simp] theorem hilbert_lpChain_eq_lpUlaChain
    (U : E d → ℝ) (h : ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (initial : Lp (E d) 2 P) (noise : ℕ → Lp (E d) 2 P) (n : ℕ) :
    Hilbert.lpChain P U h hLip initial noise n = lpUlaChain P U h hLip initial noise n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Hilbert.lpChain_succ, lpUlaChain_succ, ih]

/-- The complete error calculation from the displayed continuous-reference
inputs, including the local defect estimate and the transport-cost bridge. -/
theorem l2_reference_bound
    (U : E d → ℝ) (h : ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (initial : Lp (E d) 2 P) (noise : ℕ → Lp (E d) 2 P) (π : Measure (E d))
    (ref : L2Reference P U h L hLip noise π)
    (hh : 0 ≤ h) (hstep : (L : ℝ) * h ≤ 2) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hcontract : ∀ X Y : Lp (E d) 2 P,
      ‖(X - h • lpDrift P (gradient U) hLip X) -
        (Y - h • lpDrift P (gradient U) hLip Y)‖ ≤ q * ‖X - Y‖) (n : ℕ) :
    wasserstein2Real (P.map (lpUlaChain P U h hLip initial noise n)) π ≤
      q ^ n * ‖initial - ref.segment 0 0‖ +
        ((33 / 20 : ℝ) * (L : ℝ) * h * Real.sqrt (h * d)) / (1 - q) := by
  simpa only [hilbert_lpChain_eq_lpUlaChain] using
    Hilbert.l2_reference_bound P d U h L hLip initial noise π ref
      hh hstep q hq hq1 hcontract n

/-- Dalalyan's small-step branch with the corrected coefficient `1.65`,
derived from potential assumptions and the explicit integral reference. -/
theorem dalalyan_small_step_of_integral_reference
    (U : E d → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (hLip : LipschitzWith L (gradient U)) (hm : 0 < m) (hmL : m ≤ (L : ℝ))
    (hh : 0 < h) (hsmall : h ≤ 2 / (m + (L : ℝ)))
    (initial : Lp (E d) 2 P) (noise : ℕ → Lp (E d) 2 P) (π : Measure (E d))
    (ref : L2Reference P U h L hLip noise π) (n : ℕ) :
    wasserstein2Real (P.map (lpUlaChain P U h hLip initial noise n)) π ≤
      (1 - m * h) ^ n * ‖initial - ref.segment 0 0‖ +
        (33 / 20 : ℝ) * ((L : ℝ) / m) * Real.sqrt (h * d) := by
  simpa only [hilbert_lpChain_eq_lpUlaChain] using
    Hilbert.dalalyan_small_step_of_integral_reference P d U m h L hdiff hsc hLip
      hm hmL hh hsmall initial noise π ref n

/-- Dalalyan's large-step branch; the denominator is positive under `hL < 2`. -/
theorem dalalyan_large_step_of_integral_reference
    (U : E d → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (hLip : LipschitzWith L (gradient U)) (hm : 0 < m) (hmL : m ≤ (L : ℝ))
    (hh : 0 < h) (hlarge : 2 / (m + (L : ℝ)) ≤ h) (hstep : (L : ℝ) * h < 2)
    (initial : Lp (E d) 2 P) (noise : ℕ → Lp (E d) 2 P) (π : Measure (E d))
    (ref : L2Reference P U h L hLip noise π) (n : ℕ) :
    wasserstein2Real (P.map (lpUlaChain P U h hLip initial noise n)) π ≤
      ((L : ℝ) * h - 1) ^ n * ‖initial - ref.segment 0 0‖ +
        ((33 / 20 : ℝ) * (L : ℝ) * h / (2 - (L : ℝ) * h)) * Real.sqrt (h * d) := by
  simpa only [hilbert_lpChain_eq_lpUlaChain] using
    Hilbert.dalalyan_large_step_of_integral_reference P d U m h L hdiff hsc hLip
      hm hmL hh hlarge hstep initial noise π ref n

end ULA
