import UnadjustedLangevin.LpDrift
import UnadjustedLangevin.InitialCoupling
import UnadjustedLangevin.Coupling
import UnadjustedLangevin.Recurrence

-- This project does not prescribe Mathlib copyright headers.
set_option linter.style.header false

/-! # Dalalyan's argument from a stationary integral reference

Unlike the more general perturbation theorem, this module derives its local
error from an integral equation for the actual lifted gradient. The remaining
inputs are explicit: a stationary reference, its score moment bound, and its
square-root noise increment bound. `UnadjustedLangevin/CanonicalULA.lean`
constructs these inputs and proves the unconditional Gaussian ULA theorem.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace ULA.Hilbert

open ULA

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ)

/-- ULA in a Hilbert-space presentation, using the actual-gradient L² update.
The reference moment bounds provide its effective dimension parameter. -/
def lpChain (U : H → ℝ) (h : ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L (gradient U)) (initial : Lp H 2 P)
    (noise : ℕ → Lp H 2 P) : ℕ → Lp H 2 P
  | 0 => initial
  | n + 1 => lpUlaUpdate P U h hLip (lpChain U h hLip initial noise n) (noise n)

omit [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
@[simp] theorem lpChain_succ (U : H → ℝ) (h : ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L (gradient U)) (initial : Lp H 2 P)
    (noise : ℕ → Lp H 2 P) (n : ℕ) :
    lpChain P U h hLip initial noise (n + 1) =
      lpUlaUpdate P U h hLip (lpChain P U h hLip initial noise n) (noise n) := rfl

/-- Exactly the continuous-reference inputs to Dalalyan's coupling argument.
All norms are L² norms, so `scoreBound` and `noiseBound` are moment bounds.
`noise` is not asserted to be Gaussian by this structure. -/
structure L2Reference (U : H → ℝ) (h : ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U)) (noise : ℕ → Lp (H) 2 P)
    (π : Measure (H)) where
  segment : ℕ → ℝ → Lp (H) 2 P
  increment : ℕ → ℝ → Lp (H) 2 P
  continuous : ∀ n, Continuous (segment n)
  join : ∀ n, segment n h = segment (n + 1) 0
  noiseEndpoint : ∀ n, increment n h = Real.sqrt (2 * h) • noise n
  stationary : ∀ n, P.map (segment n 0) = π
  integralEquation : ∀ n t, t ∈ Set.Icc 0 h →
    segment n t - segment n 0 =
      -(∫ s in 0..t, lpDrift P (gradient U) hLip (segment n s)) + increment n t
  scoreBound : ∀ n t, t ∈ Set.Icc 0 h →
    ‖lpDrift P (gradient U) hLip (segment n t)‖ ≤ Real.sqrt ((L : ℝ) * d)
  noiseBound : ∀ n t, t ∈ Set.Icc 0 h →
    ‖increment n t‖ ≤ Real.sqrt (2 * (d : ℝ)) * Real.sqrt t

/-- The complete error calculation from the displayed continuous-reference
inputs, including the local defect estimate and the transport-cost bridge. -/
theorem l2_reference_bound
    (U : H → ℝ) (h : ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (initial : Lp (H) 2 P) (noise : ℕ → Lp (H) 2 P) (π : Measure (H))
    (ref : L2Reference P d U h L hLip noise π)
    (hh : 0 ≤ h) (hstep : (L : ℝ) * h ≤ 2) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hcontract : ∀ X Y : Lp (H) 2 P,
      ‖(X - h • lpDrift P (gradient U) hLip X) -
        (Y - h • lpDrift P (gradient U) hLip Y)‖ ≤ q * ‖X - Y‖) (n : ℕ) :
    wasserstein2Real (P.map (lpChain P U h hLip initial noise n)) π ≤
      q ^ n * ‖initial - ref.segment 0 0‖ +
        ((33 / 20 : ℝ) * (L : ℝ) * h * Real.sqrt (h * d)) / (1 - q) := by
  let g := lpDrift P (gradient U) hLip
  let X := lpChain P U h hLip initial noise
  let b := (33 / 20 : ℝ) * (L : ℝ) * h * Real.sqrt (h * d)
  let D (k : ℕ) := localDefect g (ref.segment k) h
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hD (k : ℕ) : ‖D k‖ ≤ b :=
    lpDrift_localDefect_bound P U L h d hLip (ref.segment k) (ref.increment k)
      hh (by positivity) hstep (ref.scoreBound k) (ref.noiseBound k) (ref.integralEquation k)
  have hreference (k : ℕ) :
      ref.segment (k + 1) 0 = ref.segment k 0 - h • g (ref.segment k 0) +
        Real.sqrt (2 * h) • noise k - D k := by
    have hi : IntervalIntegrable (fun t ↦ g (ref.segment k t)) volume 0 h :=
      ((lpDrift_lipschitz P (gradient U) hLip).continuous.comp
        (ref.continuous k)).intervalIntegrable 0 h
    have he := localDefect_euler_identity g (ref.segment k) (ref.increment k) h hi
      (ref.integralEquation k h ⟨hh, le_rfl⟩)
    rw [ref.join k, ref.noiseEndpoint k] at he
    exact he
  have hrec (k : ℕ) :
      ‖X (k + 1) - ref.segment (k + 1) 0‖ ≤ q * ‖X k - ref.segment k 0‖ + b := by
    change ‖lpChain P U h hLip initial noise (k + 1) - ref.segment (k + 1) 0‖ ≤ _
    rw [lpChain_succ, hreference k]
    have hid :
        (X k - h • g (X k) + Real.sqrt (2 * h) • noise k) -
          (ref.segment k 0 - h • g (ref.segment k 0) +
            Real.sqrt (2 * h) • noise k - D k) =
        ((X k - h • g (X k)) - (ref.segment k 0 - h • g (ref.segment k 0))) + D k := by
      module
    change ‖(X k - h • g (X k) + Real.sqrt (2 * h) • noise k) - _‖ ≤ _
    rw [hid]
    exact (norm_add_le _ _).trans (add_le_add (hcontract (X k) (ref.segment k 0)) (hD k))
  have hw := wasserstein2_le_Lp_cost_real P (X n) (ref.segment n 0)
  rw [ref.stationary n] at hw
  exact hw.trans (affine_recurrence_bound (fun k ↦ ‖X k - ref.segment k 0‖)
    q b hq hq1 hb hrec n)

/-- Dalalyan's small-step branch with the corrected coefficient `1.65`,
derived from potential assumptions and the explicit integral reference. -/
theorem dalalyan_small_step_of_integral_reference
    (U : H → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (hLip : LipschitzWith L (gradient U)) (hm : 0 < m) (hmL : m ≤ (L : ℝ))
    (hh : 0 < h) (hsmall : h ≤ 2 / (m + (L : ℝ)))
    (initial : Lp (H) 2 P) (noise : ℕ → Lp (H) 2 P) (π : Measure (H))
    (ref : L2Reference P d U h L hLip noise π) (n : ℕ) :
    wasserstein2Real (P.map (lpChain P U h hLip initial noise n)) π ≤
      (1 - m * h) ^ n * ‖initial - ref.segment 0 0‖ +
        (33 / 20 : ℝ) * ((L : ℝ) / m) * Real.sqrt (h * d) := by
  have hpos : 0 < m + (L : ℝ) := by positivity
  have hproduct : h * (m + (L : ℝ)) ≤ 2 := (le_div_iff₀ hpos).mp hsmall
  have hmh : m * h ≤ 1 := by
    nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hmL)]
  have hstep : (L : ℝ) * h ≤ 2 := by nlinarith [mul_pos hm hh]
  have hq : 0 ≤ 1 - m * h := by linarith
  have hq1 : 1 - m * h < 1 := by nlinarith [mul_pos hm hh]
  have hb := l2_reference_bound P d U h L hLip initial noise π ref hh.le hstep
    (1 - m * h) hq hq1
    (lpDrift_gradient_contract P U m h L hdiff hsc hLip hmL hpos hh.le hsmall) n
  have hid :
      ((33 / 20 : ℝ) * (L : ℝ) * h * Real.sqrt (h * d)) / (1 - (1 - m * h)) =
        (33 / 20 : ℝ) * ((L : ℝ) / m) * Real.sqrt (h * d) := by
    field_simp
    ring
  rwa [hid] at hb

/-- Dalalyan's large-step branch; the denominator is positive under `hL < 2`. -/
theorem dalalyan_large_step_of_integral_reference
    (U : H → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (hLip : LipschitzWith L (gradient U)) (hm : 0 < m) (hmL : m ≤ (L : ℝ))
    (hh : 0 < h) (hlarge : 2 / (m + (L : ℝ)) ≤ h) (hstep : (L : ℝ) * h < 2)
    (initial : Lp (H) 2 P) (noise : ℕ → Lp (H) 2 P) (π : Measure (H))
    (ref : L2Reference P d U h L hLip noise π) (n : ℕ) :
    wasserstein2Real (P.map (lpChain P U h hLip initial noise n)) π ≤
      ((L : ℝ) * h - 1) ^ n * ‖initial - ref.segment 0 0‖ +
        ((33 / 20 : ℝ) * (L : ℝ) * h / (2 - (L : ℝ) * h)) * Real.sqrt (h * d) := by
  have hpos : 0 < m + (L : ℝ) := by positivity
  have hproduct : 2 ≤ h * (m + (L : ℝ)) := (div_le_iff₀ hpos).mp hlarge
  have hq : 0 ≤ (L : ℝ) * h - 1 := by
    nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hmL)]
  have hq1 : (L : ℝ) * h - 1 < 1 := by linarith
  have hb := l2_reference_bound P d U h L hLip initial noise π ref hh.le hstep.le
    ((L : ℝ) * h - 1) hq hq1
    (lpDrift_gradient_contract_large P U m h L hdiff hsc hLip hmL hpos hh.le hlarge) n
  have hid :
      ((33 / 20 : ℝ) * (L : ℝ) * h * Real.sqrt (h * d)) / (1 - ((L : ℝ) * h - 1)) =
        ((33 / 20 : ℝ) * (L : ℝ) * h / (2 - (L : ℝ) * h)) * Real.sqrt (h * d) := by
    ring
  rwa [hid] at hb

end ULA.Hilbert
