import WassersteinMixing.ActualComparison

/-! # Score increments and defects of the constructed stationary diffusion

The primitive increment estimate is derived from the actual integral equation,
the Gibbs score moment, and the Brownian noise second moment.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal

namespace WassersteinMixing

section Reference
variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  (d : ℕ) (V : H → ℝ) (h : ℝ) (β : ℝ≥0)
  (hLip : LipschitzWith β (gradient V))
  (noise : ℕ → Lp H 2 Q) (π : Measure H)
  (R : ULA.Hilbert.L2Reference Q d V h β hLip noise π)

/-- The actual lifted score difference over an interior diffusion segment. -/
def referenceScoreIncrement (n : ℕ) (s : ℝ) : Lp H 2 Q :=
  ULA.lpDrift Q (gradient V) hLip (R.segment n 0) -
    ULA.lpDrift Q (gradient V) hLip (R.segment n s)

omit [BorelSpace H] [SecondCountableTopology H] in
/-- The SDE and its actual Brownian moment imply the displacement polynomial. -/
theorem reference_displacement_energy (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 h) :
    ‖R.segment n s - R.segment n 0‖ ^ 2 ≤
      (d : ℝ) * (2 * s ^ 2 * (β : ℝ) + 4 * s) := by
  have hinc := ULA.integral_equation_increment_bound
    (ULA.lpDrift Q (gradient V) hLip) (R.segment n) (R.increment n) h
    (Real.sqrt ((β : ℝ) * d)) (Real.sqrt (2 * (d : ℝ))) (hs.1.trans hs.2)
    (R.scoreBound n) (R.noiseBound n) (R.integralEquation n) hs
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hinc 2
  have hsq₁ := Real.sq_sqrt (mul_nonneg β.coe_nonneg (Nat.cast_nonneg d))
  have hsq₂ := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * (d : ℝ))
  have hsqs := Real.sq_sqrt hs.1
  have htwo := sq_nonneg (s * Real.sqrt ((β : ℝ) * d) -
    Real.sqrt (2 * (d : ℝ)) * Real.sqrt s)
  nlinarith

omit [BorelSpace H] [SecondCountableTopology H] in
/-- The true score increments satisfy the paper's polynomial estimate. -/
theorem reference_score_increment_polynomial (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 h) :
    ‖referenceScoreIncrement Q d V h β hLip noise π R n s‖ ^ 2 ≤
      (β : ℝ) ^ 2 * d * (2 * s ^ 2 * (β : ℝ) + 4 * s) := by
  have hl := (ULA.lpDrift_lipschitz Q (gradient V) hLip).norm_sub_le
    (R.segment n 0) (R.segment n s)
  rw [norm_sub_rev (R.segment n 0)] at hl
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hl 2
  rw [mul_pow] at hsquare
  have hdisp := reference_displacement_energy Q d V h β hLip noise π R n s hs
  have hm := mul_le_mul_of_nonneg_left hdisp (sq_nonneg (β : ℝ))
  exact hsquare.trans (by nlinarith)

/-- The manuscript's constant `6` is a consequence of stable step size. -/
theorem reference_score_increment_energy (hstep : h * (β : ℝ) ≤ 1)
    (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 h) :
    ‖referenceScoreIncrement Q d V h β hLip noise π R n s‖ ^ 2 ≤
      6 * s * (β : ℝ) ^ 2 * d := by
  have hp := reference_score_increment_polynomial Q d V h β hLip noise π R n s hs
  have hsimp := displacement_polynomial_le s h β hs.1 hs.2 β.coe_nonneg hstep
  have hm := mul_le_mul_of_nonneg_left hsimp
    (mul_nonneg (sq_nonneg (β : ℝ)) (Nat.cast_nonneg d))
  nlinarith

omit [BorelSpace H] [SecondCountableTopology H] in
/-- The true score-increment curve is continuous in the actual `L²` space. -/
theorem referenceScoreIncrement_continuous (n : ℕ) :
    Continuous (referenceScoreIncrement Q d V h β hLip noise π R n) := by
  exact continuous_const.sub ((ULA.lpDrift_lipschitz Q (gradient V) hLip).continuous.comp
    (R.continuous n))

end Reference

section Actual
variable (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V)

/-- The true gradient of the actual stationary reference. -/
def actualScore (n : ℕ) : Lp (E P.dimension) 2 (actualProbability P V) := by
  letI := actualProbability_isProbability P V hV
  exact ULA.lpDrift (actualProbability P V) (gradient V) hV.gradientLipschitz
    (actualReference P V hV n)

/-- The true score increment, with the sign appearing in the manuscript. -/
def actualScoreIncrement (n : ℕ) (s : ℝ) : Lp (E P.dimension) 2 (actualProbability P V) := by
  letI := actualProbability_isProbability P V hV
  exact actualScore P V hV n -
    ULA.lpDrift (actualProbability P V) (gradient V) hV.gradientLipschitz
      (actualSegment P V hV n s)

/-- The local Euler error is the genuine integral of the true score increment. -/
def actualDefect (n : ℕ) : Lp (E P.dimension) 2 (actualProbability P V) :=
  stationaryLocalDefect (actualScoreIncrement P V hV n) P.step

/-- The source score-energy bound is proved from Gibbs stationarity. -/
theorem actualScore_energy (n : ℕ) :
    ‖actualScore P V hV n‖ ^ 2 ≤ P.beta * P.dimension := by
  let := actualProbability_isProbability P V hV
  have hb := ULA.lpDrift_norm_le_of_strongConvex_gibbs_law (actualProbability P V) V
    P.alpha ⟨P.beta, P.beta_pos.le⟩ P.alpha_pos
    (hV.regularity.differentiable (by norm_num)) hV.strongConvexity hV.gradientLipschitz
    (actualReference P V hV n) (actualReference_stationary P V hV n)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  change ‖actualScore P V hV n‖ ^ 2 ≤
    Real.sqrt (P.beta * (Module.finrank ℝ (E P.dimension) : ℝ)) ^ 2 at hs
  have hp : 0 ≤ P.beta * (P.dimension : ℝ) := mul_nonneg P.beta_pos.le (Nat.cast_nonneg _)
  simpa only [E, finrank_euclideanSpace, Fintype.card_fin, NNReal.coe_mk,
    Real.sq_sqrt hp] using hs

/-- The paper's primitive increment constant is derived for this actual SDE. -/
theorem actualScoreIncrement_energy (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 P.step) :
    ‖actualScoreIncrement P V hV n s‖ ^ 2 ≤ 6 * s * P.beta ^ 2 * P.dimension := by
  let := actualProbability_isProbability P V hV
  have hb := reference_score_increment_energy (actualProbability P V)
    (Fintype.card (Fin P.dimension)) V P.step ⟨P.beta, P.beta_pos.le⟩
    hV.gradientLipschitz (actualNoise P V hV) (ULA.gibbsMeasure V)
    (actualReferenceData P V hV) P.step_beta_le n s hs
  change ‖actualScoreIncrement P V hV n s‖ ^ 2 ≤
    6 * s * P.beta ^ 2 * (Fintype.card (Fin P.dimension) : ℝ) at hb
  simpa only [Fintype.card_fin] using hb

/-- The actual time-increment curve is continuous. -/
theorem actualScoreIncrement_continuous (n : ℕ) : Continuous (actualScoreIncrement P V hV n) := by
  let := actualProbability_isProbability P V hV
  exact referenceScoreIncrement_continuous (actualProbability P V)
    (Fintype.card (Fin P.dimension)) V P.step ⟨P.beta, P.beta_pos.le⟩
    hV.gradientLipschitz (actualNoise P V hV) (ULA.gibbsMeasure V)
    (actualReferenceData P V hV) n

/-- Square integrability in time is derived from continuity on the compact segment. -/
theorem actualScoreIncrement_memLp (n : ℕ) :
    MemLp (actualScoreIncrement P V hV n) 2 (volume.restrict (Ioc 0 P.step)) := by
  have hc := actualScoreIncrement_continuous P V hV n
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  apply MemLp.of_bound hc.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact hC s ⟨hs.1.le, hs.2⟩

/-- The true endpoint increment is the difference of the actual grid scores. -/
theorem actualScoreIncrement_endpoint (n : ℕ) :
    actualScoreIncrement P V hV n P.step = actualScore P V hV n - actualScore P V hV (n + 1) := by
  let := actualProbability_isProbability P V hV
  have hj := (actualReferenceData P V hV).join n
  unfold actualScoreIncrement actualScore actualReference actualSegment
  rw [hj]

/-- The actual local error has the exact manuscript energy constant `3`. -/
theorem actualDefect_energy (n : ℕ) :
    ‖actualDefect P V hV n‖ ^ 2 ≤ 3 * P.step ^ 3 * P.beta ^ 2 * P.dimension :=
  stationaryLocalDefect_energy_le (actualScoreIncrement P V hV n) P.step P.beta P.dimension
    P.step_pos.le (actualScoreIncrement_memLp P V hV n)
    (fun s hs ↦ actualScoreIncrement_energy P V hV n s ⟨hs.1.le, hs.2⟩)

/-- Exact evaluation of the true defect integral against the frozen score. -/
theorem actualDefect_eq (n : ℕ) :
    letI := actualProbability_isProbability P V hV
    actualDefect P V hV n = P.step • actualScore P V hV n -
      ∫ s in (0 : ℝ)..P.step,
        ULA.lpDrift (actualProbability P V) (gradient V) hV.gradientLipschitz
          (actualSegment P V hV n s) := by
  let := actualProbability_isProbability P V hV
  have hi : IntervalIntegrable (fun s ↦ ULA.lpDrift (actualProbability P V) (gradient V)
      hV.gradientLipschitz (actualSegment P V hV n s)) volume 0 P.step :=
    ((ULA.lpDrift_lipschitz _ _ hV.gradientLipschitz).continuous.comp
      ((actualReferenceData P V hV).continuous n)).intervalIntegrable _ _
  unfold actualDefect stationaryLocalDefect actualScoreIncrement
  rw [intervalIntegral.integral_sub intervalIntegrable_const hi,
    intervalIntegral.integral_const]
  simp

/-- The actual reference endpoint has the Euler update plus its true local
error, driven by exactly the common Brownian increment. -/
theorem actualReference_step (n : ℕ) :
    actualReference P V hV (n + 1) = actualReference P V hV n -
      P.step • actualScore P V hV n + Real.sqrt (2 * P.step) • actualNoise P V hV n +
        actualDefect P V hV n := by
  let := actualProbability_isProbability P V hV
  have he := (actualReferenceData P V hV).integralEquation n P.step ⟨P.step_pos.le, le_rfl⟩
  rw [(actualReferenceData P V hV).join n, (actualReferenceData P V hV).noiseEndpoint n] at he
  change actualReference P V hV (n + 1) - actualReference P V hV n =
    -(∫ s in (0 : ℝ)..P.step, ULA.lpDrift (actualProbability P V) (gradient V)
      hV.gradientLipschitz (actualSegment P V hV n s)) +
      Real.sqrt (2 * P.step) • actualNoise P V hV n at he
  rw [actualDefect_eq P V hV n]
  rw [sub_eq_iff_eq_add] at he
  rw [he]
  module

/-- The exact synchronous error equation is derived from both actual updates.
Its drift difference is the true gradient difference, not a supplied recurrence. -/
theorem actual_error_step (n : ℕ) :
    letI := actualProbability_isProbability P V hV
    actualReference P V hV (n + 1) - actualChain P V hV (n + 1) =
      (actualReference P V hV n - actualChain P V hV n) -
        P.step • (actualScore P V hV n -
          ULA.lpDrift (actualProbability P V) (gradient V) hV.gradientLipschitz
            (actualChain P V hV n)) + actualDefect P V hV n := by
  let := actualProbability_isProbability P V hV
  have hc : actualChain P V hV (n + 1) = actualChain P V hV n -
      P.step • ULA.lpDrift (actualProbability P V) (gradient V) hV.gradientLipschitz
        (actualChain P V hV n) + Real.sqrt (2 * P.step) • actualNoise P V hV n := rfl
  rw [actualReference_step P V hV n, hc]
  module

end Actual

end WassersteinMixing
