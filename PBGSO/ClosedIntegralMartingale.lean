import PBGSO.ClosedDomainCuts

/-! # Martingale realization of every closed predictable-step integral -/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology
namespace PBGSO.FilteredBrownian
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

/-- Stopping a finite step clamps both Brownian endpoints. -/
theorem stoppedStep_clamp (a b t : ℝ≥0) (hab : a ≤ b)
    (A : Coefficient (Z := Z) Q D a) (ω : Ω) :
    stoppedStep Q D a b A t ω = ∑ i,
      (D.process i (min t b) ω - D.process i (min t a) ω) • A.value i ω := by
  by_cases hat : a ≤ t
  · simp only [stoppedStep, hat, ite_true, noiseStep,
      PredictableIsometry.stepSum, increment, min_eq_right hat]
  · have hta : t ≤ a := le_of_not_ge hat
    have htb : t ≤ b := hta.trans hab
    simp only [stoppedStep, hat, ite_false, min_eq_left hta, min_eq_left htb,
      sub_self, zero_smul, Finset.sum_const_zero]

theorem stoppedGridSum_columns_clamp (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (A : Coefficients (Z := Z) Q D τ) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    stoppedGridSum Q D τ A n t ω = ∑ i,
      BrownianGridIsometry.gridSum (D.process i) (fun k => min t (τ k))
        (fun k => (A k).value i) n ω := by
  simp only [stoppedGridSum, stoppedStep_clamp Q D _ _ t (hτ (Nat.le_succ _))]
  rw [Finset.sum_comm]
  rfl

/-- Exact pathwise refinement for stopped vector Brownian sums. -/
theorem stoppedGridSum_refine (τ υ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hυmono : Monotone υ) (d : ℕ) (hd : 0 < d) (hυ : ∀ k, υ (d * k) = τ k)
    (A : Coefficients (Z := Z) Q D τ) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    stoppedGridSum Q D υ (refine Q D τ υ hυmono d hd hυ A) (d * n) t ω =
      stoppedGridSum Q D τ A n t ω := by
  rw [stoppedGridSum_columns_clamp Q D υ hυmono,
    stoppedGridSum_columns_clamp Q D τ hτ]
  apply Finset.sum_congr rfl
  intro i _
  exact BrownianGridIsometry.gridSum_refine_mul (D.process i)
    (fun k => min t (τ k)) (fun k => min t (υ k)) d hd
    (fun k => congrArg (min t) (hυ k)) (fun k => (A k).value i) n ω

theorem stoppedIntegralLp_refine (τ υ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hυmono : Monotone υ) (d : ℕ) (hd : 0 < d) (hυ : ∀ k, υ (d * k) = τ k)
    (A : Coefficients (Z := Z) Q D τ) (n : ℕ) (t : ℝ≥0) :
    stoppedIntegralLp Q D υ hυmono (refine Q D τ υ hυmono d hd hυ A) (d * n) t =
      stoppedIntegralLp Q D τ hτ A n t := by
  apply Lp.ext
  filter_upwards [(stoppedGridSum_memLp Q D υ hυmono
    (refine Q D τ υ hυmono d hd hυ A) (d * n) t).coeFn_toLp,
    (stoppedGridSum_memLp Q D τ hτ A n t).coeFn_toLp] with ω h1 h2
  change (stoppedIntegralLp Q D υ hυmono _ _ t) ω = _ at h1
  change (stoppedIntegralLp Q D τ hτ _ _ t) ω = _ at h2
  rw [h1, h2]
  exact stoppedGridSum_refine Q D τ υ hτ hυmono d hd hυ A n t ω

/-- Stopped-output distance equals masked-input distance even when the two
actual finite sums use different compatible grid levels. -/
theorem stoppedIntegralLp_dist_cross (G : RefiningGrids) (m n : ℕ)
    (A : Coefficients (Z := Z) Q D (G.time m))
    (C : Coefficients (Z := Z) Q D (G.time n)) (t : ℝ≥0) :
    dist (stoppedIntegralLp Q D (G.time m) (G.monotone m) A (G.count m) t)
      (stochasticStep Q D (G.time n) (G.monotone n) C (G.count n)) =
    dist (timeCut Q (coefficientStep Q D (G.time m) A (G.count m)) 0 t)
      (coefficientStep Q D (G.time n) C (G.count n)) := by
  rcases le_total m n with hmn | hnm
  · obtain ⟨d, hd, hcount, htime⟩ := G.compatible m n hmn
    let R := refine Q D (G.time m) (G.time n) (G.monotone n) d hd htime A
    have hs := stoppedIntegralLp_refine Q D (G.time m) (G.time n)
      (G.monotone m) (G.monotone n) d hd htime A (G.count m) t
    have hc := coefficientStep_refine Q D (G.time m) (G.time n)
      (G.monotone n) d hd htime A (G.count m)
    rw [← hs, ← hc, ← hcount]
    exact stoppedIntegralLp_dist Q D (G.time n) (G.monotone n) R C (G.count n) t
  · obtain ⟨d, hd, hcount, htime⟩ := G.compatible n m hnm
    let R := refine Q D (G.time n) (G.time m) (G.monotone m) d hd htime C
    have hs := stochasticStep_refine Q D (G.time n) (G.time m)
      (G.monotone n) (G.monotone m) d hd htime C (G.count n)
    have hc := coefficientStep_refine Q D (G.time n) (G.time m)
      (G.monotone m) d hd htime C (G.count n)
    rw [← hs, ← hc, ← hcount]
    exact stoppedIntegralLp_dist Q D (G.time m) (G.monotone m) A R (G.count m) t

/-- The actual time-indexed integral of an arbitrary closed integrand. -/
def closedIntegral (T : ℝ≥0)
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) (t : ℝ≥0) : Lp Z 2 Q :=
  closedStepIntegral Q D (dyadicGrids T) (closedCutDomain Q D T U 0 t)

/-- Arbitrary actual finite-step approximations of U give the same stopped
stochastic-integral limit at every time. No noise-limit premise is needed. -/
theorem closedIntegral_stopped_tendsto (T : ℝ≥0)
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T))
    (A : ℕ → FiniteStepData (Z := Z) Q D (dyadicGrids T))
    (hA : Tendsto (fun n => finiteStepInput Q D (dyadicGrids T) (A n)) atTop (𝓝 U.val))
    (t : ℝ≥0) :
    Tendsto (fun n => stoppedIntegralLp Q D ((dyadicGrids T).time (A n).1)
      ((dyadicGrids T).monotone (A n).1) (A n).2 ((dyadicGrids T).count (A n).1) t)
      atTop (𝓝 (closedIntegral Q D T U t)) := by
  obtain ⟨C, hC⟩ := exists_finiteStep_approximation Q D (dyadicGrids T)
    (closedCutDomain Q D T U 0 t)
  have hcut := ((timeCut_lipschitz (I := I) (Z := Z) Q 0 t).continuous.tendsto U.val).comp hA
  have hdist := hcut.dist hC
  simp only [closedCutDomain, dist_self] at hdist
  have he := hdist.congr' (Eventually.of_forall (fun n =>
    (stoppedIntegralLp_dist_cross Q D (dyadicGrids T) (A n).1 (C n).1 (A n).2 (C n).2 t).symm))
  have hnoise := closedStepIntegral_tendsto Q D (dyadicGrids T) C
    (closedCutDomain Q D T U 0 t) hC
  exact hnoise.congr_dist (he.congr' (Eventually.of_forall (fun n => dist_comm _ _)))

/-- Every member of the literal closed predictable-step domain gives an
actual adapted martingale, derived from actual stopped finite sums. -/
theorem closedIntegral_martingale (T : ℝ≥0)
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) :
    Martingale (MartingaleL2Limit.representative Q D.filtration (closedIntegral Q D T U))
      D.filtration Q := by
  obtain ⟨A, hA⟩ := exists_finiteStep_approximation Q D (dyadicGrids T) U
  exact MartingaleL2Limit.martingale_representative Q D.filtration
    (fun n => stoppedGridSum Q D ((dyadicGrids T).time (A n).1) (A n).2
      ((dyadicGrids T).count (A n).1))
    (fun n => stoppedGridSum_martingale Q D _ ((dyadicGrids T).monotone (A n).1) _ _)
    (fun n t => stoppedGridSum_memLp Q D _ ((dyadicGrids T).monotone (A n).1) _ _ t)
    (closedIntegral Q D T U) (closedIntegral_stopped_tendsto Q D T U A hA)

theorem closedIntegral_representative_ae (T : ℝ≥0)
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) (t : ℝ≥0) :
    MartingaleL2Limit.representative Q D.filtration (closedIntegral Q D T U) t =ᵐ[Q]
      closedIntegral Q D T U t := by
  obtain ⟨A, hA⟩ := exists_finiteStep_approximation Q D (dyadicGrids T) U
  exact MartingaleL2Limit.representative_ae Q D.filtration
    (fun n => stoppedGridSum Q D ((dyadicGrids T).time (A n).1) (A n).2
      ((dyadicGrids T).count (A n).1))
    (fun n => stoppedGridSum_martingale Q D _ ((dyadicGrids T).monotone (A n).1) _ _)
    (fun n t => stoppedGridSum_memLp Q D _ ((dyadicGrids T).monotone (A n).1) _ _ t)
    (closedIntegral Q D T U) (closedIntegral_stopped_tendsto Q D T U A hA) t

theorem closedIntegral_representative_memLp (T : ℝ≥0)
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) (t : ℝ≥0) :
    MemLp (MartingaleL2Limit.representative Q D.filtration (closedIntegral Q D T U) t) 2 Q :=
  (memLp_congr_ae (closedIntegral_representative_ae Q D T U t)).mpr (Lp.memLp _)

end PBGSO.FilteredBrownian
