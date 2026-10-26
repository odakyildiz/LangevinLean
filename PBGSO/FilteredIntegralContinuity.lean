import PBGSO.FilteredIntegralMartingale

/-! # L² time continuity of the constructed vector Brownian integral -/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology RealInnerProductSpace InnerProductSpace
namespace PBGSO.FilteredBrownian
open PBGSO.QuadraticMartingale
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

def continuousIntegral (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q) (t : ℝ≥0) : Lp Z 2 Q :=
  stochasticIntegral Q D (dyadicGrids T) (continuousCutDomain Q D T u hu hU t)

theorem weightedPairing_id (X : Lp Z 2 Q) :
    weightedPairing Q (ContinuousLinearMap.id ℝ Z) X X = ‖X‖ ^ 2 := by
  rw [weightedPairing_apply]
  have he : (ContinuousLinearMap.id ℝ Z).compLpL 2 Q X = X := by
    apply Lp.ext
    exact ((ContinuousLinearMap.id ℝ Z).coeFn_compLpL X).trans (ae_of_all Q (fun _ => rfl))
  rw [he, real_inner_self_eq_norm_sq]

theorem columnWeighted_id (x : ColumnHilbert (I := I) (Z := Z) Q) :
    (∑ i, weightedPairing Q (ContinuousLinearMap.id ℝ Z) (x.ofLp i) (x.ofLp i)) = ‖x‖ ^ 2 := by
  simp only [weightedPairing_id, PiLp.norm_sq_eq_of_L2]

/-- The exact increment norm equals the actual coefficient time-energy,
including times beyond the stopping horizon. -/
theorem continuousIntegral_increment_norm_sq (T : ℝ≥0)
    (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q) (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q)
    (s t : ℝ≥0) (hst : s ≤ t) :
    ‖continuousIntegral Q D T u hu hU t - continuousIntegral Q D T u hu hU s‖ ^ 2 =
      ∫ r in Ioc (s : ℝ) t, ‖(continuousDomain Q D T u hu hU).val r‖ ^ 2 := by
  rw [← weightedPairing_id]
  rw [continuousIntegral, continuousIntegral, stochasticIntegral_increment_isometry Q D
    (ContinuousLinearMap.id ℝ Z) (fun _ _ => rfl) (dyadicGrids T)
    (continuousDomain Q D T u hu hU).val s t s.coe_nonneg (by exact_mod_cast hst)
    _ _ (continuousCutDomain_eq_timeCut Q D T u hu hU s)
    (continuousCutDomain_eq_timeCut Q D T u hu hU t)]
  simp only [columnWeighted_id]

/-- A bound on the actual diffusion columns yields the Brownian square-root
increment modulus with its explicit finite-horizon constant. -/
theorem continuousIntegral_increment_bound (T : ℝ≥0)
    (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q) (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q)
    (P : ℝ) (_hP0 : 0 ≤ P) (hP : ∀ r ∈ Icc 0 (T : ℝ), ‖u r‖ ≤ P)
    (s t : ℝ≥0) (hst : s ≤ t) :
    ‖continuousIntegral Q D T u hu hU t - continuousIntegral Q D T u hu hU s‖ ^ 2 ≤
      P ^ 2 * ((t : ℝ) - s) := by
  rw [continuousIntegral_increment_norm_sq Q D T u hu hU s t hst]
  let U := (continuousDomain Q D T u hu hU).val
  have hbound : ∀ᵐ r ∂(volume : Measure ℝ), ‖U r‖ ^ 2 ≤ P ^ 2 := by
    filter_upwards [continuousDomain_coe Q D T u hu hU] with r hr
    change ‖(continuousDomain Q D T u hu hU).val r‖ ^ 2 ≤ _
    rw [hr]
    by_cases hR : r ∈ Ioc 0 (T : ℝ)
    · rw [Set.indicator_of_mem hR]
      exact pow_le_pow_left₀ (norm_nonneg _) (hP r ⟨hR.1.le, hR.2⟩) 2
    · simp only [Set.indicator_of_notMem hR, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
      positivity
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.memLp U).aestronglyMeasurable).mp (Lp.memLp U)
  have hic : Integrable (fun _ : ℝ => P ^ 2) ((volume : Measure ℝ).restrict (Ioc (s : ℝ) t)) :=
    integrable_const _
  have hb := integral_mono_ae hi.integrableOn hic (ae_restrict_of_ae hbound)
  refine hb.trans_eq ?_
  rw [setIntegral_const, Measure.real, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (by exact_mod_cast hst)), smul_eq_mul]
  ring



/-- Global stopped-process modulus in the actual L² norm. -/
theorem continuousIntegral_norm_sq_le_dist (T : ℝ≥0)
    (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q) (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q)
    (P : ℝ) (hP0 : 0 ≤ P) (hP : ∀ r ∈ Icc 0 (T : ℝ), ‖u r‖ ≤ P) (s t : ℝ≥0) :
    ‖continuousIntegral Q D T u hu hU t - continuousIntegral Q D T u hu hU s‖ ^ 2 ≤
      P ^ 2 * dist t s := by
  rcases le_total s t with hst | hts
  · rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hst))]
    exact continuousIntegral_increment_bound Q D T u hu hU P hP0 hP s t hst
  · rw [norm_sub_rev, dist_comm, NNReal.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hts))]
    exact continuousIntegral_increment_bound Q D T u hu hU P hP0 hP t s hts

/-- Explicit Brownian square-root increment estimate for the actual
constructed stochastic integral. -/
theorem continuousIntegral_holder_bound (T : ℝ≥0)
    (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q) (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q)
    (P : ℝ) (hP0 : 0 ≤ P) (hP : ∀ r ∈ Icc 0 (T : ℝ), ‖u r‖ ≤ P) (s t : ℝ≥0) :
    ‖continuousIntegral Q D T u hu hU t - continuousIntegral Q D T u hu hU s‖ ≤
      P * Real.sqrt (dist t s) := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hP0 (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (dist_nonneg : 0 ≤ dist t s)]
  exact continuousIntegral_norm_sq_le_dist Q D T u hu hU P hP0 hP s t

/-- Compactness supplies the diffusion bound, so time continuity is a
conclusion of the constructed integral rather than an extra noise premise. -/
theorem continuousIntegral_continuous (T : ℝ≥0)
    (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q) (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q) :
    Continuous (continuousIntegral Q D T u hu hU) := by
  obtain ⟨P, hP0, hP⟩ := TimeGridContinuity.exists_horizon_bound T u hu
  apply continuous_iff_continuousAt.mpr
  intro t
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hp : 0 < P ^ 2 + 1 := by positivity
  refine ⟨ε ^ 2 / (P ^ 2 + 1), by positivity, ?_⟩
  intro s hs
  rw [dist_eq_norm]
  apply (sq_lt_sq₀ (norm_nonneg _) hε.le).mp
  have hb := continuousIntegral_norm_sq_le_dist Q D T u hu hU P hP0 hP t s
  have hd : dist s t * (P ^ 2 + 1) < ε ^ 2 := (lt_div_iff₀ hp).mp hs
  nlinarith [dist_nonneg (x := s) (y := t)]

end PBGSO.FilteredBrownian
