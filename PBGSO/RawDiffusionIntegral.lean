import PBGSO.ProductLpSections
import PBGSO.PredictableCurveIntegral
import PBGSO.ConstructedContinuousIntegral

/-! # Actual stochastic integration of raw adapted diffusion fields
Jointly strongly measurable finite-column fields with finite expected
integrated square norm are converted into actual time-L² columns. The
computed integral, martingale, continuous modification, and exact weighted
increment identity are conclusions; no L²-valued coefficient curve,
coefficient approximation, stochastic isometry, or path version is supplied.
Spatial measure separability is explicit.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology RealInnerProductSpace InnerProductSpace
namespace PBGSO.FilteredBrownian
open PBGSO.ProductLpSections PBGSO.QuadraticMartingale
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

/-- Literal L² coefficient sections of the original raw diffusion columns. -/
def rawDiffusionCurve (σ : I → ℝ → Ω → Z) : ℝ → ColumnHilbert (I := I) (Z := Z) Q :=
  columnSections Q σ

theorem rawDiffusionCurve_square (T : ℝ≥0) (σ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (h2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) :
    MemLp (rawDiffusionCurve Q σ) 2 (volume.restrict (Ioc 0 (T : ℝ))) :=
  columnSections_memLp (volume.restrict (Ioc 0 (T : ℝ))) Q σ hσ h2

/-- Raw adaptation is preserved at every deterministic time, including any
non-L² section where the literal construction chooses the zero variable. -/
theorem rawDiffusionCurve_adapted (σ : I → ℝ → Ω → Z)
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) Q)
    (t : ℝ≥0) (i : I) :
    AEStronglyMeasurable[D.filtration t] ((rawDiffusionCurve Q σ t).ofLp i) Q :=
  sectionLp_adapted Q (D.filtration t) (σ i) t (hA t i)

/-- The computed stochastic integral of the original raw field. -/
def rawDiffusionIntegral (T : ℝ≥0) (σ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (h2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) Q) :
    ℝ≥0 → Lp Z 2 Q :=
  predictableCurveIntegral Q D T (rawDiffusionCurve Q σ)
    (rawDiffusionCurve_square Q T σ hσ h2) (rawDiffusionCurve_adapted Q D σ hA)

theorem rawDiffusionIntegral_continuous (T : ℝ≥0) (σ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (h2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) Q) :
    Continuous (rawDiffusionIntegral Q D T σ hσ h2 hA) :=
  predictableCurveIntegral_continuous Q D T _ _ _

@[simp] theorem rawDiffusionIntegral_zero (T : ℝ≥0) (σ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (h2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) Q) :
    rawDiffusionIntegral Q D T σ hσ h2 hA 0 = 0 :=
  predictableCurveIntegral_zero Q D T _ _ _

/-- An actual martingale representative of the original raw-field integral. -/
theorem rawDiffusionIntegral_martingale (T : ℝ≥0) (σ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (h2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) Q) :
    Martingale (MartingaleL2Limit.representative Q D.filtration
      (rawDiffusionIntegral Q D T σ hσ h2 hA)) D.filtration Q :=
  predictableCurveIntegral_martingale Q D T _ _ _

/-- The weighted raw diffusion energy is product-integrable, derived from
literal square-norm integrability of its finite columns. -/
theorem rawDiffusion_weighted_integrable (T : ℝ≥0) (σ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (h2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) (W : Z →L[ℝ] Z) :
    Integrable (fun p : ℝ × Ω => ∑ i, ⟪σ i p.1 p.2, W (σ i p.1 p.2)⟫_ℝ)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := by
  apply integrable_finsetSum
  intro i _
  apply ((h2 i).const_mul ‖W‖).mono'
    ((hσ i).inner (W.continuous.comp_stronglyMeasurable (hσ i))).aestronglyMeasurable
  apply Eventually.of_forall
  intro p
  calc
    ‖⟪σ i p.1 p.2, W (σ i p.1 p.2)⟫_ℝ‖ ≤
        ‖σ i p.1 p.2‖ * ‖W (σ i p.1 p.2)‖ := norm_inner_le_norm _ _
    _ ≤ ‖σ i p.1 p.2‖ * (‖W‖ * ‖σ i p.1 p.2‖) :=
      mul_le_mul_of_nonneg_left (W.le_opNorm _) (norm_nonneg _)
    _ = ‖W‖ * ‖σ i p.1 p.2‖ ^ 2 := by ring

/-- The canonical martingale representative realizes the computed integral
at every deterministic time. -/
theorem rawDiffusionIntegral_representative_ae (T : ℝ≥0) (σ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (h2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) Q) (t : ℝ≥0) :
    MartingaleL2Limit.representative Q D.filtration
      (rawDiffusionIntegral Q D T σ hσ h2 hA) t =ᵐ[Q]
      rawDiffusionIntegral Q D T σ hσ h2 hA t :=
  predictableCurveIntegral_representative_ae Q D T _ _ _ t

/-- The actual representative is L² at every deterministic time. -/
theorem rawDiffusionIntegral_representative_memLp (T : ℝ≥0) (σ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (h2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) Q) (t : ℝ≥0) :
    MemLp (MartingaleL2Limit.representative Q D.filtration
      (rawDiffusionIntegral Q D T σ hσ h2 hA) t) 2 Q :=
  predictableCurveIntegral_representative_memLp Q D T _ _ _ t

/-- The exact weighted increment identity for the original raw diffusion,
with the spatial expectation and finite column sum written literally. -/
theorem rawDiffusionIntegral_increment_isometry (T : ℝ≥0) (σ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (h2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) Q)
    (W : Z →L[ℝ] Z) (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (s t : ℝ≥0) (hst : s ≤ t) (ht : t ≤ T) :
    weightedPairing Q W
      (rawDiffusionIntegral Q D T σ hσ h2 hA t - rawDiffusionIntegral Q D T σ hσ h2 hA s)
      (rawDiffusionIntegral Q D T σ hσ h2 hA t - rawDiffusionIntegral Q D T σ hσ h2 hA s) =
      ∫ r in Ioc (s : ℝ) t, ∫ ω, ∑ i, ⟪σ i r ω, W (σ i r ω)⟫_ℝ ∂Q := by
  simp only [rawDiffusionIntegral]
  rw [predictableCurveIntegral_increment_isometry Q D T _ _ _ W hW s t hst ht]
  apply integral_congr_ae
  have hle : (volume : Measure ℝ).restrict (Ioc (s : ℝ) (t : ℝ)) ≤
      volume.restrict (Ioc 0 (T : ℝ)) :=
    Measure.restrict_mono_set _ (fun r hr =>
      ⟨lt_of_le_of_lt s.coe_nonneg hr.1, hr.2.trans (by exact_mod_cast ht)⟩)
  have hsec := (columnSections_ae (volume.restrict (Ioc 0 (T : ℝ))) Q σ hσ h2).filter_mono
    (ae_mono hle)
  filter_upwards [hsec] with r hr
  have hint (i : I) : Integrable (fun ω => ⟪σ i r ω, W (σ i r ω)⟫_ℝ) Q := by
    apply (lp_weighted_pairing_integrable Q W
      ((rawDiffusionCurve Q σ r).ofLp i) ((rawDiffusionCurve Q σ r).ofLp i)).congr
    filter_upwards [hr i] with ω hω
    simp only [rawDiffusionCurve]
    rw [hω]
  rw [integral_finsetSum _ (fun i _ => hint i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [weightedPairing_apply, lp_weighted_pairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [hr i] with ω hω
  simp only [rawDiffusionCurve]
  rw [hω]

/-- Exact unweighted increments of the original raw-field integral. -/
theorem rawDiffusionIntegral_increment_norm_sq (T : ℝ≥0) (σ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (h2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) Q)
    (s t : ℝ≥0) (hst : s ≤ t) (ht : t ≤ T) :
    ‖rawDiffusionIntegral Q D T σ hσ h2 hA t - rawDiffusionIntegral Q D T σ hσ h2 hA s‖ ^ 2 =
      ∫ r in Ioc (s : ℝ) t, ∫ ω, ∑ i, ‖σ i r ω‖ ^ 2 ∂Q := by
  simpa only [weightedPairing_id, ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq] using
    rawDiffusionIntegral_increment_isometry Q D T σ hσ h2 hA
      (ContinuousLinearMap.id ℝ Z) (fun _ _ => rfl) s t hst ht

/-- Exact terminal energy, with the zero initial stochastic integral derived. -/
theorem rawDiffusionIntegral_norm_sq (T : ℝ≥0) (σ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (h2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) Q)
    (t : ℝ≥0) (ht : t ≤ T) :
    ‖rawDiffusionIntegral Q D T σ hσ h2 hA t‖ ^ 2 =
      ∫ r in Ioc 0 (t : ℝ), ∫ ω, ∑ i, ‖σ i r ω‖ ^ 2 ∂Q := by
  simpa only [rawDiffusionIntegral_zero, sub_zero, NNReal.coe_zero] using
    rawDiffusionIntegral_increment_norm_sq Q D T σ hσ h2 hA 0 t zero_le ht

/-- The original raw-field integral has a continuous adapted martingale
version, constructed internally, with no raw Brownian path premise. -/
theorem rawDiffusionIntegral_exists_continuous_martingale
    (T : ℝ≥0) (σ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (h2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) Q) :
    ∃ M : ℝ≥0 → Ω → Z, Martingale M D.filtration Q ∧
      (∀ᵐ ω ∂Q, Continuous (fun t => M t ω)) ∧
      ∀ t, M t =ᵐ[Q] rawDiffusionIntegral Q D T σ hσ h2 hA t := by
  exact exists_constructed_continuous_martingale_version Q D T _

end PBGSO.FilteredBrownian
