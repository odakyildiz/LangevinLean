import PBGSO.RawDiffusionTransport

/-! # Literal subtraction of raw stochastic diffusion fields
The raw difference is square-integrable and adapted by proved closure
properties. Actual spatial L² sections commute with subtraction almost
everywhere in time, yielding subtraction of the computed integrals and the
original raw synchronous diffusion-difference isometry.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology RealInnerProductSpace InnerProductSpace
namespace PBGSO.FilteredBrownian
open PBGSO.ProductLpSections PBGSO.QuadraticMartingale
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

/-- Actual joint strong measurability of the raw coefficient difference. -/
theorem rawSubtract_stronglyMeasurable (σ τ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (hτ : ∀ i, StronglyMeasurable (Function.uncurry (τ i))) (i : I) :
    StronglyMeasurable (fun p : ℝ × Ω => σ i p.1 p.2 - τ i p.1 p.2) :=
  (hσ i).sub (hτ i)

/-- Product-square integrability of the raw difference is derived. -/
theorem rawSubtract_square (T : ℝ≥0) (σ τ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (hτ : ∀ i, StronglyMeasurable (Function.uncurry (τ i)))
    (hσ2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hτ2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖τ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) (i : I) :
    Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2 - τ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := by
  have hs := (memLp_two_iff_integrable_sq_norm (hσ i).aestronglyMeasurable).mpr (hσ2 i)
  have ht := (memLp_two_iff_integrable_sq_norm (hτ i).aestronglyMeasurable).mpr (hτ2 i)
  exact (hs.sub ht).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)

/-- Every raw difference section retains actual past adaptation. -/
theorem rawSubtract_adapted (σ τ : I → ℝ → Ω → Z)
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) Q)
    (hB : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (τ i t) Q)
    (t : ℝ≥0) (i : I) :
    AEStronglyMeasurable[D.filtration t] (fun ω => σ i t ω - τ i t ω) Q :=
  (hA t i).sub (hB t i)

/-- Literal raw differences and bounded-linear differences give the same
actual coefficient time-L² class. -/
theorem rawDiffusionCurve_sub_ae (T : ℝ≥0) (σ τ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (hτ : ∀ i, StronglyMeasurable (Function.uncurry (τ i)))
    (hσ2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hτ2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖τ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) :
    rawDiffusionCurve Q (fun i r ω => σ i r ω - τ i r ω) =ᵐ[volume.restrict (Ioc 0 (T : ℝ))]
      rawDiffusionCurve Q σ - rawDiffusionCurve Q τ := by
  have hs : ∀ᵐ r ∂volume.restrict (Ioc 0 (T : ℝ)), ∀ i, MemLp (σ i r) 2 Q :=
    ae_all_iff.mpr (fun i => ae_memLp (volume.restrict (Ioc 0 (T : ℝ))) Q (σ i) (hσ i) (hσ2 i))
  have ht : ∀ᵐ r ∂volume.restrict (Ioc 0 (T : ℝ)), ∀ i, MemLp (τ i r) 2 Q :=
    ae_all_iff.mpr (fun i => ae_memLp (volume.restrict (Ioc 0 (T : ℝ))) Q (τ i) (hτ i) (hτ2 i))
  filter_upwards [hs, ht] with r hs ht
  apply PiLp.ext
  intro i
  change sectionLp Q (fun r ω => σ i r ω - τ i r ω) r = sectionLp Q (σ i) r - sectionLp Q (τ i) r
  apply Lp.ext
  filter_upwards [sectionLp_ae Q (fun r ω => σ i r ω - τ i r ω) ((hs i).sub (ht i)),
    sectionLp_ae Q (σ i) (hs i), sectionLp_ae Q (τ i) (ht i),
    Lp.coeFn_sub (sectionLp Q (σ i) r) (sectionLp Q (τ i) r)] with ω hd hs ht hsub
  rw [hsub, Pi.sub_apply, hd, hs, ht]

/-- Subtraction of computed raw-field integrals, with all difference-field
integrability and adaptedness derived from the primitive two fields. -/
theorem rawDiffusionIntegral_sub (T : ℝ≥0) (σ τ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (hτ : ∀ i, StronglyMeasurable (Function.uncurry (τ i)))
    (hσ2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hτ2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖τ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) Q)
    (hB : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (τ i t) Q) (t : ℝ≥0) :
    rawDiffusionIntegral Q D T (fun i r ω => σ i r ω - τ i r ω)
      (rawSubtract_stronglyMeasurable σ τ hσ hτ) (rawSubtract_square Q T σ τ hσ hτ hσ2 hτ2)
      (rawSubtract_adapted Q D σ τ hA hB) t =
      rawDiffusionIntegral Q D T σ hσ hσ2 hA t - rawDiffusionIntegral Q D T τ hτ hτ2 hB t := by
  unfold rawDiffusionIntegral
  rw [predictableCurveIntegral_eq_of_ae_coefficients Q D T _
    (rawDiffusionCurve Q σ - rawDiffusionCurve Q τ) _
    ((rawDiffusionCurve_square Q T σ hσ hσ2).sub (rawDiffusionCurve_square Q T τ hτ hτ2)) _
    (curveSubtract_adapted Q D (rawDiffusionCurve Q σ) (rawDiffusionCurve Q τ)
      (rawDiffusionCurve_adapted Q D σ hA) (rawDiffusionCurve_adapted Q D τ hB))
    (rawDiffusionCurve_sub_ae Q T σ τ hσ hτ hσ2 hτ2) t]
  exact predictableCurveIntegral_sub Q D T _ _ _ _ _ _ t

/-- Exact weighted increments of the actual difference of two original raw
noise integrals. No synchronous difference-isometry premise is supplied. -/
theorem rawDiffusionIntegral_difference_isometry (T : ℝ≥0) (σ τ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (hτ : ∀ i, StronglyMeasurable (Function.uncurry (τ i)))
    (hσ2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hτ2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖τ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) Q)
    (hB : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (τ i t) Q)
    (W : Z →L[ℝ] Z) (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (s t : ℝ≥0) (hst : s ≤ t) (ht : t ≤ T) :
    weightedPairing Q W
      ((rawDiffusionIntegral Q D T σ hσ hσ2 hA t - rawDiffusionIntegral Q D T τ hτ hτ2 hB t) -
        (rawDiffusionIntegral Q D T σ hσ hσ2 hA s - rawDiffusionIntegral Q D T τ hτ hτ2 hB s))
      ((rawDiffusionIntegral Q D T σ hσ hσ2 hA t - rawDiffusionIntegral Q D T τ hτ hτ2 hB t) -
        (rawDiffusionIntegral Q D T σ hσ hσ2 hA s - rawDiffusionIntegral Q D T τ hτ hτ2 hB s)) =
      ∫ r in Ioc (s : ℝ) t, ∫ ω, ∑ i,
        ⟪σ i r ω - τ i r ω, W (σ i r ω - τ i r ω)⟫_ℝ ∂Q := by
  have h := rawDiffusionIntegral_increment_isometry Q D T (fun i r ω => σ i r ω - τ i r ω)
    (rawSubtract_stronglyMeasurable σ τ hσ hτ) (rawSubtract_square Q T σ τ hσ hτ hσ2 hτ2)
    (rawSubtract_adapted Q D σ τ hA hB) W hW s t hst ht
  rw [rawDiffusionIntegral_sub Q D T σ τ hσ hτ hσ2 hτ2 hA hB t,
    rawDiffusionIntegral_sub Q D T σ τ hσ hτ hσ2 hτ2 hA hB s] at h
  exact h

end PBGSO.FilteredBrownian
