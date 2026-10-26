import PBGSO.RandomVariationEnergy
import PBGSO.RawDiffusionAlgebra
import PBGSO.ConstructedPredictableModel

/-! # Raw finite-variation energy from the computed original diffusion
Martingale structure, spatial noise moments, path continuity of the residual,
maximal radius and original weighted diffusion energy are all derived.
The raw drift needs only pathwise L¹ and its actual stopping variation cap.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal RealInnerProductSpace InnerProductSpace
namespace PBGSO.ConstructedRandomVariationHorizon
open FilteredBrownian QuadraticMartingale
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)
  (W : Z →L[ℝ] Z) (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
include hW

/-- Exact quadratic energy for an original raw equation driven by the
computed Brownian integral. No martingale or isometry conclusion is assumed. -/
theorem quadratic_balance (T : ℝ≥0) (σ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (hσ2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hσA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) Q)
    (x b m : ℝ → Ω → Z) (h2x : ∀ t, MemLp (x t) 2 Q)
    (hxA : ∀ t ∈ Icc 0 (T : ℝ),
      AEStronglyMeasurable[ConstructedPredictableModel.realFiltration Q D t] (x t) Q)
    (hmA : StronglyAdapted (ConstructedPredictableModel.realFiltration Q D) m)
    (hnoise : ∀ t, m t =ᵐ[Q] rawDiffusionIntegral Q D T σ hσ hσ2 hσA t.toNNReal)
    (hb : StronglyMeasurable (Function.uncurry b)) (B : Ω → ℝ) (hB : MemLp B 2 Q)
    (hxcont : ∀ᵐ ω ∂Q, ContinuousOn (fun t => x t ω) (Icc 0 (T : ℝ)))
    (hpaths : ∀ᵐ ω ∂Q, IntervalIntegrable (fun r => b r ω) volume 0 (T : ℝ) ∧
      (∫ r in 0..(T : ℝ), ‖b r ω‖) ≤ B ω ∧
      ∀ t ∈ Icc 0 (T : ℝ), x t ω = x 0 ω + (∫ r in 0..t, b r ω) + m t ω) (S : ℝ≥0) (hS : S ≤ T) :
    Integrable (fun ω => ∫ r in 0..(S : ℝ), ⟪x r ω, W (b r ω)⟫_ℝ) Q ∧
    (∫ ω, ⟪x S ω, W (x S ω)⟫_ℝ ∂Q) = (∫ ω, ⟪x 0 ω, W (x 0 ω)⟫_ℝ ∂Q) +
      2 * (∫ ω, (∫ r in 0..(S : ℝ), ⟪x r ω, W (b r ω)⟫_ℝ) ∂Q) +
      (∫ r in Ioc 0 (S : ℝ), ∫ ω, ∑ i, ⟪σ i r ω, W (σ i r ω)⟫_ℝ ∂Q) := by
  let J := rawDiffusionIntegral Q D T σ hσ hσ2 hσA
  let R := MartingaleL2Limit.representative Q D.filtration J
  have hR : Martingale R D.filtration Q :=
    rawDiffusionIntegral_martingale Q D T σ hσ hσ2 hσA
  have hrep (t : ℝ) : R t.toNNReal =ᵐ[Q] m t :=
    (rawDiffusionIntegral_representative_ae Q D T σ hσ hσ2 hσA t.toNNReal).trans (hnoise t).symm
  have hmartR : Martingale (fun t : ℝ => R t.toNNReal)
      (ConstructedPredictableModel.realFiltration Q D) Q := by
    refine ⟨fun t => hR.stronglyAdapted t.toNNReal, ?_⟩
    intro s t hst
    exact hR.condExp_ae_eq (Real.toNNReal_mono hst)
  have hm : Martingale m (ConstructedPredictableModel.realFiltration Q D) Q :=
    hmartR.congr hmA hrep
  have h2m (t : ℝ) : MemLp (m t) 2 Q := (memLp_congr_ae (hnoise t)).mpr (Lp.memLp _)
  have hmcont : ∀ᵐ ω ∂Q, ContinuousOn (fun t => m t ω) (Icc 0 (T : ℝ)) := by
    filter_upwards [hxcont, hpaths] with ω hx hp
    have hi := (IntegralQuadraticEnergy.integral_absolutelyContinuous (fun r => b r ω) hp.1).continuousOn
    rw [uIcc_of_le T.coe_nonneg] at hi
    apply ((hx.sub continuousOn_const).sub hi).congr
    intro t ht
    have he := hp.2.2 t ht
    change m t ω = (x t ω - x 0 ω) - (∫ r in 0..t, b r ω)
    rw [he]
    abel
  have hSr : (S : ℝ) ≤ T := by exact_mod_cast hS
  have hsub : Icc (0 : ℝ) S ⊆ Icc 0 (T : ℝ) := Icc_subset_Icc le_rfl hSr
  have hpathsS : ∀ᵐ ω ∂Q, IntervalIntegrable (fun r => b r ω) volume 0 (S : ℝ) ∧
      (∫ r in 0..(S : ℝ), ‖b r ω‖) ≤ B ω ∧
      ∀ t ∈ Icc 0 (S : ℝ), x t ω = x 0 ω + (∫ r in 0..t, b r ω) + m t ω := by
    filter_upwards [hpaths] with ω hp
    have hInt : IntervalIntegrable (fun r => b r ω) volume 0 (S : ℝ) := by
      apply hp.1.mono_set
      simpa only [uIcc_of_le S.coe_nonneg, uIcc_of_le T.coe_nonneg] using hsub
    refine ⟨hInt, ?_, fun t ht => hp.2.2 t (hsub ht)⟩
    exact (intervalIntegral.integral_mono_interval le_rfl S.coe_nonneg hSr
      (ae_of_all _ (fun _ => norm_nonneg _)) hp.1.norm).trans hp.2.1
  obtain ⟨hi, he⟩ := RandomVariationEnergy.quadratic_balance Q
    (ConstructedPredictableModel.realFiltration Q D) W hW S x b m h2x h2m
    (fun t ht => hxA t (hsub ht)) hm hb B hB
    (hxcont.mono (fun _ h => h.mono hsub)) (hmcont.mono (fun _ h => h.mono hsub)) hpathsS
  have henergy : (∫ ω, ⟪m S ω, W (m S ω)⟫_ℝ ∂Q) =
      ∫ r in Ioc 0 (S : ℝ), ∫ ω, ∑ i, ⟪σ i r ω, W (σ i r ω)⟫_ℝ ∂Q := by
    have hI := rawDiffusionIntegral_increment_isometry Q D T σ hσ hσ2 hσA W hW 0 S (by simp) hS
    rw [rawDiffusionIntegral_zero, sub_zero] at hI
    have hp : (∫ ω, ⟪m S ω, W (m S ω)⟫_ℝ ∂Q) = weightedPairing Q W (J S) (J S) := by
      rw [weightedPairing_apply, lp_weighted_pairing_eq_integral]
      apply integral_congr_ae
      filter_upwards [hnoise (S : ℝ)] with ω hω
      simp only [Real.toNNReal_coe] at hω
      rw [hω]
    exact hp.trans hI
  exact ⟨hi, by rwa [henergy] at he⟩

end PBGSO.ConstructedRandomVariationHorizon
