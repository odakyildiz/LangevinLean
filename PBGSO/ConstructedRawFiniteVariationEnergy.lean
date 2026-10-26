import PBGSO.RawFiniteVariationEnergy
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
namespace PBGSO.ConstructedRawFiniteVariationEnergy
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
    (hb : StronglyMeasurable (Function.uncurry b)) (c : ℝ) (hc : 0 ≤ c)
    (hxcont : ∀ᵐ ω ∂Q, ContinuousOn (fun t => x t ω) (Icc 0 (T : ℝ)))
    (hpaths : ∀ᵐ ω ∂Q, IntervalIntegrable (fun r => b r ω) volume 0 (T : ℝ) ∧
      (∫ r in 0..(T : ℝ), ‖b r ω‖) ≤ c ∧
      ∀ t ∈ Icc 0 (T : ℝ), x t ω = x 0 ω + (∫ r in 0..t, b r ω) + m t ω) :
    Integrable (fun ω => ∫ r in 0..(T : ℝ), ⟪x r ω, W (b r ω)⟫_ℝ) Q ∧
    (∫ ω, ⟪x T ω, W (x T ω)⟫_ℝ ∂Q) = (∫ ω, ⟪x 0 ω, W (x 0 ω)⟫_ℝ ∂Q) +
      2 * (∫ ω, (∫ r in 0..(T : ℝ), ⟪x r ω, W (b r ω)⟫_ℝ) ∂Q) +
      (∫ r in Ioc 0 (T : ℝ), ∫ ω, ∑ i, ⟪σ i r ω, W (σ i r ω)⟫_ℝ ∂Q) := by
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
  obtain ⟨hi, he⟩ := RawFiniteVariationEnergy.quadratic_balance Q
    (ConstructedPredictableModel.realFiltration Q D) W hW T x b m h2x h2m hxA hm hb c hc
    hxcont hmcont hpaths
  have henergy : (∫ ω, ⟪m T ω, W (m T ω)⟫_ℝ ∂Q) =
      ∫ r in Ioc 0 (T : ℝ), ∫ ω, ∑ i, ⟪σ i r ω, W (σ i r ω)⟫_ℝ ∂Q := by
    have hI := rawDiffusionIntegral_increment_isometry Q D T σ hσ hσ2 hσA W hW 0 T (by simp) le_rfl
    rw [rawDiffusionIntegral_zero, sub_zero] at hI
    have hp : (∫ ω, ⟪m T ω, W (m T ω)⟫_ℝ ∂Q) = weightedPairing Q W (J T) (J T) := by
      rw [weightedPairing_apply, lp_weighted_pairing_eq_integral]
      apply integral_congr_ae
      filter_upwards [hnoise (T : ℝ)] with ω hω
      simp only [Real.toNNReal_coe] at hω
      rw [hω]
    exact hp.trans hI
  exact ⟨hi, by rwa [henergy] at he⟩

end PBGSO.ConstructedRawFiniteVariationEnergy
