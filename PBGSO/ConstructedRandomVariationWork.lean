import PBGSO.ConstructedRandomVariationHorizon
import PBGSO.RandomVariationWork
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
namespace PBGSO.ConstructedRandomVariationWork
open FilteredBrownian QuadraticMartingale
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)
  (W : Z →L[ℝ] Z) (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)

/-- Exact quadratic energy for an original raw equation driven by the
computed Brownian integral. No martingale or isometry conclusion is assumed. -/
theorem work_product_integrable (T : ℝ≥0) (σ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (hσ2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hσA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) Q)
    (x b m : ℝ → Ω → Z) (h2x : ∀ t, MemLp (x t) 2 Q)
    (hxjoint : StronglyMeasurable (Function.uncurry x))
    (hxA : ∀ t ∈ Icc 0 (T : ℝ),
      AEStronglyMeasurable[ConstructedPredictableModel.realFiltration Q D t] (x t) Q)
    (hmA : StronglyAdapted (ConstructedPredictableModel.realFiltration Q D) m)
    (hnoise : ∀ t, m t =ᵐ[Q] rawDiffusionIntegral Q D T σ hσ hσ2 hσA t.toNNReal)
    (hb : StronglyMeasurable (Function.uncurry b)) (B : Ω → ℝ) (hB : MemLp B 2 Q)
    (hxcont : ∀ᵐ ω ∂Q, ContinuousOn (fun t => x t ω) (Icc 0 (T : ℝ)))
    (hpaths : ∀ᵐ ω ∂Q, IntervalIntegrable (fun r => b r ω) volume 0 (T : ℝ) ∧
      (∫ r in 0..(T : ℝ), ‖b r ω‖) ≤ B ω ∧
      ∀ t ∈ Icc 0 (T : ℝ), x t ω = x 0 ω + (∫ r in 0..t, b r ω) + m t ω) :
    Integrable (fun p : ℝ × Ω => ⟪x p.1 p.2, W (b p.1 p.2)⟫_ℝ)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := by
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
  let A := ExpectedBilinearLimits.spatialPairing W
  have hWork := (RandomVariationWork.integrable_and_swap Q
    (ConstructedPredictableModel.realFiltration Q D) T A x b m hxjoint hb (h2x 0) h2m
    hm B hB hxcont hmcont hpaths).1
  simp only [A, ExpectedBilinearLimits.spatialPairing_apply] at hWork
  exact hWork

end PBGSO.ConstructedRandomVariationWork
