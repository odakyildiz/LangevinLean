import PBGSO.RawLocalNoiseGlobalization
import Mathlib.Topology.Bases

/-! # Actual local-noise equality for common original diffusion fields
Global expected square diffusion and product-a.e. equal columns imply one
full-probability event of equal continuous local noise on the entire horizon.
No pathwise stochastic-operator or cancellation conclusion is supplied.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace PBGSO.FilteredBrownian
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {D : Driver (I := I) Q} {T : ℝ≥0}
  (L K : RawLocalDiffusion (Z := Z) Q D T)
  (hL : ∀ i, Integrable (fun p : ℝ × Ω => ‖L.sigma i p.1 p.2‖ ^ 2)
    ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
  (hK : ∀ i, Integrable (fun p : ℝ × Ω => ‖K.sigma i p.1 p.2‖ ^ 2)
    ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
  (hσ : ∀ i, Function.uncurry (L.sigma i) =ᵐ[(volume.restrict (Ioc 0 (T : ℝ))).prod Q]
    Function.uncurry (K.sigma i))
include hσ hL hK

/-- Every deterministic time has equal actual local noise. -/
theorem RawLocalDiffusion.localNoise_congr_ae (t : ℝ≥0) (ht : t ≤ T) :
    L.localNoise t =ᵐ[Q] K.localNoise t := by
  have he := rawDiffusionIntegral_congr_ae_coefficients Q D T L.sigma K.sigma
    L.sigma_strong K.sigma_strong hL hK L.sigma_adapted K.sigma_adapted hσ t
  have hi : rawDiffusionIntegral Q D T L.sigma L.sigma_strong hL L.sigma_adapted t =ᵐ[Q]
      rawDiffusionIntegral Q D T K.sigma K.sigma_strong hK K.sigma_adapted t :=
    Eventually.of_forall (fun ω => congrArg (fun A : Lp Z 2 Q => A ω) he)
  exact (L.localNoise_eq_global_of_square hL t ht).trans
    (hi.trans (K.localNoise_eq_global_of_square hK t ht).symm)

/-- Actual path continuity upgrades deterministic-time noise equality to a
single event on the whole horizon, independent of the local-energy gauges. -/
theorem RawLocalDiffusion.localNoise_congr_on_horizon :
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → L.localNoise t ω = K.localNoise t ω := by
  let W := Iic T
  letI : Nonempty W := ⟨⟨0, by simp [W]⟩⟩
  let τ := TopologicalSpace.denseSeq W
  have ht (n : ℕ) : (τ n).val ≤ T := (τ n).property
  filter_upwards [L.localNoise_continuous, K.localNoise_continuous,
    ae_all_iff.mpr (fun n => L.localNoise_congr_ae K hL hK hσ (τ n).val (ht n))]
    with ω hl hk he
  have hf : Continuous (fun t : W => L.localNoise t.val ω) := hl.comp continuous_subtype_val
  have hg : Continuous (fun t : W => K.localNoise t.val ω) := hk.comp continuous_subtype_val
  have heq := (TopologicalSpace.denseRange_denseSeq W).equalizer hf hg (funext he)
  intro t htt
  exact congrFun heq (⟨t, htt⟩ : W)

end PBGSO.FilteredBrownian
