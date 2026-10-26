import PBGSO.RawLocalIntegral
import PBGSO.RawDiffusionTransport

/-! # Globalizing actual local Brownian integrals from coefficient moments
Only the raw diffusion needs global expected square integrability.
No growth or moment condition on the drift or state is required.
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
  {D : Driver (I := I) Q} {T : ℝ≥0} (L : RawLocalDiffusion (Z := Z) Q D T)

theorem RawLocalDiffusion.localNoise_eq_global_of_square
    (hσ2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖L.sigma i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) (t : ℝ≥0) (ht : t ≤ T) :
    L.localNoise t =ᵐ[Q] rawDiffusionIntegral Q D T L.sigma L.sigma_strong
      hσ2 L.sigma_adapted t := by
  obtain ⟨M, hMmart, hMcont, hM⟩ := rawDiffusionIntegral_exists_continuous_martingale Q D T
    L.sigma L.sigma_strong hσ2 L.sigma_adapted
  have hstop (n : ℕ) : ∀ᵐ ω ∂Q, ∀ s : ℝ≥0,
      L.version n s ω = M (min s (L.stop n ω)) ω :=
    rawDiffusionIntegral_stopped_version Q D T (L.stop n) (L.stop_bound n) (L.stop_stopping n)
      L.sigma (L.stoppedSigma n) L.sigma_strong hσ2 L.sigma_adapted
      (L.stoppedSigma_strong n) (L.stoppedSigma_square n) (L.stoppedSigma_adapted n)
      (fun _ _ _ => rfl) M (L.version n) hM (L.version_ae n) hMcont (L.version_continuous n)
  have heq : L.localNoise t =ᵐ[Q] M t := by
    filter_upwards [ae_all_iff.mpr hstop, L.version_eventually_localNoise] with ω hs hl
    obtain ⟨n, hn, hnl⟩ := ((L.stop_eventually_horizon ω).and (hl t ht)).exists
    exact hnl.symm.trans (by simpa only [hn, min_eq_left ht] using hs n t)
  exact heq.trans (hM t)


end PBGSO.FilteredBrownian
