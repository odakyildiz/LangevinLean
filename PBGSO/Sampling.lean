import PBGSO.Framework
import ProximalLangevin.MeanFieldVariance

/-! # Actual independent-copy Monte Carlo error

The particle interaction theorem needs independent mean-field copies.
Exchangeability of interacting particles is insufficient for this identity.
Every expectation below is integration on the actual finite product law.
-/

noncomputable section
open MeasureTheory
namespace PBGSO

variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace Θ] [BorelSpace Θ]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]
  [Fintype I]

/-- Exact variance of the model's empirical gradient for independent sampler
states. No relation between the observation and sampler drift is required. -/
theorem gradient_sampling_variance (M : Model S Θ Z X I)
    (ν : Measure Z) [IsProbabilityMeasure ν] (s : S)
    (hF : MemLp (fun z => M.observation (M.parameter s) (M.position z)) 2 ν)
    (N : ℕ) (hN : 0 < N) :
    (∫ z : Fin N → Z, ‖M.particleGradient N s z - M.meanGradient ν s‖ ^ 2
      ∂Measure.pi (fun _ : Fin N => ν)) =
      (∫ z, ‖M.observation (M.parameter s) (M.position z) - M.meanGradient ν s‖ ^ 2 ∂ν) /
        (N : ℝ) :=
  ProximalLangevin.iid_empirical_variance ν
    (fun z => M.observation (M.parameter s) (M.position z)) hF hN

/-- The corresponding root mean square identity has exactly 1/sqrt(N). -/
theorem gradient_sampling_rms (M : Model S Θ Z X I)
    (ν : Measure Z) [IsProbabilityMeasure ν] (s : S)
    (hF : MemLp (fun z => M.observation (M.parameter s) (M.position z)) 2 ν)
    (N : ℕ) (hN : 0 < N) :
    Real.sqrt (∫ z : Fin N → Z, ‖M.particleGradient N s z - M.meanGradient ν s‖ ^ 2
      ∂Measure.pi (fun _ : Fin N => ν)) =
      Real.sqrt (∫ z,
        ‖M.observation (M.parameter s) (M.position z) - M.meanGradient ν s‖ ^ 2 ∂ν) /
          Real.sqrt (N : ℝ) :=
  ProximalLangevin.iid_empirical_rms ν
    (fun z => M.observation (M.parameter s) (M.position z)) hF hN

/-- A uniform one-copy variance bound implies the stated sampling rate. -/
theorem gradient_sampling_rms_le (M : Model S Θ Z X I)
    (ν : Measure Z) [IsProbabilityMeasure ν] (s : S)
    (hF : MemLp (fun z => M.observation (M.parameter s) (M.position z)) 2 ν)
    (N : ℕ) (hN : 0 < N) (V : ℝ)
    (hV : (∫ z,
      ‖M.observation (M.parameter s) (M.position z) - M.meanGradient ν s‖ ^ 2 ∂ν) ≤ V) :
    Real.sqrt (∫ z : Fin N → Z, ‖M.particleGradient N s z - M.meanGradient ν s‖ ^ 2
      ∂Measure.pi (fun _ : Fin N => ν)) ≤ Real.sqrt V / Real.sqrt (N : ℝ) := by
  rw [gradient_sampling_rms M ν s hF N hN]
  exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hV) (Real.sqrt_nonneg _)

/-- The actual finite empirical gradient is square integrable on the iid
product law whenever the one-copy observation is square integrable. -/
theorem particleGradient_memLp (M : Model S Θ Z X I)
    (ν : Measure Z) [IsProbabilityMeasure ν] (s : S)
    (hF : MemLp (fun z => M.observation (M.parameter s) (M.position z)) 2 ν)
    (N : ℕ) :
    MemLp (M.particleGradient N s) 2 (Measure.pi (fun _ : Fin N => ν)) := by
  classical
  have hi (i : Fin N) : MemLp
      (fun z : Fin N → Z => M.observation (M.parameter s) (M.position (z i))) 2
      (Measure.pi (fun _ : Fin N => ν)) :=
    hF.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => ν) i)
  exact (memLp_finsetSum Finset.univ (fun i _ => hi i)).const_smul (N : ℝ)⁻¹

/-- The same variance identity on any actual probability space carrying a
reference cloud with the iid product marginal. This transfers the sampling
bound to an interacting/reference joint law without asserting independence
of that cloud from the interacting optimiser or particles. -/
theorem gradient_sampling_variance_of_cloud_law {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (M : Model S Θ Z X I)
    (ν : Measure Z) [IsProbabilityMeasure ν] (s : S)
    (hF : MemLp (fun z => M.observation (M.parameter s) (M.position z)) 2 ν)
    (N : ℕ) (hN : 0 < N) (Y : Ω → Fin N → Z)
    (hY : AEMeasurable Y Q)
    (hLaw : Q.map Y = Measure.pi (fun _ : Fin N => ν)) :
    (∫ ω, ‖M.particleGradient N s (Y ω) - M.meanGradient ν s‖ ^ 2 ∂Q) =
      (∫ z, ‖M.observation (M.parameter s) (M.position z) - M.meanGradient ν s‖ ^ 2 ∂ν) /
        (N : ℝ) := by
  have hm := (particleGradient_memLp M ν s hF N).sub
    (memLp_const (M.meanGradient ν s))
  have hs : AEStronglyMeasurable
      (fun z : Fin N → Z => ‖M.particleGradient N s z - M.meanGradient ν s‖ ^ 2)
      (Q.map Y) := by
    rw [hLaw]
    exact hm.aestronglyMeasurable.norm.pow 2
  have he := integral_map hY hs
  rw [hLaw] at he
  exact he.symm.trans (gradient_sampling_variance M ν s hF N hN)

end PBGSO
