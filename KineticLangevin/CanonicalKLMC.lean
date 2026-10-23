import KineticLangevin.CanonicalKLMCBound
import KineticLangevin.CanonicalReferenceNoise
import KineticLangevin.StationarityTransfer

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace KineticLangevin.CanonicalCoupling
variable {d : ℕ} {μ : Measure (H d)} [IsProbabilityMeasure μ]

/-- The actual canonical global reference remains Gibbs distributed on every initial coupling extension. -/
theorem globalReferenceFlow_stationary
    (f : H d → ℝ) (m : ℝ) (hm : 0 < m) (M γ : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f))
    (c : ULA.Coupling μ (ULA.gibbsMeasure f))
    (hπ : MemLp (id : H d → H d) 2 (ULA.gibbsMeasure f)) :
    GlobalReferenceStationary c hπ f M γ hLip := by
  intro T hT t ht
  let Y := globalReferenceFlow c hπ f M γ hLip T hT
  have hs := globalReferenceFlow_spec c hπ f M γ hLip T hT
  have hjoint : ∀ h : ℝ≥0, HasLaw
      (fun p => (lpPhaseCoe (probability c) (referenceInitial c hπ) p,
        fun k : ℕ => ouInputIncrement γ (globalInput c γ) ((k : ℝ)*h) h p))
      ((kineticGibbsTarget f).prod (Measure.infinitePi (fun _ : ℕ => ouThermalLaw (E := H d) γ h)))
      (probability c) := by
    intro h
    simpa only [kineticGibbsTarget,ouThermalLaw] using initial_ouInput_jointLaw c hπ γ γ.coe_nonneg h
  have heq : ∀ s ∈ Icc 0 t, Y s-referenceInitial c hπ =
      -(∫ r in 0..s,kineticNegativeDrift (ULA.lpDrift (probability c) (gradient f) hLip) γ 1 (Y r)) +
        (globalInput c γ s,0) := by
    intro s hs'
    simpa only [hs.2.1] using hs.2.2 s ⟨hs'.1,hs'.2.trans ht.2⟩
  have hl := kinetic_integral_stationary_of_jointNoise (probability c) f m hm M γ hf hsc hLip
    (referenceInitial c hπ) (globalInput c γ) (continuous_globalInput c γ) (globalInput_zero c γ)
    hjoint Y hs.1 (⟨t,ht.1⟩ : ℝ≥0) heq
  exact ⟨(measurable_lpPhaseCoe (probability c) (Y t)).aemeasurable,hl⟩

/-- Dalalyan--Riou-Durand's first-order KLMC Wasserstein estimate for the actual canonical sampler.
All continuous reference laws, local-error identities and initial-coupling infima are proved internally. -/
theorem klmc_wasserstein_bound
    (f : H d → ℝ) (m : ℝ) (M γ : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ)) (hm : 0 < m)
    (hγ : 0 < (γ : ℝ)) (hfriction : m+(M : ℝ) ≤ (γ : ℝ)^2)
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (hstep : 4*(γ : ℝ)*(M : ℝ)*(h : ℝ) ≤ m)
    (hfinite : ULA.wasserstein2 μ (ULA.gibbsMeasure f) ≠ ⊤) (n : ℕ) :
    ULA.wasserstein2Real (klmcLaw f γ h μ n) (ULA.gibbsMeasure f) ≤
      Real.sqrt 2 * (1-3*m*(h : ℝ)/(4*(γ : ℝ)))^n * ULA.wasserstein2Real μ (ULA.gibbsMeasure f) +
        (M : ℝ)*(h : ℝ)*Real.sqrt (2*(d : ℝ))/m := by
  have hπ : MemLp (id : H d → H d) 2 (ULA.gibbsMeasure f) := ULA.memLp_id_gibbsMeasure f m hm hf hsc
  exact klmc_wasserstein_bound_of_globalStationarity hπ f m M γ hf hsc hLip hmM hm hγ hfriction
    h hh hstep hfinite (fun c => globalReferenceFlow_stationary f m hm M γ hf hsc hLip c hπ) n

end KineticLangevin.CanonicalCoupling
