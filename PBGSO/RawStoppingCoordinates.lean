import PBGSO.LocalizedDiffusion
import PBGSO.LinearGrowthMoment

/-! # Literal stopped coordinates of raw original integral equations
Stopping the original pathwise Bochner drift gives exactly the actual
coefficient mask. All state identities concern the original raw variables;
no stopped SDE or L² realization is assumed in these deterministic transfers.
-/
noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace PBGSO.RawStoppingCoordinates
variable {Ω Z : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]

/-- Original state at the literal bounded random stopping time. -/
def stoppedState (τ : Ω → ℝ≥0) (X : ℝ → Ω → Z) (t : ℝ) (ω : Ω) : Z :=
  X (min t (τ ω : ℝ)) ω

/-- Joint measurability follows from the actual time/sample coordinate map. -/
theorem stoppedState_stronglyMeasurable (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (X : ℝ → Ω → Z) (hX : StronglyMeasurable (Function.uncurry X)) :
    StronglyMeasurable (Function.uncurry (stoppedState τ X)) := by
  exact hX.comp_measurable ((measurable_fst.min
    (measurable_coe_nnreal_real.comp (hτ.comp measurable_snd))).prodMk measurable_snd)

/-- The original drift evaluated up to min(t,τ) is exactly its actual
before-stop coefficient integral, including stopping-boundary atoms. -/
theorem stoppedField_integral (τ : Ω → ℝ≥0) (b : ℝ → Ω → Z)
    (t : ℝ) (ht : 0 ≤ t) (ω : Ω) :
    (∫ r in 0..t, LocalizedDiffusion.stoppedField τ b r ω) =
      ∫ r in 0..min t (τ ω : ℝ), b r ω := by
  rw [intervalIntegral.integral_of_le ht,
    intervalIntegral.integral_of_le (le_min ht (τ ω).coe_nonneg)]
  change (∫ r in Ioc 0 t, (Iic (τ ω : ℝ)).indicator (fun r => b r ω) r) = _
  rw [setIntegral_indicator measurableSet_Iic]
  have hs : Iic (τ ω : ℝ) ∩ Ioc 0 t = Ioc 0 (min t (τ ω : ℝ)) := by
    ext r
    simp only [mem_inter_iff, mem_Iic, mem_Ioc, le_min_iff]
    tauto
  rw [Set.inter_comm, hs]

/-- A simultaneous original equation gives the literal stopped equation
by actual random-time evaluation and the proved drift-mask identity. -/
theorem stoppedState_equation (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτ : ∀ ω, τ ω ≤ T) (X b M : ℝ → Ω → Z)
    (heq : ∀ ω, ∀ t ∈ Icc 0 (T : ℝ),
      X t ω = X 0 ω + (∫ r in 0..t, b r ω) + M t ω) :
    ∀ ω, ∀ t ∈ Icc 0 (T : ℝ), stoppedState τ X t ω = X 0 ω +
      (∫ r in 0..t, LocalizedDiffusion.stoppedField τ b r ω) +
      M (min t (τ ω : ℝ)) ω := by
  intro ω t ht
  unfold stoppedState
  rw [stoppedField_integral τ b t ht.1 ω]
  exact heq ω _ ⟨le_min ht.1 (τ ω).coe_nonneg,
    (min_le_left _ _).trans ht.2⟩

/-- Genuine horizon-exhausting localizations eventually equal the original
state on every fixed horizon time; no path continuity is needed for this limit. -/
theorem stoppedState_tendsto (Q : Measure Ω) (τ : ℕ → Ω → ℝ≥0)
    (T : ℝ≥0) (X : ℝ → Ω → Z)
    (hτ : ∀ᵐ ω ∂Q, ∀ᶠ n in atTop, τ n ω = T)
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    ∀ᵐ ω ∂Q, Tendsto (fun n => stoppedState (τ n) X t ω) atTop (𝓝 (X t ω)) := by
  filter_upwards [hτ] with ω hω
  apply tendsto_const_nhds.congr'
  filter_upwards [hω] with n hn
  simp only [stoppedState, hn, min_eq_left ht.2]

end PBGSO.RawStoppingCoordinates
