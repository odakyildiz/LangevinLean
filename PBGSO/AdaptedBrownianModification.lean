import PBGSO.AdaptedBrownianWindow
import PBGSO.ContinuousVersionGlue

/-! # Constructed globally continuous adapted Brownian modifications
The process is an explicit countable-horizon past-sample series. Genuine
Gaussian fourth moments and dyadic polygons derive its continuous paths;
countably many grid identities derive overlap. Its actual adaptation remains
with respect to the original filtration, without filtration completion.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace PBGSO.AdaptedBrownianModification
open ContinuousVersionGlue AdaptedBrownianWindow
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

def process (B : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  globalVersion (fun n => candidate B (horizon n))

theorem process_stronglyAdapted (F : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0 → Ω → ℝ) (hA : StronglyAdapted F B) :
    StronglyAdapted F (process B) := by
  apply globalVersion_stronglyAdapted
  intro n
  exact candidate_stronglyAdapted F B hA (horizon n) (by unfold horizon; positivity)

variable (Q : Measure Ω) [IsProbabilityMeasure Q]
  (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B Q)
include hB

theorem process_ae (t : ℝ≥0) : process B t =ᵐ[Q] B t := by
  apply globalVersion_ae Q B (fun n => candidate B (horizon n))
  intro n s hs
  exact candidate_ae Q B hB (horizon n) (by unfold horizon; positivity) s hs

theorem process_continuous : ∀ᵐ ω ∂Q, Continuous (fun t => process B t ω) := by
  apply globalVersion_continuous Q B (fun n => candidate B (horizon n))
  · intro n t ht
    exact candidate_ae Q B hB (horizon n) (by unfold horizon; positivity) t ht
  · intro n
    exact candidate_continuous_paths Q B hB (horizon n) (by unfold horizon; positivity)

/-- Actual finite-dimensional Brownian laws and actual sample-path continuity
hold for the constructed global process. -/
theorem isBrownianReal : IsBrownianReal (process B) Q where
  toIsPreBrownianReal := hB.congr (fun t => (process_ae Q B hB t).symm)
  cont := process_continuous Q B hB

/-- A genuine Brownian modification adapted to the original filtration is
constructed from a merely pre-Brownian adapted process. -/
theorem exists_adapted_brownian_modification (F : Filtration ℝ≥0 mΩ)
    (hA : StronglyAdapted F B) :
    ∃ C : ℝ≥0 → Ω → ℝ,
      IsBrownianReal C Q ∧ StronglyAdapted F C ∧ ∀ t, C t =ᵐ[Q] B t :=
  ⟨process B, isBrownianReal Q B hB, process_stronglyAdapted F B hA, process_ae Q B hB⟩
end PBGSO.AdaptedBrownianModification
