import PBGSO.RawDampedState
import PBGSO.RawLocalPullbackLocal

/-! # Original local raw equations under measure-preserving pullback
The actual local-integral identity is derived without a global expected
coefficient square. State, drift, variation control and original initial
moment are transported, preserving the literal original raw equation.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.RawDampedState
open FilteredBrownian
variable {Ω Ω' I Z : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
  [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {R : Measure Ω'} [IsProbabilityMeasure R]
  {f : Ω → Ω'} (hf : MeasurePreserving f Q R)
  {D : Driver (I := I) R} (E : Driver (I := I) Q)
  (he : ∀ t, (pullbackDriver hf D).filtration t ≤ E.filtration t)
  (hp : ∀ i t, (pullbackDriver hf D).process i t =ᵐ[Q] E.process i t)
  {T : ℝ≥0} {L : RawLocalDiffusion (Z := Z) R D T}

/-- The genuine original strong equation on a pulled, possibly enlarged
Brownian past. Noise and law compatibility are derived by construction. -/
def Data.pullback (U : Data L) : Data (L.pullback hf E he) where
  state r ω := U.state r (f ω)
  drift r ω := U.drift r (f ω)
  state_strong := U.state_strong.comp_measurable
    (measurable_fst.prodMk (hf.measurable.comp measurable_snd))
  drift_strong := U.drift_strong.comp_measurable
    (measurable_fst.prodMk (hf.measurable.comp measurable_snd))
  drift_control r ω := U.drift_control r (f ω)
  initial_square := U.initial_square.comp_measurePreserving hf
  state_adapted t := by
    refine ⟨(U.state_adapted t).mk (U.state t) ∘ f, ?_, ?_⟩
    · exact (U.state_adapted t).stronglyMeasurable_mk.comp_measurable
        (measurable_iff_comap_le.mpr (he t))
    · exact hf.quasiMeasurePreserving.ae_eq_comp (U.state_adapted t).ae_eq_mk
  state_continuous := hf.quasiMeasurePreserving.ae U.state_continuous
  equation := by
    filter_upwards [hf.quasiMeasurePreserving.ae U.equation,
      L.pullback_localNoise_on_horizon hf E he hp] with ω hu hn r hr
    rw [hn r.toNNReal ((Real.toNNReal_le_iff_le_coe).mpr hr.2)]
    exact hu r hr

@[simp] theorem Data.pullback_state (U : Data L) (r : ℝ) (ω : Ω) :
    (U.pullback hf E he hp).state r ω = U.state r (f ω) := rfl

end PBGSO.RawDampedState
