import PBGSO.CanonicalBrownianDriver
import PBGSO.ParticleNoiseSpace

/-! # Actual filtered Brownian drivers under probability-space pullback
A measure-preserving source map transports the full filtration and all
primitive Brownian-driver properties. The actual iid particle seed space is
instantiated by its proved joint initial-cloud and whole-noise product law.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace PBGSO.FilteredBrownian
section Pullback
variable {Ω Ω' I : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
  [Fintype I] [DecidableEq I]
  {Q : Measure Ω} [IsProbabilityMeasure Q] {R : Measure Ω'} [IsProbabilityMeasure R]
  {f : Ω → Ω'} (hf : MeasurePreserving f Q R)

include hf

/-- Independence of actual sub-sigma-algebras survives a measure-preserving
pullback, proved directly on their measurable sets. -/
theorem independent_comap (m n : MeasurableSpace Ω') (hm : m ≤ mΩ') (hn : n ≤ mΩ')
    (hi : Indep m n R) : Indep (m.comap f) (n.comap f) Q := by
  apply (Indep_iff _ _ _).mpr
  intro a b ha hb
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  letI : MeasurableSpace Ω' := mΩ'
  have hma : @MeasurableSet Ω' mΩ' a' := hm a' ha'
  have hmb : @MeasurableSet Ω' mΩ' b' := hn b' hb'
  have hp (s : Set Ω') (hs : MeasurableSet s) : Q (f ⁻¹' s) = R s := by
    rw [← hf.map_eq, Measure.map_apply hf.measurable hs]
  rw [← preimage_inter, hp _ (hma.inter hmb),
    hp _ hma, hp _ hmb]
  exact (Indep_iff _ _ _).mp hi a' b' ha' hb'

/-- The actual source filtration, with no limiting or adaptedness premise. -/
def pullbackFiltration (D : Driver (I := I) R) : Filtration ℝ≥0 mΩ where
  seq t := (D.filtration t).comap f
  mono' _ _ h := MeasurableSpace.comap_mono (D.filtration.mono h)
  le' t := (MeasurableSpace.comap_mono (D.filtration.le t)).trans hf.measurable.comap_le

/-- The whole vector filtered Brownian driver on the actual pulled source. -/
def pullbackDriver (D : Driver (I := I) R) : Driver (I := I) Q where
  process i t ω := D.process i t (f ω)
  brownian i := ⟨fun s ↦ (D.brownian i).hasLaw s |>.comp hf.hasLaw⟩
  filtration := pullbackFiltration hf D
  adapted i t := (D.adapted i t).comp_measurable (measurable_iff_comap_le.mpr le_rfl)
  increment_coordinates s t hst := by
    let X := fun i ω ↦ D.process i t ω - D.process i s ω
    have hm (i : I) : Measurable (X i) := increment_measurable R D s t i
    have hX (i : I) : HasLaw (X i) (R.map (X i)) R := ⟨(hm i).aemeasurable, rfl⟩
    have hi := ((D.increment_coordinates s t hst).hasLaw_pi hX).comp hf.hasLaw
    exact (iIndepFun_iff_hasLaw_pi_pi (fun i ↦ (hX i).comp hf.hasLaw)).mpr hi
  future_independent s t hst := by
    have hi := independent_comap hf
      (MeasurableSpace.comap (fun ω i ↦ D.process i t ω - D.process i s ω) inferInstance)
      (D.filtration s)
      ((measurable_pi_iff.mpr fun i ↦ increment_measurable R D s t i).comap_le)
      (D.filtration.le s) (D.future_independent s t hst)
    simpa only [pullbackFiltration, MeasurableSpace.comap_comp, Function.comp_def] using hi

@[simp] theorem pullbackDriver_process (D : Driver (I := I) R) (i : I) (t : ℝ≥0) (ω : Ω) :
    (pullbackDriver hf D).process i t ω = D.process i t (f ω) := rfl

end Pullback
end PBGSO.FilteredBrownian

namespace PBGSO.ParticleBrownianDriver
variable {Z J : Type*} [NormedAddCommGroup Z] [MeasurableSpace Z]
  [BorelSpace Z] [SecondCountableTopology Z] [Fintype J] [DecidableEq J]
  (μ : Measure Z) [IsProbabilityMeasure μ] (N : ℕ)

/-- A fully constructed filtered vector Brownian driver on actual independent
complete particle seeds. Its initial cloud and full flattened noise law are
proved, rather than supplied as independence assumptions. -/
def driver : FilteredBrownian.Driver (I := Fin N × J) (ParticleNoiseSpace.probability (J := J) μ N) :=
  FilteredBrownian.pullbackDriver (ParticleNoiseSpace.initial_noise_preserving (J := J) μ N)
    (CanonicalBrownianDriver.driver (I := Fin N × J) (Measure.pi fun _ : Fin N ↦ μ))

/-- Its process is exactly the original flattened per-particle coordinate. -/
@[simp] theorem driver_process (ij : Fin N × J) (t : ℝ≥0)
    (ω : Fin N → Z × ULA.CanonicalBrownian.VectorSample J) :
    (driver μ N).process ij t ω = ULA.CanonicalBrownian.coordinate ij.2 t (ω ij.1).2 := rfl

end PBGSO.ParticleBrownianDriver
