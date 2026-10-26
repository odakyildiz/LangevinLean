import PBGSO.FilteredBrownian
import PBGSO.BrownianVectorFiltration

/-! # The actual canonical vector Brownian driver with random initial state
The full joint natural filtration contains the initial state and every
spatial Brownian past. Independence and adaptation are derived from the
actual product source, without a supplied future-past independence premise.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace PBGSO.CanonicalBrownianDriver
variable {Z I : Type*} [MeasurableSpace Z] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [BorelSpace Z] [SecondCountableTopology Z]
  (μ : Measure Z) [IsProbabilityMeasure μ]

/-- Actual Brownian coordinates on independent initial-state/noise seeds. -/
def coordinate (i : I) (t : ℝ≥0) (p : Z × ULA.CanonicalBrownian.VectorSample I) : ℝ :=
  ULA.CanonicalBrownian.coordinate i t p.2

/-- Each coordinate is adapted to the full joint initial/noise filtration. -/
theorem coordinate_adapted (i : I) :
    StronglyAdapted (CanonicalInitialFiltration.filtration (Z := Z) (I := I))
      (coordinate (Z := Z) i) := by
  intro t
  have h : StronglyMeasurable[CanonicalInitialFiltration.filtration (Z := Z) (I := I) t]
      (CanonicalInitialFiltration.process (Z := Z) (I := I) t) :=
    Filtration.stronglyAdapted_natural
      (fun r ↦ (CanonicalInitialFiltration.process_measurable (Z := Z) (I := I) r).stronglyMeasurable) t
  exact ((continuous_apply i).comp continuous_snd).comp_stronglyMeasurable h

/-- Spatial increment independence follows from the independent complete
coordinate Brownian sources after the actual random-initial pullback. -/
theorem increment_coordinates_independent (s t : ℝ≥0) :
    iIndepFun (fun (i : I) (p : Z × ULA.CanonicalBrownian.VectorSample I) ↦
      coordinate i t p - coordinate i s p) (μ.prod (ULA.CanonicalBrownian.vectorProbability I)) := by
  let R := ULA.CanonicalBrownian.vectorProbability I
  let X := fun i (ω : ULA.CanonicalBrownian.VectorSample I) ↦
    ULA.CanonicalBrownian.coordinate i t ω - ULA.CanonicalBrownian.coordinate i s ω
  have hX (i : I) : HasLaw (X i) (R.map (X i)) R :=
    ⟨(((ULA.CanonicalBrownian.process_measurable t).comp (measurable_pi_apply i)).sub
      ((ULA.CanonicalBrownian.process_measurable s).comp (measurable_pi_apply i))).aemeasurable, rfl⟩
  have hi : iIndepFun X R := (ULA.CanonicalBrownian.coordinate_paths_independent I).comp
    (fun _ p ↦ p t - p s) (fun _ ↦ (measurable_pi_apply t).sub (measurable_pi_apply s))
  have hfull := (hi.hasLaw_pi hX).comp
    (measurePreserving_snd (μ := μ) (ν := R)).hasLaw
  exact (iIndepFun_iff_hasLaw_pi_pi (fun i ↦ (hX i).comp
    (measurePreserving_snd (μ := μ) (ν := R)).hasLaw)).mpr hfull

/-- The complete future increment vector is independent of the whole
initial-state and joint Brownian past, not only of each coordinate past. -/
theorem future_independent (s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap
      (fun p : Z × ULA.CanonicalBrownian.VectorSample I ↦ fun i ↦ coordinate i t p - coordinate i s p)
      inferInstance) (CanonicalInitialFiltration.filtration (Z := Z) (I := I) s)
      (μ.prod (ULA.CanonicalBrownian.vectorProbability I)) := by
  have hi := (canonical_brownian_future_initial_past_independent (I := I) μ s).comp
    (measurable_pi_iff.mpr fun i ↦ (measurable_pi_apply (t - s)).comp (measurable_pi_apply i))
    (measurable_pi_iff.mpr fun u : Iic s ↦ measurable_fst.prodMk
      (measurable_pi_iff.mpr fun j ↦
        ((measurable_pi_apply u).comp (measurable_pi_apply j)).comp measurable_snd))
  rw [CanonicalInitialFiltration.filtration, Filtration.natural_eq_comap]
  change IndepFun (fun p : Z × ULA.CanonicalBrownian.VectorSample I ↦ fun i ↦
    coordinate i t p - coordinate i s p)
    (fun p (u : Iic s) ↦ CanonicalInitialFiltration.process u p) _
  change IndepFun (fun p : Z × ULA.CanonicalBrownian.VectorSample I ↦ fun i ↦
    ULA.CanonicalBrownian.coordinate i (s + (t - s)) p.2 -
      ULA.CanonicalBrownian.coordinate i s p.2)
    (fun p (u : Iic s) ↦ CanonicalInitialFiltration.process u p) _ at hi
  rwa [add_tsub_cancel_of_le hst] at hi

/-- A fully constructed primitive vector Brownian Driver on the actual
independent random-initial/noise space and its full natural filtration. -/
def driver : FilteredBrownian.Driver (I := I) (μ.prod (ULA.CanonicalBrownian.vectorProbability I)) where
  process := coordinate
  brownian i := ⟨fun s ↦ (ULA.CanonicalBrownian.coordinate_isPreBrownian i).hasLaw s |>.comp
    (measurePreserving_snd (μ := μ) (ν := ULA.CanonicalBrownian.vectorProbability I)).hasLaw⟩
  filtration := CanonicalInitialFiltration.filtration
  adapted := coordinate_adapted
  increment_coordinates := fun s t _ ↦ increment_coordinates_independent μ s t
  future_independent := future_independent μ

end PBGSO.CanonicalBrownianDriver
