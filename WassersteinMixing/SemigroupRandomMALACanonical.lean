import WassersteinMixing.SemigroupRandomMALA
import WassersteinMixing.ActualComparison

/-! # Actual Brownian and uniform realization of the MALA comparison

Independent uniform draws are appended to the canonical Brownian space. The
resulting Gaussian/uniform path has the exact iid product law, and the paired
recursion therefore realizes the existing synchronous coupling measure.
-/
noncomputable section
set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory
open scoped unitInterval NNReal ENNReal

namespace WassersteinMixing.RandomMALA.Canonical

abbrev Space (P : Parameters) := ActualSpace P × (ℕ → I)

def uniformPath : Measure (ℕ → I) := Measure.infinitePi (fun _ : ℕ ↦ (volume : Measure I))

instance uniformPath_isProbability : IsProbabilityMeasure uniformPath := by
  unfold uniformPath
  infer_instance

def probability (P : Parameters) (V : E P.dimension → ℝ) : Measure (Space P) :=
  (actualProbability P V).prod uniformPath

theorem probability_isProbability (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) : IsProbabilityMeasure (probability P V) := by
  let := actualProbability_isProbability P V hV
  unfold probability
  infer_instance

/-- The actual Brownian-normalized Gaussian innovations at an arbitrary refining step. -/
def gaussian (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V)
    (r : ℝ) : ℕ → Lp (E P.dimension) 2 (actualProbability P V) := by
  let := actualTarget_isProbability P V hV
  exact ULA.Hilbert.productNoise
    (ULA.CanonicalBrownian.vectorProbability (Fin P.dimension)) (diagonalGibbsCoupling P V)
    (ULA.Hilbert.canonicalEulerNoise r)
    (ULA.Hilbert.sourceEulerNoise_memLp _ ULA.CanonicalBrownian.coordinate
      ULA.CanonicalBrownian.coordinate_isPreBrownian r)

theorem gaussian_path_law (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (r : ℝ) (hr : 0 < r) :
    (actualProbability P V).map (fun ω n ↦ gaussian P V hV r n ω) =
      Measure.infinitePi (fun _ : ℕ ↦ stdGaussian (E P.dimension)) := by
  let := actualTarget_isProbability P V hV
  let := actualProbability_isProbability P V hV
  apply ULA.gaussianInnovations_pathLaw
  · intro n
    exact (Lp.aestronglyMeasurable _).aemeasurable
  · intro n i
    exact ULA.Hilbert.productEulerNoise_coordinateLaw _ (diagonalGibbsCoupling P V)
      ULA.CanonicalBrownian.coordinate ULA.CanonicalBrownian.coordinate_isPreBrownian r hr n i
  · exact ULA.Hilbert.productEulerNoise_independent _ (diagonalGibbsCoupling P V)
      ULA.CanonicalBrownian.coordinate ULA.CanonicalBrownian.coordinate_isPreBrownian r hr
      (ULA.CanonicalBrownian.coordinate_grid_paths_independent (Fin P.dimension) r.toNNReal)

theorem initial_gaussian_law (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (r : ℝ) (hr : 0 < r) :
    (actualProbability P V).map
      (fun ω ↦ (actualInitial P V hV ω, fun n ↦ gaussian P V hV r n ω)) =
      (ULA.gibbsMeasure V).prod
        (Measure.infinitePi (fun _ : ℕ ↦ stdGaussian (E P.dimension))) := by
  let := actualTarget_isProbability P V hV
  let := actualProbability_isProbability P V hV
  have hc : ULA.couplingCost (diagonalGibbsCoupling P V).joint ≠ ⊤ := by
    rw [diagonalGibbsCoupling_cost]
    exact ENNReal.zero_ne_top
  have hind := ULA.Hilbert.productEulerNoise_independentInitial
    (ULA.CanonicalBrownian.vectorProbability (Fin P.dimension)) (diagonalGibbsCoupling P V)
    hc (actualTarget_memLp P V hV) ULA.CanonicalBrownian.coordinate
    ULA.CanonicalBrownian.coordinate_isPreBrownian r
  change IndepFun (actualInitial P V hV)
    (fun ω n ↦ gaussian P V hV r n ω) (actualProbability P V) at hind
  rw [hind.map_prod_eq_prod_map_map (Lp.aestronglyMeasurable _).aemeasurable
    (aemeasurable_pi_iff.mpr fun n ↦ (Lp.aestronglyMeasurable _).aemeasurable),
    gaussian_path_law P V hV r hr]
  congr 1
  exact ULA.initialExtension_lpInitial_law _ _ hc (actualTarget_memLp P V hV)

def input (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V)
    (r : ℝ) (ω : Space P) : (E P.dimension) × (ℕ → (E P.dimension) × I) :=
  (actualInitial P V hV ω.1, fun n ↦ (gaussian P V hV r n ω.1, ω.2 n))

theorem input_law (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (r : ℝ) (hr : 0 < r) :
    (probability P V).map (input P V hV r) =
      (ULA.gibbsMeasure V).prod
        (Measure.infinitePi (fun _ : ℕ ↦ innovationLaw)) := by
  let := actualTarget_isProbability P V hV
  let := actualProbability_isProbability P V hV
  exact augment_initial_noise_law (actualProbability P V) (ULA.gibbsMeasure V)
    (stdGaussian (E P.dimension)) (volume : Measure I)
    (actualInitial P V hV) (fun ω n ↦ gaussian P V hV r n ω)
    (Lp.aestronglyMeasurable _).aemeasurable
    (aemeasurable_pi_iff.mpr fun n ↦ (Lp.aestronglyMeasurable _).aemeasurable)
    (initial_gaussian_law P V hV r hr)

/-- The simultaneous ordinary Euler and MALA states, on the actual shared source. -/
def state (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V)
    (r : ℝ) (n : ℕ) (ω : Space P) : E P.dimension × E P.dimension :=
  ULA.noiseDrivenChain (RandomMALA.update V r)
    ((input P V hV r ω).1, (input P V hV r ω).1) (input P V hV r ω).2 n

theorem state_law (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (probability P V).map (state P V hV r n) =
      ULA.malaCoupledChain V r (ULA.gibbsMeasure V) n := by
  let := actualTarget_isProbability P V hV
  have hi : AEMeasurable (input P V hV r) (probability P V) := by
    exact ((Lp.aestronglyMeasurable _).aemeasurable.comp_fst).prodMk
      (aemeasurable_pi_iff.mpr fun n ↦
        ((Lp.aestronglyMeasurable _).aemeasurable.comp_fst).prodMk (by fun_prop))
  let F : (E P.dimension) × (ℕ → (E P.dimension) × I) →
      E P.dimension × E P.dimension :=
    fun p ↦ ULA.noiseDrivenChain (RandomMALA.update V r) (p.1, p.1) p.2 n
  have hF : Measurable F :=
    (ULA.noiseDrivenChain_measurable _
      (update_measurable V r ⟨P.beta, P.beta_pos.le⟩
        (hV.regularity.differentiable (by norm_num)) hV.gradientLipschitz) n).comp
          ((measurable_fst.prodMk measurable_fst).prodMk measurable_snd)
  rw [show state P V hV r n = F ∘ input P V hV r from rfl,
    ← AEMeasurable.map_map_of_aemeasurable hF.aemeasurable hi, input_law P V hV r hr]
  rw [← chainLaw_eq_coupledChain V r ⟨P.beta, P.beta_pos.le⟩
    (hV.regularity.differentiable (by norm_num)) hV.gradientLipschitz (ULA.gibbsMeasure V) n]
  unfold ULA.chainLaw
  have hprod := Measure.map_prod_map (ULA.gibbsMeasure V)
    (Measure.infinitePi (fun _ : ℕ ↦ innovationLaw (E := E P.dimension)))
    (show Measurable (fun x : E P.dimension ↦ (x, x)) by fun_prop) measurable_id
  simp only [Measure.map_id] at hprod
  rw [hprod, Measure.map_map
    (ULA.noiseDrivenChain_measurable _ (update_measurable V r
      ⟨P.beta, P.beta_pos.le⟩ (hV.regularity.differentiable (by norm_num))
      hV.gradientLipschitz) n) (by fun_prop)]
  rfl

end WassersteinMixing.RandomMALA.Canonical
