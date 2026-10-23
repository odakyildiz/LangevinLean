import KIPLMC.Geometry
import KineticLangevin.Gaussian

/-! # The actual correlated KIPLMC1 innovation measure

Every spatial coordinate receives the same two-dimensional Gaussian pair
constructed by the shared kinetic library. Distinct spatial coordinates are
independent, while velocity and position within each pair retain their Gram
covariance. This works directly with IPLA's arbitrary particle index set.
-/

noncomputable section
set_option linter.style.header false
open MeasureTheory ProbabilityTheory
namespace KIPLMC

/-- The spatial coordinate set of the scaled particle state. -/
abbrev Coordinate (N dθ dx : ℕ) := Fin dθ ⊕ (Fin N × Fin dx)

/-- Independent copies of the shared two-dimensional kinetic Gaussian. -/
def exponentialNoiseBlocks (N dθ dx : ℕ) (γ h : ℝ) :
    Measure (Coordinate N dθ dx → EuclideanSpace ℝ (Fin 2)) :=
  Measure.pi (fun _ ↦ KineticLangevin.klmcGaussian γ h)

instance exponentialNoiseBlocks_probability (N dθ dx : ℕ) (γ h : ℝ) :
    IsProbabilityMeasure (exponentialNoiseBlocks N dθ dx γ h) := by
  unfold exponentialNoiseBlocks
  infer_instance

/-- Reorganize coordinate pairs into a velocity vector and a position vector. -/
def assembleExponentialNoise {N dθ dx : ℕ}
    (ω : Coordinate N dθ dx → EuclideanSpace ℝ (Fin 2)) :
    State N dθ dx × State N dθ dx :=
  (WithLp.toLp 2 (fun i ↦ ω i 0), WithLp.toLp 2 (fun i ↦ ω i 1))

theorem assembleExponentialNoise_measurable (N dθ dx : ℕ) :
    Measurable (@assembleExponentialNoise N dθ dx) := by
  unfold assembleExponentialNoise
  fun_prop

/-- One actual KIPLMC1 phase innovation before the factor `sqrt (2γ/N)`. -/
def exponentialNoise (N dθ dx : ℕ) (γ h : ℝ) :
    Measure (State N dθ dx × State N dθ dx) :=
  (exponentialNoiseBlocks N dθ dx γ h).map assembleExponentialNoise

instance exponentialNoise_probability (N dθ dx : ℕ) (γ h : ℝ) :
    IsProbabilityMeasure (exponentialNoise N dθ dx γ h) := by
  constructor
  rw [exponentialNoise, Measure.map_apply (assembleExponentialNoise_measurable N dθ dx)
    MeasurableSet.univ, Set.preimage_univ, measure_univ]

/-- The coordinate blocks are independent on the constructed probability space. -/
theorem exponentialNoiseBlocks_independent (N dθ dx : ℕ) (γ h : ℝ) :
    iIndepFun (fun i (ω : Coordinate N dθ dx → EuclideanSpace ℝ (Fin 2)) ↦ ω i)
      (exponentialNoiseBlocks N dθ dx γ h) := by
  exact iIndepFun_pi (fun _ ↦ measurable_id.aemeasurable)

/-- Each velocity-position coordinate pair has the exact shared Gaussian law.
The common covariance is the proved Gram matrix, not an independence premise
between velocity and position. -/
theorem exponentialNoise_coordinate_law (N dθ dx : ℕ) (γ h : ℝ)
    (i : Coordinate N dθ dx) :
    (exponentialNoise N dθ dx γ h).map
      (fun z ↦ WithLp.toLp 2 (fun j : Fin 2 ↦ if j = 0 then z.1 i else z.2 i)) =
      KineticLangevin.klmcGaussian γ h := by
  rw [exponentialNoise, Measure.map_map (by fun_prop) (assembleExponentialNoise_measurable N dθ dx)]
  change (exponentialNoiseBlocks N dθ dx γ h).map
    (fun ω ↦ WithLp.toLp 2 (fun j : Fin 2 ↦ if j = 0 then (assembleExponentialNoise ω).1 i
      else (assembleExponentialNoise ω).2 i)) = _
  have he : (fun ω : Coordinate N dθ dx → EuclideanSpace ℝ (Fin 2) ↦
      WithLp.toLp 2 (fun j : Fin 2 ↦ if j = 0 then (assembleExponentialNoise ω).1 i
        else (assembleExponentialNoise ω).2 i)) = fun ω ↦ ω i := by
    funext ω
    ext j
    fin_cases j <;> simp [assembleExponentialNoise]
  rw [he]
  exact (measurePreserving_eval
    (fun _ : Coordinate N dθ dx ↦ KineticLangevin.klmcGaussian γ h) i).map_eq

end KIPLMC
