import IPLA.Dynamics
import IPLA.ProductReference
import Mathlib.Probability.Independence.InfinitePi

set_option linter.style.header false

/-! # The canonical law of Gaussian IPLA

The coordinate laws and independence fields of `GaussianInnovations` determine
the entire noise-path law. Packing a single countable product of standard real
Gaussian coordinates avoids any assumed grouping of independent vector blocks.
Initialization is independent of that path by the existing algorithm hypothesis.
The actual IPLA output laws therefore depend only on the initialization law,
the potential, and the step size, irrespective of their probability realization.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace IPLA

/-- A coordinate records the iteration and the parameter or particle block. -/
abbrev NoiseCoordinate (N dθ dx : ℕ) := ℕ × (Fin dθ ⊕ (Fin N × Fin dx))

/-- The canonical scalar noise source: independent standard real Gaussians. -/
def canonicalFlatNoiseLaw (N dθ dx : ℕ) : Measure (NoiseCoordinate N dθ dx → ℝ) :=
  Measure.infinitePi (fun _ ↦ gaussianReal 0 1)

/-- Group scalar coordinates into the Euclidean noise vector at each time. -/
def packNoisePath {N dθ dx : ℕ} (w : NoiseCoordinate N dθ dx → ℝ) : ℕ → State N dθ dx :=
  fun k ↦ WithLp.toLp 2 (fun a ↦ w (k, a))

/-- Packing the countable coordinate source is measurable. -/
theorem packNoisePath_measurable (N dθ dx : ℕ) :
    Measurable (@packNoisePath N dθ dx) := by
  refine measurable_pi_iff.mpr fun k ↦ ?_
  exact (WithLp.measurable_toLp 2 _).comp
    (measurable_pi_iff.mpr fun a ↦ measurable_pi_apply (k, a))

/-- The canonical vector-valued Gaussian noise-path law. -/
def canonicalNoisePathLaw (N dθ dx : ℕ) : Measure (ℕ → State N dθ dx) :=
  (canonicalFlatNoiseLaw N dθ dx).map packNoisePath

instance canonicalFlatNoiseLaw_isProbabilityMeasure (N dθ dx : ℕ) :
    IsProbabilityMeasure (canonicalFlatNoiseLaw N dθ dx) := by
  unfold canonicalFlatNoiseLaw
  infer_instance

instance canonicalNoisePathLaw_isProbabilityMeasure (N dθ dx : ℕ) :
    IsProbabilityMeasure (canonicalNoisePathLaw N dθ dx) := by
  unfold canonicalNoisePathLaw
  infer_instance

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

/-- The Gaussian coordinate hypotheses identify the complete flattened path law. -/
theorem GaussianInnovations.flatNoisePath_law {N dθ dx : ℕ}
    (initial : Lp (State N dθ dx) 2 P) (noise : ℕ → Lp (State N dθ dx) 2 P)
    (hGaussian : GaussianInnovations P initial noise) :
    P.map (fun ω (j : NoiseCoordinate N dθ dx) ↦ noise j.1 ω j.2) =
      canonicalFlatNoiseLaw N dθ dx := by
  have hp := hGaussian.independent.map_fun_eq_infinitePi_map₀'
    (fun j : NoiseCoordinate N dθ dx ↦ (hGaussian.coordinateLaw j.1 j.2).aemeasurable)
  simpa only [canonicalFlatNoiseLaw, (hGaussian.coordinateLaw _ _).map_eq] using hp

/-- The vector-valued path law is derived from the scalar Gaussian hypotheses,
including every coordinate and every iteration. -/
theorem GaussianInnovations.noisePath_law {N dθ dx : ℕ}
    (initial : Lp (State N dθ dx) 2 P) (noise : ℕ → Lp (State N dθ dx) 2 P)
    (hGaussian : GaussianInnovations P initial noise) :
    P.map (fun ω k ↦ noise k ω) = canonicalNoisePathLaw N dθ dx := by
  have hflat : AEMeasurable (fun ω (j : NoiseCoordinate N dθ dx) ↦ noise j.1 ω j.2) P :=
    aemeasurable_pi_iff.mpr fun j ↦ (hGaussian.coordinateLaw j.1 j.2).aemeasurable
  rw [canonicalNoisePathLaw, ← hGaussian.flatNoisePath_law P initial noise]
  rw [AEMeasurable.map_map_of_aemeasurable
    (packNoisePath_measurable N dθ dx).aemeasurable hflat]
  congr 1

/-- The generic ULA update for `U_N` is exactly the scaled IPLA update. -/
theorem pointwiseUpdate_eq_scaledUpdate {N dθ dx : ℕ} (U : Joint dθ dx → ℝ) (γ : ℝ)
    (z ξ : State N dθ dx) :
    pointwiseUpdate (potential U) (γ / N) z ξ = scaledUpdate U γ z ξ := by
  simp only [pointwiseUpdate, scaledUpdate, mul_div_assoc]

/-- Exact identification of the generic noise recursion with the IPLA recursion. -/
theorem noiseDrivenChain_eq_scaledChain {N dθ dx : ℕ} (U : Joint dθ dx → ℝ) (γ : ℝ)
    (initial : State N dθ dx) (noise : ℕ → State N dθ dx) (k : ℕ) :
    ULA.noiseDrivenChain (pointwiseUpdate (potential U) (γ / N)) initial noise k =
      scaledChain U γ initial noise k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [ULA.noiseDrivenChain_succ, scaledChain_succ, ih, pointwiseUpdate_eq_scaledUpdate]

variable [IsProbabilityMeasure P]

/-- The law in the IPLA convergence statement is the canonical law of the
actual Gaussian algorithm. No reference process is involved in this result. -/
theorem laws_eq_canonicalChainLaw {N dθ dx : ℕ} (U : Joint dθ dx → ℝ) (γ : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (initial : Lp (State N dθ dx) 2 P) (noise : ℕ → Lp (State N dθ dx) 2 P)
    (hGaussian : GaussianInnovations P initial noise) (k : ℕ) :
    laws P U γ L hdiff hLip initial noise k =
      ULA.chainLaw (pointwiseUpdate (potential U) (γ / N)) (P.map initial)
        (canonicalNoisePathLaw N dθ dx) k := by
  rw [laws_eq_scaledChain P U γ L hdiff hLip initial noise k]
  simp_rw [← noiseDrivenChain_eq_scaledChain]
  rw [ULA.noiseDrivenChain_law_of_indep P _
    (pointwiseUpdate_measurable (potential U) (γ / N) ((N : ℝ≥0) * L)
      (potential_gradient_lipschitz hdiff hLip))
    initial (fun ω n ↦ noise n ω) (Lp.aestronglyMeasurable initial).aemeasurable
    (aemeasurable_pi_iff.mpr fun n ↦ (Lp.aestronglyMeasurable (noise n)).aemeasurable)
    hGaussian.independentInitial k, hGaussian.noisePath_law P initial noise]

/-- Two Gaussian implementations of IPLA with the same initial law have the
same output law, even when they use different underlying probability spaces. -/
theorem laws_eq_of_initialLaw_eq
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    {N dθ dx : ℕ} (U : Joint dθ dx → ℝ) (γ : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (initial : Lp (State N dθ dx) 2 P) (noise : ℕ → Lp (State N dθ dx) 2 P)
    (initial' : Lp (State N dθ dx) 2 P') (noise' : ℕ → Lp (State N dθ dx) 2 P')
    (hGaussian : GaussianInnovations P initial noise)
    (hGaussian' : GaussianInnovations P' initial' noise')
    (hinitial : P.map initial = P'.map initial') (k : ℕ) :
    laws P U γ L hdiff hLip initial noise k =
      laws P' U γ L hdiff hLip initial' noise' k := by
  rw [laws_eq_canonicalChainLaw P U γ L hdiff hLip initial noise hGaussian k,
    laws_eq_canonicalChainLaw P' U γ L hdiff hLip initial' noise' hGaussian' k, hinitial]

end IPLA
