import UnadjustedLangevin.ProductBrownian
import IPLA.AlgorithmLaw
import UnadjustedLangevin.GibbsStationarity
import UnadjustedLangevin.GaussianInnovationVectors

set_option linter.style.header false

/-! # IPLA adaptation of the shared ULA Brownian construction

The Langevin reference, stochastic laws, and Dalalyan estimate are implemented
in `UnadjustedLangevin`. This file only packages those facts in IPLA's block
coordinates and identifies them with the algorithm's Gaussian innovations.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace IPLA
open ULA ULA.Hilbert

section Algorithm

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
  (Q : Measure S) [IsProbabilityMeasure Q]
  {N dθ dx : ℕ} {μ π : Measure (State N dθ dx)} [IsProbabilityMeasure μ]

local instance algorithmProductProbability (c : Coupling μ π) :
    IsProbabilityMeasure (initialExtension c Q) := initialExtension_isProbabilityMeasure c Q

/-- The concrete product realization satisfies every distributional field of
the actual IPLA algorithm. Standard Gaussian laws and all independence claims
are conclusions from the independent Brownian coordinate source. -/
theorem productGaussianInnovations (c : Coupling μ π) (hc : couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (fun x : State N dθ dx ↦ x) 2 π)
    (B : (Fin dθ ⊕ (Fin N × Fin dx)) → ℝ≥0 → S → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) Q) (h : ℝ) (hh : 0 < h)
    (hpaths : iIndepFun (fun i ω (n : ℕ) ↦ B i ((n : ℝ≥0) * h.toNNReal) ω) Q) :
    GaussianInnovations (initialExtension c Q) (initialExtension_lpInitial c Q hc hπ)
      (productNoise Q c (sourceEulerNoise Q B hB h) (sourceEulerNoise_memLp Q B hB h)) where
  coordinateLaw := productEulerNoise_coordinateLaw Q c B hB h hh
  independent := productEulerNoise_independent Q c B hB h hh hpaths
  independentInitial := productEulerNoise_independentInitial Q c hc hπ B hB h

/-- The law produced by the Brownian product construction is exactly the law
of any supplied Gaussian IPLA implementation with the same initialization.
This bridge has no stationarity or reference-process hypothesis. -/
theorem laws_eq_productBrownianOutput
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Joint dθ dx → ℝ) (γ : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (initial : Lp (State N dθ dx) 2 P) (noise : ℕ → Lp (State N dθ dx) 2 P)
    (hGaussian : GaussianInnovations P initial noise)
    (π : Measure (State N dθ dx)) (c : Coupling (P.map initial) π)
    (hc : couplingCost c.joint ≠ ⊤) (hπ : MemLp (fun x : State N dθ dx ↦ x) 2 π)
    (B : (Fin dθ ⊕ (Fin N × Fin dx)) → ℝ≥0 → S → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) Q) (hh : 0 < γ / N)
    (hpaths : iIndepFun (fun i ω (n : ℕ) ↦ B i ((n : ℝ≥0) * (γ / N).toNNReal) ω) Q)
    (k : ℕ) :
    laws P U γ L hdiff hLip initial noise k =
      productOutputLaw Q (potential U) (γ / N) (P.map initial)
        (sourceEulerNoise Q B hB (γ / N)) k := by
  have : IsProbabilityMeasure (P.map initial) := inferInstance
  have : IsProbabilityMeasure (initialExtension c Q) := initialExtension_isProbabilityMeasure c Q
  have heq := laws_eq_of_initialLaw_eq P (initialExtension c Q) U γ L hdiff hLip
    initial noise (initialExtension_lpInitial c Q hc hπ)
      (productNoise Q c (sourceEulerNoise Q B hB (γ / N))
        (sourceEulerNoise_memLp Q B hB (γ / N)))
    hGaussian (productGaussianInnovations Q c hc hπ B hB (γ / N) hh hpaths)
      (initialExtension_lpInitial_law c Q hc hπ).symm k
  rw [heq, laws]
  exact product_chain_outputLaw Q c hc hπ (potential U) (γ / N) ((N : ℝ≥0) * L)
    (potential_gradient_lipschitz hdiff hLip) (sourceEulerNoise Q B hB (γ / N))
    (sourceEulerNoise_memLp Q B hB (γ / N)) k

/-- The actual IPLA law is precisely ULA for the rescaled lifted potential.
All vector Gaussian and independence facts follow from the displayed scalar
innovation specification of the algorithm. -/
theorem laws_eq_ulaLawStep
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Joint dθ dx → ℝ) (γ : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (initial : Lp (State N dθ dx) 2 P) (noise : ℕ → Lp (State N dθ dx) 2 P)
    (hGaussian : GaussianInnovations P initial noise) (k : ℕ) :
    laws P U γ L hdiff hLip initial noise k =
      (ULA.ulaLawStep (potential U) (γ / N))^[k] (P.map initial) := by
  have hW : ∀ n, AEMeasurable (noise n) P :=
    fun n ↦ (Lp.aestronglyMeasurable (noise n)).aemeasurable
  exact ULA.hilbert_lpChain_law_eq_ulaLawStep P (potential U) (γ / N)
    ((N : ℝ≥0) * L) (potential_gradient_lipschitz hdiff hLip) initial noise
    hGaussian.independentInitial
    (ULA.gaussianInnovations_vectorIndependent P (fun n ω ↦ noise n ω)
      hW hGaussian.coordinateLaw hGaussian.independent)
    (ULA.gaussianInnovations_vectorLaw P (fun n ω ↦ noise n ω)
      hW hGaussian.coordinateLaw hGaussian.independent) k

end Algorithm
end IPLA
