import ProximalLangevin.SplittingLaw
import IPLA.AlgorithmLaw
import UnadjustedLangevin.GaussianInnovationVectors

set_option linter.style.header false

/-!
# Canonical Gaussian law of the actual PIPGLA algorithm

The scalar-coordinate Gaussian laws and independence in
`IPLA.GaussianInnovations` determine the full iid vector noise path.  Applying
the actual PIPGLA recursion therefore gives the same output law in every
probability realization with the same initialization law.  No Gibbs target,
stationary reference, or convergence estimate is assumed in these identities.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ProximalLangevin

variable {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
  {N dθ dx : ℕ} (hN : 0 < N)
  {g₁ g₂ : IPLA.Joint dθ dx → ℝ} {L₁ : ℝ≥0}
  (hg₁ : Differentiable ℝ g₁) (hLip : LipschitzWith L₁ (gradient g₁))
  (hg₂ : ConvexOn ℝ Set.univ g₂) (hb : ∃ b : ℝ, ∀ z, b ≤ g₂ z)
  {lam : ℝ} (hlam : 0 < lam) (γ : ℝ)

include hN hg₁ hLip hg₂ hb hlam

/-- The full iid vector Gaussian algorithm law follows from the original
scalar-coordinate Gaussian hypotheses. -/
theorem pipglaLaws_eq_canonicalGaussian
    (initial : Lp (IPLA.State N dθ dx) 2 Q)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 Q)
    (hGaussian : IPLA.GaussianInnovations Q initial noise) (n : ℕ) :
    pipglaLaws Q g₁ (prox g₂ lam) γ initial (fun k ↦ noise k) n =
      ULA.chainLaw (pipglaUpdate g₁ (prox g₂ lam) γ) (Q.map initial)
        (Measure.infinitePi (fun _ : ℕ ↦ stdGaussian (IPLA.State N dθ dx))) n := by
  exact pipglaLaws_eq_canonical Q hN hg₁ hLip hg₂ hb hlam γ initial (fun k ↦ noise k)
    (Lp.aestronglyMeasurable initial).aemeasurable
    (fun k ↦ (Lp.aestronglyMeasurable (noise k)).aemeasurable)
    hGaussian.independentInitial
    (ULA.gaussianInnovations_vectorIndependent Q (fun k ↦ noise k)
      (fun k ↦ (Lp.aestronglyMeasurable (noise k)).aemeasurable)
      hGaussian.coordinateLaw hGaussian.independent)
    (stdGaussian (IPLA.State N dθ dx))
    (ULA.gaussianInnovations_vectorLaw Q (fun k ↦ noise k)
      (fun k ↦ (Lp.aestronglyMeasurable (noise k)).aemeasurable)
      hGaussian.coordinateLaw hGaussian.independent) n

/-- An equivalent canonical law uses the repository's single countable
product of scalar Gaussian coordinates, grouped into vector innovations. -/
theorem pipglaLaws_eq_canonicalNoisePath
    (initial : Lp (IPLA.State N dθ dx) 2 Q)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 Q)
    (hGaussian : IPLA.GaussianInnovations Q initial noise) (n : ℕ) :
    pipglaLaws Q g₁ (prox g₂ lam) γ initial (fun k ↦ noise k) n =
      ULA.chainLaw (pipglaUpdate g₁ (prox g₂ lam) γ) (Q.map initial)
        (IPLA.canonicalNoisePathLaw N dθ dx) n := by
  unfold pipglaLaws
  simp_rw [pipglaChain_eq_noiseDrivenChain]
  rw [ULA.noiseDrivenChain_law_of_indep Q _
    (pipglaUpdate_measurable hN hg₁ hLip hg₂ hb hlam γ)
    initial (fun ω n ↦ noise n ω) (Lp.aestronglyMeasurable initial).aemeasurable
    (aemeasurable_pi_iff.mpr fun k ↦ (Lp.aestronglyMeasurable (noise k)).aemeasurable)
    hGaussian.independentInitial n, hGaussian.noisePath_law Q initial noise]

/-- Gaussian realizations on different probability spaces give identical
actual PIPGLA output laws when the initialization laws agree. -/
theorem pipglaLaws_eq_of_initialLaw_eq
    {Ω' : Type*} [MeasurableSpace Ω'] (Q' : Measure Ω') [IsProbabilityMeasure Q']
    (initial : Lp (IPLA.State N dθ dx) 2 Q)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 Q)
    (initial' : Lp (IPLA.State N dθ dx) 2 Q')
    (noise' : ℕ → Lp (IPLA.State N dθ dx) 2 Q')
    (hGaussian : IPLA.GaussianInnovations Q initial noise)
    (hGaussian' : IPLA.GaussianInnovations Q' initial' noise')
    (hinitial : Q.map initial = Q'.map initial') (n : ℕ) :
    pipglaLaws Q g₁ (prox g₂ lam) γ initial (fun k ↦ noise k) n =
      pipglaLaws Q' g₁ (prox g₂ lam) γ initial' (fun k ↦ noise' k) n := by
  rw [pipglaLaws_eq_canonicalGaussian Q hN hg₁ hLip hg₂ hb hlam γ initial noise hGaussian n,
    pipglaLaws_eq_canonicalGaussian Q' hN hg₁ hLip hg₂ hb hlam γ initial' noise' hGaussian' n,
    hinitial]

end ProximalLangevin
