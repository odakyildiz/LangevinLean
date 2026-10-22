import ProximalLangevin.SplittingContraction
import UnadjustedLangevin.ChainLaw

set_option linter.style.header false

/-! # Actual PIPGLA laws and their square-integrable realizations

The output law is that of the displayed pairwise proximal recursion.
Measurability, finite quadratic moments, and canonical iid law transfer are
proved. No stochastic convergence estimate is supplied to this interface.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ProximalLangevin

theorem pairwiseMap_prox_lipschitz {N dθ dx : ℕ} (hN : 0 < N)
    {g₂ : IPLA.Joint dθ dx → ℝ} (hg₂ : ConvexOn ℝ Set.univ g₂)
    (hb : ∃ b : ℝ, ∀ z, b ≤ g₂ z) {lam : ℝ} (hlam : 0 < lam) :
    LipschitzWith 1 (@pairwiseMap N dθ dx (prox g₂ lam)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using
    pairwiseMap_nonexpansive hN (prox g₂ lam) (prox_lipschitz hg₂ hb hlam) z w

/-- The exact splitting update is jointly measurable in the state and noise. -/
theorem pipglaUpdate_measurable {N dθ dx : ℕ} (hN : 0 < N)
    {g₁ g₂ : IPLA.Joint dθ dx → ℝ} {L₁ : ℝ≥0}
    (hg₁ : Differentiable ℝ g₁) (hLip : LipschitzWith L₁ (gradient g₁))
    (hg₂ : ConvexOn ℝ Set.univ g₂) (hb : ∃ b : ℝ, ∀ z, b ≤ g₂ z)
    {lam : ℝ} (hlam : 0 < lam) (γ : ℝ) :
    Measurable (Function.uncurry (@pipglaUpdate N dθ dx g₁ (prox g₂ lam) γ)) := by
  have hg : Measurable (gradient (@IPLA.potential N dθ dx g₁)) :=
    (IPLA.potential_gradient_lipschitz hg₁ hLip).continuous.measurable
  have hs : Measurable (Function.uncurry (@IPLA.scaledUpdate N dθ dx g₁ γ)) :=
    (measurable_fst.sub ((hg.comp measurable_fst).const_smul (γ / N))).add
      (measurable_snd.const_smul (Real.sqrt (2 * γ / N)))
  exact (pairwiseMap_prox_lipschitz hN hg₂ hb hlam).continuous.measurable.comp hs

/-- The pointwise recursion is the existing generic noise-driven chain. -/
theorem pipglaChain_eq_noiseDrivenChain {N dθ dx : ℕ}
    (g₁ : IPLA.Joint dθ dx → ℝ) (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx)
    (γ : ℝ) (z : IPLA.State N dθ dx) (noise : ℕ → IPLA.State N dθ dx) (n : ℕ) :
    pipglaChain g₁ P γ z noise n = ULA.noiseDrivenChain (pipglaUpdate g₁ P γ) z noise n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change pipglaUpdate g₁ P γ (pipglaChain g₁ P γ z noise n) (noise n) =
        pipglaUpdate g₁ P γ (ULA.noiseDrivenChain (pipglaUpdate g₁ P γ) z noise n) (noise n)
      exact congrArg (fun a ↦ pipglaUpdate g₁ P γ a (noise n)) ih

/-- The law of the actual PIPGLA state after a supplied innovation sequence. -/
def pipglaLaws {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    {N dθ dx : ℕ} (g₁ : IPLA.Joint dθ dx → ℝ)
    (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx) (γ : ℝ)
    (initial : Ω → IPLA.State N dθ dx) (noise : ℕ → Ω → IPLA.State N dθ dx)
    (n : ℕ) : Measure (IPLA.State N dθ dx) :=
  Q.map (fun ω ↦ pipglaChain g₁ P γ (initial ω) (fun k ↦ noise k ω) n)

section LpRealization
variable {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    {N dθ dx : ℕ} (hN : 0 < N)
    {g₁ g₂ : IPLA.Joint dθ dx → ℝ} (lam γ : ℝ) (L₁ : ℝ≥0)
    (hg₁ : Differentiable ℝ g₁) (hLip : LipschitzWith L₁ (gradient g₁))
    (hg₂ : ConvexOn ℝ Set.univ g₂) (hb : ∃ b : ℝ, ∀ z, b ≤ g₂ z)
    (hlam : 0 < lam)

/-- The actual noisy forward step followed by the genuine pairwise
proximal map, represented in L². -/
def lpPipglaUpdate (X Z : Lp (IPLA.State N dθ dx) 2 Q) :
    Lp (IPLA.State N dθ dx) 2 Q :=
  ULA.lpDrift Q (pairwiseMap (prox g₂ lam))
    (pairwiseMap_prox_lipschitz hN hg₂ hb hlam)
    (ULA.lpUlaUpdate Q (@IPLA.potential N dθ dx g₁) (γ / N)
      (IPLA.potential_gradient_lipschitz hg₁ hLip) X Z)

theorem lpPipglaUpdate_coe (X Z : Lp (IPLA.State N dθ dx) 2 Q) :
    lpPipglaUpdate Q hN lam γ L₁ hg₁ hLip hg₂ hb hlam X Z =ᵐ[Q]
      fun ω ↦ pipglaUpdate g₁ (prox g₂ lam) γ (X ω) (Z ω) := by
  filter_upwards [ULA.lpDrift_coe Q (pairwiseMap (prox g₂ lam))
      (pairwiseMap_prox_lipschitz hN hg₂ hb hlam)
      (ULA.lpUlaUpdate Q (@IPLA.potential N dθ dx g₁) (γ / N)
        (IPLA.potential_gradient_lipschitz hg₁ hLip) X Z),
    ULA.lpUlaUpdate_coe Q (@IPLA.potential N dθ dx g₁) (γ / N)
      (IPLA.potential_gradient_lipschitz hg₁ hLip) X Z] with ω h₁ h₂
  rw [lpPipglaUpdate, h₁, h₂]
  congr 2
  have hs : 2 * (γ / N) = 2 * γ / N := by ring
  simp only [hs]

/-- Every iterate is an actual L² random variable. -/
def lpPipglaChain (initial : Lp (IPLA.State N dθ dx) 2 Q)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 Q) : ℕ → Lp (IPLA.State N dθ dx) 2 Q
  | 0 => initial
  | n + 1 => lpPipglaUpdate Q hN lam γ L₁ hg₁ hLip hg₂ hb hlam
      (lpPipglaChain initial noise n) (noise n)

theorem lpPipglaChain_coe (initial : Lp (IPLA.State N dθ dx) 2 Q)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 Q) (n : ℕ) :
    lpPipglaChain Q hN lam γ L₁ hg₁ hLip hg₂ hb hlam initial noise n =ᵐ[Q]
      fun ω ↦ pipglaChain g₁ (prox g₂ lam) γ (initial ω) (fun k ↦ noise k ω) n := by
  induction n with
  | zero => exact Filter.Eventually.of_forall fun _ ↦ rfl
  | succ n ih =>
    filter_upwards [lpPipglaUpdate_coe Q hN lam γ L₁ hg₁ hLip hg₂ hb hlam
      (lpPipglaChain Q hN lam γ L₁ hg₁ hLip hg₂ hb hlam initial noise n) (noise n), ih]
      with ω hu hi
    simpa only [lpPipglaChain, pipglaChain, algorithmChain, hi] using hu

theorem pipglaLaws_eq_lpLaw (initial : Lp (IPLA.State N dθ dx) 2 Q)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 Q) (n : ℕ) :
    pipglaLaws Q g₁ (prox g₂ lam) γ initial (fun k ↦ noise k) n =
      Q.map (lpPipglaChain Q hN lam γ L₁ hg₁ hLip hg₂ hb hlam initial noise n) :=
  Measure.map_congr (lpPipglaChain_coe Q hN lam γ L₁ hg₁ hLip hg₂ hb hlam
    initial noise n).symm

include hN hg₁ hLip hg₂ hb hlam in
theorem pipglaLaws_isProbability (initial : Lp (IPLA.State N dθ dx) 2 Q)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 Q) (n : ℕ) :
    IsProbabilityMeasure (pipglaLaws Q g₁ (prox g₂ lam) γ initial (fun k ↦ noise k) n) := by
  rw [pipglaLaws_eq_lpLaw Q hN lam γ L₁ hg₁ hLip hg₂ hb hlam initial noise n]
  constructor
  rw [Measure.map_apply_of_aemeasurable (Lp.aestronglyMeasurable _).aemeasurable
    MeasurableSet.univ, Set.preimage_univ, measure_univ]

end LpRealization

/-- Any independent iid realization has the canonical splitting law. This
proves law transfer across coupling spaces without a convergence assumption. -/
theorem pipglaLaws_eq_canonical {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] {N dθ dx : ℕ} (hN : 0 < N)
    {g₁ g₂ : IPLA.Joint dθ dx → ℝ} {L₁ : ℝ≥0}
    (hg₁ : Differentiable ℝ g₁) (hLip : LipschitzWith L₁ (gradient g₁))
    (hg₂ : ConvexOn ℝ Set.univ g₂) (hb : ∃ b : ℝ, ∀ z, b ≤ g₂ z)
    {lam : ℝ} (hlam : 0 < lam) (γ : ℝ)
    (initial : Ω → IPLA.State N dθ dx) (noise : ℕ → Ω → IPLA.State N dθ dx)
    (hinit : AEMeasurable initial Q) (hnoise : ∀ k, AEMeasurable (noise k) Q)
    (hind : IndepFun initial (fun ω k ↦ noise k ω) Q)
    (hiid : iIndepFun noise Q) (η : Measure (IPLA.State N dθ dx))
    (hlaw : ∀ k, Q.map (noise k) = η) (n : ℕ) :
    pipglaLaws Q g₁ (prox g₂ lam) γ initial noise n =
      ULA.chainLaw (pipglaUpdate g₁ (prox g₂ lam) γ) (Q.map initial)
        (Measure.infinitePi (fun _ : ℕ ↦ η)) n := by
  unfold pipglaLaws
  simp_rw [pipglaChain_eq_noiseDrivenChain]
  exact ULA.noiseDrivenChain_law_of_iid Q (pipglaUpdate g₁ (prox g₂ lam) γ)
    (pipglaUpdate_measurable hN hg₁ hLip hg₂ hb hlam γ)
    initial noise hinit hnoise hind hiid η hlaw n

end ProximalLangevin
