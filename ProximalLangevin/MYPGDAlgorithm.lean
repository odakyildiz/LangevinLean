import ProximalLangevin.MYPGDTransport
import ProximalLangevin.MYIPLA
import UnadjustedLangevin.MarkovLaw
import UnadjustedLangevin.GaussianInnovationVectors

set_option linter.style.header false

/-! # The actual MYPGD recursion and its Gaussian Markov law

MYPGD is precisely MYIPLA with the parameter coordinates of each innovation
erased. The original full Gaussian innovations determine its latent-noise
Markov law; Gaussianity of the erased innovation is never asserted.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace ProximalLangevin

/-- MYPGD removes precisely the parameter noise from the displayed MYIPLA step. -/
def mypgdUpdate {N dθ dx : ℕ} (g₁ : IPLA.Joint dθ dx → ℝ)
    (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx) (η γ : ℝ)
    (z ξ : IPLA.State N dθ dx) : IPLA.State N dθ dx :=
  myiplaUpdate g₁ P η γ z (latentNoiseCLM ξ)

/-- The actual MYPGD chain driven by supplied full innovations. -/
def mypgdChain {N dθ dx : ℕ} (g₁ : IPLA.Joint dθ dx → ℝ)
    (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx) (η γ : ℝ)
    (initial : IPLA.State N dθ dx) (noise : ℕ → IPLA.State N dθ dx) :
    ℕ → IPLA.State N dθ dx := algorithmChain (mypgdUpdate g₁ P η γ) initial noise

/-- MYPGD is exactly MYIPLA applied to the latent-only innovations. -/
theorem mypgdChain_eq_myiplaChain {N dθ dx : ℕ} (g₁ : IPLA.Joint dθ dx → ℝ)
    (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx) (η γ : ℝ)
    (initial : IPLA.State N dθ dx) (noise : ℕ → IPLA.State N dθ dx) (n : ℕ) :
    mypgdChain g₁ P η γ initial noise n =
      myiplaChain g₁ P η γ initial (fun k => latentNoiseCLM (noise k)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change myiplaUpdate g₁ P η γ (mypgdChain g₁ P η γ initial noise n)
      (latentNoiseCLM (noise n)) = _
    rw [ih]
    rfl

theorem mypgdChain_eq_noiseDrivenChain {N dθ dx : ℕ} (g₁ : IPLA.Joint dθ dx → ℝ)
    (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx) (η γ : ℝ)
    (initial : IPLA.State N dθ dx) (noise : ℕ → IPLA.State N dθ dx) (n : ℕ) :
    mypgdChain g₁ P η γ initial noise n =
      ULA.noiseDrivenChain (mypgdUpdate g₁ P η γ) initial noise n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change mypgdUpdate g₁ P η γ (mypgdChain g₁ P η γ initial noise n) (noise n) = _
    rw [ih]
    rfl

/-- The output law of the actual MYPGD recursion. -/
def mypgdLaws {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    {N dθ dx : ℕ} (g₁ : IPLA.Joint dθ dx → ℝ)
    (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx) (η γ : ℝ)
    (initial : Ω → IPLA.State N dθ dx) (noise : ℕ → Ω → IPLA.State N dθ dx)
    (n : ℕ) : Measure (IPLA.State N dθ dx) :=
  Q.map (fun ω => mypgdChain g₁ P η γ (initial ω) (fun k => noise k ω) n)

/-- The drift/noise formula for the actual Moreau proximal construction. -/
theorem mypgdUpdate_eq_latentGaussianUpdate {N dθ dx : ℕ} (hN : 0 < N)
    {g₁ g₂ : IPLA.Joint dθ dx → ℝ} (hg₁ : Differentiable ℝ g₁)
    (hg₂ : ConvexOn ℝ univ g₂) (hb : ∃ b, ∀ x, b ≤ g₂ x)
    {η : ℝ} (hη : 0 < η) (γ : ℝ) :
    mypgdUpdate (N := N) g₁ (prox g₂ η) η γ =
      latentGaussianUpdate
        (fun z => z - (γ / N) • gradient (IPLA.potential (smoothedPotential g₁ g₂ η)) z)
        (Real.sqrt (2 * γ / N)) := by
  funext z ξ
  exact myiplaUpdate_eq_scaledUpdate hN hg₁ (moreau_differentiable hg₂ hb hη)
    (prox g₂ η) hη.ne' (gradient_moreau hg₂ hb hη) γ z (latentNoiseCLM ξ)

/-- The full-noise update used for comparison is the actual MYIPLA update. -/
theorem myiplaUpdate_eq_fullGaussianUpdate {N dθ dx : ℕ} (hN : 0 < N)
    {g₁ g₂ : IPLA.Joint dθ dx → ℝ} (hg₁ : Differentiable ℝ g₁)
    (hg₂ : ConvexOn ℝ univ g₂) (hb : ∃ b, ∀ x, b ≤ g₂ x)
    {η : ℝ} (hη : 0 < η) (γ : ℝ) :
    myiplaUpdate (N := N) g₁ (prox g₂ η) η γ =
      fullGaussianUpdate
        (fun z => z - (γ / N) • gradient (IPLA.potential (smoothedPotential g₁ g₂ η)) z)
        (Real.sqrt (2 * γ / N)) := by
  funext z ξ
  exact myiplaUpdate_eq_scaledUpdate hN hg₁ (moreau_differentiable hg₂ hb hη)
    (prox g₂ η) hη.ne' (gradient_moreau hg₂ hb hη) γ z ξ

section GaussianLaw
variable {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    {N dθ dx : ℕ} (hN : 0 < N)
    {g₁ g₂ : IPLA.Joint dθ dx → ℝ} {L₁ : ℝ≥0}
    (hg₁ : Differentiable ℝ g₁) (hLip : LipschitzWith L₁ (gradient g₁))
    (hg₂ : ConvexOn ℝ univ g₂) (hb : ∃ b, ∀ x, b ≤ g₂ x)
    {η : ℝ} (hη : 0 < η) (γ : ℝ)

include hN hg₁ hLip hg₂ hb hη

omit hN in
private theorem smoothed_forward_lipschitz :
    LipschitzWith (1 + Real.nnabs (γ / N) * ((N : ℝ≥0) * smoothingLipschitz L₁ η))
      (fun z : IPLA.State N dθ dx =>
        z - (γ / N) • gradient (IPLA.potential (smoothedPotential g₁ g₂ η)) z) := by
  have hres : gradient (moreau g₂ η) = residual g₂ η := funext (gradient_moreau hg₂ hb hη)
  have hLe : LipschitzWith η.toNNReal⁻¹ (gradient (moreau g₂ η)) := by
    rw [hres]
    simpa only [Real.toNNReal_inv] using residual_lipschitz hg₂ hb hη
  have hLV := smoothed_gradient_lipschitz hg₁ (moreau_differentiable hg₂ hb hη) hLip hLe
  have hgrad : LipschitzWith ((N : ℝ≥0) * smoothingLipschitz L₁ η)
      (gradient (@IPLA.potential N dθ dx (smoothedPotential g₁ g₂ η))) :=
    IPLA.potential_gradient_lipschitz (hg₁.add (moreau_differentiable hg₂ hb hη)) hLV
  exact LipschitzWith.id.sub ((lipschitzWith_smul (γ / N)).comp hgrad)

/-- The actual Gaussian realization has the proved latent-noise Markov law. -/
theorem mypgdLaws_eq_markovLaws
    (initial : Lp (IPLA.State N dθ dx) 2 Q)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 Q)
    (hGaussian : IPLA.GaussianInnovations Q initial noise) (n : ℕ) :
    mypgdLaws Q g₁ (prox g₂ η) η γ initial (fun k => noise k) n =
      ULA.markovLaws (latentGaussianUpdate
        (fun z => z - (γ / N) • gradient (IPLA.potential (smoothedPotential g₁ g₂ η)) z)
        (Real.sqrt (2 * γ / N))) (stdGaussian (IPLA.State N dθ dx)) (Q.map initial) n := by
  have hD := smoothed_forward_lipschitz (N := N) hg₁ hLip hg₂ hb hη γ
  have hF : Measurable (Function.uncurry (mypgdUpdate (N := N) g₁ (prox g₂ η) η γ)) := by
    rw [mypgdUpdate_eq_latentGaussianUpdate hN hg₁ hg₂ hb hη γ]
    exact latentGaussianUpdate_measurable hD _
  unfold mypgdLaws
  simp_rw [mypgdChain_eq_noiseDrivenChain]
  rw [ULA.noiseDrivenChain_law_eq_markovLaws Q _ hF initial (fun k => noise k)
    (Lp.aestronglyMeasurable initial).aemeasurable
    (fun k => (Lp.aestronglyMeasurable (noise k)).aemeasurable)
    hGaussian.independentInitial
    (ULA.gaussianInnovations_vectorIndependent Q (fun k => noise k)
      (fun k => (Lp.aestronglyMeasurable (noise k)).aemeasurable)
      hGaussian.coordinateLaw hGaussian.independent)
    (stdGaussian (IPLA.State N dθ dx))
    (ULA.gaussianInnovations_vectorLaw Q (fun k => noise k)
      (fun k => (Lp.aestronglyMeasurable (noise k)).aemeasurable)
      hGaussian.coordinateLaw hGaussian.independent) n,
    mypgdUpdate_eq_latentGaussianUpdate hN hg₁ hg₂ hb hη γ]

/-- The same full innovations give the ordinary full-noise MYIPLA Markov law. -/
theorem myiplaLaws_eq_markovLaws
    (initial : Lp (IPLA.State N dθ dx) 2 Q)
    (noise : ℕ → Lp (IPLA.State N dθ dx) 2 Q)
    (hGaussian : IPLA.GaussianInnovations Q initial noise) (n : ℕ) :
    myiplaLaws Q g₁ (prox g₂ η) η γ initial (fun k => noise k) n =
      ULA.markovLaws (fullGaussianUpdate
        (fun z => z - (γ / N) • gradient (IPLA.potential (smoothedPotential g₁ g₂ η)) z)
        (Real.sqrt (2 * γ / N))) (stdGaussian (IPLA.State N dθ dx)) (Q.map initial) n := by
  have hD := smoothed_forward_lipschitz (N := N) hg₁ hLip hg₂ hb hη γ
  have hF : Measurable (Function.uncurry (myiplaUpdate (N := N) g₁ (prox g₂ η) η γ)) := by
    rw [myiplaUpdate_eq_fullGaussianUpdate hN hg₁ hg₂ hb hη γ]
    exact fullGaussianUpdate_measurable hD _
  unfold myiplaLaws
  have hchain (x : IPLA.State N dθ dx) (w : ℕ → IPLA.State N dθ dx) (k : ℕ) :
      myiplaChain g₁ (prox g₂ η) η γ x w k =
        ULA.noiseDrivenChain (myiplaUpdate g₁ (prox g₂ η) η γ) x w k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      change myiplaUpdate _ _ _ _ (myiplaChain _ _ _ _ x w k) (w k) = _
      rw [ih]
      rfl
  simp_rw [hchain]
  rw [ULA.noiseDrivenChain_law_eq_markovLaws Q _ hF initial (fun k => noise k)
    (Lp.aestronglyMeasurable initial).aemeasurable
    (fun k => (Lp.aestronglyMeasurable (noise k)).aemeasurable)
    hGaussian.independentInitial
    (ULA.gaussianInnovations_vectorIndependent Q (fun k => noise k)
      (fun k => (Lp.aestronglyMeasurable (noise k)).aemeasurable)
      hGaussian.coordinateLaw hGaussian.independent)
    (stdGaussian (IPLA.State N dθ dx))
    (ULA.gaussianInnovations_vectorLaw Q (fun k => noise k)
      (fun k => (Lp.aestronglyMeasurable (noise k)).aemeasurable)
      hGaussian.coordinateLaw hGaussian.independent) n,
    myiplaUpdate_eq_fullGaussianUpdate hN hg₁ hg₂ hb hη γ]

end GaussianLaw

end ProximalLangevin
