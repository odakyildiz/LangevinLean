import WassersteinMixing.SemigroupContinuity
import KineticLangevin.FlowPullback
import UnadjustedLangevin.EulerLimit

/-! # Lifting the actual Langevin comparison to independent auxiliary randomness

Measure-preserving source pullback commutes with the nonlinear gradient
drift, its Bochner integral equation, Euler approximations, and stationary
observable evaluations. This allows a genuinely independent uniform path to
be appended for the MALA approximation without changing the diffusion operator.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped NNReal

namespace WassersteinMixing

variable {Ω Ξ E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {P : Measure Ω} {Q : Measure Ξ} [IsFiniteMeasure P] [IsFiniteMeasure Q]
  (φ : Ξ → Ω) (hφ : MeasurePreserving φ Q P)

/-- The same integral solution remains an actual integral solution after a
measure-preserving enlargement of its probability space. -/
theorem langevin_integral_sourceLift (g : E → E) (L : ℝ≥0) (hg : LipschitzWith L g)
    (initial : Lp E 2 P) (B Y : ℝ → Lp E 2 P) (hY : Continuous Y)
    (T : ℝ) (heq : ∀ t ∈ Icc 0 T, Y t - initial =
      -(∫ s in 0..t, ULA.lpDrift P g hg (Y s)) + B t) :
    ∀ t ∈ Icc 0 T,
      KineticLangevin.sourcePullback φ hφ (Y t) -
          KineticLangevin.sourcePullback φ hφ initial =
        -(∫ s in 0..t, ULA.lpDrift Q g hg (KineticLangevin.sourcePullback φ hφ (Y s))) +
          KineticLangevin.sourcePullback φ hφ (B t) := by
  intro t ht
  have he := congrArg (KineticLangevin.sourcePullback φ hφ) (heq t ht)
  simp only [map_sub, map_add, map_neg] at he
  have hi := (KineticLangevin.sourcePullback φ hφ).intervalIntegral_comp_comm (μ := volume)
    (((ULA.lpDrift_lipschitz P g hg).continuous.comp hY).intervalIntegrable 0 t)
  simp only [Function.comp_def] at hi
  rw [← hi] at he
  simpa only [KineticLangevin.lpDrift_sourcePullback] using he

/-- Matching-noise Euler approximations also commute with the source lift. -/
theorem additiveEulerChain_sourceLift (g : E → E) (L : ℝ≥0) (hg : LipschitzWith L g)
    (step : ℝ) (initial : Lp E 2 P) (B : ℝ → Lp E 2 P) (n : ℕ) :
    KineticLangevin.sourcePullback φ hφ
      (ULA.additiveEulerChain (ULA.lpDrift P g hg) step initial B n) =
    ULA.additiveEulerChain (ULA.lpDrift Q g hg) step
      (KineticLangevin.sourcePullback φ hφ initial)
      (fun t ↦ KineticLangevin.sourcePullback φ hφ (B t)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ULA.additiveEulerChain_succ, map_add, map_sub, map_smul]
    rw [← KineticLangevin.lpDrift_sourcePullback φ hφ g L hg, ih]

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

omit [SecondCountableTopology E] in
/-- The exact law of each source-lifted actual state. -/
theorem sourceLift_law (X : Lp E 2 P) :
    Q.map (KineticLangevin.sourcePullback φ hφ X) = P.map X :=
  KineticLangevin.sourcePullback_map φ hφ X

omit [SecondCountableTopology E] in
/-- Pulling back real states and then evaluating complex observables agrees
exactly with pulling back the original observable evaluation. -/
theorem stationaryEvaluation_sourceLift (μ : Measure E) (X : Lp E 2 P)
    (hX : P.map X = μ) (f : Lp F 2 μ) :
    StationaryObservables.evaluation (𝕜 := 𝕜) μ Q
      (KineticLangevin.sourcePullback φ hφ X) ((sourceLift_law φ hφ X).trans hX) f =
      Lp.compMeasurePreservingₗᵢ 𝕜 φ hφ
        (StationaryObservables.evaluation (𝕜 := 𝕜) μ P X hX f) := by
  apply Lp.ext
  have hstate := KineticLangevin.sourcePullback_coe φ hφ X
  have hx : MeasurePreserving X P μ := ⟨(Lp.stronglyMeasurable X).measurable, hX⟩
  have hlift : MeasurePreserving (KineticLangevin.sourcePullback φ hφ X) Q μ :=
    ⟨(Lp.stronglyMeasurable _).measurable, (sourceLift_law φ hφ X).trans hX⟩
  have hnew := Lp.coeFn_compMeasurePreserving f hlift
  have hold := Lp.coeFn_compMeasurePreserving f hx
  have holdφ := hφ.quasiMeasurePreserving.ae_eq_comp hold
  have hpull := Lp.coeFn_compMeasurePreserving
    (StationaryObservables.evaluation (𝕜 := 𝕜) μ P X hX f) hφ
  filter_upwards [hstate, hnew, holdφ, hpull] with ξ hs hn ho hp
  exact hn.trans ((congrArg f hs).trans (ho.symm.trans hp.symm))

end WassersteinMixing
