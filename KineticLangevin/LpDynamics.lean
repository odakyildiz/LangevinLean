import KineticLangevin.Integrator
import UnadjustedLangevin.LpDrift

/-! # The L² numerical chain represents the original KLMC chain

All operations on L² classes agree almost everywhere with the corresponding
vector operations on their representatives. In particular, the lifted
gradient is the original gradient pointwise. The following identities prove
that the stochastic analysis studies the implemented exponential and KLMC
updates, rather than a different abstract recursion on equivalence classes.
-/

noncomputable section
open MeasureTheory
open scoped NNReal

namespace KineticLangevin

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (P : Measure Ω) [IsFiniteMeasure P]

/-- Read a velocity-position pair of L² classes as a random phase vector. -/
def lpPhaseCoe (S : Lp H 2 P × Lp H 2 P) (ω : Ω) : H × H := (S.1 ω, S.2 ω)

private theorem affine_lp_coe (a b : ℝ) (X Y Z : Lp H 2 P) :
    (a • X - b • Y + Z : Lp H 2 P) =ᵐ[P] fun ω ↦ a • X ω - b • Y ω + Z ω := by
  filter_upwards [Lp.coeFn_add (a • X - b • Y) Z, Lp.coeFn_sub (a • X) (b • Y),
    Lp.coeFn_smul a X, Lp.coeFn_smul b Y] with ω ha hs hX hY
  simp only [ha, hs, hX, hY, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]

/-- The actual lifted exponential update is the original pointwise update. -/
theorem lp_exponentialStep_coe (f : H → ℝ) (M : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (γ h : ℝ)
    (S N : Lp H 2 P × Lp H 2 P) :
    (fun ω ↦ lpPhaseCoe P (exponentialStep (ULA.lpDrift P (gradient f) hLip) γ h S N) ω) =ᵐ[P]
      fun ω ↦ exponentialStep (gradient f) γ h (lpPhaseCoe P S ω) (lpPhaseCoe P N ω) := by
  let G := ULA.lpDrift P (gradient f) hLip
  have hv := affine_lp_coe P (psi γ 0 h) (psi γ 1 h) S.1 (G S.2) N.1
  have hp := affine_lp_coe P (psi γ 1 h) (psi γ 2 h) S.1 (G S.2) (S.2 + N.2)
  have hid : (exponentialStep G γ h S N).2 =
      psi γ 1 h • S.1 - psi γ 2 h • G S.2 + (S.2 + N.2) := by
    unfold exponentialStep
    abel
  filter_upwards [hv, hp, Lp.coeFn_add S.2 N.2,
    ULA.lpDrift_coe P (gradient f) hLip S.2] with ω hv hp hsum hg
  apply Prod.ext
  · change (exponentialStep G γ h S N).1 ω = _
    change (psi γ 0 h • S.1 - psi γ 1 h • G S.2 + N.1 : Lp H 2 P) ω = _
    rw [hv, hg]
    rfl
  · change (exponentialStep G γ h S N).2 ω = _
    rw [hid, hp, hsum, hg]
    change psi γ 1 h • S.1 ω - psi γ 2 h • gradient f (S.2 ω) +
      (S.2 ω + N.2 ω) = S.2 ω + psi γ 1 h • S.1 ω - psi γ 2 h • gradient f (S.2 ω) + N.2 ω
    abel

/-- Scalar multiplication of phase innovations also agrees pointwise. -/
theorem lpPhaseCoe_smul_ae (c : ℝ) (N : Lp H 2 P × Lp H 2 P) :
    (fun ω ↦ lpPhaseCoe P (c • N) ω) =ᵐ[P] fun ω ↦ c • lpPhaseCoe P N ω := by
  filter_upwards [Lp.coeFn_smul c N.1, Lp.coeFn_smul c N.2] with ω h1 h2
  exact Prod.ext h1 h2

/-- The actual lifted KLMC update, including its fluctuation-dissipation
noise scaling, represents exactly the paper's pointwise update. -/
theorem lp_klmcStep_coe (f : H → ℝ) (M : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (γ h : ℝ)
    (S N : Lp H 2 P × Lp H 2 P) :
    (fun ω ↦ lpPhaseCoe P (klmcStep (ULA.lpDrift P (gradient f) hLip) γ h S N) ω) =ᵐ[P]
      fun ω ↦ klmcStep (gradient f) γ h (lpPhaseCoe P S ω) (lpPhaseCoe P N ω) := by
  have he := lp_exponentialStep_coe P f M hLip γ h S (Real.sqrt (2 * γ) • N)
  filter_upwards [he, lpPhaseCoe_smul_ae P (Real.sqrt (2 * γ)) N] with ω he hn
  simpa only [klmcStep, hn] using he

/-- Every lifted KLMC iterate represents the original noise-driven KLMC
chain almost everywhere, for the supplied initial condition and innovations. -/
theorem lp_klmcChain_coe (f : H → ℝ) (M : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (γ h : ℝ)
    (initial : Lp H 2 P × Lp H 2 P) (noise : ℕ → Lp H 2 P × Lp H 2 P) (n : ℕ) :
    (fun ω ↦ lpPhaseCoe P (klmcChain (ULA.lpDrift P (gradient f) hLip) γ h initial noise n) ω) =ᵐ[P]
      fun ω ↦ klmcChain (gradient f) γ h (lpPhaseCoe P initial ω)
        (fun k ↦ lpPhaseCoe P (noise k) ω) n := by
  induction n with
  | zero => exact Filter.Eventually.of_forall fun _ ↦ rfl
  | succ n ih =>
      have he := lp_klmcStep_coe P f M hLip γ h
        (klmcChain (ULA.lpDrift P (gradient f) hLip) γ h initial noise n) (noise n)
      filter_upwards [he, ih] with ω hstep hprevious
      simpa only [klmcChain_succ, hprevious] using hstep

end KineticLangevin
