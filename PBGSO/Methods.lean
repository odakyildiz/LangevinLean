import KineticLangevin.OBABO
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# New pathwise bounds for the two PBGSO implementation methods

The bounds in this file concern the **actual discrete update maps**. They do not
assert a Gibbs target, a stochastic stationary law, or an optimal mixing rate.
Forces in the optimiser and sampler may be unrelated. Supplied innovations are
arbitrary vectors: consequently the estimates also hold samplewise for Gaussian
innovations, without assuming that the optimiser receives thermal noise.
-/
noncomputable section
open MeasureTheory
namespace PBGSO
namespace Methods

variable {E Θ X : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The sum norm on a momentum-position difference, independent of the ambient
product space's max norm. The order is `(momentum, position)`. -/
def phaseError (z w : E × E) : ℝ := ‖z.1 - w.1‖ + ‖z.2 - w.2‖

/-- Triangle inequality for the explicit sum of coordinate errors. -/
theorem phaseError_triangle (z u w : E × E) :
    phaseError z w ≤ phaseError z u + phaseError u w := by
  have hp : ‖z.1 - w.1‖ ≤ ‖z.1 - u.1‖ + ‖u.1 - w.1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  have hq : ‖z.2 - w.2‖ ≤ ‖z.2 - u.2‖ + ‖u.2 - w.2‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  unfold phaseError
  linarith

/-- A finite geometric sum, which remains defined at amplification factor one. -/
def amplificationSum (a : ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, a ^ k

/-- Iteration with a possibly time-dependent innovation. -/
def trajectory {S I : Type*} (step : S → I → S) (noise : ℕ → I) (z : S) : ℕ → S
  | 0 => z
  | n + 1 => step (trajectory step noise z n) (noise n)

/-- Finite accumulation used below. Each application proves its recurrence
from concrete maps, rather than assuming it as a modelling hypothesis. -/
theorem finite_accumulation (e : ℕ → ℝ) (a b : ℝ) (ha : 0 ≤ a)
    (hstep : ∀ n, e (n + 1) ≤ a * e n + b) (n : ℕ) :
    e n ≤ a ^ n * e 0 + b * amplificationSum a n := by
  induction n with
  | zero => simp [amplificationSum]
  | succ n ih =>
    calc
      e (n + 1) ≤ a * e n + b := hstep n
      _ ≤ a * (a ^ n * e 0 + b * amplificationSum a n) + b := by gcongr
      _ = a ^ (n + 1) * e 0 + b * amplificationSum a (n + 1) := by
        simp only [amplificationSum, geom_sum_succ, pow_succ]
        ring


private theorem norm_sub_add_le (a b c d : E) :
    ‖(a + b) - (c + d)‖ ≤ ‖a - c‖ + ‖b - d‖ := by
  have he : (a + b) - (c + d) = (a - c) + (b - d) := by module
  rw [he]
  exact norm_add_le _ _

private theorem norm_sub_sub_le (a b c d : E) :
    ‖(a - b) - (c - d)‖ ≤ ‖a - c‖ + ‖b - d‖ := by
  have he : (a - b) - (c - d) = (a - c) - (b - d) := by module
  rw [he]
  exact norm_sub_le _ _

/-- The force kick has an explicit Lipschitz amplification factor. -/
theorem kick_error (G : E → E) (L h : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (z w : E × E) :
    phaseError (KineticLangevin.kickStep G h z)
      (KineticLangevin.kickStep G h w) ≤ (1 + |h| * L) * phaseError z w := by
  have hn : ‖(z.1 - h • G z.2) - (w.1 - h • G w.2)‖ ≤
      ‖z.1 - w.1‖ + |h| * (L * ‖z.2 - w.2‖) := by
    calc
      _ ≤ ‖z.1 - w.1‖ + ‖h • G z.2 - h • G w.2‖ := norm_sub_sub_le _ _ _ _
      _ = ‖z.1 - w.1‖ + |h| * ‖G z.2 - G w.2‖ := by
        rw [← smul_sub, norm_smul, Real.norm_eq_abs]
      _ ≤ _ := by gcongr; exact hLip _ _
  dsimp [phaseError, KineticLangevin.kickStep]
  nlinarith [norm_nonneg (z.1 - w.1), mul_nonneg (abs_nonneg h) hL]

/-- The drift shear has amplification at most `1+|h|`. -/
theorem drift_error (h : ℝ) (z w : E × E) :
    phaseError (KineticLangevin.driftStep h z)
      (KineticLangevin.driftStep h w) ≤ (1 + |h|) * phaseError z w := by
  have hn : ‖(z.2 + h • z.1) - (w.2 + h • w.1)‖ ≤
      ‖z.2 - w.2‖ + |h| * ‖z.1 - w.1‖ := by
    calc
      _ ≤ ‖z.2 - w.2‖ + ‖h • z.1 - h • w.1‖ := norm_sub_add_le _ _ _ _
      _ = _ := by rw [← smul_sub, norm_smul, Real.norm_eq_abs]
  dsimp [phaseError, KineticLangevin.driftStep]
  nlinarith [mul_nonneg (abs_nonneg h) (norm_nonneg (z.2 - w.2))]

/-- A damped thermostat is nonexpansive with synchronous innovations, and its
response to innovation perturbation is exactly controlled by `|σ|`. -/
theorem thermostat_error (η σ : ℝ) (hη : |η| ≤ 1) (z w : E × E) (ξ ζ : E) :
    phaseError (KineticLangevin.ornsteinStep η σ ξ z)
      (KineticLangevin.ornsteinStep η σ ζ w) ≤ phaseError z w + |σ| * ‖ξ - ζ‖ := by
  have hn : ‖(η • z.1 + σ • ξ) - (η • w.1 + σ • ζ)‖ ≤
      |η| * ‖z.1 - w.1‖ + |σ| * ‖ξ - ζ‖ := by
    calc
      _ ≤ ‖η • z.1 - η • w.1‖ + ‖σ • ξ - σ • ζ‖ := norm_sub_add_le _ _ _ _
      _ = _ := by simp only [← smul_sub, norm_smul, Real.norm_eq_abs]
  dsimp [phaseError, KineticLangevin.ornsteinStep]
  nlinarith [mul_le_mul_of_nonneg_right hη (norm_nonneg (z.1 - w.1))]

/-- The general coupled force. `Fbar` is the empirical optimiser force and `G`
is the sampler force, usually `∇ₓE`; no common potential is imposed. -/
def coupledForce (Fbar : Θ → X → Θ) (G : Θ → X → X) (q : Θ × X) : Θ × X :=
  (Fbar q.1 q.2, G q.1 q.2)

/-- The paper's M-MFPO OBABO map. A particle innovation has zero optimiser
coordinate; hence both optimiser thermostat stages are deterministic. -/
def momentumStep (Fbar : Θ → X → Θ) (G : Θ → X → X) (γ h : ℝ)
    (z : (Θ × X) × (Θ × X)) (ξ ξ' : X) : (Θ × X) × (Θ × X) :=
  KineticLangevin.obaboStep (coupledForce Fbar G) h
    (Real.exp (-γ * h / 2)) (Real.sqrt (1 - Real.exp (-γ * h))) z (0, ξ) (0, ξ')

/-- An explicit conservative amplification coefficient for a BAB stage. -/
def momentumAmplification (L h : ℝ) : ℝ := (1 + |h| * L / 2) ^ 2 * (1 + |h|)

/-- New one-step OBABO robustness estimate. Its force Lipschitz hypothesis is
on the arbitrary coupled vector field, not a joint-potential Hessian. -/
theorem obabo_error (G : E → E) (L h η σ : ℝ) (hL : 0 ≤ L) (hη : |η| ≤ 1)
    (hLip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (z w : E × E) (ξ ξ' ζ ζ' : E) :
    phaseError (KineticLangevin.obaboStep G h η σ z ξ ξ')
      (KineticLangevin.obaboStep G h η σ w ζ ζ') ≤
      momentumAmplification L h * phaseError z w +
        |σ| * (momentumAmplification L h * ‖ξ - ζ‖ + ‖ξ' - ζ'‖) := by
  let a := 1 + |h| * L / 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hd : 0 ≤ 1 + |h| := by positivity
  have hh : 1 + |h / 2| * L = a := by dsimp [a]; rw [abs_div]; norm_num; ring
  have h1 := thermostat_error η σ hη z w ξ ζ
  have h2 := kick_error G L (h / 2) hL hLip
    (KineticLangevin.ornsteinStep η σ ξ z) (KineticLangevin.ornsteinStep η σ ζ w)
  rw [hh] at h2
  have h3 := drift_error h
    (KineticLangevin.kickStep G (h / 2) (KineticLangevin.ornsteinStep η σ ξ z))
    (KineticLangevin.kickStep G (h / 2) (KineticLangevin.ornsteinStep η σ ζ w))
  have h4 := kick_error G L (h / 2) hL hLip
    (KineticLangevin.driftStep h
      (KineticLangevin.kickStep G (h / 2) (KineticLangevin.ornsteinStep η σ ξ z)))
    (KineticLangevin.driftStep h
      (KineticLangevin.kickStep G (h / 2) (KineticLangevin.ornsteinStep η σ ζ w)))
  rw [hh] at h4
  have h5 := thermostat_error η σ hη
    (KineticLangevin.kickStep G (h / 2) (KineticLangevin.driftStep h
      (KineticLangevin.kickStep G (h / 2) (KineticLangevin.ornsteinStep η σ ξ z))))
    (KineticLangevin.kickStep G (h / 2) (KineticLangevin.driftStep h
      (KineticLangevin.kickStep G (h / 2) (KineticLangevin.ornsteinStep η σ ζ w)))) ξ' ζ'
  calc
    _ ≤ a * ((1 + |h|) * (a * (phaseError z w + |σ| * ‖ξ - ζ‖))) +
        |σ| * ‖ξ' - ζ'‖ := by
      apply h5.trans
      gcongr
      exact h4.trans (mul_le_mul_of_nonneg_left
        (h3.trans (mul_le_mul_of_nonneg_left
          (h2.trans (mul_le_mul_of_nonneg_left h1 ha)) hd)) ha)
    _ = _ := by dsimp [momentumAmplification, a]; ring

/-- New finite-step perturbation bound for the concrete OBABO map. For a
synchronous coupling (`ε=0`) the initial discrepancy is multiplied by `A^n`.
The estimate is finite horizon stability, not a claim that `A<1`. -/
theorem obabo_finite_error (G : E → E) (L h η σ ε : ℝ)
    (hL : 0 ≤ L) (hη : |η| ≤ 1)
    (hLip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (ξ ζ : ℕ → E × E) (hnoise : ∀ n,
      ‖(ξ n).1 - (ζ n).1‖ ≤ ε ∧ ‖(ξ n).2 - (ζ n).2‖ ≤ ε)
    (z w : E × E) (n : ℕ) :
    phaseError (trajectory (fun s r ↦ KineticLangevin.obaboStep G h η σ s r.1 r.2) ξ z n)
      (trajectory (fun s r ↦ KineticLangevin.obaboStep G h η σ s r.1 r.2) ζ w n) ≤
      momentumAmplification L h ^ n * phaseError z w +
        (|σ| * (momentumAmplification L h + 1) * ε) *
          amplificationSum (momentumAmplification L h) n := by
  have hA : 0 ≤ momentumAmplification L h := by unfold momentumAmplification; positivity
  apply finite_accumulation _ _ _ hA _ n
  intro k
  dsimp only [trajectory]
  apply (obabo_error G L h η σ hL hη hLip _ _ _ _ _ _).trans
  have h1 := mul_le_mul_of_nonneg_left (hnoise k).1 hA
  have h2 := mul_le_mul_of_nonneg_left (add_le_add h1 (hnoise k).2) (abs_nonneg σ)
  nlinarith

/-- Finite-horizon accumulation only requires the local estimate on steps
strictly preceding the requested endpoint. -/
theorem finite_accumulation_upto (e : ℕ → ℝ) (a b : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    (∀ k, k < n → e (k + 1) ≤ a * e k + b) →
    e n ≤ a ^ n * e 0 + b * amplificationSum a n := by
  induction n with
  | zero => intro _; simp [amplificationSum]
  | succ n ih =>
    intro hstep
    have hi := ih (fun k hk ↦ hstep k (Nat.lt.step hk))
    calc
      e (n + 1) ≤ a * e n + b := hstep n (Nat.lt_succ_self n)
      _ ≤ a * (a ^ n * e 0 + b * amplificationSum a n) + b := by gcongr
      _ = a ^ (n + 1) * e 0 + b * amplificationSum a (n + 1) := by
        simp only [amplificationSum, geom_sum_succ, pow_succ]
        ring

end Methods
end PBGSO
