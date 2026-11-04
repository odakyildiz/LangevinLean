import WassersteinMixing.SemigroupPoisson
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.Probability.Process.Filtration

set_option linter.style.header false

/-! # Poisson correctors on a stationary Markov process

This reusable process lemma needs only the proved operator identities of the
semigroup corrector. The actual Langevin construction supplies these identities
from the paper's potential assumptions; a spectral basis is not required.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology

namespace WassersteinMixing

variable (H E : Type*) {Ω : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The discrete observations of a stationary Markov semigroup with its
constructed bounded Poisson operator. -/
structure PoissonProcess (Q : Measure Ω) (h : ℝ) (hh : 0 < h) where
  transition : H →L[ℝ] H
  corrector : H →L[ℝ] H
  poissonSource : H →L[ℝ] H
  corrector_norm : ∀ f, ‖corrector f‖ ≤ h * ‖f‖
  corrector_energy : ∀ f,
    inner ℝ (corrector f) (corrector f - transition (corrector f)) ≤
      h ^ 2 * inner ℝ f (f - transition f)
  poisson_identity : ∀ f, corrector f - transition (corrector f) = poissonSource f
  filtration : Filtration ℕ ‹MeasurableSpace Ω›
  eval : ℕ → H →ₗᵢ[ℝ] Lp E 2 Q
  adapted : ∀ n f, AEStronglyMeasurable[filtration n] (eval n f) Q
  markov : ∀ n f,
    (condExpL2 E ℝ (filtration.le n) (eval (n + 1) f) : Lp E 2 Q) =
      eval n (transition f)

variable {H E} {Q : Measure Ω} {h : ℝ} {hh : 0 < h}

namespace PoissonProcess

variable (S : PoissonProcess H E Q h hh)

/-- Adapted stationary evaluations are fixed by the actual conditional projection. -/
theorem condExp_eval_self (f : H) (n : ℕ) :
    (condExpL2 E ℝ (S.filtration.le n) (S.eval n f) : Lp E 2 Q) = S.eval n f := by
  have : Fact (S.filtration n ≤ ‹MeasurableSpace Ω›) := ⟨S.filtration.le n⟩
  change (lpMeas E ℝ (S.filtration n) 2 Q).starProjection (S.eval n f) = S.eval n f
  exact Submodule.starProjection_eq_self_iff.mpr
    (mem_lpMeas_iff_aestronglyMeasurable.mpr (S.adapted n f))

/-- The stationary increment energy is derived from the Markov conditional
projection and the isometries; it is not a process hypothesis. -/
theorem eval_increment_norm_sq (f : H) (n : ℕ) :
    ‖S.eval (n + 1) f - S.eval n f‖ ^ 2 =
      2 * inner ℝ f (f - S.transition f) := by
  have hp := inner_condExpL2_eq_inner_fun (𝕜 := ℝ) (S.filtration.le n)
    (S.eval (n + 1) f) (S.eval n f) (S.adapted n f)
  rw [S.markov, (S.eval n).inner_map_map] at hp
  rw [norm_sub_sq_real, (S.eval (n + 1)).norm_map, (S.eval n).norm_map,
    inner_sub_right, real_inner_self_eq_norm_sq, ← hp,
    real_inner_comm f]
  ring

/-- The actual corrector evaluated at time `n h`. -/
def correctorAt (f : H) (n : ℕ) : Lp E 2 Q :=
  S.eval n (S.corrector f)

/-- Corrector evaluations are adapted because they are functions of the
current state in the Markov realization. -/
theorem correctorAt_adapted (f : H) (n : ℕ) :
    AEStronglyMeasurable[S.filtration n] (S.correctorAt f n) Q :=
  S.adapted n _

/-- Its `L²` norm bound follows from the constructed operator and stationarity. -/
theorem correctorAt_norm_le (f : H) (n : ℕ) :
    ‖S.correctorAt f n‖ ≤ h * ‖f‖ := by
  simpa only [correctorAt, (S.eval n).norm_map] using
    S.corrector_norm f

/-- Any proved score-energy bound transfers to the evaluated corrector. -/
theorem correctorAt_norm_sq_le (f : H) (B : ℝ) (hscore : ‖f‖ ^ 2 ≤ B) (n : ℕ) :
    ‖S.correctorAt f n‖ ^ 2 ≤ h ^ 2 * B := by
  have hn := S.correctorAt_norm_le f n
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hm := mul_le_mul_of_nonneg_left hscore (sq_nonneg h)
  nlinarith

/-- The corrector increment is smaller than the score increment by `h²`.
Both increment identities and the semigroup energy domination are proved earlier. -/
theorem correctorAt_increment_norm_sq_le (f : H) (n : ℕ) :
    ‖S.correctorAt f n - S.correctorAt f (n + 1)‖ ^ 2 ≤
      h ^ 2 * ‖S.eval (n + 1) f - S.eval n f‖ ^ 2 := by
  rw [norm_sub_rev (S.correctorAt f n) (S.correctorAt f (n + 1))]
  change ‖S.eval (n + 1) _ - S.eval n _‖ ^ 2 ≤ _
  rw [S.eval_increment_norm_sq, S.eval_increment_norm_sq]
  have he := S.corrector_energy f
  nlinarith

/-- The paper's score-increment constant gives its corrector-increment constant. -/
theorem correctorAt_increment_energy_le (f : H) (β d : ℝ) (n : ℕ)
    (hincrement : ‖S.eval (n + 1) f - S.eval n f‖ ^ 2 ≤ 6 * h * β ^ 2 * d) :
    ‖S.correctorAt f n - S.correctorAt f (n + 1)‖ ^ 2 ≤ 6 * h ^ 3 * β ^ 2 * d := by
  have hm := mul_le_mul_of_nonneg_left hincrement (sq_nonneg h)
  exact (S.correctorAt_increment_norm_sq_le f n).trans (by nlinarith)

/-- The residual is defined from the actual defect and the constructed corrector. -/
def martingaleAt (f : H) (D : ℕ → Lp E 2 Q) (n : ℕ) : Lp E 2 Q :=
  D n - (S.correctorAt f n - S.correctorAt f (n + 1))

/-- The coboundary/martingale decomposition is an exact vector identity. -/
theorem defect_decomposition (f : H) (D : ℕ → Lp E 2 Q) (n : ℕ) :
    D n = S.correctorAt f n - S.correctorAt f (n + 1) + S.martingaleAt f D n := by
  unfold martingaleAt
  abel

/-- The primitive conditional mean of the local defect and the proved Poisson
equation imply exact conditional centering of the residual. -/
theorem martingaleAt_condExp_zero (f : H) (D : ℕ → Lp E 2 Q) (n : ℕ)
    (hmean : (condExpL2 E ℝ (S.filtration.le n) (D n) : Lp E 2 Q) =
      S.eval n (S.poissonSource f)) :
    (condExpL2 E ℝ (S.filtration.le n) (S.martingaleAt f D n) : Lp E 2 Q) = 0 := by
  simp only [martingaleAt, correctorAt, map_sub, Submodule.coe_sub]
  rw [hmean, S.condExp_eval_self, S.markov]
  rw [← map_sub, S.poisson_identity, sub_self]

/-- The centered residual is orthogonal to every current adapted `L²` vector. -/
theorem martingaleAt_inner_eq_zero (f : H) (D : ℕ → Lp E 2 Q) (n : ℕ)
    (hmean : (condExpL2 E ℝ (S.filtration.le n) (D n) : Lp E 2 Q) =
      S.eval n (S.poissonSource f))
    (predictable : Lp E 2 Q)
    (hadapted : AEStronglyMeasurable[S.filtration n] predictable Q) :
    inner ℝ predictable (S.martingaleAt f D n) = 0 := by
  have hp := inner_condExpL2_eq_inner_fun (𝕜 := ℝ) (S.filtration.le n)
    (S.martingaleAt f D n) predictable hadapted
  rw [S.martingaleAt_condExp_zero f D n hmean, inner_zero_left] at hp
  simpa only [real_inner_comm predictable] using hp.symm

/-- The two independently proved local estimates yield the paper's `18`
without a martingale-energy premise. -/
theorem martingaleAt_energy_le (f : H) (D : ℕ → Lp E 2 Q) (β d : ℝ) (n : ℕ)
    (hdefect : ‖D n‖ ^ 2 ≤ 3 * h ^ 3 * β ^ 2 * d)
    (hincrement : ‖S.eval (n + 1) f - S.eval n f‖ ^ 2 ≤ 6 * h * β ^ 2 * d) :
    ‖S.martingaleAt f D n‖ ^ 2 ≤ 18 * h ^ 3 * β ^ 2 * d := by
  have hg := S.correctorAt_increment_energy_le f β d n hincrement
  have ht := norm_sub_le (D n) (S.correctorAt f n - S.correctorAt f (n + 1))
  have hs := mul_self_le_mul_self (norm_nonneg _) ht
  change ‖D n - (S.correctorAt f n - S.correctorAt f (n + 1))‖ ^ 2 ≤ _
  nlinarith [sq_nonneg (‖D n‖ - ‖S.correctorAt f n - S.correctorAt f (n + 1)‖)]

end PoissonProcess
end WassersteinMixing
