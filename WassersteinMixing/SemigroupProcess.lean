import WassersteinMixing.ComplexRealCorrector
import WassersteinMixing.PoissonProcess

/-! # From the constructed semigroup corrector to the Markov comparison

All corrector identities in the comparison process are supplied by the strong
semigroup construction. Only evaluations and their actual Markov identity are
needed to connect the observable space with its probability-space realization.
-/
noncomputable section
set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory

namespace WassersteinMixing
open ComplexRealCorrector

variable {R H E Ω : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup R] [InnerProductSpace ℝ R] [CompleteSpace R]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The real Poisson source is a genuine bounded operator. Its integral form
is proved below from the constructed corrector equation. -/
def semigroupPoissonSource (S : ReversibleSemigroup H) (i : R →ₗᵢ[ℝ] H)
    (h : ℝ) (hh : 0 ≤ h) : R →L[ℝ] R :=
  realCorrector S i h hh - realOp S i h ∘L realCorrector S i h hh

theorem semigroupPoissonSource_eq_integral (S : ReversibleSemigroup H)
    (i : R →ₗᵢ[ℝ] H) (hreal : PreservesReal S i) (h : ℝ) (hh : 0 ≤ h) (f : R) :
    semigroupPoissonSource S i h hh f = ∫ t in 0..h, f - realOp S i t f := by
  change realCorrector S i h hh f - realOp S i h (realCorrector S i h hh f) = _
  exact realCorrector_poisson S i hreal h hh f

/-- The stationary Poisson comparison process built from the actual semigroup
corrector, without any eigenbasis or corrector-bound assumption. -/
def semigroupPoissonProcess (Q : Measure Ω) (S : ReversibleSemigroup H)
    (i : R →ₗᵢ[ℝ] H) (hreal : PreservesReal S i) (h : ℝ) (hh : 0 < h)
    (filtration : Filtration ℕ mΩ) (eval : ℕ → R →ₗᵢ[ℝ] Lp E 2 Q)
    (hadapted : ∀ n f, AEStronglyMeasurable[filtration n] (eval n f) Q)
    (hmarkov : ∀ n f,
      (condExpL2 E ℝ (filtration.le n) (eval (n + 1) f) : Lp E 2 Q) =
        eval n (realOp S i h f)) : PoissonProcess R E Q h hh where
  transition := realOp S i h
  corrector := realCorrector S i h hh.le
  poissonSource := semigroupPoissonSource S i h hh.le
  corrector_norm := realCorrector_norm_le S i hreal h hh.le
  corrector_energy := realCorrector_energy_le S i hreal h hh.le hh.le
  poisson_identity := fun _ ↦ rfl
  filtration := filtration
  eval := eval
  adapted := hadapted
  markov := hmarkov

end WassersteinMixing
