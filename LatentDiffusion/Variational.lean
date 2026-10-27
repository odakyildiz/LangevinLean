import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic

/-! # The normalized variational problem

The free energy is defined by its canonical normalized form, minus log evidence
plus average actual KL divergence. Admissibility retains finite KL before any
`toReal` conversion. Identifying this definition with a density integral needs
the usual log-integrability and normalization identities; those are not inferred
from pointwise smoothness. The theorem is valid for arbitrary measurable latent
spaces and arbitrary parameter sets, so in particular for tilted latent models.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LatentDiffusion

variable {A Z : Type*} [MeasurableSpace Z] {M : ℕ}

/-- The tilted log evidence and its normalized posterior at each datum. -/
structure PosteriorFamily (A Z : Type*) [MeasurableSpace Z] (M : ℕ) where
  logEvidence : A → ℝ
  posterior : A → Fin M → ProbabilityMeasure Z

namespace PosteriorFamily
variable (P : PosteriorFamily A Z M)

/-- Excludes infinite entropy from real arithmetic. -/
def Admissible (a : A) (q : Fin M → ProbabilityMeasure Z) : Prop :=
  ∀ m, InformationTheory.klDiv (q m : Measure Z) (P.posterior a m : Measure Z) ≠ ⊤

/-- The normalized free energy, equal to the log-density definition on its
finite integrability domain. -/
def freeEnergy (a : A) (q : Fin M → ProbabilityMeasure Z) : ℝ :=
  -P.logEvidence a + (M : ℝ)⁻¹ *
    ∑ m, (InformationTheory.klDiv (q m : Measure Z) (P.posterior a m : Measure Z)).toReal

def IsGlobalMin (a : A) (q : Fin M → ProbabilityMeasure Z) : Prop :=
  P.Admissible a q ∧ ∀ b r, P.Admissible b r → P.freeEnergy a q ≤ P.freeEnergy b r

theorem posterior_admissible (a : A) : P.Admissible a (P.posterior a) := by
  intro m
  simp

theorem posterior_freeEnergy (a : A) : P.freeEnergy a (P.posterior a) = -P.logEvidence a := by
  simp [freeEnergy]

theorem lower_bound (a : A) (q : Fin M → ProbabilityMeasure Z) :
    -P.logEvidence a ≤ P.freeEnergy a q := by
  unfold freeEnergy
  have h : 0 ≤ (M : ℝ)⁻¹ *
      ∑ m, (InformationTheory.klDiv (q m : Measure Z) (P.posterior a m : Measure Z)).toReal :=
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))
  linarith

/-- Equality in the variational bound identifies every posterior, using
Gibbs' equality theorem for actual finite measures. -/
theorem equality_iff (hM : 0 < M) (a : A) (q : Fin M → ProbabilityMeasure Z)
    (hq : P.Admissible a q) :
    P.freeEnergy a q = -P.logEvidence a ↔ q = P.posterior a := by
  constructor
  · intro he
    have hsum : (∑ m, (InformationTheory.klDiv (q m : Measure Z)
        (P.posterior a m : Measure Z)).toReal) = 0 := by
      have hm : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM)
      have hh : (M : ℝ)⁻¹ * (∑ m, (InformationTheory.klDiv (q m : Measure Z)
          (P.posterior a m : Measure Z)).toReal) = 0 := by
        unfold freeEnergy at he
        linarith
      exact (mul_eq_zero.mp hh).resolve_left (inv_ne_zero hm)
    funext m
    have hm : (InformationTheory.klDiv (q m : Measure Z)
        (P.posterior a m : Measure Z)).toReal = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)).mp hsum
        m (Finset.mem_univ m)
    have hz : InformationTheory.klDiv (q m : Measure Z) (P.posterior a m : Measure Z) = 0 :=
      (ENNReal.toReal_eq_zero_iff _).mp hm |>.resolve_right (hq m)
    letI : IsProbabilityMeasure (q m : Measure Z) := (q m).property
    letI : IsProbabilityMeasure (P.posterior a m : Measure Z) := (P.posterior a m).property
    have hm := InformationTheory.klDiv_eq_zero_iff.mp hz
    exact Subtype.ext hm
  · intro he
    subst q
    exact P.posterior_freeEnergy a

/-- Proposition 1, including the unique optimal variational distribution.
No existence of a log-evidence maximizer is assumed or concluded. -/
theorem global_minimizers_iff (hM : 0 < M) (a : A)
    (q : Fin M → ProbabilityMeasure Z) :
    P.IsGlobalMin a q ↔
      (∀ b, P.logEvidence b ≤ P.logEvidence a) ∧ q = P.posterior a := by
  constructor
  · rintro ⟨hq, hmin⟩
    have he : P.freeEnergy a q = -P.logEvidence a := le_antisymm
      (by simpa only [P.posterior_freeEnergy] using
        hmin a (P.posterior a) (P.posterior_admissible a)) (P.lower_bound a q)
    refine ⟨fun b => ?_, (P.equality_iff hM a q hq).mp he⟩
    have hb := hmin b (P.posterior b) (P.posterior_admissible b)
    rw [he, P.posterior_freeEnergy] at hb
    linarith
  · rintro ⟨hmax, rfl⟩
    refine ⟨P.posterior_admissible a, fun b r _ => ?_⟩
    rw [P.posterior_freeEnergy]
    exact (neg_le_neg (hmax b)).trans (P.lower_bound b r)

theorem maximizer_iff_exists_minimizer (hM : 0 < M) (a : A) :
    (∀ b, P.logEvidence b ≤ P.logEvidence a) ↔ ∃ q, P.IsGlobalMin a q := by
  constructor
  · intro h
    exact ⟨P.posterior a, (P.global_minimizers_iff hM a _).mpr ⟨h, rfl⟩⟩
  · rintro ⟨q, hq⟩
    exact ((P.global_minimizers_iff hM a q).mp hq).1
end PosteriorFamily

/-- The valid zero-tilt comparison requires a true optimum attaining zero
gap. Zero gap only at a tilted optimum is insufficient. -/
theorem zero_gap_comparator {ell tilted : A → ℝ} (a b : A)
    (hupper : ∀ x, tilted x ≤ ell x)
    (htrue : ∀ x, ell x ≤ ell b) (hzero : tilted b = ell b)
    (hmax : ∀ x, tilted x ≤ tilted a) :
    ell a = ell b := by
  have h := hmax b
  rw [hzero] at h
  exact le_antisymm (htrue a) (h.trans (hupper a))

/-- A zero-penalty tilted maximizer can fail to maximize the true likelihood.
Both likelihoods and gaps here are exact real numbers on a two-point model. -/
theorem zero_gap_at_tilted_max_not_sufficient :
    let ell : Bool → ℝ := fun b => if b then 1 else 0
    let gap : Bool → ℝ := fun b => if b then 2 else 0
    (∀ b, 0 ≤ gap b) ∧ gap false = 0 ∧
      (∀ b, ell b - gap b ≤ ell false - gap false) ∧ ell false < ell true := by
  dsimp
  refine ⟨?_, by norm_num, ?_, by norm_num⟩ <;> intro b <;> cases b <;> norm_num

end LatentDiffusion
