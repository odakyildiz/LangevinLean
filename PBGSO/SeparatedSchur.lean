import PBGSO.SeparatedCriteria

/-! # The full two-by-two small-gain condition

The smaller eigenvalue is written by its explicit quadratic formula. The
quadratic lower bound and positivity under the paper's determinant condition
are proved algebraically, then applied to the already derived actual coupling
work bounds. This also covers small-gain matrices that fail diagonal dominance.
-/
noncomputable section
open MeasureTheory Set
open scoped NNReal RealInnerProductSpace
namespace PBGSO

/-- Explicit smaller eigenvalue of [[a,-c/2],[-c/2,b]]. -/
def smallGainSpectralRate (a b c : ℝ) : ℝ :=
  (a + b - Real.sqrt ((a - b) ^ 2 + c ^ 2)) / 2

theorem smallGainSpectralRate_margins (a b c : ℝ) :
    0 ≤ a - smallGainSpectralRate a b c ∧
    0 ≤ b - smallGainSpectralRate a b c ∧
    c ^ 2 = 4 * (a - smallGainSpectralRate a b c) *
      (b - smallGainSpectralRate a b c) := by
  have hs := Real.sq_sqrt (show 0 ≤ (a - b) ^ 2 + c ^ 2 by positivity)
  have hp := Real.sqrt_nonneg ((a - b) ^ 2 + c ^ 2)
  have ha : a - b ≤ Real.sqrt ((a - b) ^ 2 + c ^ 2) := by
    nlinarith [sq_nonneg c]
  have hb : b - a ≤ Real.sqrt ((a - b) ^ 2 + c ^ 2) := by
    nlinarith [sq_nonneg c]
  dsimp [smallGainSpectralRate]
  constructor
  · linarith
  constructor
  · linarith
  · nlinarith

/-- The exact quadratic-form lower bound for the explicit spectral rate,
including degenerate eigenvalues and vanishing off-diagonal entries. -/
theorem small_gain_spectral_form (a b c u v : ℝ) :
    -a * u ^ 2 - b * v ^ 2 + c * u * v ≤
      -smallGainSpectralRate a b c * (u ^ 2 + v ^ 2) := by
  obtain ⟨ha, hb, he⟩ := smallGainSpectralRate_margins a b c
  by_cases hp : 0 < a - smallGainSpectralRate a b c
  · exact small_gain_schur hp he.le
  · have hz : a - smallGainSpectralRate a b c = 0 := le_antisymm (le_of_not_gt hp) ha
    have hc : c = 0 := by rw [hz, mul_zero, zero_mul] at he; nlinarith [sq_nonneg c]
    have hn := mul_nonneg hb (sq_nonneg v)
    subst c
    nlinarith

/-- The paper's positive-diagonal and determinant conditions give a
strictly positive rate, rather than merely positivity of a quadratic form. -/
theorem smallGainSpectralRate_pos {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hdet : c ^ 2 < 4 * a * b) : 0 < smallGainSpectralRate a b c := by
  have hs := Real.sq_sqrt (show 0 ≤ (a - b) ^ 2 + c ^ 2 by positivity)
  have hp := Real.sqrt_nonneg ((a - b) ^ 2 + c ^ 2)
  have hlt : Real.sqrt ((a - b) ^ 2 + c ^ 2) < a + b := by nlinarith
  dsimp [smallGainSpectralRate]
  linarith

variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype I]

/-- The full explicit spectral rate of the source small-gain matrix. -/
def separatedSpectralRate (D : TwistedGeometry S Z) (rO rS : ℝ)
    (LΨ LF Lb Lσ : ℝ≥0) : ℝ :=
  smallGainSpectralRate
    (rO - D.conditionNumber * (Lσ : ℝ) ^ 2 / 2)
    (rS - D.conditionNumber * (Lσ : ℝ) ^ 2 / 2)
    (Real.sqrt D.conditionNumber * ((LΨ : ℝ) * (LF : ℝ) + (Lb : ℝ)))

/-- Full actual-law small-gain criterion at the explicit spectral rate.
Every optimiser and sampler work estimate comes from the primitive separated
assumptions. The final joint inequality is a conclusion. -/
theorem separated_joint_monotonicity_spectral (M : Model S Θ Z X I)
    (D : TwistedGeometry S Z) {rO rS : ℝ} {LΨ LF Lb Lσ : ℝ≥0}
    (H : SeparatedAssumptions M D rO rS LΨ LF Lb Lσ) :
    TwistedJointMonotonicity M D (separatedSpectralRate D rO rS LΨ LF Lb Lσ) := by
  intro t ht s s' ν ν' Λ hc hp hp' hν hν' _ _ hwork hcost
  letI := hp
  letI := hp'
  have ho := separated_optimizer_work_bound M D H t ht s s' ν ν' hν hν' Λ hc hcost
  have hs := separated_sampler_integral_bound M D H s s' ν ν' Λ hc hwork hcost
  have hqO := D.optimizerSq_nonneg (s - s')
  have hqS : 0 ≤ ∫ zz, D.samplerSq (zz.1 - zz.2) ∂Λ :=
    integral_nonneg (fun zz => D.samplerSq_nonneg _)
  have hg := small_gain_spectral_form
    (rO - D.conditionNumber * (Lσ : ℝ) ^ 2 / 2)
    (rS - D.conditionNumber * (Lσ : ℝ) ^ 2 / 2)
    (Real.sqrt D.conditionNumber * ((LΨ : ℝ) * (LF : ℝ) + (Lb : ℝ)))
    (Real.sqrt (D.optimizerSq (s - s')))
    (Real.sqrt (∫ zz, D.samplerSq (zz.1 - zz.2) ∂Λ))
  rw [Real.sq_sqrt hqO, Real.sq_sqrt hqS] at hg
  dsimp only [separatedSpectralRate]
  nlinarith

/-- Precisely the source's three strict scalar conditions ensure that the
certified full law-level rate is positive. -/
theorem separatedSpectralRate_pos (D : TwistedGeometry S Z) (rO rS : ℝ)
    (LΨ LF Lb Lσ : ℝ≥0)
    (hO : 0 < 2 * rO - D.conditionNumber * (Lσ : ℝ) ^ 2)
    (hS : 0 < 2 * rS - D.conditionNumber * (Lσ : ℝ) ^ 2)
    (hdet : D.conditionNumber * ((LΨ : ℝ) * (LF : ℝ) + (Lb : ℝ)) ^ 2 <
      (2 * rO - D.conditionNumber * (Lσ : ℝ) ^ 2) *
        (2 * rS - D.conditionNumber * (Lσ : ℝ) ^ 2)) :
    0 < separatedSpectralRate D rO rS LΨ LF Lb Lσ := by
  have hκ : 0 ≤ D.conditionNumber := le_trans (by norm_num : (0 : ℝ) ≤ 1)
    D.conditionNumber_ge_one
  apply smallGainSpectralRate_pos (by linarith) (by linarith)
  rw [mul_pow, Real.sq_sqrt hκ]
  nlinarith

end PBGSO
