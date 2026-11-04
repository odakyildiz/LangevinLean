import WassersteinMixing.Parameters
import KineticLangevin.FlowLaw
import UnadjustedLangevin.MALACoupling
import UnadjustedLangevin.MarkovLaw

set_option linter.style.header false

/-! # Contraction of the actual independent-noise ULA laws

The potential hypotheses prove the sharp pathwise contraction.  Extending
arbitrary initial couplings by the same noise then proves the transport
contraction of the genuine Markov laws, including ordinary Gaussian ULA.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace WassersteinMixing

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] in
/-- Shared noise cancels, and the original potential hypotheses give the
paper's exact contraction `1 - α h`. -/
theorem ula_shared_noise_contraction (P : Parameters) (V : H → ℝ)
    (hV : PotentialAssumptions P V) (x y z : H) :
    ‖ULA.malaProposal V P.step x z - ULA.malaProposal V P.step y z‖ ≤
      P.contraction * ‖x - y‖ := by
  have hsum : 0 < P.alpha + P.beta := add_pos P.alpha_pos P.beta_pos
  have hsmall : P.step ≤ 2 / (P.alpha + P.beta) := by
    apply (le_div_iff₀ hsum).mpr
    have hcurv := mul_le_mul_of_nonneg_left P.alpha_le_beta P.step_pos.le
    nlinarith [P.step_beta_le]
  have hc := ULA.strong_smooth_gradient_step_contract V P.alpha P.step
    ⟨P.beta, P.beta_pos.le⟩ (hV.regularity.differentiable (by norm_num))
    hV.strongConvexity hV.gradientLipschitz P.alpha_le_beta hsum P.step_pos.le hsmall x y
  simpa only [ULA.malaProposal, add_sub_add_right_eq_sub, Parameters.contraction] using hc

/-- One actual Markov step contracts Wasserstein distance for any shared
independent innovation law, so in particular for standard Gaussian noise. -/
theorem ula_markovStep_wasserstein2_le (P : Parameters) (V : H → ℝ)
    (hV : PotentialAssumptions P V) (η : Measure H) [IsProbabilityMeasure η]
    (μ ν : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ULA.wasserstein2 (ULA.markovStep (ULA.malaProposal V P.step) η μ)
      (ULA.markovStep (ULA.malaProposal V P.step) η ν) ≤
      ENNReal.ofReal P.contraction * ULA.wasserstein2 μ ν := by
  let q : ℝ≥0 := ⟨P.contraction, P.contraction_nonneg⟩
  have hF := ULA.malaProposal_measurable V P.step ⟨P.beta, P.beta_pos.le⟩ hV.gradientLipschitz
  have hb := KineticLangevin.randomMapLaw_wasserstein2_le
    (Function.uncurry (ULA.malaProposal V P.step)) hF q
    (fun x y z ↦ ula_shared_noise_contraction P V hV x y z) μ ν η
  have he : (q : ℝ≥0∞) = ENNReal.ofReal P.contraction := by
    exact (ENNReal.ofReal_coe_nnreal (p := q)).symm
  rw [he] at hb
  exact hb

/-- Iteration of the actual Markov laws preserves the exact geometric factor. -/
theorem ula_markovLaws_wasserstein2_le (P : Parameters) (V : H → ℝ)
    (hV : PotentialAssumptions P V) (η : Measure H) [IsProbabilityMeasure η]
    (μ ν : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (k : ℕ) :
    ULA.wasserstein2 (ULA.markovLaws (ULA.malaProposal V P.step) η μ k)
      (ULA.markovLaws (ULA.malaProposal V P.step) η ν k) ≤
      (ENNReal.ofReal P.contraction) ^ k * ULA.wasserstein2 μ ν := by
  have hF := ULA.malaProposal_measurable V P.step ⟨P.beta, P.beta_pos.le⟩ hV.gradientLipschitz
  induction k with
  | zero => simp [ULA.markovLaws]
  | succ k ih =>
    have hμ := ULA.markovLaws_isProbability (ULA.malaProposal V P.step) hF μ η k
    have hν := ULA.markovLaws_isProbability (ULA.malaProposal V P.step) hF ν η k
    have hb := ula_markovStep_wasserstein2_le P V hV η
      (ULA.markovLaws (ULA.malaProposal V P.step) η μ k)
      (ULA.markovLaws (ULA.malaProposal V P.step) η ν k)
    calc
      _ ≤ ENNReal.ofReal P.contraction *
          ULA.wasserstein2 (ULA.markovLaws (ULA.malaProposal V P.step) η μ k)
            (ULA.markovLaws (ULA.malaProposal V P.step) η ν k) := hb
      _ ≤ ENNReal.ofReal P.contraction *
          ((ENNReal.ofReal P.contraction) ^ k * ULA.wasserstein2 μ ν) :=
        mul_le_mul' le_rfl ih
      _ = _ := by rw [pow_succ]; ac_rfl

omit [BorelSpace H] in
/-- The Markov-law implementation is exactly the existing Gaussian ULA
transition iterated on its initial measure. -/
theorem ula_iterate_eq_markovLaws (V : H → ℝ) (h : ℝ) (μ : Measure H) (k : ℕ) :
    (ULA.ulaLawStep V h)^[k] μ =
      ULA.markovLaws (ULA.malaProposal V h) (stdGaussian H) μ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ULA.markovLaws, ← ih]
    rfl

/-- Wasserstein contraction of the existing actual independent-Gaussian ULA
algorithm, with no assumed coupling or contraction field. -/
theorem ula_iterate_wasserstein2_le (P : Parameters) (V : H → ℝ)
    (hV : PotentialAssumptions P V) (μ ν : Measure H)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (k : ℕ) :
    ULA.wasserstein2 ((ULA.ulaLawStep V P.step)^[k] μ)
      ((ULA.ulaLawStep V P.step)^[k] ν) ≤
      (ENNReal.ofReal P.contraction) ^ k * ULA.wasserstein2 μ ν := by
  rw [ula_iterate_eq_markovLaws, ula_iterate_eq_markovLaws]
  exact ula_markovLaws_wasserstein2_le P V hV (stdGaussian H) μ ν k

/-- Finite initial transport gives the ordinary real-valued contraction;
the proved extended bound also guarantees finite output transport. -/
theorem ula_iterate_wasserstein2Real_le (P : Parameters) (V : H → ℝ)
    (hV : PotentialAssumptions P V) (μ ν : Measure H)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hfinite : ULA.wasserstein2 μ ν ≠ ⊤) (k : ℕ) :
    ULA.wasserstein2Real ((ULA.ulaLawStep V P.step)^[k] μ)
      ((ULA.ulaLawStep V P.step)^[k] ν) ≤
      P.contraction ^ k * ULA.wasserstein2Real μ ν := by
  have hb := ula_iterate_wasserstein2_le P V hV μ ν k
  have hprod : (ENNReal.ofReal P.contraction) ^ k * ULA.wasserstein2 μ ν ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hfinite
  have hr := ENNReal.toReal_mono hprod hb
  simpa only [ULA.wasserstein2Real, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal P.contraction_nonneg] using hr

/-- Finite initial transport stays finite under the actual Gaussian chain. -/
theorem ula_iterate_transport_finite (P : Parameters) (V : H → ℝ)
    (hV : PotentialAssumptions P V) (μ ν : Measure H)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hfinite : ULA.wasserstein2 μ ν ≠ ⊤) (k : ℕ) :
    ULA.wasserstein2 ((ULA.ulaLawStep V P.step)^[k] μ)
      ((ULA.ulaLawStep V P.step)^[k] ν) ≠ ⊤ := by
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hfinite)
    (ula_iterate_wasserstein2_le P V hV μ ν k)

/-- Once a genuine invariant probability law has been identified, contraction
towards it follows from the potential hypotheses and its invariance equality. -/
theorem ula_to_invariant_wasserstein2Real_le (P : Parameters) (V : H → ℝ)
    (hV : PotentialAssumptions P V) (μ ν : Measure H)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ULA.ulaLawStep V P.step ν = ν)
    (hfinite : ULA.wasserstein2 μ ν ≠ ⊤) (k : ℕ) :
    ULA.wasserstein2Real ((ULA.ulaLawStep V P.step)^[k] μ) ν ≤
      P.contraction ^ k * ULA.wasserstein2Real μ ν := by
  have hb := ula_iterate_wasserstein2Real_le P V hV μ ν hfinite k
  rw [Function.iterate_fixed hν k] at hb
  exact hb

end WassersteinMixing
