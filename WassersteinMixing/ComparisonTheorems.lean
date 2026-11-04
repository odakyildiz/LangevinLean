import WassersteinMixing.PoissonComparison
import WassersteinMixing.Invariant
import WassersteinMixing.TransportGeometry
import WassersteinMixing.Complexity
import UnadjustedLangevin.Gibbs

set_option linter.style.header false

/-! # Transport conclusions of the stationary Poisson comparison

These reusable transport lemmas combine the proved synchronous comparison with
the constructed Gaussian ULA invariant law. The paper endpoints instantiate
this comparison using only the source potential assumptions.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace WassersteinMixing

variable {H E Ω : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Q : Measure Ω} {P : Parameters}

/-- The exact law identifications needed to apply the abstract comparison to
this paper. No invariant law or numerical error conclusion is assumed. -/
structure ULAPoissonComparison (S : PoissonProcess H E Q P.step P.step_pos)
    (score : H) (V : E → ℝ) extends PoissonComparison S score where
  dimension_eq : P.dimension = Module.finrank ℝ E
  target_law : Q.map (reference 0) = ULA.gibbsMeasure V
  chain_law : ∀ n, Q.map (chain n) =
    (ULA.ulaLawStep V P.step)^[n] (ULA.gibbsMeasure V)

namespace ULAPoissonComparison
variable {S : PoissonProcess H E Q P.step P.step_pos} {score : H} {V : E → ℝ}
  (C : ULAPoissonComparison S score V)

include C in
/-- The checked comparison bounds every actual stationary-start Gaussian iterate. -/
theorem stationary_start_bound (n : ℕ) :
    ULA.wasserstein2Real (ULA.gibbsMeasure V)
      ((ULA.ulaLawStep V P.step)^[n] (ULA.gibbsMeasure V)) ≤ P.bias := by
  have h := C.toPoissonComparison.stationary_transport_bound n
  rwa [C.target_law, C.chain_law] at h

include C in
theorem stationary_start_finite (n : ℕ) :
    ULA.wasserstein2 (ULA.gibbsMeasure V)
      ((ULA.ulaLawStep V P.step)^[n] (ULA.gibbsMeasure V)) ≠ ⊤ := by
  have h := C.toPoissonComparison.stationary_transport_finite n
  rwa [C.target_law, C.chain_law] at h

end ULAPoissonComparison

/-- Actual independent-Gaussian iteration preserves the probability normalization. -/
theorem ula_iterate_isProbability (P : Parameters) (V : E → ℝ)
    (hV : PotentialAssumptions P V) (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure ((ULA.ulaLawStep V P.step)^[n] μ) := by
  rw [ula_iterate_eq_markovLaws]
  exact ULA.markovLaws_isProbability (ULA.malaProposal V P.step)
    (ULA.malaProposal_measurable V P.step ⟨P.beta, P.beta_pos.le⟩ hV.gradientLipschitz)
    μ (ProbabilityTheory.stdGaussian E) n

/-- Finiteness of the transport to the constructed invariant law is proved
from second moments and the actual Markov contraction. -/
theorem transport_invariant_finite (P : Parameters) (V : E → ℝ)
    (hV : PotentialAssumptions P V) (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : E → E) 2 μ) (n : ℕ) :
    ULA.wasserstein2 ((ULA.ulaLawStep V P.step)^[n] μ) (invariantLaw P V hV) ≠ ⊤ := by
  have h := ula_iterate_transport_finite P V hV μ (invariantLaw P V hV)
    (ULA.wasserstein2_ne_top_of_memLp μ _ hμ (invariantLaw_memLp P V hV)) n
  rwa [Function.iterate_fixed (invariantLaw_invariant P V hV) n] at h

variable {S : PoissonProcess H E Q P.step P.step_pos} {score : H} {V : E → ℝ}

/-- Theorem 1's exact bias conclusion for the genuinely constructed invariant
law, from the actual-law Poisson comparison. -/
theorem bias_from_comparison (hV : PotentialAssumptions P V) (C : ULAPoissonComparison S score V) :
    ULA.wasserstein2Real (ULA.gibbsMeasure V) (invariantLaw P V hV) ≤
      6 * P.step * Real.sqrt (P.condition * P.beta * P.dimension) := by
  let π := ULA.gibbsMeasure V
  let ν := invariantLaw P V hV
  let : IsProbabilityMeasure π := ULA.isProbabilityMeasure_gibbsMeasure V P.alpha
    P.alpha_pos (hV.regularity.differentiable (by norm_num)) hV.strongConvexity
  have hπ : MemLp (id : E → E) 2 π := ULA.memLp_id_gibbsMeasure V P.alpha
    P.alpha_pos (hV.regularity.differentiable (by norm_num)) hV.strongConvexity
  have hupper (n : ℕ) : ULA.wasserstein2Real π ν ≤
      P.bias + ULA.wasserstein2Real ((ULA.ulaLawStep V P.step)^[n] π) ν := by
    let := ula_iterate_isProbability P V hV π n
    have ht := wasserstein2Real_triangle π ((ULA.ulaLawStep V P.step)^[n] π) ν
      (C.stationary_start_finite n) (transport_invariant_finite P V hV π hπ n)
    have hb := C.stationary_start_bound n
    linarith
  have hlim := invariantLaw_attraction P V hV π hπ
  have he : Tendsto (fun n : ℕ ↦ P.bias +
      ULA.wasserstein2Real ((ULA.ulaLawStep V P.step)^[n] π) ν) atTop (𝓝 P.bias) := by
    simpa only [add_zero] using tendsto_const_nhds.add hlim
  exact le_of_tendsto_of_tendsto tendsto_const_nhds he (Eventually.of_forall hupper)

/-- Corollary 1.1's finite-time statement for the actual Gaussian ULA laws.
No transport triangle, invariant existence, contraction, or limit is assumed. -/
theorem convergence_from_comparison (hV : PotentialAssumptions P V)
    (C : ULAPoissonComparison S score V) (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : E → E) 2 μ) (n : ℕ) :
    ULA.wasserstein2Real ((ULA.ulaLawStep V P.step)^[n] μ) (ULA.gibbsMeasure V) ≤
      P.contraction ^ n * ULA.wasserstein2Real μ (invariantLaw P V hV) +
        6 * P.step * Real.sqrt (P.condition * P.beta * P.dimension) := by
  let ν := invariantLaw P V hV
  let π := ULA.gibbsMeasure V
  let : IsProbabilityMeasure π := ULA.isProbabilityMeasure_gibbsMeasure V P.alpha
    P.alpha_pos (hV.regularity.differentiable (by norm_num)) hV.strongConvexity
  let := ula_iterate_isProbability P V hV μ n
  have hπ : MemLp (id : E → E) 2 π := ULA.memLp_id_gibbsMeasure V P.alpha
    P.alpha_pos (hV.regularity.differentiable (by norm_num)) hV.strongConvexity
  have ht := wasserstein2Real_triangle ((ULA.ulaLawStep V P.step)^[n] μ) ν π
    (transport_invariant_finite P V hV μ hμ n)
    (ULA.wasserstein2_ne_top_of_memLp ν π (invariantLaw_memLp P V hV) hπ)
  rw [wasserstein2Real_symm ν π] at ht
  have hc := invariantLaw_mixing P V hV μ hμ n
  have hb := bias_from_comparison hV C
  linarith

/-- The exact scale-invariant mixing complexity, for the actual Gaussian laws,
with the same actual-law Poisson comparison. -/
theorem accuracy_from_comparison (hV : PotentialAssumptions P V)
    (C : ULAPoissonComparison S score V) (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : E → E) 2 μ) (ε : ℝ) (hε : 0 < ε)
    (hstep : P.step = paperStep P.beta P.dimension ε) (n : ℕ)
    (hn : iterationPrefactor P.alpha P.beta P.dimension ε *
      Real.log (1 + 2 * Real.sqrt P.alpha *
        ULA.wasserstein2Real μ (invariantLaw P V hV) / ε) ≤ (n : ℝ)) :
    Real.sqrt P.alpha *
      ULA.wasserstein2Real ((ULA.ulaLawStep V P.step)^[n] μ) (ULA.gibbsMeasure V) ≤ ε := by
  have hd : 0 < P.dimension := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hs := hstep
    simp only [hz, paperStep, Nat.cast_zero, Real.sqrt_zero, mul_zero, div_zero,
      min_eq_right (by norm_num : (0 : ℝ) ≤ 1), mul_zero] at hs
    exact P.step_pos.ne' hs
  have hb := convergence_from_comparison hV C μ hμ n
  have hs := mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg P.alpha)
  have hnumerical := paper_complexity_bound P.alpha P.beta P.dimension
    (ULA.wasserstein2Real μ (invariantLaw P V hV)) ε P.alpha_pos P.alpha_le_beta
    (by exact_mod_cast hd) ENNReal.toReal_nonneg hε n hn
  apply hs.trans
  simpa only [Parameters.contraction, Parameters.condition, hstep] using hnumerical

end WassersteinMixing
