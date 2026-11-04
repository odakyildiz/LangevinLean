import WassersteinMixing.SemigroupEuler
import WassersteinMixing.SemigroupGlobal

/-! # Actual shifted Brownian Euler approximations

Restarting the constructed global Langevin solution at time `a` gives the
integral equation driven by the actual future Brownian increments. Matching
Euler approximations therefore converge to `X_(a+t)` from the actual state
`X_a`, without a Markov or semigroup hypothesis.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

namespace WassersteinMixing.CanonicalSemigroup

/-- The global solution restarts at every nonnegative time with its actual
Brownian increment source, by subtraction of the integral equation. -/
theorem shifted_state_integral (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (a T : ℝ) (ha : 0 ≤ a) (hT : 0 ≤ T) :
    letI := actualProbability_isProbability P V hV
    ∀ t ∈ Icc 0 T, state P V hV (a + t) - state P V hV a =
      -(∫ s in 0..t, ULA.lpDrift (actualProbability P V) (gradient V)
        hV.gradientLipschitz (state P V hV (a + s))) +
      ULA.brownianLangevinNoise (actualProbability P V) (brownian P)
        (brownian_preBrownian P V hV) a t := by
  let := actualProbability_isProbability P V hV
  exact ULA.lp_brownian_integral_shift (actualProbability P V) V
    ⟨P.beta, P.beta_pos.le⟩ hV.gradientLipschitz (initial P V hV)
    (brownian P) (brownian_preBrownian P V hV) (state P V hV)
    (continuous_state P V hV) (a + T)
    (fun t ht ↦ state_integral P V hV t ht.1) a T ha hT le_rfl

/-- Fixed-horizon Euler convergence from the actual state at a shifted time. -/
theorem shiftedEuler_tendsto (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    letI := actualProbability_isProbability P V hV
    Tendsto (fun n : ℕ ↦ ULA.additiveEulerChain
      (ULA.lpDrift (actualProbability P V) (gradient V) hV.gradientLipschitz)
      (t / ((n + 1 : ℕ) : ℝ)) (state P V hV a)
      (ULA.brownianLangevinNoise (actualProbability P V) (brownian P)
        (brownian_preBrownian P V hV) a) (n + 1)) atTop (𝓝 (state P V hV (a + t))) := by
  let := actualProbability_isProbability P V hV
  exact ULA.lp_langevin_integral_euler_tendsto (actualProbability P V) V
    ⟨P.beta, P.beta_pos.le⟩ hV.gradientLipschitz (state P V hV a)
    (ULA.brownianLangevinNoise (actualProbability P V) (brownian P)
      (brownian_preBrownian P V hV) a) (fun s ↦ state P V hV (a + s))
    (ULA.brownianLangevinNoise_zero _ _ _ a)
    ((continuous_state P V hV).comp (continuous_const.add continuous_id)) t ht
    (shifted_state_integral P V hV a t ha ht)

/-- The same actual shifted endpoint limit on arbitrary positive vanishing
meshes and step counts with convergent elapsed times. -/
theorem shiftedEuler_variable_tendsto {I : Type*} {l : Filter I}
    (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V)
    (a T : ℝ) (ha : 0 ≤ a) (hT : 0 ≤ T)
    (step : I → ℝ) (count : I → ℕ) (hstep : ∀ i, 0 ≤ step i)
    (hmesh : Tendsto step l (𝓝 0)) (hbound : ∀ i, (count i : ℝ) * step i ≤ T)
    (t : ℝ) (htime : Tendsto (fun i ↦ (count i : ℝ) * step i) l (𝓝 t)) :
    letI := actualProbability_isProbability P V hV
    Tendsto (fun i ↦ ULA.additiveEulerChain
      (ULA.lpDrift (actualProbability P V) (gradient V) hV.gradientLipschitz)
      (step i) (state P V hV a)
      (ULA.brownianLangevinNoise (actualProbability P V) (brownian P)
        (brownian_preBrownian P V hV) a) (count i)) l (𝓝 (state P V hV (a + t))) := by
  let := actualProbability_isProbability P V hV
  exact additiveEulerChain_variable_tendsto
    (ULA.lpDrift (actualProbability P V) (gradient V) hV.gradientLipschitz)
    ⟨P.beta, P.beta_pos.le⟩ (ULA.lpDrift_lipschitz _ _ hV.gradientLipschitz)
    (state P V hV a)
    (ULA.brownianLangevinNoise (actualProbability P V) (brownian P)
      (brownian_preBrownian P V hV) a) (fun s ↦ state P V hV (a + s))
    (ULA.brownianLangevinNoise_zero _ _ _ a)
    ((continuous_state P V hV).comp (continuous_const.add continuous_id)) T hT
    (shifted_state_integral P V hV a T ha hT) step count hstep hmesh hbound t htime

end WassersteinMixing.CanonicalSemigroup
