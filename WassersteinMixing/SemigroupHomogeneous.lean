import WassersteinMixing.SemigroupEulerMap
import WassersteinMixing.SemigroupPair
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! # Time-homogeneity of the actual Langevin transition

Restarted Euler endpoints are measurable functions of the stationary state
and the fresh Brownian future. The actual input-pair laws agree at all cut
times. Finite Euler anchored laws therefore agree, and genuine Euler limits
give equality of the actual diffusion anchored laws.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace WassersteinMixing.CanonicalSemigroup

/-- The actual finite shifted Euler state. -/
def shiftedEuler (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (a : ℝ≥0) (h : ℝ) (n : ℕ) :
    Lp (E P.dimension) 2 (actualProbability P V) := by
  let := actualProbability_isProbability P V hV
  exact ULA.additiveEulerChain
    (ULA.lpDrift (actualProbability P V) (gradient V) hV.gradientLipschitz) h
    (state P V hV a)
    (ULA.brownianLangevinNoise (actualProbability P V) (brownian P)
      (brownian_preBrownian P V hV) a) n

/-- Equality of actual fresh-input laws gives equality of finite anchored
Euler laws at any two nonnegative starting times. -/
theorem shiftedEuler_pair_law (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (a b : ℝ≥0) (h : ℝ) (hh : 0 ≤ h) (n : ℕ) :
    (actualProbability P V).map (fun ω ↦
      (state P V hV a ω, shiftedEuler P V hV a h n ω)) =
    (actualProbability P V).map (fun ω ↦
      (state P V hV b ω, shiftedEuler P V hV b h n ω)) := by
  let := actualProbability_isProbability P V hV
  let F : (E P.dimension × (Fin P.dimension → ℝ≥0 → ℝ)) →
      E P.dimension × E P.dimension := fun p ↦ (p.1, pointwiseEulerMap P V h n p)
  have hF : Measurable F := measurable_fst.prodMk (pointwiseEulerMap_measurable P V hV h n)
  have hlaw (c : ℝ≥0) : (actualProbability P V).map (fun ω ↦
      (state P V hV c ω, shiftedEuler P V hV c h n ω)) =
      ((actualProbability P V).map (fun ω ↦
        (state P V hV c ω, actualBrownianFuture P c ω))).map F := by
    rw [Measure.map_map hF ((Lp.stronglyMeasurable _).measurable.prodMk
      (actualBrownianFuture_measurable P c))]
    apply Measure.map_congr
    filter_upwards [shiftedEuler_coe P V hV c h hh n] with ω he
    exact Prod.ext rfl he
  rw [hlaw a, hlaw b, actualState_future_joint_law_eq P V hV a b]

/-- The true diffusion's anchored pair law is invariant under simultaneous
forward shifts of both times. This is derived from actual Brownian inputs. -/
theorem state_pair_law (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (a b : ℝ≥0) (t : ℝ) (ht : 0 ≤ t) :
    (actualProbability P V).map (fun ω ↦
      (state P V hV a ω, state P V hV ((a : ℝ) + t) ω)) =
    (actualProbability P V).map (fun ω ↦
      (state P V hV b ω, state P V hV ((b : ℝ) + t) ω)) := by
  let := actualProbability_isProbability P V hV
  let r : ℕ → ℝ := fun n ↦ t / ((n + 1 : ℕ) : ℝ)
  let X := fun (c : ℝ≥0) (n : ℕ) (ω : ActualSpace P) ↦
    (state P V hV c ω, shiftedEuler P V hV c (r n) (n + 1) ω)
  let Z := fun (c : ℝ≥0) (ω : ActualSpace P) ↦
    (state P V hV c ω, state P V hV ((c : ℝ) + t) ω)
  have hm (c : ℝ≥0) (n : ℕ) : AEMeasurable (X c n) (actualProbability P V) :=
    (Lp.aestronglyMeasurable _).aemeasurable.prodMk (Lp.aestronglyMeasurable _).aemeasurable
  have hlim (c : ℝ≥0) : TendstoInMeasure (actualProbability P V) (X c) atTop (Z c) := by
    have he := tendstoInMeasure_of_tendsto_Lp (shiftedEuler_tendsto P V hV c t c.coe_nonneg ht)
    intro ε hε
    simpa only [X, Z, r, shiftedEuler, Prod.edist_eq, edist_self, zero_max] using he ε hε
  have hd (c : ℝ≥0) := (hlim c).tendstoInDistribution (hm c)
  have heq (n : ℕ) : (actualProbability P V).map (X a n) =
      (actualProbability P V).map (X b n) :=
    shiftedEuler_pair_law P V hV a b (r n) (by dsimp [r]; positivity) (n + 1)
  have hd' : TendstoInDistribution (X a) atTop (Z b)
      (fun _ ↦ actualProbability P V) (actualProbability P V) := by
    refine ⟨hm a, (hd b).aemeasurable_limit, ?_⟩
    apply (hd b).tendsto.congr'
    exact Eventually.of_forall fun n ↦ Subtype.ext (heq n).symm
  exact tendstoInDistribution_unique (X a) (hd a) hd'

variable {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The actual transition compressed at any starting time is the same
operator as the transition compressed at zero. -/
theorem shifted_compression_eq_op (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (a : ℝ≥0) (t : ℝ) (ht : 0 ≤ t) :
    ObservableTransition.compression (evaluation (𝕜 := 𝕜) (F := F) P V hV a)
      (evaluation P V hV ((a : ℝ) + t)) = op P V hV t := by
  apply StationaryObservables.compression_eq_of_pair_law (𝕜 := 𝕜)
    (ULA.gibbsMeasure V) (actualProbability P V) (actualProbability P V)
    (state P V hV a) (state P V hV ((a : ℝ) + t)) (state P V hV 0) (state P V hV t)
    (state_law P V hV a) (state_law P V hV ((a : ℝ) + t))
    (state_law P V hV 0) (state_law P V hV t)
  simpa only [NNReal.coe_zero, zero_add] using state_pair_law P V hV a 0 t ht

end WassersteinMixing.CanonicalSemigroup
