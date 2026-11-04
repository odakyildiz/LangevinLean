import WassersteinMixing.ActualMarkovPast
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-! # The actual restarted state and fresh Brownian input

The state at every nonnegative cut time is measurable from the past. Its
joint law with the independent future is exactly the Gibbs/future product,
and the entire future path law does not depend on the cut time.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace WassersteinMixing

variable (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V)

theorem actualState_adapted_pastAt (a : ℝ≥0) :
    AEStronglyMeasurable[ULA.lpLangevinPast (actualProbability P V)
      (CanonicalSemigroup.initial P V hV) (actualBrownianNoise P V hV) (a : ℝ)]
      (CanonicalSemigroup.state P V hV a) (actualProbability P V) := by
  let := actualProbability_isProbability P V hV
  exact ULA.lp_langevin_integral_naturalPast (actualProbability P V) V
    ⟨P.beta, P.beta_pos.le⟩ hV.gradientLipschitz (CanonicalSemigroup.initial P V hV)
    (actualBrownianNoise P V hV) (CanonicalSemigroup.state P V hV)
    (ULA.brownianLangevinNoise_continuous _ _ _ _) (ULA.brownianLangevinNoise_zero _ _ _ _)
    (CanonicalSemigroup.continuous_state P V hV) a a.coe_nonneg
    (fun t ht ↦ CanonicalSemigroup.state_integral P V hV t ht.1) a ⟨a.coe_nonneg, le_rfl⟩

/-- The actual state is independent of the complete fresh Brownian future. -/
theorem actualState_future_independent (a : ℝ≥0) :
    IndepFun (CanonicalSemigroup.state P V hV a) (actualBrownianFuture P a) (actualProbability P V) := by
  have hx := actualState_adapted_pastAt P V hV a
  have hi := actualBrownian_future_independent_pastAt P V hV a
  have hm : (inferInstance : MeasurableSpace (E P.dimension)).comap (hx.mk _) ≤
      ULA.lpLangevinPast (actualProbability P V) (CanonicalSemigroup.initial P V hV)
        (actualBrownianNoise P V hV) (a : ℝ) := hx.stronglyMeasurable_mk.measurable.comap_le
  have hi' : IndepFun (actualBrownianFuture P a) (hx.mk _) (actualProbability P V) :=
    indep_of_indep_of_le_right hi hm
  exact hi'.symm.congr hx.ae_eq_mk.symm (Filter.EventuallyEq.rfl)

/-- Exact fresh-input product law at the actual stationary state. -/
theorem actualState_future_joint_law (a : ℝ≥0) :
    (actualProbability P V).map (fun ω ↦
      (CanonicalSemigroup.state P V hV a ω, actualBrownianFuture P a ω)) =
      (ULA.gibbsMeasure V).prod ((actualProbability P V).map (actualBrownianFuture P a)) := by
  let := actualProbability_isProbability P V hV
  rw [(actualState_future_independent P V hV a).map_prod_eq_prod_map_map
    (Lp.aestronglyMeasurable _).aemeasurable (actualBrownianFuture_measurable P a).aemeasurable,
    CanonicalSemigroup.state_law]

private theorem preBrownian_shift_path_law {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B Q) (hBmeas : ∀ t, Measurable (B t)) (a b : ℝ≥0) :
    Q.map (fun ω t ↦ B (a + t) ω - B a ω) = Q.map (fun ω t ↦ B (b + t) ω - B b ω) := by
  apply (map_eq_iff_forall_finset_map_restrict_eq
    (measurable_pi_iff.mpr (fun t ↦ (hBmeas _).sub (hBmeas _))).aemeasurable
    (measurable_pi_iff.mpr (fun t ↦ (hBmeas _).sub (hBmeas _))).aemeasurable).mpr
  intro I
  exact (hB.shift a).hasLaw I |>.map_eq.trans ((hB.shift b).hasLaw I).map_eq.symm

include hV in
/-- Shift-invariance of the entire raw vector future law, proved from the
Brownian finite-dimensional distributions and coordinate independence. -/
theorem actualBrownianFuture_law_eq (a b : ℝ≥0) :
    (actualProbability P V).map (actualBrownianFuture P a) =
      (actualProbability P V).map (actualBrownianFuture P b) := by
  let := actualTarget_isProbability P V hV
  let := (diagonalGibbsCoupling P V).isProbabilityMeasure
  let Q := ULA.CanonicalBrownian.vectorProbability (Fin P.dimension)
  let F : ℝ≥0 → ULA.CanonicalBrownian.VectorSample (Fin P.dimension) →
      Fin P.dimension → ℝ≥0 → ℝ := fun c ω i t ↦
      ULA.CanonicalBrownian.coordinate i (c + t) ω - ULA.CanonicalBrownian.coordinate i c ω
  have hF : ∀ c, Measurable (F c) := by
    intro c
    exact measurable_pi_iff.mpr (fun i ↦ measurable_pi_iff.mpr (fun t ↦
      ((ULA.CanonicalBrownian.process_measurable _).comp (measurable_pi_apply i)).sub
      ((ULA.CanonicalBrownian.process_measurable _).comp (measurable_pi_apply i))))
  have hind (c : ℝ≥0) : iIndepFun (fun i ω ↦ F c ω i) Q :=
    (ULA.CanonicalBrownian.coordinate_paths_independent (Fin P.dimension)).comp
      (fun _ p t ↦ p (c + t) - p c) (by intro i; fun_prop)
  have hmap (c : ℝ≥0) : Q.map (F c) =
      Measure.infinitePi (fun i ↦ Q.map (fun ω ↦ F c ω i)) := by
    exact (hind c).map_fun_eq_infinitePi_map (fun i ↦
      show Measurable (fun ω ↦ F c ω i) from (measurable_pi_apply i).comp (hF c))
  have he : Q.map (F a) = Q.map (F b) := by
    rw [hmap a, hmap b]
    congr 1
    funext i
    exact preBrownian_shift_path_law Q (ULA.CanonicalBrownian.coordinate i)
      (ULA.CanonicalBrownian.coordinate_isPreBrownian i)
      (fun t ↦ (ULA.CanonicalBrownian.process_measurable t).comp (measurable_pi_apply i)) a b
  have hp (c : ℝ≥0) : (actualProbability P V).map (actualBrownianFuture P c) = Q.map (F c) := by
    change ((diagonalGibbsCoupling P V).joint.prod Q).map ((F c) ∘ Prod.snd) = _
    rw [← Measure.map_map (hF c) measurable_snd, Measure.map_snd_prod]
    simp only [measure_univ, one_smul]
  rw [hp a, hp b, he]

/-- The entire restarted input pair has the same law at every cut time. -/
theorem actualState_future_joint_law_eq (a b : ℝ≥0) :
    (actualProbability P V).map (fun ω ↦
      (CanonicalSemigroup.state P V hV a ω, actualBrownianFuture P a ω)) =
    (actualProbability P V).map (fun ω ↦
      (CanonicalSemigroup.state P V hV b ω, actualBrownianFuture P b ω)) := by
  rw [actualState_future_joint_law P V hV a, actualState_future_joint_law P V hV b,
    actualBrownianFuture_law_eq P V hV a b]

end WassersteinMixing
