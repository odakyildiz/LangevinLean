import WassersteinMixing.ConditionalMarkovClosure
import WassersteinMixing.SemigroupEulerMap
import WassersteinMixing.ObservableRange
import WassersteinMixing.SemigroupHomogeneous

/-! # The actual conditional Markov identity

The full Brownian past is independent of future increments. Conditional
averaging first proves the Markov property for actual finite Euler maps.
Their true strong limit, bounded observable convergence, and target `L²`
density prove it for every square-integrable observable of the diffusion.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BoundedContinuousFunction
namespace WassersteinMixing

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V)

omit [CompleteSpace H] in
private theorem actualEvaluation_bcf_eq_boundedComposition (t : ℝ) (φ : E P.dimension →ᵇ H) :
    letI := actualTarget_isProbability P V hV
    letI := actualProbability_isProbability P V hV
    CanonicalSemigroup.evaluation (𝕜 := ℝ) P V hV t
      (BoundedContinuousFunction.toLp 2 (ULA.gibbsMeasure V) ℝ φ) =
      boundedComposition (actualProbability P V) (CanonicalSemigroup.state P V hV t) φ := by
  let := actualTarget_isProbability P V hV
  let := actualProbability_isProbability P V hV
  apply Lp.ext
  have hx : MeasurePreserving (CanonicalSemigroup.state P V hV t)
      (actualProbability P V) (ULA.gibbsMeasure V) :=
    ⟨(Lp.stronglyMeasurable _).measurable, CanonicalSemigroup.state_law P V hV t⟩
  have he := (Lp.coeFn_compMeasurePreserving
    (BoundedContinuousFunction.toLp 2 (ULA.gibbsMeasure V) ℝ φ) hx).trans
    (hx.quasiMeasurePreserving.ae_eq_comp (BoundedContinuousFunction.coeFn_toLp 2 (ULA.gibbsMeasure V) ℝ φ))
  exact he.trans (boundedComposition_coe _ _ φ).symm

omit [CompleteSpace H] in
/-- Every evaluated target observable is adapted to the actual past at its
current time, by actual state adaptedness and measurable composition. -/
theorem actualEvaluation_adapted_pastAt (a : ℝ≥0) (f : Lp H 2 (ULA.gibbsMeasure V)) :
    AEStronglyMeasurable[ULA.lpLangevinPast (actualProbability P V)
      (CanonicalSemigroup.initial P V hV) (actualBrownianNoise P V hV) (a : ℝ)]
      (CanonicalSemigroup.evaluation (𝕜 := ℝ) P V hV a f) (actualProbability P V) := by
  have hx : MeasurePreserving (CanonicalSemigroup.state P V hV a)
      (actualProbability P V) (ULA.gibbsMeasure V) :=
    ⟨(Lp.stronglyMeasurable _).measurable, CanonicalSemigroup.state_law P V hV a⟩
  have ha := actualState_adapted_pastAt P V hV a
  have hf := (Lp.stronglyMeasurable f).comp_measurable ha.measurable_mk
  apply hf.aestronglyMeasurable.congr
  exact (ha.ae_eq_mk.fun_comp f).symm.trans (Lp.coeFn_compMeasurePreserving f hx).symm

/-- Conditional means of all future observables depend only on the actual
current state, as proved by Euler approximation and density. -/
theorem actual_conditional_state_measurable (a : ℝ≥0) (t : ℝ) (ht : 0 ≤ t)
    (f : Lp H 2 (ULA.gibbsMeasure V)) :
    AEStronglyMeasurable[(inferInstance : MeasurableSpace (E P.dimension)).comap
      (CanonicalSemigroup.state P V hV a)]
      (condExpL2 H ℝ (ULA.lpLangevinPast_le (actualProbability P V)
        (CanonicalSemigroup.initial P V hV) (actualBrownianNoise P V hV) (a : ℝ))
        (CanonicalSemigroup.evaluation (𝕜 := ℝ) P V hV (a + t) f) : Lp H 2 (actualProbability P V))
      (actualProbability P V) := by
  let := actualTarget_isProbability P V hV
  let := actualProbability_isProbability P V hV
  let m := ULA.lpLangevinPast (actualProbability P V) (CanonicalSemigroup.initial P V hV)
    (actualBrownianNoise P V hV) (a : ℝ)
  let : MeasurableSpace (ActualSpace P) := Prod.instMeasurableSpace
  have hm : m ≤ (inferInstance : MeasurableSpace (ActualSpace P)) :=
    ULA.lpLangevinPast_le (actualProbability P V) (CanonicalSemigroup.initial P V hV)
      (actualBrownianNoise P V hV) (a : ℝ)
  let C : Lp H 2 (ULA.gibbsMeasure V) → Lp H 2 (actualProbability P V) := fun g ↦
    (condExpL2 H ℝ hm (CanonicalSemigroup.evaluation (𝕜 := ℝ) P V hV (a + t) g) : Lp H 2 _)
  let mx := (inferInstance : MeasurableSpace (E P.dimension)).comap (CanonicalSemigroup.state P V hV a)
  let : MeasurableSpace (ActualSpace P) := Prod.instMeasurableSpace
  have hclosed : IsClosed {g : Lp H 2 (ULA.gibbsMeasure V) | AEStronglyMeasurable[mx] (C g) (actualProbability P V)} :=
    (isClosed_aestronglyMeasurable (Lp.stronglyMeasurable (CanonicalSemigroup.state P V hV a)).measurable.comap_le).preimage
      (continuous_subtype_val.comp ((condExpL2 H ℝ hm).continuous.comp
        (CanonicalSemigroup.evaluation (𝕜 := ℝ) P V hV (a + t)).continuous))
  have hdense : DenseRange (BoundedContinuousFunction.toLp 2 (ULA.gibbsMeasure V) ℝ :
      (E P.dimension →ᵇ H) →L[ℝ] Lp H 2 (ULA.gibbsMeasure V)) :=
    BoundedContinuousFunction.toLp_denseRange H (ULA.gibbsMeasure V) ℝ (by norm_num)
  apply (closure_minimal (t := {g : Lp H 2 (ULA.gibbsMeasure V) |
    AEStronglyMeasurable[mx] (C g) (actualProbability P V)}) ?_ hclosed) (hdense f)
  rintro _ ⟨φ, rfl⟩
  let Z : ℕ → Lp (E P.dimension) 2 (actualProbability P V) := fun n ↦
    ULA.additiveEulerChain (ULA.lpDrift (actualProbability P V) (gradient V) hV.gradientLipschitz)
      (t / ((n + 1 : ℕ) : ℝ)) (CanonicalSemigroup.state P V hV a)
      (ULA.brownianLangevinNoise (actualProbability P V) (CanonicalSemigroup.brownian P)
        (CanonicalSemigroup.brownian_preBrownian P V hV) a) (n + 1)
  have hzlim : Tendsto Z atTop (𝓝 (CanonicalSemigroup.state P V hV (a + t))) :=
    CanonicalSemigroup.shiftedEuler_tendsto P V hV a t a.coe_nonneg ht
  have hlim := boundedComposition_tendsto (𝕜 := ℝ) (actualProbability P V) Z
    (CanonicalSemigroup.state P V hV (a + t)) hzlim φ
  change AEStronglyMeasurable[mx] (C (BoundedContinuousFunction.toLp 2 (ULA.gibbsMeasure V) ℝ φ)) _
  dsimp only [C]
  rw [actualEvaluation_bcf_eq_boundedComposition]
  apply condExpL2_state_measurable_of_tendsto m (actualProbability P V) hm
    (CanonicalSemigroup.state P V hV a) (Lp.stronglyMeasurable _).measurable
    (fun n ↦ boundedComposition (actualProbability P V) (Z n) φ) _ hlim
  intro n
  let F : E P.dimension × (Fin P.dimension → ℝ≥0 → ℝ) → H := fun p ↦
    φ (CanonicalSemigroup.pointwiseEulerMap P V (t / ((n + 1 : ℕ) : ℝ)) (n + 1) p)
  have hF : StronglyMeasurable F := φ.continuous.stronglyMeasurable.comp_measurable
    (CanonicalSemigroup.pointwiseEulerMap_measurable P V hV _ _)
  apply condExpL2_independent_input_state_measurable m (actualProbability P V) hm
    (CanonicalSemigroup.state P V hV a) (actualBrownianFuture P a)
    (actualState_adapted_pastAt P V hV a) (actualBrownianFuture_measurable P a)
    (actualBrownian_future_independent_pastAt P V hV a) _ F hF
  exact (boundedComposition_coe _ (Z n) φ).trans
    ((CanonicalSemigroup.shiftedEuler_coe P V hV a _ (div_nonneg ht (by positivity)) (n + 1)).fun_comp φ)

/-- The actual diffusion satisfies the conditional Markov identity with
respect to the complete initial/Brownian past. No conditional transition
identity is assumed: it follows from independence, Euler convergence,
Doob--Dynkin factorization and proved time homogeneity. -/
theorem actualEvaluation_markov_pastAt (a : ℝ≥0) (t : ℝ) (ht : 0 ≤ t)
    (f : Lp H 2 (ULA.gibbsMeasure V)) :
    (condExpL2 H ℝ (ULA.lpLangevinPast_le (actualProbability P V)
      (CanonicalSemigroup.initial P V hV) (actualBrownianNoise P V hV) (a : ℝ))
      (CanonicalSemigroup.evaluation (𝕜 := ℝ) P V hV (a + t) f) : Lp H 2 (actualProbability P V)) =
      CanonicalSemigroup.evaluation (𝕜 := ℝ) P V hV a
        (CanonicalSemigroup.op (𝕜 := ℝ) P V hV t f) := by
  let J := CanonicalSemigroup.evaluation (𝕜 := ℝ) (F := H) P V hV a
  let Y := CanonicalSemigroup.evaluation (𝕜 := ℝ) (F := H) P V hV (a + t) f
  have hm := ULA.lpLangevinPast_le (actualProbability P V)
    (CanonicalSemigroup.initial P V hV) (actualBrownianNoise P V hV) (a : ℝ)
  have hx : MeasurePreserving (CanonicalSemigroup.state P V hV a)
      (actualProbability P V) (ULA.gibbsMeasure V) :=
    ⟨(Lp.stronglyMeasurable _).measurable, CanonicalSemigroup.state_law P V hV a⟩
  obtain ⟨g, hg⟩ := observable_range_of_state_measurable (actualProbability P V)
    (ULA.gibbsMeasure V) (CanonicalSemigroup.state P V hV a) hx
    (condExpL2 H ℝ hm Y : Lp H 2 (actualProbability P V))
    (actual_conditional_state_measurable P V hV a t ht f)
  have hrange : (condExpL2 H ℝ hm Y : Lp H 2 (actualProbability P V)) ∈ Set.range J := ⟨g, hg⟩
  have he := conditional_eq_evaluation_adjoint (actualProbability P V) J hm Y
    (fun g ↦ actualEvaluation_adapted_pastAt P V hV a g) hrange
  change (condExpL2 H ℝ hm Y : Lp H 2 (actualProbability P V)) =
    J (ObservableTransition.compression J
      (CanonicalSemigroup.evaluation (𝕜 := ℝ) P V hV (a + t)) f) at he
  rw [CanonicalSemigroup.shifted_compression_eq_op P V hV a t ht] at he
  exact he

end WassersteinMixing
