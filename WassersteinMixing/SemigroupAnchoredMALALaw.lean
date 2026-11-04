import WassersteinMixing.SemigroupRandomMALAAnchors
import WassersteinMixing.SemigroupMALAPair

/-! # Exact anchored MALA laws on the canonical Brownian source

The independent-noise recursion retains its initial state. Its finite-step
pair law is identified with the explicitly reversible kernel power.
-/
noncomputable section
set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal unitInterval

namespace WassersteinMixing.RandomMALA

section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem anchored_chainLaw (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V))
    (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) :
    ULA.chainLaw (anchoredUpdate V h) (μ.map (fun x ↦ (x, x)))
      (Measure.infinitePi (fun _ : ℕ ↦ innovationLaw)) n =
        μ ⊗ₘ StationaryKernelPower.kernelPower (MALAStationaryPair.explicitKernel V h) n := by
  let := MALAStationaryPair.explicitKernel_isMarkov V h L hdiff hLip
  have hinit : IsProbabilityMeasure (μ.map (fun x ↦ (x, x))) := by
    constructor
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ,
      Set.preimage_univ, measure_univ]
  rw [ULA.chainLaw_eq_markovLaws _ (anchoredUpdate_measurable V h L hdiff hLip)]
  induction n with
  | zero => exact (StationaryKernelPower.anchored_pair_zero μ _).symm
  | succ n ih =>
    rw [ULA.markovLaws, ih, anchored_markovStep V h L hdiff hLip]
    exact (StationaryKernelPower.anchored_pair_succ μ _ n).symm

end General
namespace Canonical

variable (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V)

/-- Every measurable recursion on the constructed initial/noise data has the
canonical iid law; this also covers recursions retaining an initial anchor. -/
theorem recursion_law {H : Type*} [MeasurableSpace H]
    (F : H → ((E P.dimension) × I) → H) (hF : Measurable (Function.uncurry F))
    (j : E P.dimension → H) (hj : Measurable j)
    (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (probability P V).map (fun ω ↦ ULA.noiseDrivenChain F
      (j (input P V hV r ω).1) (input P V hV r ω).2 n) =
      ULA.chainLaw F ((ULA.gibbsMeasure V).map j)
        (Measure.infinitePi (fun _ : ℕ ↦ innovationLaw)) n := by
  let := actualTarget_isProbability P V hV
  let G : (E P.dimension) × (ℕ → (E P.dimension) × I) → H :=
    fun p ↦ ULA.noiseDrivenChain F (j p.1) p.2 n
  have hG : Measurable G :=
    (ULA.noiseDrivenChain_measurable F hF n).comp
      ((hj.comp measurable_fst).prodMk measurable_snd)
  change (probability P V).map (G ∘ input P V hV r) = _
  rw [← AEMeasurable.map_map_of_aemeasurable hG.aemeasurable
    (input_aemeasurable P V hV r), input_law P V hV r hr]
  unfold ULA.chainLaw
  have hprod := Measure.map_prod_map (ULA.gibbsMeasure V)
    (Measure.infinitePi (fun _ : ℕ ↦ innovationLaw (E := E P.dimension))) hj measurable_id
  simp only [Measure.map_id] at hprod
  rw [hprod, Measure.map_map (ULA.noiseDrivenChain_measurable F hF n) (by fun_prop)]
  rfl

/-- The true initial/MALA pair has exactly the explicit reversible finite-step law. -/
theorem anchored_state_law (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (probability P V).map
      (fun ω ↦ (actualInitial P V hV ω.1, (state P V hV r n ω).2)) =
        MALAStationaryPair.explicitPowerJointLaw V r n := by
  let := actualTarget_isProbability P V hV
  have hrec := recursion_law P V hV (anchoredUpdate V r)
    (anchoredUpdate_measurable V r ⟨P.beta, P.beta_pos.le⟩
      (hV.regularity.differentiable (by norm_num)) hV.gradientLipschitz)
    (fun x ↦ (x, x)) (by fun_prop) r hr n
  rw [anchored_chainLaw V r ⟨P.beta, P.beta_pos.le⟩
    (hV.regularity.differentiable (by norm_num)) hV.gradientLipschitz] at hrec
  apply (Measure.map_congr ?_).trans hrec
  exact Filter.Eventually.of_forall fun ω ↦
    (anchored_chain_eq V r (actualInitial P V hV ω.1) (input P V hV r ω).2 n).symm

/-- The initial/MALA pair is reversible as a consequence of its exact law. -/
theorem anchored_state_swap (r : ℝ) (hr : 0 < r) (n : ℕ) :
    ((probability P V).map
      (fun ω ↦ (actualInitial P V hV ω.1, (state P V hV r n ω).2))).map Prod.swap =
      (probability P V).map
        (fun ω ↦ (actualInitial P V hV ω.1, (state P V hV r n ω).2)) := by
  let := actualTarget_isProbability P V hV
  rw [anchored_state_law P V hV r hr n]
  exact MALAStationaryPair.explicitPowerJointLaw_swap V r ⟨P.beta, P.beta_pos.le⟩
    hr (hV.regularity.differentiable (by norm_num)) hV.gradientLipschitz n

end Canonical
end WassersteinMixing.RandomMALA
