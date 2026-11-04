import WassersteinMixing.Parameters
import WassersteinMixing.Transport
import UnadjustedLangevin.LpDrift
import UnadjustedLangevin.MALACoupling
import UnadjustedLangevin.TransportMoments
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Topology.MetricSpace.Contracting

set_option linter.style.header false

/-! # Constructing the actual invariant law from an iid past

The operator `X ↦ F(X ∘ tail) + a ξ₀` acts on the complete Hilbert space
`L²` of an iid noise sequence. Its contraction gives a genuine fixed random
variable. Independence of the first noise from the tail proves invariance
of its law under the original independent-noise transition. No invariant
law or fixed-point equation is supplied as an assumption.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology

namespace WassersteinMixing
namespace AdditiveInvariant

variable {E : Type*} [MeasurableSpace E]

/-- The canonical iid past, indexed from the most recent innovation. -/
def probability (η : Measure E) : Measure (ℕ → E) := Measure.infinitePi (fun _ : ℕ ↦ η)

instance probability_isProbability (η : Measure E) [IsProbabilityMeasure η] :
    IsProbabilityMeasure (probability η) := by unfold probability; infer_instance

/-- Dropping the most recent innovation leaves the same iid distribution. -/
theorem tail_measurePreserving (η : Measure E) [IsProbabilityMeasure η] :
    MeasurePreserving (fun ω : ℕ → E ↦ fun n ↦ ω (n + 1)) (probability η) (probability η) := by
  refine ⟨by fun_prop, ?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj Nat.succ_injective

/-- The complete older past is independent of the most recent innovation. -/
theorem tail_independent_head (η : Measure E) [IsProbabilityMeasure η] :
    IndepFun (fun ω : ℕ → E ↦ fun n ↦ ω (n + 1)) (fun ω ↦ ω 0) (probability η) := by
  have hi : iIndepFun (fun n (ω : ℕ → E) ↦ ω n) (probability η) :=
    iIndepFun_infinitePi (X := fun _ x ↦ x) (by fun_prop)
  apply IndepFun.process_indepFun (fun n ↦ by fun_prop) (by fun_prop)
  intro I
  have hdis : Disjoint (I.image Nat.succ) ({0} : Finset ℕ) := by
    simp only [Finset.disjoint_singleton_right, Finset.mem_image]
    rintro ⟨a, _, ha⟩
    exact Nat.succ_ne_zero a ha
  have hp := hi.indepFun_finset (I.image Nat.succ) {0} hdis (by fun_prop)
  exact hp.comp
    (φ := fun w : (i : (I.image Nat.succ : Finset ℕ)) → E ↦
      fun i : I ↦ w ⟨i + 1, Finset.mem_image.mpr ⟨i, i.property, rfl⟩⟩)
    (ψ := fun w : (i : ({0} : Finset ℕ)) → E ↦ w ⟨0, by simp⟩)
    (by fun_prop) (by fun_prop)

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [BorelSpace E] [SecondCountableTopology E]

/-- Pulling back an `L²` random vector to the older past is an isometry. -/
def tailPullback (η : Measure E) [IsProbabilityMeasure η] :
    Lp E 2 (probability η) →ₗᵢ[ℝ] Lp E 2 (probability η) :=
  Lp.compMeasurePreservingₗᵢ ℝ _ (tail_measurePreserving η)

/-- The actual most recent innovation, as a square-integrable random vector. -/
def headLp (η : Measure E) [IsProbabilityMeasure η]
    (hη : MemLp (id : E → E) 2 η) : Lp E 2 (probability η) :=
  (hη.comp_measurePreserving (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ η) 0)).toLp
    (fun ω : ℕ → E ↦ ω 0)

/-- The random fixed-point operator, with its noise on the same canonical past. -/
def pastOperator (η : Measure E) [IsProbabilityMeasure η]
    (hη : MemLp (id : E → E) 2 η) (F : E → E) (q : ℝ≥0)
    (hF : LipschitzWith q F) (a : ℝ) (X : Lp E 2 (probability η)) :
    Lp E 2 (probability η) :=
  ULA.lpDrift (probability η) F hF (tailPullback η X) + a • headLp η hη

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Its contraction is derived from the state contraction and the tail isometry. -/
theorem pastOperator_lipschitz (η : Measure E) [IsProbabilityMeasure η]
    (hη : MemLp (id : E → E) 2 η) (F : E → E) (q : ℝ≥0)
    (hF : LipschitzWith q F) (a : ℝ) :
    LipschitzWith q (pastOperator η hη F q hF a) := by
  apply LipschitzWith.of_dist_le_mul
  intro X Y
  simp only [pastOperator, dist_add_right]
  have hb := (ULA.lpDrift_lipschitz (probability η) F hF).dist_le_mul
    (tailPullback η X) (tailPullback η Y)
  rwa [(tailPullback η).isometry.dist_eq] at hb

/-- A genuine fixed random variable selected by the Banach contraction theorem. -/
def state (η : Measure E) [IsProbabilityMeasure η]
    (hη : MemLp (id : E → E) 2 η) (F : E → E) (q : ℝ≥0)
    (hF : LipschitzWith q F) (hq : q < 1) (a : ℝ) : Lp E 2 (probability η) :=
  ContractingWith.fixedPoint (pastOperator η hη F q hF a)
    ⟨hq, pastOperator_lipschitz η hη F q hF a⟩

omit [BorelSpace E] [SecondCountableTopology E] in
/-- The fixed random variable has the literal affine random recursion. -/
theorem state_recursion (η : Measure E) [IsProbabilityMeasure η]
    (hη : MemLp (id : E → E) 2 η) (F : E → E) (q : ℝ≥0)
    (hF : LipschitzWith q F) (hq : q < 1) (a : ℝ) :
    state η hη F q hF hq a =ᵐ[probability η] fun ω ↦
      F (state η hη F q hF hq a (fun n ↦ ω (n + 1))) + a • ω 0 := by
  let X := state η hη F q hF hq a
  have hfix : pastOperator η hη F q hF a X = X :=
    (ContractingWith.fixedPoint_isFixedPt
      (⟨hq, pastOperator_lipschitz η hη F q hF a⟩ :
        ContractingWith q (pastOperator η hη F q hF a))).eq
  have ht := Lp.coeFn_compMeasurePreserving X (tail_measurePreserving η)
  have hn := (hη.comp_measurePreserving
    (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ η) 0)).coeFn_toLp
  change headLp η hη =ᵐ[probability η] (fun ω : ℕ → E ↦ ω 0) at hn
  have he : pastOperator η hη F q hF a X =ᵐ[probability η] fun ω ↦
      F (X (fun n ↦ ω (n + 1))) + a • ω 0 := by
    filter_upwards [Lp.coeFn_add
      (ULA.lpDrift (probability η) F hF (tailPullback η X)) (a • headLp η hη),
      ULA.lpDrift_coe (probability η) F hF (tailPullback η X), ht,
      Lp.coeFn_smul a (headLp η hη), hn] with ω hadd hcomp htail hsmul hhead
    change (ULA.lpDrift (probability η) F hF (tailPullback η X) + a • headLp η hη) ω = _
    rw [hadd]
    simp only [Pi.add_apply]
    rw [hcomp, hsmul]
    simp only [Pi.smul_apply]
    change F (Lp.compMeasurePreserving _ (tail_measurePreserving η) X ω) +
      a • headLp η hη ω = _
    rw [hhead]
    rw [htail]
    rfl
  rw [hfix] at he
  exact he

/-- The candidate invariant measure is the law of the constructed `L²` fixed point. -/
def law (η : Measure E) [IsProbabilityMeasure η]
    (hη : MemLp (id : E → E) 2 η) (F : E → E) (q : ℝ≥0)
    (hF : LipschitzWith q F) (hq : q < 1) (a : ℝ) : Measure E :=
  (probability η).map (state η hη F q hF hq a)

instance law_isProbability (η : Measure E) [IsProbabilityMeasure η]
    (hη : MemLp (id : E → E) 2 η) (F : E → E) (q : ℝ≥0)
    (hF : LipschitzWith q F) (hq : q < 1) (a : ℝ) :
    IsProbabilityMeasure (law η hη F q hF hq a) := by
  unfold law
  constructor
  rw [Measure.map_apply_of_aemeasurable (Lp.aestronglyMeasurable _).aemeasurable
    MeasurableSet.univ, Set.preimage_univ, measure_univ]

/-- The constructed invariant candidate has a finite second moment. -/
theorem law_memLp (η : Measure E) [IsProbabilityMeasure η]
    (hη : MemLp (id : E → E) 2 η) (F : E → E) (q : ℝ≥0)
    (hF : LipschitzWith q F) (hq : q < 1) (a : ℝ) :
    MemLp (id : E → E) 2 (law η hη F q hF hq a) := by
  exact (memLp_map_measure_iff (by fun_prop)
    (Lp.aestronglyMeasurable _).aemeasurable).mpr (Lp.memLp _)

/-- Head/tail independence identifies the fixed-point law with the output
of the original independent-noise transition. This proves actual invariance. -/
theorem law_invariant (η : Measure E) [IsProbabilityMeasure η]
    (hη : MemLp (id : E → E) 2 η) (F : E → E) (q : ℝ≥0)
    (hF : LipschitzWith q F) (hq : q < 1) (a : ℝ) :
    ((law η hη F q hF hq a).prod η).map (fun p ↦ F p.1 + a • p.2) =
      law η hη F q hF hq a := by
  let X := state η hη F q hF hq a
  have hX : Measurable X := (Lp.stronglyMeasurable X).measurable
  have htail : Measurable (fun ω : ℕ → E ↦ fun n ↦ ω (n + 1)) := by fun_prop
  have hind := (tail_independent_head η).comp hX measurable_id
  change IndepFun (fun ω : ℕ → E ↦ X (fun n ↦ ω (n + 1)))
    (fun ω ↦ ω 0) (probability η) at hind
  have hpair : (probability η).map (fun ω ↦ (X (fun n ↦ ω (n + 1)), ω 0)) =
      (law η hη F q hF hq a).prod η := by
    have hp := hind.map_prod_eq_prod_map_map (hX.comp htail).aemeasurable
      (measurable_pi_apply 0).aemeasurable
    have hxlaw : (probability η).map (fun ω ↦ X (fun n ↦ ω (n + 1))) =
        law η hη F q hF hq a := by
      calc
        _ = ((probability η).map (fun ω : ℕ → E ↦ fun n ↦ ω (n + 1))).map X :=
          (Measure.map_map hX htail).symm
        _ = _ := by rw [(tail_measurePreserving η).map_eq]; rfl
    have hn : (probability η).map (fun ω : ℕ → E ↦ ω 0) = η :=
      Measure.infinitePi_map_eval (fun _ : ℕ ↦ η) 0
    simpa only [Function.comp_def, hxlaw, hn] using hp
  have hupdate : Measurable (fun p : E × E ↦ F p.1 + a • p.2) :=
    (hF.continuous.measurable.comp measurable_fst).add (measurable_snd.const_smul a)
  rw [← hpair, Measure.map_map hupdate (by fun_prop)]
  exact Measure.map_congr (state_recursion η hη F q hF hq a).symm

end AdditiveInvariant

section ULA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The deterministic gradient part of the actual ULA update. -/
def ulaGradientStep (P : Parameters) (V : E → ℝ) (x : E) : E :=
  x - P.step • gradient V x

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Its contraction is derived from the original potential assumptions. -/
theorem ulaGradientStep_lipschitz (P : Parameters) (V : E → ℝ)
    (hV : PotentialAssumptions P V) :
    LipschitzWith ⟨P.contraction, P.contraction_nonneg⟩ (ulaGradientStep P V) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hc := ula_shared_noise_contraction P V hV x y 0
  simp only [ULA.malaProposal, smul_zero, add_zero] at hc
  simp only [dist_eq_norm, ulaGradientStep]
  convert hc using 1
  rfl

/-- The invariant law is constructed from the original potential and the
actual standard Gaussian innovations, using a fixed point on an iid past. -/
def invariantLaw (P : Parameters) (V : E → ℝ) (hV : PotentialAssumptions P V) : Measure E :=
  AdditiveInvariant.law (stdGaussian E) (IsGaussian.memLp_id (stdGaussian E) 2 (by norm_num))
    (ulaGradientStep P V) ⟨P.contraction, P.contraction_nonneg⟩
    (ulaGradientStep_lipschitz P V hV) P.contraction_lt_one (Real.sqrt (2 * P.step))

instance invariantLaw_isProbability (P : Parameters) (V : E → ℝ)
    (hV : PotentialAssumptions P V) : IsProbabilityMeasure (invariantLaw P V hV) := by
  unfold invariantLaw
  exact AdditiveInvariant.law_isProbability (stdGaussian E)
    (IsGaussian.memLp_id (stdGaussian E) 2 (by norm_num))
    (ulaGradientStep P V) ⟨P.contraction, P.contraction_nonneg⟩
    (ulaGradientStep_lipschitz P V hV) P.contraction_lt_one (Real.sqrt (2 * P.step))

/-- Finite second moments of the actual ULA invariant law are a conclusion. -/
theorem invariantLaw_memLp (P : Parameters) (V : E → ℝ)
    (hV : PotentialAssumptions P V) : MemLp (id : E → E) 2 (invariantLaw P V hV) :=
  AdditiveInvariant.law_memLp _ _ _ _ _ _ _

/-- The constructed probability measure is invariant for the existing actual
ULA law transition, with no invariance assumption. -/
theorem invariantLaw_invariant (P : Parameters) (V : E → ℝ)
    (hV : PotentialAssumptions P V) :
    ULA.ulaLawStep V P.step (invariantLaw P V hV) = invariantLaw P V hV := by
  exact AdditiveInvariant.law_invariant (stdGaussian E)
    (IsGaussian.memLp_id (stdGaussian E) 2 (by norm_num))
    (ulaGradientStep P V) ⟨P.contraction, P.contraction_nonneg⟩
    (ulaGradientStep_lipschitz P V hV) P.contraction_lt_one (Real.sqrt (2 * P.step))

/-- The original ULA laws contract to the constructed invariant probability
measure, for every initialization with a finite second moment. -/
theorem invariantLaw_mixing (P : Parameters) (V : E → ℝ)
    (hV : PotentialAssumptions P V) (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : E → E) 2 μ) (k : ℕ) :
    ULA.wasserstein2Real ((ULA.ulaLawStep V P.step)^[k] μ) (invariantLaw P V hV) ≤
      P.contraction ^ k * ULA.wasserstein2Real μ (invariantLaw P V hV) := by
  exact ula_to_invariant_wasserstein2Real_le P V hV μ (invariantLaw P V hV)
    (invariantLaw_invariant P V hV)
    (ULA.wasserstein2_ne_top_of_memLp μ _ hμ (invariantLaw_memLp P V hV)) k

/-- Actual convergence to the invariant law in quadratic Wasserstein distance. -/
theorem invariantLaw_attraction (P : Parameters) (V : E → ℝ)
    (hV : PotentialAssumptions P V) (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : E → E) 2 μ) :
    Filter.Tendsto (fun k : ℕ ↦
      ULA.wasserstein2Real ((ULA.ulaLawStep V P.step)^[k] μ) (invariantLaw P V hV))
      Filter.atTop (𝓝 0) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one P.contraction_nonneg
    P.contraction_lt_one
  apply squeeze_zero (fun k ↦ ENNReal.toReal_nonneg) (invariantLaw_mixing P V hV μ hμ)
  simpa only [zero_mul] using hp.mul_const (ULA.wasserstein2Real μ (invariantLaw P V hV))

end ULA
end WassersteinMixing
