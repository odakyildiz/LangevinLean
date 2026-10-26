import PBGSO.RawDampedState
import PBGSO.RawLocalLinearMap

/-! # Actual pairing of two original locally defined raw equations
Both equations use the same finite Brownian vector. The paired local
coefficient and its genuine gauge are constructed, and projection identities
are proved for the actual local integrals, with no global noise square moment.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.RawPairDynamics
open FilteredBrownian
variable {Ω I E F : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  {Q : Measure Ω} [IsProbabilityMeasure Q] {D : Driver (I := I) Q} {T : ℝ≥0}

abbrev Joint (E F : Type*) := WithLp 2 (E × F)

def pack : (E × F) ≃L[ℝ] Joint E F := (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm

def first : Joint E F →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ E F).comp (pack (E := E) (F := F)).symm.toContinuousLinearMap

def second : Joint E F →L[ℝ] F :=
  (ContinuousLinearMap.snd ℝ E F).comp (pack (E := E) (F := F)).symm.toContinuousLinearMap

def coefficient (L : RawLocalDiffusion (Z := E) Q D T)
    (K : RawLocalDiffusion (Z := F) Q D T) :
    RawLocalDiffusion (Z := Joint E F) Q D T := by
  let c : ℝ := max 1 ‖(pack (E := E) (F := F)).toContinuousLinearMap‖
  refine {
    sigma := fun i r ω => pack (L.sigma i r ω,K.sigma i r ω)
    sigma_strong := fun i => (pack (E := E) (F := F)).continuous.comp_stronglyMeasurable
      ((L.sigma_strong i).prodMk (K.sigma_strong i))
    sigma_adapted := fun t i => (pack (E := E) (F := F)).continuous.comp_aestronglyMeasurable
      ((L.sigma_adapted t i).prodMk (K.sigma_adapted t i))
    q := fun r ω => c*(L.q r ω+K.q r ω)
    q_strong := stronglyMeasurable_const.mul (L.q_strong.add K.q_strong)
    q_nonneg := fun r ω => mul_nonneg (le_trans zero_le_one (le_max_left _ _))
      (add_nonneg (L.q_nonneg r ω) (K.q_nonneg r ω))
    q_local := fun ω => ((L.q_local ω).add (K.q_local ω)).const_mul c
    q_progressive := ?_
    sigma_control := ?_ }
  · intro t
    have hc : StronglyMeasurable[(inferInstance : MeasurableSpace ℝ).prod (D.filtration t)]
        (fun _ : ℝ × Ω => c) := stronglyMeasurable_const
    convert hc.mul ((L.q_progressive t).add (K.q_progressive t)) using 1
    funext p
    by_cases h : p.1 ∈ Ioc 0 (t : ℝ) <;> simp [h]
  · intro r ω
    have hn : 0 ≤ L.q r ω+K.q r ω := add_nonneg (L.q_nonneg r ω) (K.q_nonneg r ω)
    calc
      _ = (∑ i, ‖L.sigma i r ω‖ ^ 2)+(∑ i, ‖K.sigma i r ω‖ ^ 2) := by
        simp_rw [WithLp.prod_norm_sq_eq_of_L2]
        change (∑ i, (‖L.sigma i r ω‖ ^ 2+‖K.sigma i r ω‖ ^ 2)) = _
        exact Finset.sum_add_distrib
      _ ≤ L.q r ω+K.q r ω := add_le_add (L.sigma_control r ω) (K.sigma_control r ω)
      _ ≤ c*(L.q r ω+K.q r ω) := le_mul_of_one_le_left hn (le_max_left _ _)

variable (L : RawLocalDiffusion (Z := E) Q D T) (K : RawLocalDiffusion (Z := F) Q D T)

/-- The actual full local stochastic integral projects to both original
noises on one common event throughout the horizon. -/
theorem noise_projections :
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T →
      (first ((coefficient L K).localNoise t ω) = L.localNoise t ω) ∧
      (second ((coefficient L K).localNoise t ω) = K.localNoise t ω) := by
  have he : ∀ᵐ ω ∂Q, ∀ i r, r ∈ Ioc 0 (T : ℝ) →
      L.sigma i r ω = first ((coefficient L K).sigma i r ω) :=
    Eventually.of_forall (fun _ _ _ _ => rfl)
  have hf : ∀ᵐ ω ∂Q, ∀ i r, r ∈ Ioc 0 (T : ℝ) →
      K.sigma i r ω = second ((coefficient L K).sigma i r ω) :=
    Eventually.of_forall (fun _ _ _ _ => rfl)
  filter_upwards [(coefficient L K).localNoise_linearMap_congr first L he,
    (coefficient L K).localNoise_linearMap_congr second K hf] with ω he hf t ht
  exact ⟨(he t ht).symm,(hf t ht).symm⟩

/-- The raw paired drift is controlled by the constructed localization gauge. -/
theorem drift_control (U : RawDampedState.Data L) (V : RawDampedState.Data K)
    (r : ℝ) (ω : Ω) :
    ‖pack (U.drift r ω,V.drift r ω)‖ ≤ (coefficient L K).q r ω := by
  let A := (pack (E := E) (F := F)).toContinuousLinearMap
  have hu := U.drift_control r ω
  have hv := V.drift_control r ω
  have hq : max ‖U.drift r ω‖ ‖V.drift r ω‖ ≤ L.q r ω+K.q r ω :=
    max_le (hu.trans (le_add_of_nonneg_right (K.q_nonneg r ω)))
      (hv.trans (le_add_of_nonneg_left (L.q_nonneg r ω)))
  calc
    _ ≤ ‖A‖*‖(U.drift r ω,V.drift r ω)‖ := A.le_opNorm _
    _ ≤ ‖A‖*(L.q r ω+K.q r ω) := mul_le_mul_of_nonneg_left hq (ContinuousLinearMap.opNorm_nonneg A)
    _ ≤ max 1 ‖A‖*(L.q r ω+K.q r ω) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _)
        (add_nonneg (L.q_nonneg r ω) (K.q_nonneg r ω))

/-- Both original strong equations assemble into an actual paired raw
strong equation. Its stochastic integral is computed from the paired
physical columns; it is never an assumed matched-noise process. -/
def pair (U : RawDampedState.Data L) (V : RawDampedState.Data K) :
    RawDampedState.Data (coefficient L K) := by
  let A := pack (E := E) (F := F)
  let b : ℝ → Ω → Joint E F := fun r ω => A (U.drift r ω,V.drift r ω)
  have hb : StronglyMeasurable (Function.uncurry b) :=
    A.continuous.comp_stronglyMeasurable (U.drift_strong.prodMk V.drift_strong)
  have hbi (ω : Ω) : IntervalIntegrable (fun r => b r ω) volume 0 (T : ℝ) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mpr
    exact ((coefficient L K).q_local ω).mono' hb.of_uncurry_right.aestronglyMeasurable
      (Eventually.of_forall (fun r => drift_control L K U V r ω))
  refine {
    state := fun r ω => A (U.state r ω,V.state r ω)
    drift := b
    state_strong := A.continuous.comp_stronglyMeasurable (U.state_strong.prodMk V.state_strong)
    drift_strong := hb
    drift_control := drift_control L K U V
    initial_square := ?_
    state_adapted := fun t => A.continuous.comp_aestronglyMeasurable
      ((U.state_adapted t).prodMk (V.state_adapted t))
    state_continuous := ?_
    equation := ?_ }
  · let J := A.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ E F)
    let H := A.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ E F)
    convert (J.comp_memLp' U.initial_square).add (H.comp_memLp' V.initial_square) using 1
    funext ω
    change A (U.state 0 ω,V.state 0 ω) = A (U.state 0 ω,0)+A (0,V.state 0 ω)
    calc
      _ = A ((U.state 0 ω,0)+(0,V.state 0 ω)) := by congr 1 <;> simp
      _ = _ := map_add A _ _
  · filter_upwards [U.state_continuous,V.state_continuous] with ω hu hv
    exact A.continuous.comp_continuousOn (hu.prodMk hv)
  · filter_upwards [U.equation,V.equation,noise_projections L K] with ω hu hv hn t ht
    have hit : IntervalIntegrable (fun r => b r ω) volume 0 t := by
      apply (hbi ω).mono_set
      simpa only [uIcc_of_le ht.1,uIcc_of_le T.coe_nonneg] using
        (Icc_subset_Icc le_rfl ht.2 : Icc 0 t ⊆ Icc 0 (T : ℝ))
    have he := (first (E := E) (F := F)).intervalIntegral_comp_comm hit
    have hf := (second (E := E) (F := F)).intervalIntegral_comp_comm hit
    have htt : t.toNNReal ≤ T := (Real.toNNReal_le_iff_le_coe).mpr ht.2
    apply A.symm.injective
    apply Prod.ext
    · change U.state t ω = U.state 0 ω+first (∫ r in 0..t,b r ω)+
        first ((coefficient L K).localNoise t.toNNReal ω)
      rw [(hn t.toNNReal htt).1,← he]
      exact hu t ht
    · change V.state t ω = V.state 0 ω+second (∫ r in 0..t,b r ω)+
        second ((coefficient L K).localNoise t.toNNReal ω)
      rw [(hn t.toNNReal htt).2,← hf]
      exact hv t ht

end PBGSO.RawPairDynamics
