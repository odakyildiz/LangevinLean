import PBGSO.AdditiveWeakRealization
import PBGSO.LpPullback
import UnadjustedLangevin.InitialExtension

/-! # Law-coherent actual additive mean-field processes on every initial coupling

Each marginal process is constructed once on its own initial-law × noise
space. The two measure-preserving projections of initial-coupling × noise pull
back those actual processes. Their output marginals are therefore the same
fixed laws for every initial coupling, and their sampler input is literally
common. No output-law identity or contraction estimate is assumed.
Only the empty marginal and singleton quadratic pair test domains are claimed;
full marginal Itô equivalence and frozen-target invariance remain separate.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators RealInnerProductSpace InnerProductSpace Topology
namespace PBGSO

section GlobalPullback
variable {Ω Ω' A G Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {Q : Measure Ω} {Q' : Measure Ω'} [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
  {f : Ω' → Ω}

/-- Actual global integral equations commute with measure-preserving
pullback, with exactly the pulled-back sampler input. -/
theorem IsGlobalAdditiveIntegralSolution.pullback
    (hf : MeasurePreserving f Q' Q) {L : LipschitzDynamics A Z G}
    {Y : ℝ → A × Lp Z 2 Q} {B : ℝ → Lp Z 2 Q}
    (HY : IsGlobalAdditiveIntegralSolution Q L Y B) :
    IsGlobalAdditiveIntegralSolution Q' L (fun t ↦ jointPullbackCLM hf (Y t))
      (fun t ↦ lpPullbackCLM hf (B t)) where
  continuous := (jointPullbackCLM hf).continuous.comp HY.continuous
  equation := by
    intro t ht
    exact (integral_solution_pullback hf L (Y 0) B Y HY.continuous t
      (fun r hr ↦ HY.equation r hr.1)).2 t ⟨ht, le_rfl⟩

end GlobalPullback

namespace AdditiveCanonical
variable {Ξ A G Z X I : Type*} [MeasurableSpace Ξ]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype I]
  (R : Measure Ξ) [IsProbabilityMeasure R]

/-- Canonical actual initial variable on initial-law × noise space. -/
def initialSampler (μ : Measure Z) (hμ : MemLp (fun z : Z ↦ z) 2 μ) : Lp Z 2 (μ.prod R) :=
  (hμ.comp_fst R).toLp (fun p : Z × Ξ ↦ p.1)

theorem initialSampler_coe (μ : Measure Z) (hμ : MemLp (fun z : Z ↦ z) 2 μ) :
    initialSampler R μ hμ =ᵐ[μ.prod R] fun p ↦ p.1 :=
  (hμ.comp_fst R).coeFn_toLp

theorem initialSampler_law (μ : Measure Z) (hμ : MemLp (fun z : Z ↦ z) 2 μ) :
    (μ.prod R).map (initialSampler R μ hμ) = μ := by
  rw [Measure.map_congr (initialSampler_coe R μ hμ)]
  exact (measurePreserving_fst (μ := μ) (ν := R)).map_eq

/-- The sampler input is pulled back from the noise coordinate, independent
of the initial sampler coordinate under the product source. -/
def input (μ : Measure Z) [IsProbabilityMeasure μ] (B : ℝ → Lp Z 2 R) :
    ℝ → Lp Z 2 (μ.prod R) :=
  fun t ↦ lpPullbackCLM (measurePreserving_snd (μ := μ) (ν := R)) (B t)

/-- The actual global primitive mean-field process selected once for each
initial law and deterministic optimiser state. -/
def flow (L : LipschitzDynamics A Z G) (μ : Measure Z) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun z : Z ↦ z) 2 μ) (a : A)
    (B : ℝ → Lp Z 2 R) (hB : Continuous B) (hB0 : B 0 = 0) :
    ℝ → A × Lp Z 2 (μ.prod R) :=
  Classical.choose (exists_global_additive_integral_solution (μ.prod R) L
    (a, initialSampler R μ hμ) (input R μ B)
    ((lpPullbackCLM (measurePreserving_snd (μ := μ) (ν := R))).continuous.comp hB)
    (by simp [input, hB0]))

theorem flow_spec (L : LipschitzDynamics A Z G) (μ : Measure Z) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun z : Z ↦ z) 2 μ) (a : A)
    (B : ℝ → Lp Z 2 R) (hB : Continuous B) (hB0 : B 0 = 0) :
    IsGlobalAdditiveIntegralSolution (μ.prod R) L (flow R L μ hμ a B hB hB0) (input R μ B) ∧
      flow R L μ hμ a B hB hB0 0 = (a, initialSampler R μ hμ) :=
  Classical.choose_spec (exists_global_additive_integral_solution (μ.prod R) L
    (a, initialSampler R μ hμ) (input R μ B)
    ((lpPullbackCLM (measurePreserving_snd (μ := μ) (ν := R))).continuous.comp hB)
    (by simp [input, hB0]))

/-- Actual marginal optimiser coordinate and sampler law of the fixed flow. -/
def optimizer (L : LipschitzDynamics A Z G) (μ : Measure Z) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun z : Z ↦ z) 2 μ) (a : A)
    (B : ℝ → Lp Z 2 R) (hB : Continuous B) (hB0 : B 0 = 0) (t : ℝ) : A :=
  (flow R L μ hμ a B hB hB0 t).1

def law (L : LipschitzDynamics A Z G) (μ : Measure Z) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun z : Z ↦ z) 2 μ) (a : A)
    (B : ℝ → Lp Z 2 R) (hB : Continuous B) (hB0 : B 0 = 0) (t : ℝ) : Measure Z :=
  (μ.prod R).map (flow R L μ hμ a B hB hB0 t).2

@[simp] theorem law_zero (L : LipschitzDynamics A Z G) (μ : Measure Z) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun z : Z ↦ z) 2 μ) (a : A)
    (B : ℝ → Lp Z 2 R) (hB : Continuous B) (hB0 : B 0 = 0) :
    law R L μ hμ a B hB hB0 0 = μ := by
  unfold law
  rw [(flow_spec R L μ hμ a B hB hB0).2]
  exact initialSampler_law R μ hμ

/-- First marginal/noise projection preserves the actual product law. -/
theorem extension_left_preserving (μ ν : Measure Z) [IsProbabilityMeasure μ]
    (c : ULA.Coupling μ ν) :
    MeasurePreserving (fun p : (Z × Z) × Ξ ↦ (p.1.1, p.2))
      (ULA.initialExtension c R) (μ.prod R) :=
  ⟨by fun_prop, ULA.initialExtension_initial_noise c R⟩

/-- Second marginal/noise projection preserves the actual product law. -/
theorem extension_right_preserving (μ ν : Measure Z) [IsProbabilityMeasure μ]
    (c : ULA.Coupling μ ν) :
    MeasurePreserving (fun p : (Z × Z) × Ξ ↦ (p.1.2, p.2))
      (ULA.initialExtension c R) (ν.prod R) := by
  refine ⟨by fun_prop, ?_⟩
  haveI := c.isProbabilityMeasure
  change (c.joint.prod R).map (Prod.map Prod.snd id) = _
  simpa only [c.snd, Measure.map_id] using
    (Measure.map_prod_map c.joint R measurable_snd measurable_id).symm

/-- Every genuine initial coupling realizes the same two already
constructed marginal law trajectories, on its explicit independent-noise
product extension. The fixed output laws are a proved consequence of
measure-preserving pullback. -/
theorem realize_all_initial_couplings
    (L : LipschitzDynamics A Z G) (M : Model A G Z X I)
    (H : AdditiveModelCompatibility L M) (D : TwistedGeometry A Z)
    (μ ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp (fun z : Z ↦ z) 2 μ) (hν : MemLp (fun z : Z ↦ z) 2 ν)
    (a b : A) (B : ℝ → Lp Z 2 R) (hB : Continuous B) (hB0 : B 0 = 0)
    (c : ULA.Coupling μ ν) :
    ∃ Λ : ℝ → Measure (Z × Z),
      IsCoupledWeakSolution M ∅ {couplingQuadratic D}
        (optimizer R L μ hμ a B hB hB0) (optimizer R L ν hν b B hB hB0)
        (law R L μ hμ a B hB hB0) (law R L ν hν b B hB hB0) Λ ∧ Λ 0 = c.joint := by
  let Q := ULA.initialExtension c R
  letI : IsProbabilityMeasure c.joint := c.isProbabilityMeasure
  letI : IsProbabilityMeasure Q := ULA.initialExtension_isProbabilityMeasure c R
  let hf := extension_left_preserving R μ ν c
  let hg := extension_right_preserving R μ ν c
  let hn := measurePreserving_snd (μ := c.joint) (ν := R)
  let Y := flow R L μ hμ a B hB hB0
  let W := flow R L ν hν b B hB hB0
  let Yc := fun t ↦ jointPullbackCLM hf (Y t)
  let Wc := fun t ↦ jointPullbackCLM hg (W t)
  have hY := (flow_spec R L μ hμ a B hB hB0).1.pullback hf
  have hW := (flow_spec R L ν hν b B hB hB0).1.pullback hg
  have hYL : (fun t ↦ lpPullbackCLM hf (input R μ B t)) = fun t ↦ lpPullbackCLM hn (B t) := by
    funext t
    unfold input
    rw [lpPullback_comp]
    rfl
  have hWR : (fun t ↦ lpPullbackCLM hg (input R ν B t)) = fun t ↦ lpPullbackCLM hn (B t) := by
    funext t
    unfold input
    rw [lpPullback_comp]
    rfl
  rw [hYL] at hY
  rw [hWR] at hW
  have hcoupled := hY.isCoupledWeakSolution_quadratic hW M H D
  have hleft : IsGlobalAdditiveIntegralSolution.samplerLaw (Q := Q) Yc =
      law R L μ hμ a B hB hB0 := by
    funext t
    exact lpPullback_law hf (Y t).2
  have hright : IsGlobalAdditiveIntegralSolution.samplerLaw (Q := Q) Wc =
      law R L ν hν b B hB hB0 := by
    funext t
    exact lpPullback_law hg (W t).2
  change IsCoupledWeakSolution M ∅ {couplingQuadratic D}
    (optimizer R L μ hμ a B hB hB0) (optimizer R L ν hν b B hB hB0)
    (IsGlobalAdditiveIntegralSolution.samplerLaw (Q := Q) Yc)
    (IsGlobalAdditiveIntegralSolution.samplerLaw (Q := Q) Wc)
    (fun t ↦ samplerPairLaw Q (Yc t).2 (Wc t).2) at hcoupled
  rw [hleft, hright] at hcoupled
  refine ⟨_, hcoupled, ?_⟩
  change Q.map (fun ω ↦ ((Yc 0).2 ω, (Wc 0).2 ω)) = c.joint
  have hy0 : (Yc 0).2 = lpPullbackCLM hf (initialSampler R μ hμ) := by
    change lpPullbackCLM hf (flow R L μ hμ a B hB hB0 0).2 = _
    rw [(flow_spec R L μ hμ a B hB hB0).2]
  have hw0 : (Wc 0).2 = lpPullbackCLM hg (initialSampler R ν hν) := by
    change lpPullbackCLM hg (flow R L ν hν b B hB hB0 0).2 = _
    rw [(flow_spec R L ν hν b B hB hB0).2]
  rw [hy0, hw0]
  have hu : lpPullbackCLM hf (initialSampler R μ hμ) =ᵐ[Q] fun ω ↦ ω.1.1 :=
    (lpPullback_coe hf _).trans (hf.quasiMeasurePreserving.ae_eq_comp (initialSampler_coe R μ hμ))
  have hv : lpPullbackCLM hg (initialSampler R ν hν) =ᵐ[Q] fun ω ↦ ω.1.2 :=
    (lpPullback_coe hg _).trans (hg.quasiMeasurePreserving.ae_eq_comp (initialSampler_coe R ν hν))
  rw [Measure.map_congr (hu.prodMk hv)]
  exact ULA.initialExtension_joint c R

/-- Source A3 contracts the actual constructed law trajectories, with no
assumed all-couplings realization or output-law equality. The realization is
provided by the explicit initial-coupling × noise construction above. -/
theorem constructed_law_contraction
    (L : LipschitzDynamics A Z G) (M : Model A G Z X I)
    (H : AdditiveModelCompatibility L M) (D : TwistedGeometry A Z)
    (μ ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp (fun z : Z ↦ z) 2 μ) (hν : MemLp (fun z : Z ↦ z) 2 ν)
    (a b : A) (B : ℝ → Lp Z 2 R) (hB : Continuous B) (hB0 : B 0 = 0)
    (ρ T : ℝ) (hmono : TwistedJointMonotonicity M D ρ) (t : ℝ) (ht : t ∈ Icc 0 T) :
    optimizerLawDistance (optimizer R L μ hμ a B hB hB0 t)
      (optimizer R L ν hν b B hB hB0 t)
      (law R L μ hμ a B hB hB0 t) (law R L ν hν b B hB hB0 t) ≤
      Real.sqrt D.conditionNumber * Real.exp (-ρ * t) * optimizerLawDistance a b μ ν := by
  have hm0 := law_zero R L μ hμ a B hB hB0
  have hn0 := law_zero R L ν hν b B hB hB0
  letI : IsProbabilityMeasure (law R L μ hμ a B hB hB0 0) := by rw [hm0]; infer_instance
  letI : IsProbabilityMeasure (law R L ν hν b B hB hB0 0) := by rw [hn0]; infer_instance
  have hm : MemLp (fun z : Z ↦ z) 2 (law R L μ hμ a B hB hB0 0) := by rw [hm0]; exact hμ
  have hn : MemLp (fun z : Z ↦ z) 2 (law R L ν hν b B hB hB0 0) := by rw [hn0]; exact hν
  have hrealize : ∀ c : ULA.Coupling (law R L μ hμ a B hB hB0 0) (law R L ν hν b B hB hB0 0),
      ∃ Λ : ℝ → Measure (Z × Z),
        IsCoupledWeakSolution M ∅ {couplingQuadratic D}
          (optimizer R L μ hμ a B hB hB0) (optimizer R L ν hν b B hB hB0)
          (law R L μ hμ a B hB hB0) (law R L ν hν b B hB hB0) Λ ∧ Λ 0 = c.joint := by
    intro c
    let c' : ULA.Coupling μ ν := ⟨c.joint, c.fst.trans hm0, c.snd.trans hn0⟩
    exact realize_all_initial_couplings R L M H D μ ν hμ hν a b B hB hB0 c'
  have h := weak_law_contraction M D ∅ {couplingQuadratic D}
    (optimizer R L μ hμ a B hB hB0) (optimizer R L ν hν b B hB hB0)
    (law R L μ hμ a B hB hB0) (law R L ν hν b B hB hB0) hm hn
    (Set.mem_singleton _) ρ T hmono hrealize t ht
  have ha : optimizer R L μ hμ a B hB hB0 0 = a :=
    congrArg Prod.fst (flow_spec R L μ hμ a B hB hB0).2
  have hb : optimizer R L ν hν b B hB hB0 0 = b :=
    congrArg Prod.fst (flow_spec R L ν hν b B hB hB0).2
  simpa only [hm0, hn0, ha, hb] using h

end AdditiveCanonical
end PBGSO
