import KineticLangevin.HamiltonianError
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Corrected Verlet invariance and weak approximation

The accepted move below is the ordinary Verlet map. The rejected move flips
the velocity. Its exact Gibbs invariance follows from the explicitly proved
Metropolis invariance and the exact symmetry of the Gibbs density.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal ENNReal
namespace KineticLangevin

section Graph
variable {H : Type*} [MeasurableSpace H]

/-- The two marginals of a Metropolis graph are the explicitly weighted
accepted proposal and rejected initial state. -/
theorem metropolisOutput_graph (π : Measure H) (J : H → H) (hJ : Measurable J)
    (a : H×H → ℝ) (ha : Measurable a) :
    ULA.metropolisOutput (π.map (proposalGraph J)) a =
      (π.withDensity (fun z ↦ ENNReal.ofReal (a (z,J z)))).map J +
      π.withDensity (fun z ↦ ENNReal.ofReal (1-a (z,J z))) := by
  have hG : Measurable (proposalGraph J) := measurable_id.prodMk hJ
  have hm := ULA.map_weighted_comp π (proposalGraph J) hG
    (fun p ↦ ENNReal.ofReal (a p)) ha.ennreal_ofReal
  have hn := ULA.map_weighted_comp π (proposalGraph J) hG
    (fun p ↦ ENNReal.ofReal (1-a p)) (measurable_const.sub ha).ennreal_ofReal
  unfold ULA.metropolisOutput ULA.acceptedFlow ULA.rejectedFlow
  rw [← hm,← hn,Measure.map_map measurable_snd hG,Measure.map_map measurable_fst hG]
  simp only [proposalGraph,Function.comp_def,Measure.map_id']

end Graph

section Verlet
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure E) [SFinite μ] [Measure.IsAddLeftInvariant μ] [Measure.IsNegInvariant μ]

/-- Product-Haar phase measure weighted by the actual Hamiltonian density. -/
def hamiltonianGibbs (f : E → ℝ) : Measure (E×E) :=
  (μ.prod μ).withDensity (fun z ↦ ENNReal.ofReal (Real.exp (-hamiltonianEnergy f z)))

/-- Velocity reversal preserves the actual Hamiltonian Gibbs density. -/
theorem hamiltonianGibbs_reverseVelocity (f : E → ℝ) (hf : Measurable f) :
    (hamiltonianGibbs μ f).map reverseVelocity = hamiltonianGibbs μ f := by
  have hw : Measurable (fun z : E×E ↦ ENNReal.ofReal (Real.exp (-hamiltonianEnergy f z))) := by
    unfold hamiltonianEnergy
    fun_prop
  have hm := ULA.map_weighted_comp (μ.prod μ) reverseVelocity
    (reverseVelocity_measurePreserving μ).measurable _ hw
  simpa only [Function.comp_def,hamiltonianEnergy_reverseVelocity,
    (reverseVelocity_measurePreserving μ).map_eq,hamiltonianGibbs] using hm

/-- Actual acceptance probability for a Verlet energy change. -/
def verletAcceptance (f : E → ℝ) (h : ℝ) (z : E×E) : ℝ :=
  min 1 (Real.exp (-(hamiltonianEnergy f (verletStep (gradient f) h z)-
    hamiltonianEnergy f z)))

theorem verletAcceptance_measurable (f : E → ℝ) (hf : Measurable f)
    (hg : Measurable (gradient f)) (h : ℝ) : Measurable (verletAcceptance f h) := by
  unfold verletAcceptance hamiltonianEnergy verletStep kickStep driftStep
  fun_prop

theorem verletAcceptance_nonneg (f : E → ℝ) (h : ℝ) (z : E×E) :
    0 ≤ verletAcceptance f h z := le_min (by norm_num) (Real.exp_pos _).le

theorem verletAcceptance_le_one (f : E → ℝ) (h : ℝ) (z : E×E) :
    verletAcceptance f h z ≤ 1 := min_le_left _ _

/-- Applying velocity reversal after the proved Metropolis step gives
ordinary Verlet on acceptance and a velocity flip on rejection. The sum of
these two explicit weighted pushforwards is exactly the Gibbs measure. -/
theorem correctedVerlet_preserves_gibbs (f : E → ℝ) (hf : Measurable f)
    (hg : Measurable (gradient f)) (h : ℝ) :
    ((hamiltonianGibbs μ f).withDensity (fun z ↦ ENNReal.ofReal (verletAcceptance f h z))).map
        (verletStep (gradient f) h) +
      ((hamiltonianGibbs μ f).withDensity (fun z ↦ ENNReal.ofReal (1-verletAcceptance f h z))).map
        reverseVelocity = hamiltonianGibbs μ f := by
  let a : (E×E)×(E×E) → ℝ := fun p ↦ min 1
    (Real.exp (-hamiltonianEnergy f p.2)/Real.exp (-hamiltonianEnergy f p.1))
  have ha : Measurable a := by dsimp [a]; unfold hamiltonianEnergy; fun_prop
  have hJ := (verletProposal_measurePreserving μ (gradient f) hg h).measurable
  have hm := metropolis_verlet_preserves_gibbs μ f hf hg h
  change ULA.metropolisOutput ((hamiltonianGibbs μ f).map
    (proposalGraph (verletProposal (gradient f) h))) a = hamiltonianGibbs μ f at hm
  rw [metropolisOutput_graph _ _ hJ a ha] at hm
  have he (z : E×E) : a (z,verletProposal (gradient f) h z) = verletAcceptance f h z := by
    simp only [a,verletProposal,hamiltonianEnergy_reverseVelocity,verletAcceptance,
      ← Real.exp_sub]
    congr 2
    ring
  simp only [he] at hm
  have hh := congrArg (fun ν : Measure (E×E) ↦ ν.map reverseVelocity) hm
  rw [Measure.map_add _ _ (reverseVelocity_measurePreserving μ).measurable,
    Measure.map_map (reverseVelocity_measurePreserving μ).measurable hJ,
    hamiltonianGibbs_reverseVelocity μ f hf] at hh
  convert hh using 2
  congr 1
  funext z
  simp only [Function.comp_def,verletProposal,reverseVelocity_twice]

end Verlet
end KineticLangevin
