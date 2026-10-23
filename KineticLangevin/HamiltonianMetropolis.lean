import KineticLangevin.Hamiltonian
import UnadjustedLangevin.Metropolis

/-! # Exact Gibbs invariance of a corrected Verlet proposal

The velocity-reversed Verlet proposal is a volume-preserving involution.
Its graph measure is therefore symmetric under swapping the old and new
state. The ordinary Metropolis accepted-flow argument proves an actual
measure identity for every positive measurable Gibbs weight. This supplies
a concrete invariant approximating dynamics; convergence to the unadjusted
Hamiltonian or kinetic flow remains a separate analytic obligation.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace KineticLangevin

section Involutions
variable {H : Type*} [MeasurableSpace H]

/-- The old/new-state graph of an explicit deterministic proposal. -/
def proposalGraph (J : H → H) (z : H) : H × H := (z,J z)

/-- A measure-preserving involution has a symmetric old/new graph measure. -/
theorem proposalGraph_swap_invariant (base : Measure H) (J : H → H)
    (hJ : Function.Involutive J) (hp : MeasurePreserving J base base) :
    (base.map (proposalGraph J)).map Prod.swap = base.map (proposalGraph J) := by
  have hg : Measurable (proposalGraph J) := measurable_id.prodMk hp.measurable
  have he : Prod.swap ∘ proposalGraph J = proposalGraph J ∘ J := by
    funext z
    exact Prod.ext rfl (hJ z).symm
  rw [Measure.map_map measurable_swap hg, he,
    ← Measure.map_map hg hp.measurable, hp.map_eq]

/-- Metropolizing an explicit volume-preserving involution preserves every
positive measurable density, as an exact pushforward measure identity. -/
theorem metropolis_involution_preserves_density (base : Measure H) (J : H → H)
    (hJ : Function.Involutive J) (hp : MeasurePreserving J base base)
    (w : H → ℝ) (hw : Measurable w) (hwpos : ∀ z, 0 < w z) :
    ULA.metropolisOutput
      ((base.withDensity (fun z ↦ ENNReal.ofReal (w z))).map (proposalGraph J))
      (fun p ↦ min 1 (w p.2 / w p.1)) =
        base.withDensity (fun z ↦ ENNReal.ofReal (w z)) := by
  have hg : Measurable (proposalGraph J) := measurable_id.prodMk hp.measurable
  let W : H × H → ℝ := fun p ↦ w p.1
  have hW : Measurable W := hw.comp measurable_fst
  have hweighted : ((base.withDensity (fun z ↦ ENNReal.ofReal (w z))).map (proposalGraph J)) =
      (base.map (proposalGraph J)).withDensity (fun p ↦ ENNReal.ofReal (W p)) := by
    exact ULA.map_weighted_comp base (proposalGraph J) hg
      (fun p ↦ ENNReal.ofReal (W p)) hW.ennreal_ofReal
  have hm := ULA.metropolisOutput_density_eq_initial (base.map (proposalGraph J))
    (proposalGraph_swap_invariant base J hJ hp) W hW (fun p ↦ hwpos p.1)
  have hfirst : ((base.map (proposalGraph J)).withDensity
      (fun p ↦ ENNReal.ofReal (W p))).map Prod.fst =
        base.withDensity (fun z ↦ ENNReal.ofReal (w z)) := by
    rw [← hweighted,Measure.map_map measurable_fst hg]
    simp only [proposalGraph,Function.comp_def,Measure.map_id']
  rw [hweighted]
  exact hm.trans hfirst

end Involutions

/-- The Metropolis rejection probability is bounded by the positive
energy increase, using only the exponential tangent inequality. -/
theorem metropolis_rejection_le_energy_increase (d : ℝ) :
    1 - min 1 (Real.exp (-d)) ≤ max d 0 := by
  by_cases hd : 0 ≤ d
  · rw [min_eq_right (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hd)),max_eq_left hd]
    have he := Real.add_one_le_exp (-d)
    linarith
  · have hn : d ≤ 0 := le_of_not_ge hd
    rw [min_eq_left (Real.one_le_exp_iff.mpr (neg_nonneg.mpr hn)),max_eq_right hn]
    simp

theorem metropolis_rejection_le_abs_energy (d : ℝ) :
    1 - min 1 (Real.exp (-d)) ≤ |d| := by
  exact (metropolis_rejection_le_energy_increase d).trans
    (max_le (le_abs_self d) (abs_nonneg d))

section Verlet
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure E) [SFinite μ] [Measure.IsAddLeftInvariant μ] [Measure.IsNegInvariant μ]

/-- The actual corrected Verlet kernel preserves its Gibbs weighted measure.
Both its proposal and acceptance ratio are explicit functions of the potential. -/
theorem metropolis_verlet_preserves_gibbs (f : E → ℝ) (hf : Measurable f)
    (hg : Measurable (gradient f)) (h : ℝ) :
    ULA.metropolisOutput
      (((μ.prod μ).withDensity (fun z ↦ ENNReal.ofReal (Real.exp (-hamiltonianEnergy f z)))).map
        (proposalGraph (verletProposal (gradient f) h)))
      (fun p ↦ min 1 (Real.exp (-hamiltonianEnergy f p.2) /
        Real.exp (-hamiltonianEnergy f p.1))) =
      (μ.prod μ).withDensity (fun z ↦ ENNReal.ofReal (Real.exp (-hamiltonianEnergy f z))) := by
  apply metropolis_involution_preserves_density (μ.prod μ) (verletProposal (gradient f) h)
    (verletProposal_involutive (gradient f) h) (verletProposal_measurePreserving μ (gradient f) hg h)
  · unfold hamiltonianEnergy
    fun_prop
  · intro z
    exact Real.exp_pos _

end Verlet
end KineticLangevin
