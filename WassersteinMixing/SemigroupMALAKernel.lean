import WassersteinMixing.SemigroupPowers
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Kernel.Composition.WithDensity

set_option linter.style.header false

/-! # The actual independent-Gaussian MALA transition kernel

The kernel is built from a deterministic current state, an independent standard
Gaussian proposal innovation, and the actual acceptance/rejection weights.
Its value at a state is the existing MALA law step from that Dirac law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace WassersteinMixing.MALAStationaryPair

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The deterministic current state paired with an actual independent Gaussian. -/
def gaussianPairKernel : Kernel E (E × E) :=
  Kernel.id ×ₖ Kernel.const E (stdGaussian E)

instance gaussianPairKernel_isMarkov : IsMarkovKernel (gaussianPairKernel (E := E)) := by
  unfold gaussianPairKernel
  infer_instance

/-- The actual accepted/rejected Gaussian MALA transition kernel. -/
def explicitKernel (V : E → ℝ) (h : ℝ) : Kernel E E :=
  ((gaussianPairKernel (E := E)).withDensity
      (fun _ p ↦ ENNReal.ofReal (ULA.malaProposalAcceptance V h p))).map
        (fun p ↦ ULA.malaProposal V h p.1 p.2) +
  ((gaussianPairKernel (E := E)).withDensity
      (fun _ p ↦ ENNReal.ofReal (1 - ULA.malaProposalAcceptance V h p))).map Prod.fst

/-- Evaluation gives the original MALA update from the actual Dirac initialization. -/
theorem explicitKernel_apply (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) (x : E) :
    explicitKernel V h x = ULA.malaOneStep V h (Measure.dirac x) := by
  have ha := ULA.malaProposalAcceptance_measurable V h L hdiff hLip
  have hacc : Measurable (Function.uncurry
      (fun (_ : E) (p : E × E) ↦ ENNReal.ofReal (ULA.malaProposalAcceptance V h p))) :=
    (ha.comp measurable_snd).ennreal_ofReal
  have hrej : Measurable (Function.uncurry
      (fun (_ : E) (p : E × E) ↦ ENNReal.ofReal (1 - ULA.malaProposalAcceptance V h p))) :=
    (measurable_const.sub (ha.comp measurable_snd)).ennreal_ofReal
  simp only [explicitKernel, add_apply,
    Kernel.map_apply _ (ULA.malaProposal_measurable V h L hLip),
    Kernel.map_apply _ measurable_fst, Kernel.withDensity_apply _ hacc,
    Kernel.withDensity_apply _ hrej, gaussianPairKernel, Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply, ULA.malaOneStep]

omit [CompleteSpace E] [BorelSpace E] in
/-- Integrating the current/Gaussian kernel gives the actual independent product law. -/
theorem gaussianPairKernel_comp (μ : Measure E) [SFinite μ] :
    gaussianPairKernel (E := E) ∘ₘ μ = μ.prod (stdGaussian E) := by
  rw [gaussianPairKernel, ← Measure.compProd_eq_comp_prod, Measure.compProd_const]

/-- The explicit kernel acts on every initial law by the existing actual
independent-Gaussian MALA step, including the full rejection mass. -/
theorem explicitKernel_comp (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V))
    (μ : Measure E) [SFinite μ] :
    explicitKernel V h ∘ₘ μ = ULA.malaOneStep V h μ := by
  have ha := ULA.malaProposalAcceptance_measurable V h L hdiff hLip
  have hrej : Measurable (fun p : E × E ↦
      ENNReal.ofReal (1 - ULA.malaProposalAcceptance V h p)) := by fun_prop
  rw [explicitKernel, Measure.add_comp,
    ← Measure.map_comp μ _ (ULA.malaProposal_measurable V h L hLip),
    ← Measure.map_comp μ _ measurable_fst,
    ← Measure.withDensity_comp ha.ennreal_ofReal,
    ← Measure.withDensity_comp hrej,
    gaussianPairKernel_comp]
  rfl

/-- Actual acceptance and rejection partition all mass at each current state. -/
theorem explicitKernel_isMarkov (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) :
    IsMarkovKernel (explicitKernel V h) := by
  constructor
  intro x
  rw [explicitKernel_apply V h L hdiff hLip]
  constructor
  unfold ULA.malaOneStep
  rw [Measure.add_apply,
    Measure.map_apply (ULA.malaProposal_measurable V h L hLip) MeasurableSet.univ,
    Measure.map_apply measurable_fst MeasurableSet.univ]
  simp only [Set.preimage_univ]
  have ha := ULA.malaProposalAcceptance_measurable V h L hdiff hLip
  have hmass := congrArg (fun m : Measure (E × E) ↦ m Set.univ)
    (ULA.acceptedFlow_add_rejectedFlow ((Measure.dirac x).prod (stdGaussian E))
      (ULA.malaProposalAcceptance V h) ha
      (fun p ↦ ULA.malaAcceptance_nonneg V h p.1 (ULA.malaProposal V h p.1 p.2))
      (fun p ↦ ULA.malaAcceptance_le_one V h p.1 (ULA.malaProposal V h p.1 p.2)))
  simpa only [ULA.acceptedFlow, ULA.rejectedFlow, Measure.add_apply, measure_univ] using hmass

end WassersteinMixing.MALAStationaryPair
