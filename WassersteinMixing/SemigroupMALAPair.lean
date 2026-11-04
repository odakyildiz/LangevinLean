import WassersteinMixing.SemigroupMALAKernel
import Mathlib.Probability.Kernel.Composition.Lemmas

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Identifying the actual fresh-noise MALA pair and its anchored powers

The pair kernel retains the current state next to the accepted/rejected output.
Its first coordinate is deterministically the current state, so it equals the
product of the Dirac current state and the explicit MALA transition. Integrating
against Gibbs identifies it with the proved reversible Gaussian proposal pair.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace WassersteinMixing.MALAStationaryPair

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual fresh-Gaussian current/output pair before integrating the input law. -/
def freshJointKernel (V : E → ℝ) (h : ℝ) : Kernel E (E × E) :=
  ((gaussianPairKernel (E := E)).withDensity
      (fun _ p ↦ ENNReal.ofReal (ULA.malaProposalAcceptance V h p))).map
        (fun p ↦ (p.1, ULA.malaProposal V h p.1 p.2)) +
  ((gaussianPairKernel (E := E)).withDensity
      (fun _ p ↦ ENNReal.ofReal (1 - ULA.malaProposalAcceptance V h p))).map
        (fun p ↦ (p.1, p.1))

/-- The actual fresh pair for an arbitrary initial law. -/
def freshJointMeasure (V : E → ℝ) (h : ℝ) (μ : Measure E) : Measure (E × E) :=
  ((μ.prod (stdGaussian E)).withDensity
      (fun p ↦ ENNReal.ofReal (ULA.malaProposalAcceptance V h p))).map
        (fun p ↦ (p.1, ULA.malaProposal V h p.1 p.2)) +
  ((μ.prod (stdGaussian E)).withDensity
      (fun p ↦ ENNReal.ofReal (1 - ULA.malaProposalAcceptance V h p))).map
        (fun p ↦ (p.1, p.1))

theorem freshJointKernel_comp (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V))
    (μ : Measure E) [SFinite μ] :
    freshJointKernel V h ∘ₘ μ = freshJointMeasure V h μ := by
  have hp := measurable_fst.prodMk (ULA.malaProposal_measurable V h L hLip)
  have ha := ULA.malaProposalAcceptance_measurable V h L hdiff hLip
  have hrej : Measurable (fun p : E × E ↦
      ENNReal.ofReal (1 - ULA.malaProposalAcceptance V h p)) := by fun_prop
  rw [freshJointKernel, Measure.add_comp, ← Measure.map_comp μ _ hp,
    ← Measure.map_comp μ _ (measurable_fst.prodMk measurable_fst),
    ← Measure.withDensity_comp ha.ennreal_ofReal, ← Measure.withDensity_comp hrej,
    gaussianPairKernel_comp]
  rfl

/-- Exact acceptance/rejection partition fixes the first marginal for every input. -/
theorem freshJointMeasure_fst (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) (μ : Measure E) :
    (freshJointMeasure V h μ).map Prod.fst = μ := by
  have hp := measurable_fst.prodMk (ULA.malaProposal_measurable V h L hLip)
  rw [freshJointMeasure, Measure.map_add _ _ measurable_fst,
    Measure.map_map measurable_fst hp,
    Measure.map_map measurable_fst (measurable_fst.prodMk measurable_fst)]
  change (((μ.prod (stdGaussian E)).withDensity
      (fun p ↦ ENNReal.ofReal (ULA.malaProposalAcceptance V h p))).map Prod.fst +
    ((μ.prod (stdGaussian E)).withDensity
      (fun p ↦ ENNReal.ofReal (1 - ULA.malaProposalAcceptance V h p))).map Prod.fst) = _
  rw [← Measure.map_add _ _ measurable_fst]
  have ha := ULA.malaProposalAcceptance_measurable V h L hdiff hLip
  rw [show (μ.prod (stdGaussian E)).withDensity
      (fun p ↦ ENNReal.ofReal (ULA.malaProposalAcceptance V h p)) +
    (μ.prod (stdGaussian E)).withDensity
      (fun p ↦ ENNReal.ofReal (1 - ULA.malaProposalAcceptance V h p)) =
        μ.prod (stdGaussian E) from
      ULA.acceptedFlow_add_rejectedFlow _ _ ha
        (fun p ↦ ULA.malaAcceptance_nonneg V h p.1 (ULA.malaProposal V h p.1 p.2))
        (fun p ↦ ULA.malaAcceptance_le_one V h p.1 (ULA.malaProposal V h p.1 p.2))]
  simp

/-- The first coordinate of the pair kernel is the actual deterministic current state. -/
theorem freshJointKernel_fst (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) (x : E) :
    (freshJointKernel V h x).map Prod.fst = Measure.dirac x := by
  have he : freshJointKernel V h ∘ₘ Measure.dirac x = freshJointKernel V h x := by
    ext s hs
    rw [Measure.bind_apply hs (Kernel.aemeasurable _),
      lintegral_dirac' x ((freshJointKernel V h).measurable_coe hs)]
  rw [← he, freshJointKernel_comp V h L hdiff hLip]
  exact freshJointMeasure_fst V h L hdiff hLip _

/-- The second coordinate of the pair kernel is exactly the explicit MALA transition. -/
theorem freshJointKernel_snd (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient V)) (x : E) :
    (freshJointKernel V h x).map Prod.snd = explicitKernel V h x := by
  have hp := ULA.malaProposal_measurable V h L hLip
  simp only [freshJointKernel, explicitKernel, add_apply,
    Kernel.map_apply _ (measurable_fst.prodMk hp),
    Kernel.map_apply _ (measurable_fst.prodMk measurable_fst),
    Kernel.map_apply _ hp, Kernel.map_apply _ measurable_fst,
    Measure.map_add _ _ measurable_snd,
    Measure.map_map measurable_snd (measurable_fst.prodMk hp),
    Measure.map_map measurable_snd (measurable_fst.prodMk measurable_fst)]
  rfl

/-- A pair measure with a deterministic first coordinate is its Dirac/product law. -/
theorem measure_eq_dirac_prod (J : Measure (E × E)) (x : E)
    (hfst : J.map Prod.fst = Measure.dirac x) :
    J = (Measure.dirac x).prod (J.map Prod.snd) := by
  have : IsProbabilityMeasure J := by
    constructor
    have hm := congrArg (fun μ : Measure E ↦ μ Set.univ) hfst
    simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,
      Set.preimage_univ, measure_univ] using hm
  have hAE : ∀ᵐ p ∂J, p.1 = x := by
    rw [ae_iff]
    change J (Prod.fst ⁻¹' ({x}ᶜ : Set E)) = 0
    rw [← Measure.map_apply measurable_fst (measurableSet_singleton x).compl, hfst]
    simp
  calc
    J = J.map (fun p : E × E ↦ (p.1, p.2)) := Measure.map_id.symm
    _ = J.map (fun p : E × E ↦ (x, p.2)) := by
      apply Measure.map_congr
      filter_upwards [hAE] with p hp
      exact Prod.ext hp rfl
    _ = (J.map Prod.snd).map (Prod.mk x) :=
      (Measure.map_map measurable_prodMk_left measurable_snd).symm
    _ = _ := (Measure.dirac_prod x).symm

/-- The fresh pair kernel equals deterministic current state times the actual transition. -/
theorem freshJointKernel_eq_id_prod (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) :
    freshJointKernel V h = Kernel.id ×ₖ explicitKernel V h := by
  have := explicitKernel_isMarkov V h L hdiff hLip
  ext x : 1
  rw [Kernel.prod_apply, Kernel.id_apply,
    ← freshJointKernel_snd V h L hLip x]
  exact measure_eq_dirac_prod _ x (freshJointKernel_fst V h L hdiff hLip x)

/-- Actual fresh Gaussian pair mass is exactly the original Metropolis pair construction. -/
theorem freshJointMeasure_eq_metropolis (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) (μ : Measure E) :
    freshJointMeasure V h μ =
      metropolisJoint (ULA.malaProposalJoint V h μ)
        (fun p ↦ ULA.malaAcceptance V h p.1 p.2) := by
  let T : E × E → E × E := fun p ↦ (p.1, ULA.malaProposal V h p.1 p.2)
  let a : E × E → ℝ := fun p ↦ ULA.malaAcceptance V h p.1 p.2
  have hT : Measurable T := measurable_fst.prodMk (ULA.malaProposal_measurable V h L hLip)
  have ha : Measurable a := by
    have hV := hdiff.continuous
    have hg := hLip.continuous
    unfold a ULA.malaAcceptance ULA.malaLogRatio
    fun_prop
  have hacc := ULA.map_weighted_comp (μ.prod (stdGaussian E)) T hT
    (fun p ↦ ENNReal.ofReal (a p)) ha.ennreal_ofReal
  have hrej := ULA.map_weighted_comp (μ.prod (stdGaussian E)) T hT
    (fun p ↦ ENNReal.ofReal (1 - a p)) (measurable_const.sub ha).ennreal_ofReal
  unfold metropolisJoint ULA.acceptedFlow ULA.rejectedFlow ULA.malaProposalJoint
  change freshJointMeasure V h μ =
    (((μ.prod (stdGaussian E)).map T).withDensity (fun p ↦ ENNReal.ofReal (a p))) +
    ((((μ.prod (stdGaussian E)).map T).withDensity
      (fun p ↦ ENNReal.ofReal (1 - a p))).map (fun p ↦ (p.1, p.1)))
  rw [← hacc, ← hrej, Measure.map_map (measurable_fst.prodMk measurable_fst) hT]
  rfl

/-- The actual stationary fresh-noise MALA pair is the previously proved reversible pair. -/
theorem explicitKernel_pair_eq (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V))
    (μ : Measure E) [SFinite μ] :
    μ ⊗ₘ explicitKernel V h =
      metropolisJoint (ULA.malaProposalJoint V h μ)
        (fun p ↦ ULA.malaAcceptance V h p.1 p.2) := by
  have := explicitKernel_isMarkov V h L hdiff hLip
  rw [Measure.compProd_eq_comp_prod,
    ← freshJointKernel_eq_id_prod V h L hdiff hLip,
    freshJointKernel_comp V h L hdiff hLip,
    freshJointMeasure_eq_metropolis V h L hdiff hLip]

/-- In particular, the actual Gibbs-start pair is exactly the Gaussian detailed-balance law. -/
theorem explicitKernel_gibbs_pair_eq (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    [SFinite (ULA.gibbsMeasure V)]
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) :
    ULA.gibbsMeasure V ⊗ₘ explicitKernel V h = jointLaw V h :=
  explicitKernel_pair_eq V h L hdiff hLip _

end WassersteinMixing.MALAStationaryPair

namespace WassersteinMixing.StationaryKernelPower
variable {E : Type*} [MeasurableSpace E]

/-- The same actual kernel power can advance by its final transition. -/
theorem kernelPower_succ_last (κ : Kernel E E) (n : ℕ) :
    kernelPower κ (n + 1) = κ ∘ₖ kernelPower κ n := by
  induction n with
  | zero => simp [kernelPower, Kernel.id_comp, Kernel.comp_id]
  | succ n ih =>
    rw [kernelPower, ih, Kernel.comp_assoc]
    exact congrArg (fun η ↦ κ ∘ₖ η) ih

/-- The anchored pair advances its endpoint while retaining the actual initial state. -/
theorem anchored_pair_succ (μ : Measure E) [SFinite μ]
    (κ : Kernel E E) [IsMarkovKernel κ] (n : ℕ) :
    μ ⊗ₘ kernelPower κ (n + 1) =
      (Kernel.id ∥ₖ κ) ∘ₘ (μ ⊗ₘ kernelPower κ n) := by
  rw [kernelPower_succ_last, Measure.parallelComp_comp_compProd]

/-- At zero steps the actual pair retains the same initial value twice. -/
theorem anchored_pair_zero (μ : Measure E) [SFinite μ] (κ : Kernel E E) :
    μ ⊗ₘ kernelPower κ 0 = μ.map (fun x ↦ (x, x)) := by
  rw [kernelPower, Measure.compProd_id]
  rfl

end WassersteinMixing.StationaryKernelPower

namespace WassersteinMixing.MALAStationaryPair
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual Gibbs-start MALA pair with its initial coordinate retained. -/
def explicitPowerJointLaw (V : E → ℝ) (h : ℝ) (n : ℕ) : Measure (E × E) :=
  ULA.gibbsMeasure V ⊗ₘ StationaryKernelPower.kernelPower (explicitKernel V h) n

theorem explicitPowerJointLaw_isProbability (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    [IsProbabilityMeasure (ULA.gibbsMeasure V)]
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) (n : ℕ) :
    IsProbabilityMeasure (explicitPowerJointLaw V h n) := by
  have := explicitKernel_isMarkov V h L hdiff hLip
  unfold explicitPowerJointLaw
  infer_instance

/-- Detailed balance of every actual fresh-noise anchored MALA power. -/
theorem explicitPowerJointLaw_swap (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    [IsProbabilityMeasure (ULA.gibbsMeasure V)] (hh : 0 < h)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) (n : ℕ) :
    (explicitPowerJointLaw V h n).map Prod.swap = explicitPowerJointLaw V h n := by
  have := explicitKernel_isMarkov V h L hdiff hLip
  apply StationaryKernelPower.kernelPower_pair_swap
  rw [explicitKernel_gibbs_pair_eq V h L hdiff hLip]
  exact jointLaw_swap V h L hh hdiff hLip

theorem explicitPowerJointLaw_fst (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    [IsProbabilityMeasure (ULA.gibbsMeasure V)]
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) (n : ℕ) :
    (explicitPowerJointLaw V h n).map Prod.fst = ULA.gibbsMeasure V := by
  have := explicitKernel_isMarkov V h L hdiff hLip
  exact StationaryKernelPower.kernelPower_pair_fst _ _ n

theorem explicitPowerJointLaw_snd (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    [IsProbabilityMeasure (ULA.gibbsMeasure V)] (hh : 0 < h)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) (n : ℕ) :
    (explicitPowerJointLaw V h n).map Prod.snd = ULA.gibbsMeasure V := by
  rw [ULA.marginals_eq_of_swap_invariant _
    (explicitPowerJointLaw_swap V h L hh hdiff hLip n)]
  exact explicitPowerJointLaw_fst V h L hdiff hLip n

/-- Fresh-noise finite-step pairs satisfy the actual endpoint-update recurrence. -/
theorem explicitPowerJointLaw_succ (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    [IsProbabilityMeasure (ULA.gibbsMeasure V)]
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) (n : ℕ) :
    explicitPowerJointLaw V h (n + 1) =
      (Kernel.id ∥ₖ explicitKernel V h) ∘ₘ explicitPowerJointLaw V h n := by
  have := explicitKernel_isMarkov V h L hdiff hLip
  exact StationaryKernelPower.anchored_pair_succ _ _ n

end WassersteinMixing.MALAStationaryPair
