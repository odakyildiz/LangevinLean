import UnadjustedLangevin.MALAInvariance
import WassersteinMixing.Semigroup

set_option linter.style.header false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Exact reversibility of the actual stationary MALA pair

The pair law retains accepted proposals and rejected mass on the diagonal.
Its symmetry is a measure identity obtained from the actual Gaussian proposal
density and the ordinary Metropolis ratio. No reversible-kernel assumption is
introduced.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace WassersteinMixing
namespace MALAStationaryPair

section Measurable
variable {E : Type*} [MeasurableSpace E]

/-- The actual current/next-state law, retaining rejection on the diagonal. -/
def metropolisJoint (proposal : Measure (E × E)) (acceptance : E × E → ℝ) :
    Measure (E × E) :=
  ULA.acceptedFlow proposal acceptance +
    (ULA.rejectedFlow proposal acceptance).map (fun p ↦ (p.1, p.1))

/-- The first coordinate has the original proposal's initial-state marginal. -/
theorem metropolisJoint_fst (proposal : Measure (E × E)) (acceptance : E × E → ℝ)
    (ha : Measurable acceptance) (ha0 : ∀ p, 0 ≤ acceptance p)
    (ha1 : ∀ p, acceptance p ≤ 1) :
    (metropolisJoint proposal acceptance).map Prod.fst = proposal.map Prod.fst := by
  unfold metropolisJoint
  rw [Measure.map_add _ _ measurable_fst,
    Measure.map_map measurable_fst (measurable_fst.prodMk measurable_fst)]
  change (ULA.acceptedFlow proposal acceptance).map Prod.fst +
    (ULA.rejectedFlow proposal acceptance).map Prod.fst = _
  rw [← Measure.map_add _ _ measurable_fst,
    ULA.acceptedFlow_add_rejectedFlow proposal acceptance ha ha0 ha1]

/-- The next-state marginal is the original accepted/rejected Metropolis step. -/
theorem metropolisJoint_snd (proposal : Measure (E × E)) (acceptance : E × E → ℝ) :
    (metropolisJoint proposal acceptance).map Prod.snd =
      ULA.metropolisOutput proposal acceptance := by
  unfold metropolisJoint ULA.metropolisOutput
  rw [Measure.map_add _ _ measurable_snd,
    Measure.map_map measurable_snd (measurable_fst.prodMk measurable_fst)]
  rfl

/-- Accepted-flow balance gives full pair-law symmetry, including rejection. -/
theorem metropolisJoint_swap (proposal : Measure (E × E)) (acceptance : E × E → ℝ)
    (haccepted : (ULA.acceptedFlow proposal acceptance).map Prod.swap =
      ULA.acceptedFlow proposal acceptance) :
    (metropolisJoint proposal acceptance).map Prod.swap =
      metropolisJoint proposal acceptance := by
  unfold metropolisJoint
  rw [Measure.map_add _ _ measurable_swap, haccepted,
    Measure.map_map measurable_swap (measurable_fst.prodMk measurable_fst)]
  rfl

/-- The actual Metropolis accepted density is symmetric against a symmetric base. -/
theorem acceptedFlow_swap_of_density (base : Measure (E × E))
    (hbase : base.map Prod.swap = base) (w : E × E → ℝ)
    (hw : Measurable w) (hw0 : ∀ p, 0 < w p) :
    (ULA.acceptedFlow (base.withDensity (fun p ↦ ENNReal.ofReal (w p)))
      (ULA.metropolisAcceptance w)).map Prod.swap =
    ULA.acceptedFlow (base.withDensity (fun p ↦ ENNReal.ofReal (w p)))
      (ULA.metropolisAcceptance w) := by
  rw [ULA.acceptedFlow_density base w hw hw0]
  let v : E × E → ℝ≥0∞ := fun p ↦ ENNReal.ofReal (min (w p) (w p.swap))
  have hv : Measurable v := (hw.min (hw.comp measurable_swap)).ennreal_ofReal
  have hs : v ∘ (MeasurableEquiv.prodComm : (E × E) ≃ᵐ (E × E)) = v := by
    funext p
    change ENNReal.ofReal (min (w p.swap) (w p.swap.swap)) =
      ENNReal.ofReal (min (w p) (w p.swap))
    rw [Prod.swap_swap, min_comm]
  have hm := ULA.map_weighted_comp_equiv base
    (MeasurableEquiv.prodComm : (E × E) ≃ᵐ (E × E)) v hv
  change (base.withDensity (v ∘ (MeasurableEquiv.prodComm : (E × E) ≃ᵐ (E × E)))).map
    Prod.swap = (base.map Prod.swap).withDensity v at hm
  rw [hs, hbase] at hm
  exact hm

end Measurable

section ActualMALA
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual MALA current/next pair initialized at its normalized Gibbs law. -/
def jointLaw (V : E → ℝ) (h : ℝ) : Measure (E × E) :=
  metropolisJoint (ULA.malaProposalJoint V h (ULA.gibbsMeasure V))
    (fun p ↦ ULA.malaAcceptance V h p.1 p.2)

private theorem acceptance_measurable (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) :
    Measurable (fun p : E × E ↦ ULA.malaAcceptance V h p.1 p.2) := by
  have hV := hdiff.continuous
  have hg := hLip.continuous
  unfold ULA.malaAcceptance ULA.malaLogRatio
  fun_prop

/-- The first marginal is the actual Gibbs target, by exact mass partition. -/
theorem jointLaw_fst (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) :
    (jointLaw V h).map Prod.fst = ULA.gibbsMeasure V := by
  rw [jointLaw, metropolisJoint_fst _ _ (acceptance_measurable V h L hdiff hLip)
    (fun p ↦ ULA.malaAcceptance_nonneg V h p.1 p.2)
    (fun p ↦ ULA.malaAcceptance_le_one V h p.1 p.2)]
  unfold ULA.malaProposalJoint
  rw [Measure.map_map measurable_fst
    (measurable_fst.prodMk (ULA.malaProposal_measurable V h L hLip))]
  change ((ULA.gibbsMeasure V).prod (stdGaussian E)).map Prod.fst = _
  simp

/-- The second marginal is exactly the actual MALA update of the Gibbs law. -/
theorem jointLaw_snd_eq_step (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) :
    (jointLaw V h).map Prod.snd = ULA.malaOneStep V h (ULA.gibbsMeasure V) := by
  rw [jointLaw, metropolisJoint_snd,
    ULA.malaOneStep_eq_metropolisOutput V h L hdiff hLip]

/-- Detailed balance of the actual Gaussian MALA pair at the original Gibbs law. -/
theorem jointLaw_swap (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    (hh : 0 < h) (hdiff : Differentiable ℝ V)
    (hLip : LipschitzWith L (gradient V)) :
    (jointLaw V h).map Prod.swap = jointLaw V h := by
  apply metropolisJoint_swap
  let base : Measure (E × E) :=
    ((ULA.gibbsPartition V)⁻¹ * ENNReal.ofReal (ULA.gaussianProposalNormalizer (H := E) h)) •
      (volume.prod volume)
  have hb : base.map Prod.swap = base := by
    dsimp [base]
    rw [Measure.map_smul _ measurable_swap.aemeasurable, Measure.prod_swap]
  have hw : Measurable (ULA.malaJointWeight V h) := by
    have hV := hdiff.continuous
    have hg := hLip.continuous
    unfold ULA.malaJointWeight
    fun_prop
  have ha : (fun p : E × E ↦ ULA.malaAcceptance V h p.1 p.2) =
      ULA.metropolisAcceptance (ULA.malaJointWeight V h) := by
    funext p
    unfold ULA.malaAcceptance ULA.metropolisAcceptance
    rw [ULA.malaJointWeight_ratio]
  rw [ha, ULA.malaProposalJoint_gibbs_density V h L hh hdiff hLip]
  exact acceptedFlow_swap_of_density base hb _ hw (fun _ ↦ Real.exp_pos _)

/-- The second marginal equals the Gibbs law, as a consequence of reversibility. -/
theorem jointLaw_snd (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    (hh : 0 < h) (hdiff : Differentiable ℝ V)
    (hLip : LipschitzWith L (gradient V)) :
    (jointLaw V h).map Prod.snd = ULA.gibbsMeasure V := by
  rw [ULA.marginals_eq_of_swap_invariant _ (jointLaw_swap V h L hh hdiff hLip)]
  exact jointLaw_fst V h L hdiff hLip

/-- The actual stationary pair is a probability measure whenever its Gibbs
marginal has the derived probability normalization. -/
theorem jointLaw_isProbability (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    [IsProbabilityMeasure (ULA.gibbsMeasure V)]
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) :
    IsProbabilityMeasure (jointLaw V h) := by
  constructor
  have hm := congrArg (fun μ : Measure E ↦ μ Set.univ) (jointLaw_fst V h L hdiff hLip)
  simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,
    Set.preimage_univ, measure_univ] using hm

variable {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The genuine MALA transition on square-integrable observables, constructed
from the actual stationary current/next-state law. -/
def operator (V : E → ℝ) (h : ℝ) (L : ℝ≥0) (hh : 0 < h)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) :
    Lp F 2 (ULA.gibbsMeasure V) →L[𝕜] Lp F 2 (ULA.gibbsMeasure V) :=
  StationaryPair.transition (𝕜 := 𝕜) (ULA.gibbsMeasure V) (jointLaw V h)
    (jointLaw_fst V h L hdiff hLip) (jointLaw_snd V h L hh hdiff hLip)

/-- Its norm bound is a conclusion of the actual stationary marginals. -/
theorem operator_norm_le (V : E → ℝ) (h : ℝ) (L : ℝ≥0) (hh : 0 < h)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) :
    ‖operator (𝕜 := 𝕜) (F := F) V h L hh hdiff hLip‖ ≤ 1 :=
  StationaryPair.transition_opNorm_le (𝕜 := 𝕜) (ULA.gibbsMeasure V) (jointLaw V h)
    (jointLaw_fst V h L hdiff hLip) (jointLaw_snd V h L hh hdiff hLip)

/-- Exact detailed balance proves self-adjointness of the constructed MALA
operator; self-adjointness is not included among its hypotheses. -/
theorem operator_isSelfAdjoint (V : E → ℝ) (h : ℝ) (L : ℝ≥0) (hh : 0 < h)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) :
    IsSelfAdjoint (operator (𝕜 := 𝕜) (F := F) V h L hh hdiff hLip) :=
  StationaryPair.transition_isSelfAdjoint (𝕜 := 𝕜) (ULA.gibbsMeasure V) (jointLaw V h)
    (jointLaw_fst V h L hdiff hLip) (jointLaw_snd V h L hh hdiff hLip)
    (jointLaw_swap V h L hh hdiff hLip)

/-- Every finite MALA operator power is self-adjoint. -/
theorem operator_pow_isSelfAdjoint (V : E → ℝ) (h : ℝ) (L : ℝ≥0) (hh : 0 < h)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) (n : ℕ) :
    IsSelfAdjoint (operator (𝕜 := 𝕜) (F := F) V h L hh hdiff hLip ^ n) :=
  (operator_isSelfAdjoint (𝕜 := 𝕜) (F := F) V h L hh hdiff hLip).pow n

/-- Every finite MALA operator power remains a contraction. -/
theorem operator_pow_norm_le (V : E → ℝ) (h : ℝ) (L : ℝ≥0) (hh : 0 < h)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) (n : ℕ) :
    ‖operator (𝕜 := 𝕜) (F := F) V h L hh hdiff hLip ^ n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul]
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_apply_eq_comp]
    exact (ih _).trans (StationaryPair.transition_norm_le (𝕜 := 𝕜)
      (ULA.gibbsMeasure V) (jointLaw V h) (jointLaw_fst V h L hdiff hLip)
      (jointLaw_snd V h L hh hdiff hLip) f)

omit [CompleteSpace F] in
/-- Detailed balance gives the exact two-time correlation symmetry for
ordinary continuous observables, independently of an abstract operator name. -/
theorem jointLaw_correlation_symmetric (V : E → ℝ) (h : ℝ) (L : ℝ≥0) (hh : 0 < h)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V))
    (f g : E → F) (hf : Continuous f) (hg : Continuous g) :
    (∫ p, inner 𝕜 (f p.2) (g p.1) ∂jointLaw V h) =
      ∫ p, inner 𝕜 (f p.1) (g p.2) ∂jointLaw V h := by
  have hm := integral_map (μ := jointLaw V h) measurable_swap.aemeasurable
    (show AEStronglyMeasurable (fun p : E × E ↦ inner 𝕜 (f p.2) (g p.1))
      ((jointLaw V h).map Prod.swap) from
      ((hf.comp continuous_snd).inner (hg.comp continuous_fst)).aestronglyMeasurable)
  rw [jointLaw_swap V h L hh hdiff hLip] at hm
  exact hm

end ActualMALA
end MALAStationaryPair
end WassersteinMixing
