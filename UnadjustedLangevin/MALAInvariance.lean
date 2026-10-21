import UnadjustedLangevin.MALACoupling
import UnadjustedLangevin.GaussianProposalPairDensity

set_option linter.style.header false

/-! # Exact Gibbs invariance of the Metropolis approximation

The actual Gaussian proposal density gives a positive joint density. Its
Metropolis acceptance ratio makes the accepted flow symmetric. Thus the
normalized Gibbs measure is invariant, with no stationarity premise.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ULA

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

/-- Current state and proposed state under the actual Gaussian innovation. -/
def malaProposalJoint (U : H → ℝ) (h : ℝ) (μ : Measure H) : Measure (H × H) :=
  (μ.prod (stdGaussian H)).map (fun p ↦ (p.1, malaProposal U h p.1 p.2))

/-- The strictly positive real joint density, with both constant normalizers
kept in the symmetric base measure. -/
def malaJointWeight (U : H → ℝ) (h : ℝ) (p : H × H) : ℝ :=
  Real.exp (-U p.1 - ‖p.2 - p.1 + h • gradient U p.1‖ ^ 2 / (4 * h))

/-- The reverse-to-forward density ratio is the displayed MALA ratio. -/
theorem malaJointWeight_ratio (U : H → ℝ) (h : ℝ) (p : H × H) :
    malaJointWeight U h p.swap / malaJointWeight U h p =
      Real.exp (malaLogRatio U h p.1 p.2) := by
  unfold malaJointWeight malaLogRatio
  rw [← Real.exp_sub]
  congr 1
  dsimp only [Prod.swap]
  ring

/-- The law-based step is exactly accepted and rejected flow of the proposal
pair. This identity retains rejection mass rather than renormalizing it. -/
theorem malaOneStep_eq_metropolisOutput (U : H → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U)) (μ : Measure H) :
    malaOneStep U h μ = metropolisOutput (malaProposalJoint U h μ)
      (fun p ↦ malaAcceptance U h p.1 p.2) := by
  let T : H × H → H × H := fun p ↦ (p.1, malaProposal U h p.1 p.2)
  let a : H × H → ℝ := fun p ↦ malaAcceptance U h p.1 p.2
  have hT : Measurable T := measurable_fst.prodMk (malaProposal_measurable U h L hLip)
  have ha : Measurable a := by
    have hU := hdiff.continuous
    have hg := hLip.continuous
    unfold a malaAcceptance malaLogRatio
    fun_prop
  have hacc := map_weighted_comp (μ.prod (stdGaussian H)) T hT
    (fun p ↦ ENNReal.ofReal (a p)) ha.ennreal_ofReal
  have hrej := map_weighted_comp (μ.prod (stdGaussian H)) T hT
    (fun p ↦ ENNReal.ofReal (1 - a p)) (measurable_const.sub ha).ennreal_ofReal
  change _ = (((μ.prod (stdGaussian H)).map T).withDensity
      (fun p ↦ ENNReal.ofReal (a p))).map Prod.snd +
    (((μ.prod (stdGaussian H)).map T).withDensity
      (fun p ↦ ENNReal.ofReal (1 - a p))).map Prod.fst
  rw [← hacc, ← hrej, Measure.map_map measurable_snd hT,
    Measure.map_map measurable_fst hT]
  rfl

/-- The actual proposal pair has a positive density against a symmetric base. -/
theorem malaProposalJoint_gibbs_density (U : H → ℝ) (h : ℝ) (L : ℝ≥0)
    (hh : 0 < h) (hdiff : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) :
    malaProposalJoint U h (gibbsMeasure U) =
      (((gibbsPartition U)⁻¹ * ENNReal.ofReal (gaussianProposalNormalizer (H := H) h)) •
        (volume.prod volume)).withDensity (fun p ↦ ENNReal.ofReal (malaJointWeight U h p)) := by
  have hg : Measurable (gradient U) := hLip.continuous.measurable
  have hU : Measurable U := hdiff.continuous.measurable
  have hc : Measurable (fun x ↦ x - h • gradient U x) :=
    measurable_id.sub (hg.const_smul h)
  have hw : Measurable (gibbsWeight U) := by unfold gibbsWeight; fun_prop
  have hq : Measurable (fun p : H × H ↦
      gaussianProposalDensity h (p.1 - h • gradient U p.1) p.2) := by
    unfold gaussianProposalDensity
    fun_prop
  have hp := gaussian_proposal_pair_density (gibbsMeasure U)
    (fun x ↦ x - h • gradient U x) hc h hh
  change malaProposalJoint U h (gibbsMeasure U) = _ at hp
  rw [hp, gibbsMeasure, Measure.prod_smul_left, prod_withDensity_left hw,
    withDensity_smul_measure]
  rw [← withDensity_mul _ (show Measurable (fun p : H × H ↦ gibbsWeight U p.1) from
    hw.comp measurable_fst) hq]
  have hd : (fun p : H × H ↦ gibbsWeight U p.1 *
      gaussianProposalDensity h (p.1 - h • gradient U p.1) p.2) =
      ENNReal.ofReal (gaussianProposalNormalizer (H := H) h) •
        (fun p ↦ ENNReal.ofReal (malaJointWeight U h p)) := by
    funext p
    change ENNReal.ofReal (Real.exp (-U p.1)) * ENNReal.ofReal
        (gaussianProposalNormalizer (H := H) h *
          Real.exp (-‖p.2 - (p.1 - h • gradient U p.1)‖ ^ 2 / (4 * h))) =
      ENNReal.ofReal (gaussianProposalNormalizer (H := H) h) *
        ENNReal.ofReal (malaJointWeight U h p)
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),
      ← ENNReal.ofReal_mul (gaussianProposalNormalizer_pos h hh).le]
    congr 1
    unfold malaJointWeight
    have he : p.2 - (p.1 - h • gradient U p.1) = p.2 - p.1 + h • gradient U p.1 := by abel
    rw [he]
    calc
      _ = gaussianProposalNormalizer (H := H) h * (Real.exp (-U p.1) *
          Real.exp (-‖p.2 - p.1 + h • gradient U p.1‖ ^ 2 / (4 * h))) := by ring
      _ = _ := by
        rw [← Real.exp_add]
        congr 2
        ring
  change (gibbsPartition U)⁻¹ • (volume.prod volume).withDensity
    (fun p ↦ gibbsWeight U p.1 * gaussianProposalDensity h
      (p.1 - h • gradient U p.1) p.2) = _
  rw [hd, withDensity_smul _ (by
    unfold malaJointWeight
    fun_prop), smul_smul, withDensity_smul_measure]

/-- The exact MALA step preserves the explicitly normalized Gibbs law.
Only the source potential assumptions are used; no invariant-law input occurs. -/
theorem malaOneStep_gibbs_invariant (U : H → ℝ) (h : ℝ) (L : ℝ≥0)
    (hh : 0 < h) (hdiff : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) :
    malaOneStep U h (gibbsMeasure U) = gibbsMeasure U := by
  let base : Measure (H × H) :=
    ((gibbsPartition U)⁻¹ * ENNReal.ofReal (gaussianProposalNormalizer (H := H) h)) •
      (volume.prod volume)
  have hb : base.map Prod.swap = base := by
    dsimp [base]
    rw [Measure.map_smul _ measurable_swap.aemeasurable, Measure.prod_swap]
  have hw : Measurable (malaJointWeight U h) := by
    have hU := hdiff.continuous
    have hg := hLip.continuous
    unfold malaJointWeight
    fun_prop
  have hw0 : ∀ p, 0 < malaJointWeight U h p := fun _ ↦ Real.exp_pos _
  have ha : (fun p ↦ malaAcceptance U h p.1 p.2) =
      metropolisAcceptance (malaJointWeight U h) := by
    funext p
    unfold malaAcceptance metropolisAcceptance
    rw [malaJointWeight_ratio]
  have hd := malaProposalJoint_gibbs_density U h L hh hdiff hLip
  change malaProposalJoint U h (gibbsMeasure U) =
    base.withDensity (fun p ↦ ENNReal.ofReal (malaJointWeight U h p)) at hd
  rw [malaOneStep_eq_metropolisOutput U h L hdiff hLip, ha, hd,
    metropolisOutput_density_eq_initial base hb _ hw hw0, ← hd]
  unfold malaProposalJoint
  rw [Measure.map_map measurable_fst
    (measurable_fst.prodMk (malaProposal_measurable U h L hLip))]
  change ((gibbsMeasure U).prod (stdGaussian H)).map Prod.fst = _
  simpa using (Measure.map_fst_prod (μ := gibbsMeasure U) (ν := stdGaussian H))

end ULA
