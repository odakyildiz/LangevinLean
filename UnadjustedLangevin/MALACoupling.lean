import UnadjustedLangevin.MALAError
import UnadjustedLangevin.Metropolis
import UnadjustedLangevin.PotentialAssumptions

set_option linter.style.header false

/-! # Synchronous coupling of ULA and stationary MALA

The joint step uses one Gaussian innovation for both proposals. Acceptance
moves both coordinates to their proposals; rejection leaves the MALA
coordinate fixed. All acceptance and rejection mass is retained explicitly.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ULA

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

/-- The standard MALA acceptance probability between two states. -/
def malaAcceptance (U : H → ℝ) (h : ℝ) (x y : H) : ℝ :=
  min 1 (Real.exp (malaLogRatio U h x y))

/-- Acceptance probability as a function of a state and its innovation. -/
def malaProposalAcceptance (U : H → ℝ) (h : ℝ) (p : H × H) : ℝ :=
  malaAcceptance U h p.1 (malaProposal U h p.1 p.2)

theorem malaAcceptance_nonneg (U : H → ℝ) (h : ℝ) (x y : H) :
    0 ≤ malaAcceptance U h x y := le_min (by norm_num) (Real.exp_nonneg _)

theorem malaAcceptance_le_one (U : H → ℝ) (h : ℝ) (x y : H) :
    malaAcceptance U h x y ≤ 1 := min_le_left _ _

theorem malaProposal_measurable (U : H → ℝ) (h : ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U)) :
    Measurable (fun p : H × H ↦ malaProposal U h p.1 p.2) := by
  have hg : Measurable (gradient U) := hLip.continuous.measurable
  exact (measurable_fst.sub ((hg.comp measurable_fst).const_smul h)).add
    (measurable_snd.const_smul (Real.sqrt (2 * h)))

theorem malaProposalAcceptance_measurable (U : H → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U)) :
    Measurable (malaProposalAcceptance U h) := by
  have hU : Continuous U := hdiff.continuous
  have hg : Continuous (gradient U) := hLip.continuous
  have hc : Continuous (malaProposalAcceptance U h) := by
    unfold malaProposalAcceptance malaAcceptance malaLogRatio malaProposal
    fun_prop
  exact hc.measurable

/-- One ordinary ULA transition on laws. -/
def ulaLawStep (U : H → ℝ) (h : ℝ) (μ : Measure H) : Measure H :=
  (μ.prod (stdGaussian H)).map (fun p ↦ malaProposal U h p.1 p.2)

/-- One MALA transition, including the rejection probability at its current state. -/
def malaOneStep (U : H → ℝ) (h : ℝ) (μ : Measure H) : Measure H :=
  ((μ.prod (stdGaussian H)).withDensity
      (fun p ↦ ENNReal.ofReal (malaProposalAcceptance U h p))).map
        (fun p ↦ malaProposal U h p.1 p.2) +
    ((μ.prod (stdGaussian H)).withDensity
      (fun p ↦ ENNReal.ofReal (1 - malaProposalAcceptance U h p))).map Prod.fst

/-- The synchronous coupling step: both proposals use exactly the same Gaussian vector. -/
def malaCoupledStep (U : H → ℝ) (h : ℝ) (ρ : Measure (H × H)) : Measure (H × H) :=
  let base := ρ.prod (stdGaussian H)
  let a := fun p : (H × H) × H ↦ malaProposalAcceptance U h (p.1.2, p.2)
  (base.withDensity (fun p ↦ ENNReal.ofReal (a p))).map
      (fun p ↦ (malaProposal U h p.1.1 p.2, malaProposal U h p.1.2 p.2)) +
    (base.withDensity (fun p ↦ ENNReal.ofReal (1 - a p))).map
      (fun p ↦ (malaProposal U h p.1.1 p.2, p.1.2))

private theorem weighted_accept_reject_add {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (a : A → ℝ) (ha : Measurable a)
    (ha0 : ∀ p, 0 ≤ a p) (ha1 : ∀ p, a p ≤ 1) :
    μ.withDensity (fun p ↦ ENNReal.ofReal (a p)) +
      μ.withDensity (fun p ↦ ENNReal.ofReal (1 - a p)) = μ := by
  rw [← withDensity_add_left ha.ennreal_ofReal]
  have hw : (fun p ↦ ENNReal.ofReal (a p) + ENNReal.ofReal (1 - a p)) = 1 := by
    funext p
    rw [← ENNReal.ofReal_add (ha0 p) (sub_nonneg.mpr (ha1 p))]
    simp
  change μ.withDensity (fun p ↦ ENNReal.ofReal (a p) + ENNReal.ofReal (1 - a p)) = μ
  rw [hw, withDensity_one]

/-- The first coordinate always performs the ordinary ULA transition. -/
theorem malaCoupledStep_fst (U : H → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (ρ : Measure (H × H)) [SFinite ρ] :
    (malaCoupledStep U h ρ).map Prod.fst = ulaLawStep U h (ρ.map Prod.fst) := by
  let F : (H × H) × H → H × H := fun p ↦ (p.1.1, p.2)
  let G : (H × H) × H → H × H := fun p ↦ (p.1.2, p.2)
  have hF : Measurable F := measurable_fst.fst.prodMk measurable_snd
  have hG : Measurable G := measurable_fst.snd.prodMk measurable_snd
  have hp := malaProposal_measurable U h L hLip
  have hpx : Measurable (fun p : (H × H) × H ↦ malaProposal U h p.1.1 p.2) := hp.comp hF
  have hpy : Measurable (fun p : (H × H) × H ↦ malaProposal U h p.1.2 p.2) := hp.comp hG
  have haccmap : Measurable (fun p : (H × H) × H ↦
      (malaProposal U h p.1.1 p.2, malaProposal U h p.1.2 p.2)) := hpx.prodMk hpy
  have hrejmap : Measurable (fun p : (H × H) × H ↦
      (malaProposal U h p.1.1 p.2, p.1.2)) := hpx.prodMk measurable_fst.snd
  have ha : Measurable (fun p ↦ malaProposalAcceptance U h (G p)) :=
    (malaProposalAcceptance_measurable U h L hdiff hLip).comp hG
  have hmap : (ρ.prod (stdGaussian H)).map F = (ρ.map Prod.fst).prod (stdGaussian H) := by
    change (ρ.prod (stdGaussian H)).map (Prod.map Prod.fst id) = _
    simpa only [Measure.map_id] using
      (Measure.map_prod_map ρ (stdGaussian H) measurable_fst measurable_id).symm
  unfold malaCoupledStep
  rw [Measure.map_add _ _ measurable_fst,
    Measure.map_map measurable_fst haccmap, Measure.map_map measurable_fst hrejmap]
  change ((ρ.prod (stdGaussian H)).withDensity
      (fun p ↦ ENNReal.ofReal (malaProposalAcceptance U h (G p)))).map
        (fun p ↦ malaProposal U h p.1.1 p.2) +
    ((ρ.prod (stdGaussian H)).withDensity
      (fun p ↦ ENNReal.ofReal (1 - malaProposalAcceptance U h (G p)))).map
        (fun p ↦ malaProposal U h p.1.1 p.2) = _
  rw [← Measure.map_add _ _ hpx, weighted_accept_reject_add _ _ ha
    (fun p ↦ malaAcceptance_nonneg U h _ _) (fun p ↦ malaAcceptance_le_one U h _ _)]
  rw [ulaLawStep, ← hmap, Measure.map_map hp hF]
  rfl

/-- The second coordinate performs exactly one MALA transition. -/
theorem malaCoupledStep_snd (U : H → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (ρ : Measure (H × H)) [SFinite ρ] :
    (malaCoupledStep U h ρ).map Prod.snd = malaOneStep U h (ρ.map Prod.snd) := by
  let F : (H × H) × H → H × H := fun p ↦ (p.1.1, p.2)
  let G : (H × H) × H → H × H := fun p ↦ (p.1.2, p.2)
  have hF : Measurable F := measurable_fst.fst.prodMk measurable_snd
  have hG : Measurable G := measurable_fst.snd.prodMk measurable_snd
  have hp := malaProposal_measurable U h L hLip
  have hpx : Measurable (fun p : (H × H) × H ↦ malaProposal U h p.1.1 p.2) := hp.comp hF
  have hpy : Measurable (fun p : (H × H) × H ↦ malaProposal U h p.1.2 p.2) := hp.comp hG
  have haccmap : Measurable (fun p : (H × H) × H ↦
      (malaProposal U h p.1.1 p.2, malaProposal U h p.1.2 p.2)) := hpx.prodMk hpy
  have hrejmap : Measurable (fun p : (H × H) × H ↦
      (malaProposal U h p.1.1 p.2, p.1.2)) := hpx.prodMk measurable_fst.snd
  have ha := malaProposalAcceptance_measurable U h L hdiff hLip
  have hmap : (ρ.prod (stdGaussian H)).map G = (ρ.map Prod.snd).prod (stdGaussian H) := by
    change (ρ.prod (stdGaussian H)).map (Prod.map Prod.snd id) = _
    simpa only [Measure.map_id] using
      (Measure.map_prod_map ρ (stdGaussian H) measurable_snd measurable_id).symm
  have hacc := map_weighted_comp (ρ.prod (stdGaussian H)) G hG
    (fun p ↦ ENNReal.ofReal (malaProposalAcceptance U h p)) ha.ennreal_ofReal
  have hrej := map_weighted_comp (ρ.prod (stdGaussian H)) G hG
    (fun p ↦ ENNReal.ofReal (1 - malaProposalAcceptance U h p))
    (measurable_const.sub ha).ennreal_ofReal
  unfold malaCoupledStep
  rw [Measure.map_add _ _ measurable_snd,
    Measure.map_map measurable_snd haccmap, Measure.map_map measurable_snd hrejmap]
  change ((ρ.prod (stdGaussian H)).withDensity
      ((fun p ↦ ENNReal.ofReal (malaProposalAcceptance U h p)) ∘ G)).map
        ((fun p ↦ malaProposal U h p.1 p.2) ∘ G) +
    ((ρ.prod (stdGaussian H)).withDensity
      ((fun p ↦ ENNReal.ofReal (1 - malaProposalAcceptance U h p)) ∘ G)).map
        (Prod.fst ∘ G) = _
  rw [← Measure.map_map hp hG, ← Measure.map_map measurable_fst hG,
    hacc, hrej, hmap]
  rfl

/-- The coupling step preserves total probability. -/
theorem malaCoupledStep_isProbability (U : H → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (ρ : Measure (H × H)) [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (malaCoupledStep U h ρ) := by
  have : IsProbabilityMeasure ((malaCoupledStep U h ρ).map Prod.fst) := by
    rw [malaCoupledStep_fst U h L hdiff hLip ρ]
    unfold ulaLawStep
    infer_instance
  exact Measure.isProbabilityMeasure_of_map measurable_fst.aemeasurable

/-- Start both algorithms at the same state and iterate the explicit coupled step. -/
def malaCoupledChain (U : H → ℝ) (h : ℝ) (μ : Measure H) : ℕ → Measure (H × H)
  | 0 => μ.map (fun x ↦ (x, x))
  | n + 1 => malaCoupledStep U h (malaCoupledChain U h μ n)

theorem malaCoupledChain_isProbability (U : H → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (μ : Measure H) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (malaCoupledChain U h μ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (μ.map (fun x ↦ (x, x))))
  | succ n ih =>
      have := ih
      exact malaCoupledStep_isProbability U h L hdiff hLip _

/-- The first marginal is precisely the iterated ULA law transition. -/
theorem malaCoupledChain_fst (U : H → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (μ : Measure H) [IsProbabilityMeasure μ] (n : ℕ) :
    (malaCoupledChain U h μ n).map Prod.fst = (ulaLawStep U h)^[n] μ := by
  induction n with
  | zero =>
      change (μ.map (fun x ↦ (x, x))).map Prod.fst = μ
      have hdiag : Measurable (fun x : H ↦ (x, x)) := measurable_id.prodMk measurable_id
      rw [Measure.map_map measurable_fst hdiag]
      exact Measure.map_id
  | succ n ih =>
      have := malaCoupledChain_isProbability U h L hdiff hLip μ n
      rw [malaCoupledChain, malaCoupledStep_fst U h L hdiff hLip, ih,
        Function.iterate_succ_apply']

/-- Exact one-step invariance implies that the second marginal is stationary
at every coupling step. The separate density/detailed-balance theorem
discharges the displayed one-step equality. -/
theorem malaCoupledChain_snd (U : H → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (π : Measure H) [IsProbabilityMeasure π]
    (hstationary : malaOneStep U h π = π) (n : ℕ) :
    (malaCoupledChain U h π n).map Prod.snd = π := by
  induction n with
  | zero =>
      change (π.map (fun x ↦ (x, x))).map Prod.snd = π
      have hdiag : Measurable (fun x : H ↦ (x, x)) := measurable_id.prodMk measurable_id
      rw [Measure.map_map measurable_snd hdiag]
      exact Measure.map_id
  | succ n ih =>
      have := malaCoupledChain_isProbability U h L hdiff hLip π n
      rw [malaCoupledChain, malaCoupledStep_snd U h L hdiff hLip, ih, hstationary]

/-- Shared Gaussian noise cancels, so a sufficiently small proposal is nonexpansive. -/
theorem malaProposal_nonexpansive (U : H → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hm : 0 < m) (hh : 0 ≤ h) (hsmall : h ≤ 2 / (m + (L : ℝ)))
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (hLip : LipschitzWith L (gradient U)) (x y ξ : H) :
    ‖malaProposal U h x ξ - malaProposal U h y ξ‖ ≤ ‖x - y‖ := by
  rcases subsingleton_or_nontrivial H with hs | hn
  · simp [Subsingleton.elim x y]
  · have hc := strong_smooth_gradient_step_contract U m h L hdiff hsc hLip
      (strongConvex_le_lipschitz hdiff hsc hLip) (by positivity) hh hsmall x y
    have heq : malaProposal U h x ξ - malaProposal U h y ξ =
        (x - h • gradient U x) - (y - h • gradient U y) := by
      simp only [malaProposal]; abel
    rw [heq]
    exact hc.trans (by nlinarith [mul_nonneg (mul_nonneg hm.le hh) (norm_nonneg (x-y))])

/-- The expected distance after choosing acceptance or rejection is bounded
by the old distance plus the rejected proposal displacement. -/
theorem malaCoupledStep_pointwise (U : H → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hm : 0 < m) (hh : 0 ≤ h) (hsmall : h ≤ 2 / (m + (L : ℝ)))
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (hLip : LipschitzWith L (gradient U)) (x y ξ : H) :
    malaProposalAcceptance U h (y,ξ) *
        ‖malaProposal U h x ξ - malaProposal U h y ξ‖ +
      (1 - malaProposalAcceptance U h (y,ξ)) * ‖malaProposal U h x ξ - y‖ ≤
      ‖x-y‖ + malaRejectionDisplacement U h y ξ := by
  have ha0 := malaAcceptance_nonneg U h y (malaProposal U h y ξ)
  have ha1 := malaAcceptance_le_one U h y (malaProposal U h y ξ)
  change 0 ≤ malaProposalAcceptance U h (y,ξ) at ha0
  change malaProposalAcceptance U h (y,ξ) ≤ 1 at ha1
  have ht : ‖malaProposal U h x ξ-y‖ ≤
      ‖malaProposal U h x ξ-malaProposal U h y ξ‖ + ‖malaProposal U h y ξ-y‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le
      (malaProposal U h x ξ-malaProposal U h y ξ) (malaProposal U h y ξ-y)
  have ht' := mul_le_mul_of_nonneg_left ht (sub_nonneg.mpr ha1)
  have hc := malaProposal_nonexpansive U m h L hm hh hsmall hdiff hsc hLip x y ξ
  unfold malaRejectionDisplacement malaProposalAcceptance malaAcceptance at *
  nlinarith

/-- Extended first-moment transport cost; finiteness is proved below. -/
def malaL1Cost (ρ : Measure (H × H)) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal ‖p.1-p.2‖ ∂ρ

private theorem lintegral_weighted_map {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (f : A → B) (hf : Measurable f) (a : A → ℝ)
    (ha : Measurable a) (ha0 : ∀ x, 0 ≤ a x) (b : B → ℝ) (hb : Measurable b) :
    (∫⁻ z, ENNReal.ofReal (b z) ∂(μ.withDensity (fun x ↦ ENNReal.ofReal (a x))).map f) =
      ∫⁻ x, ENNReal.ofReal (a x * b (f x)) ∂μ := by
  have hbf : Measurable (fun x ↦ b (f x)) := hb.comp hf
  rw [lintegral_map hb.ennreal_ofReal hf,
    lintegral_withDensity_eq_lintegral_mul μ ha.ennreal_ofReal hbf.ennreal_ofReal]
  apply lintegral_congr
  intro x
  exact (ENNReal.ofReal_mul (ha0 x)).symm

private theorem malaCoupledStep_cost_formula (U : H → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (ρ : Measure (H × H)) :
    malaL1Cost (malaCoupledStep U h ρ) =
      ∫⁻ p : (H × H) × H, ENNReal.ofReal
        (malaProposalAcceptance U h (p.1.2,p.2) *
          ‖malaProposal U h p.1.1 p.2 - malaProposal U h p.1.2 p.2‖ +
          (1-malaProposalAcceptance U h (p.1.2,p.2)) *
          ‖malaProposal U h p.1.1 p.2-p.1.2‖) ∂ρ.prod (stdGaussian H) := by
  have hp := malaProposal_measurable U h L hLip
  have hF : Measurable (fun p : (H × H) × H ↦ (p.1.1,p.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have hG : Measurable (fun p : (H × H) × H ↦ (p.1.2,p.2)) :=
    measurable_fst.snd.prodMk measurable_snd
  have ha : Measurable (fun p : (H × H) × H ↦ malaProposalAcceptance U h (p.1.2,p.2)) :=
    (malaProposalAcceptance_measurable U h L hdiff hLip).comp hG
  have hr : Measurable (fun p : (H × H) × H ↦ 1-malaProposalAcceptance U h (p.1.2,p.2)) :=
    measurable_const.sub ha
  have hd : Measurable (fun p : H × H ↦ ‖p.1-p.2‖) :=
    (measurable_fst.sub measurable_snd).norm
  have hpx : Measurable (fun p : (H × H) × H ↦ malaProposal U h p.1.1 p.2) := hp.comp hF
  have hpy : Measurable (fun p : (H × H) × H ↦ malaProposal U h p.1.2 p.2) := hp.comp hG
  unfold malaL1Cost malaCoupledStep
  rw [lintegral_add_measure,
    lintegral_weighted_map _ _ (hpx.prodMk hpy) _ ha
      (fun p ↦ malaAcceptance_nonneg U h _ _) _ hd,
    lintegral_weighted_map _ _ (hpx.prodMk measurable_fst.snd) _ hr
      (fun p ↦ sub_nonneg.mpr (malaAcceptance_le_one U h _ _)) _ hd]
  rw [← lintegral_add_left]
  · apply lintegral_congr
    intro p
    exact (ENNReal.ofReal_add (mul_nonneg (malaAcceptance_nonneg U h _ _) (norm_nonneg _))
      (mul_nonneg (sub_nonneg.mpr (malaAcceptance_le_one U h _ _)) (norm_nonneg _))).symm
  · exact (ha.mul ((hpx.sub hpy).norm)).ennreal_ofReal

/-- A single coupled step adds at most the proved Gibbs-averaged rejection error. -/
theorem malaCoupledStep_cost_le (U : H → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hm : 0 < m) (hh : 0 < h) (h1 : h ≤ 1)
    (hsmall : h ≤ 2 / (m + (L : ℝ)))
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (hLip : LipschitzWith L (gradient U))
    (ρ : Measure (H × H)) [IsProbabilityMeasure ρ]
    (hsnd : ρ.map Prod.snd = gibbsMeasure U) :
    malaL1Cost (malaCoupledStep U h ρ) ≤ malaL1Cost ρ +
      ENNReal.ofReal (malaRejectionConstant U L * h * Real.sqrt h) := by
  have hd : Measurable (fun p : H × H ↦ ENNReal.ofReal ‖p.1-p.2‖) :=
    (measurable_fst.sub measurable_snd).norm.ennreal_ofReal
  have hU := hdiff.continuous
  have hg := hLip.continuous
  have hr : Measurable (fun p : H × H ↦ malaRejectionDisplacement U h p.1 p.2) := by
    have hc : Continuous (fun p : H × H ↦ malaRejectionDisplacement U h p.1 p.2) := by
      unfold malaRejectionDisplacement malaLogRatio malaProposal
      fun_prop
    exact hc.measurable
  let G : (H × H) × H → H × H := fun p ↦ (p.1.2,p.2)
  have hG : Measurable G := measurable_fst.snd.prodMk measurable_snd
  have hmap : (ρ.prod (stdGaussian H)).map G = malaPairMeasure U := by
    change (ρ.prod (stdGaussian H)).map (Prod.map Prod.snd id) = _
    rw [← Measure.map_prod_map ρ (stdGaussian H) measurable_snd measurable_id,
      Measure.map_id, hsnd]
    rfl
  have hold : (∫⁻ p : (H × H) × H, ENNReal.ofReal ‖p.1.1-p.1.2‖
      ∂ρ.prod (stdGaussian H)) = malaL1Cost ρ := by
    rw [← lintegral_map hd measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
    rfl
  have hrej : (∫⁻ p : (H × H) × H, ENNReal.ofReal
      (malaRejectionDisplacement U h p.1.2 p.2) ∂ρ.prod (stdGaussian H)) ≤
      ENNReal.ofReal (malaRejectionConstant U L*h*Real.sqrt h) := by
    change (∫⁻ p, ENNReal.ofReal
      (malaRejectionDisplacement U h (G p).1 (G p).2) ∂ρ.prod (stdGaussian H)) ≤ _
    rw [← lintegral_map hr.ennreal_ofReal hG, hmap,
      ← ofReal_integral_eq_lintegral_ofReal
        (malaRejectionDisplacement_integrable U m h L hm hh h1 hdiff hsc hLip)
        (Filter.Eventually.of_forall fun p ↦ malaRejectionDisplacement_nonneg U h p.1 p.2)]
    exact ENNReal.ofReal_le_ofReal
      (malaRejectionDisplacement_integral_bound U m h L hm hh h1 hdiff hsc hLip)
  rw [malaCoupledStep_cost_formula U h L hdiff hLip]
  calc
    _ ≤ ∫⁻ p : (H × H) × H, ENNReal.ofReal
        (‖p.1.1-p.1.2‖ + malaRejectionDisplacement U h p.1.2 p.2)
        ∂ρ.prod (stdGaussian H) :=
      lintegral_mono fun p ↦ ENNReal.ofReal_le_ofReal
        (malaCoupledStep_pointwise U m h L hm hh.le hsmall hdiff hsc hLip _ _ _)
    _ = malaL1Cost ρ + (∫⁻ p : (H × H) × H,
        ENNReal.ofReal (malaRejectionDisplacement U h p.1.2 p.2) ∂ρ.prod (stdGaussian H)) := by
      simp_rw [ENNReal.ofReal_add (norm_nonneg _) (malaRejectionDisplacement_nonneg U h _ _)]
      have hd' : Measurable (fun p : (H × H) × H ↦ ENNReal.ofReal ‖p.1.1-p.1.2‖) :=
        hd.comp measurable_fst
      rw [lintegral_add_left hd', hold]
    _ ≤ _ := add_le_add le_rfl hrej

/-- The explicit synchronous coupling has first-moment cost at most the
number of steps times the local rejection error. -/
theorem malaCoupledChain_cost_le (U : H → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hm : 0 < m) (hh : 0 < h) (h1 : h ≤ 1)
    (hsmall : h ≤ 2 / (m + (L : ℝ)))
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (hLip : LipschitzWith L (gradient U))
    (hstationary : malaOneStep U h (gibbsMeasure U) = gibbsMeasure U) (n : ℕ) :
    malaL1Cost (malaCoupledChain U h (gibbsMeasure U) n) ≤
      (n : ℝ≥0∞) * ENNReal.ofReal (malaRejectionConstant U L*h*Real.sqrt h) := by
  haveI := isProbabilityMeasure_gibbsMeasure U m hm hdiff hsc
  induction n with
  | zero =>
      have hdiag : Measurable (fun x : H ↦ (x,x)) := measurable_id.prodMk measurable_id
      have hd : Measurable (fun p : H × H ↦ ENNReal.ofReal ‖p.1-p.2‖) :=
        (measurable_fst.sub measurable_snd).norm.ennreal_ofReal
      change (∫⁻ p : H × H, ENNReal.ofReal ‖p.1-p.2‖
        ∂(gibbsMeasure U).map (fun x ↦ (x,x))) ≤ _
      rw [lintegral_map hd hdiag]
      simp
  | succ n ih =>
      haveI := malaCoupledChain_isProbability U h L hdiff hLip (gibbsMeasure U) n
      have hs := malaCoupledChain_snd U h L hdiff hLip (gibbsMeasure U) hstationary n
      have hb := malaCoupledStep_cost_le U m h L hm hh h1 hsmall hdiff hsc hLip _ hs
      change malaL1Cost (malaCoupledStep U h (malaCoupledChain U h (gibbsMeasure U) n)) ≤ _
      have hc := add_le_add ih (le_refl (ENNReal.ofReal (malaRejectionConstant U L*h*Real.sqrt h)))
      exact hb.trans (by simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hc)

/-- The coupling distance is integrable, as a conclusion of the quantitative
extended-cost estimate rather than an additional moment hypothesis. -/
theorem malaCoupledChain_distance_integrable (U : H → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hm : 0 < m) (hh : 0 < h) (h1 : h ≤ 1)
    (hsmall : h ≤ 2 / (m + (L : ℝ)))
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (hLip : LipschitzWith L (gradient U))
    (hstationary : malaOneStep U h (gibbsMeasure U) = gibbsMeasure U) (n : ℕ) :
    Integrable (fun p : H × H ↦ ‖p.1-p.2‖)
      (malaCoupledChain U h (gibbsMeasure U) n) := by
  have hd : Measurable (fun p : H × H ↦ ‖p.1-p.2‖) :=
    (measurable_fst.sub measurable_snd).norm
  refine ⟨hd.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun p : H × H ↦ norm_nonneg (p.1-p.2))).2 ?_⟩
  exact lt_of_le_of_lt (malaCoupledChain_cost_le U m h L hm hh h1 hsmall hdiff hsc hLip
    hstationary n) (by finiteness)

/-- Ordinary expected distance between ULA and stationary MALA, with an
explicit finite constant depending only on the original potential. -/
theorem malaCoupledChain_distance_integral_le (U : H → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hm : 0 < m) (hh : 0 < h) (h1 : h ≤ 1)
    (hsmall : h ≤ 2 / (m + (L : ℝ)))
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (hLip : LipschitzWith L (gradient U))
    (hstationary : malaOneStep U h (gibbsMeasure U) = gibbsMeasure U) (n : ℕ) :
    (∫ p : H × H, ‖p.1-p.2‖ ∂malaCoupledChain U h (gibbsMeasure U) n) ≤
      (n : ℝ) * malaRejectionConstant U L * h * Real.sqrt h := by
  have hb := malaCoupledChain_cost_le U m h L hm hh h1 hsmall hdiff hsc hLip hstationary n
  have hC := malaRejectionConstant_nonneg U L
  have hrewrite : (n : ℝ≥0∞) * ENNReal.ofReal (malaRejectionConstant U L*h*Real.sqrt h) =
      ENNReal.ofReal ((n : ℝ)*malaRejectionConstant U L*h*Real.sqrt h) := by
    rw [show (n : ℝ)*malaRejectionConstant U L*h*Real.sqrt h =
      (n : ℝ)*(malaRejectionConstant U L*h*Real.sqrt h) by ring,
      ENNReal.ofReal_mul (Nat.cast_nonneg n)]
    simp
  rw [hrewrite] at hb
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
  rw [ofReal_integral_eq_lintegral_ofReal
    (malaCoupledChain_distance_integrable U m h L hm hh h1 hsmall hdiff hsc hLip hstationary n)
    (Filter.Eventually.of_forall fun p : H × H ↦ norm_nonneg (p.1-p.2))]
  exact hb

end ULA
