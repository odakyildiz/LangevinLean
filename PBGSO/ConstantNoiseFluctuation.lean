import PBGSO.RawConstantNoiseContraction
import PBGSO.ParameterBound

/-! # Source gradient fluctuations control positive raw coupling work
Dirac instances of the original joint condition and the primitive Lipschitz
optimizer response control positive work by actual observation fluctuations.
Uniform reference variance and stationary-target observation L¹ then justify
Fubini without any growth bound on the sampler drift.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators RealInnerProductSpace InnerProductSpace
namespace PBGSO.ConstantNoiseFluctuation
variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [Fintype I]
  (M : Model S Θ Z X I) (D : TwistedGeometry S Z)

/-- Actual deterministic gradients can replace the two Dirac gradients.
Only centered observation fluctuations can create positive work. -/
theorem positive_work_le (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hmono : TwistedJointMonotonicity M D ρ) (t : ℝ) (ht : 0 ≤ t)
    (LΨ : ℝ≥0)
    (hΨ : ∀ s g g', ‖M.optimizer t s g - M.optimizer t s g'‖ ≤ (LΨ : ℝ) * ‖g-g'‖)
    (s s' : S) (g g' : Θ) (z w : Z) :
    max (⟪s-s',D.optimizerWeight (M.optimizer t s g-M.optimizer t s' g')⟫_ℝ +
      samplerCouplingWork M D s s' (z,w)) 0 ≤
      ‖D.optimizerWeight‖ * ‖s-s'‖ * (LΨ : ℝ) *
        (‖M.observation (M.parameter s) (M.position z)-g‖ +
          ‖M.observation (M.parameter s') (M.position w)-g'‖) := by
  let f := M.observation (M.parameter s) (M.position z)
  let f' := M.observation (M.parameter s') (M.position w)
  have hd := particleCouplingWork_le M D ρ hmono 1 (by norm_num) t ht
    s s' (fun _ => z) (fun _ => w)
  have hd' : ⟪s-s',D.optimizerWeight (M.optimizer t s f-M.optimizer t s' f')⟫_ℝ +
      samplerCouplingWork M D s s' (z,w) ≤ 0 := by
    have hp : 0 ≤ D.optimizerSq (s-s') + D.samplerSq (z-w) :=
      add_nonneg (D.optimizerSq_nonneg _) (D.samplerSq_nonneg _)
    have hn : -ρ * (D.optimizerSq (s-s') + D.samplerSq (z-w)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hρ) hp
    have hd'' : ⟪s-s',D.optimizerWeight (M.optimizer t s f-M.optimizer t s' f')⟫_ℝ +
        samplerCouplingWork M D s s' (z,w) ≤
        -ρ * (D.optimizerSq (s-s') + D.samplerSq (z-w)) := by
      simpa [particleCouplingWork,particleCouplingEnergy,Model.particleField,
        Model.particleGradient,Fin.sum_univ_one,f,f'] using hd
    exact hd''.trans hn
  let e := (M.optimizer t s g-M.optimizer t s f) -
      (M.optimizer t s' g'-M.optimizer t s' f')
  have he : ‖e‖ ≤ (LΨ : ℝ) * (‖f-g‖+‖f'-g'‖) := by
    calc
      ‖e‖ ≤ ‖M.optimizer t s g-M.optimizer t s f‖ +
          ‖M.optimizer t s' g'-M.optimizer t s' f'‖ := norm_sub_le _ _
      _ ≤ (LΨ : ℝ) * ‖g-f‖ + (LΨ : ℝ) * ‖g'-f'‖ := add_le_add (hΨ _ _ _) (hΨ _ _ _)
      _ = _ := by rw [norm_sub_rev g f,norm_sub_rev g' f']; ring
  have hi : ⟪s-s',D.optimizerWeight e⟫_ℝ ≤
      ‖D.optimizerWeight‖ * ‖s-s'‖ * (LΨ : ℝ) * (‖f-g‖+‖f'-g'‖) := by
    calc
      _ ≤ ‖s-s'‖ * ‖D.optimizerWeight e‖ := real_inner_le_norm _ _
      _ ≤ ‖s-s'‖ * (‖D.optimizerWeight‖ * ‖e‖) :=
        mul_le_mul_of_nonneg_left (D.optimizerWeight.le_opNorm _) (norm_nonneg _)
      _ ≤ ‖s-s'‖ * (‖D.optimizerWeight‖ * ((LΨ : ℝ) * (‖f-g‖+‖f'-g'‖))) := by gcongr
      _ = _ := by ring
  apply max_le
  · have heq : M.optimizer t s g-M.optimizer t s' g' =
        (M.optimizer t s f-M.optimizer t s' f')+e := by dsimp [e]; abel
    rw [heq,map_add,inner_add_right]
    change _ ≤ ‖D.optimizerWeight‖ * ‖s-s'‖ * (LΨ : ℝ) * (‖f-g‖+‖f'-g'‖)
    linarith
  · positivity

section Raw
variable {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
 [DecidableEq I]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [MeasurableSpace Θ] [BorelSpace Θ] [SecondCountableTopology Θ]
  {W : FilteredBrownian.Driver (I := I) Q} {T : ℝ≥0}
  {L K : FilteredBrownian.RawLocalDiffusion (Z := Z) Q W T}
  (U : RawConstantNoiseContraction.Data Q M W T L)

/-- The actual raw observation, with the model's full state projections. -/
def observation (r : ℝ) (ω : Ω) : Θ :=
  M.observation (M.parameter (U.optimizer r)) (M.position (U.sampler r ω))

/-- The center is the actual expectation on the same source space. -/
def fluctuation (r : ℝ) (ω : Ω) : Θ :=
  observation M Q U r ω - ∫ ω', observation M Q U r ω' ∂Q

variable (hF : Measurable (fun p : S × Z => M.observation (M.parameter p.1) (M.position p.2)))

include hF in
theorem observation_strong : StronglyMeasurable (Function.uncurry (observation M Q U)) := by
  exact hF.stronglyMeasurable.comp_measurable
    ((U.optimizer_strong.measurable.comp measurable_fst).prodMk U.sampler_strong.measurable)

include hF in
theorem mean_eq (r : ℝ) : (∫ ω, observation M Q U r ω ∂Q) =
    M.meanGradient (Q.map (U.sampler r)) (U.optimizer r) := by
  exact (integral_map (U.sampler_strong.of_uncurry_left.measurable.aemeasurable)
    ((hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)).symm

include hF in
theorem fluctuation_strong : StronglyMeasurable (Function.uncurry (fluctuation M Q U)) := by
  exact (observation_strong M Q U hF).sub
    ((observation_strong M Q U hF).integral_prod_right'.comp_measurable measurable_fst)

include hF in
/-- Uniform mathematical variance (with its actual L² domain) gives genuine
spacetime L¹ observation fluctuations by Cauchy--Schwarz and Fubini. -/
theorem fluctuation_integrable_of_variance (V : ℝ)
    (h2 : ∀ r ∈ Icc 0 (T : ℝ), MemLp (observation M Q U r) 2 Q)
    (hVar : ∀ r ∈ Icc 0 (T : ℝ), ∫ ω, ‖fluctuation M Q U r ω‖ ^ 2 ∂Q ≤ V) :
    Integrable (Function.uncurry (fluctuation M Q U))
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := by
  have hf (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) : MemLp (fluctuation M Q U r) 2 Q :=
    (h2 r hr).sub (memLp_const _)
  have hb (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) :
      (∫ ω, ‖fluctuation M Q U r ω‖ ∂Q) ≤ Real.sqrt V := by
    have hc := integral_mul_le_sqrt_integrals Q (fun ω => ‖fluctuation M Q U r ω‖)
      (fun _ : Ω => (1 : ℝ)) (hf r hr).norm (memLp_const _)
    have he : (∫ ω, ‖fluctuation M Q U r ω‖ ∂Q) ≤
        Real.sqrt (∫ ω, ‖fluctuation M Q U r ω‖ ^ 2 ∂Q) := by simpa using hc
    exact he.trans (Real.sqrt_le_sqrt (hVar r hr))
  apply (integrable_prod_iff (fluctuation_strong M Q U hF).aestronglyMeasurable).mpr
  refine ⟨?_,?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact (hf r ⟨hr.1.le,hr.2⟩).integrable (by norm_num)
  · apply (integrable_const (Real.sqrt V)).mono'
      (fluctuation_strong M Q U hF).norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact hb r ⟨hr.1.le,hr.2⟩

include hF in
/-- A stationary target requires only L¹ observation integrability. -/
theorem fluctuation_integrable_of_stationarity (sStar : S) (νStar : Measure Z) [IsProbabilityMeasure νStar]
    (hopt : ∀ r ∈ Icc 0 (T : ℝ), U.optimizer r = sStar)
    (hlaw : ∀ r ∈ Icc 0 (T : ℝ), Q.map (U.sampler r) = νStar)
    (hobs : Integrable (fun z => M.observation (M.parameter sStar) (M.position z)) νStar) :
    Integrable (Function.uncurry (fluctuation M Q U))
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := by
  let f := fun z => M.observation (M.parameter sStar) (M.position z) - M.meanGradient νStar sStar
  have hi : Integrable f νStar := hobs.sub (integrable_const _)
  have hFmeas : Measurable f := (hF.comp (measurable_const.prodMk measurable_id)).sub_const _
  have he (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) :
      fluctuation M Q U r = f ∘ U.sampler r := by
    funext ω
    rw [fluctuation,mean_eq M Q U hF,hopt r hr,hlaw r hr]
    simp only [observation,f,Function.comp_apply,hopt r hr]
  have hm (r : ℝ) : AEMeasurable (U.sampler r) Q := U.sampler_strong.of_uncurry_left.measurable.aemeasurable
  have hs (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) : Integrable (fluctuation M Q U r) Q := by
    rw [he r hr]
    apply (integrable_map_measure hFmeas.aestronglyMeasurable (hm r)).mp
    rwa [hlaw r hr]
  have hv (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) :
      (∫ ω, ‖fluctuation M Q U r ω‖ ∂Q) = ∫ z, ‖f z‖ ∂νStar := by
    rw [he r hr]
    change (∫ ω, ‖f (U.sampler r ω)‖ ∂Q) = _
    rw [← integral_map (hm r) hFmeas.norm.aestronglyMeasurable,hlaw r hr]
  apply (integrable_prod_iff (fluctuation_strong M Q U hF).aestronglyMeasurable).mpr
  refine ⟨?_,?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hs r ⟨hr.1.le,hr.2⟩
  · apply (integrable_const (∫ z, ‖f z‖ ∂νStar)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact (hv r ⟨hr.1.le,hr.2⟩).symm


include hF in
/-- Primitive integral optimizer equations derive a compact optimizer-gap
bound. Dirac A3 and integrable centered observations then imply genuine
positive coupling-work integrability on the original, unstopped process. -/
theorem positive_work_integrable
    (V : RawConstantNoiseContraction.Data Q M W T K)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hmono : TwistedJointMonotonicity M D ρ)
    (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i)
    (LΨ : ℝ≥0)
    (hΨ : ∀ r ∈ Icc 0 (T : ℝ), ∀ s g g',
      ‖M.optimizer r s g-M.optimizer r s g'‖ ≤ (LΨ : ℝ)*‖g-g'‖)
    (hU : Integrable (Function.uncurry (fluctuation M Q U))
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hV : Integrable (Function.uncurry (fluctuation M Q V))
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) :
    Integrable (fun p : ℝ × Ω =>
      max (RawConstantNoiseContraction.rawMetricBilinear D
        (RawConstantNoiseContraction.pairState Q M U V p.1 p.2)
        (RawConstantNoiseContraction.pairDrift Q M U V p.1 p.2)) 0)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := by
  let μ := (volume.restrict (Ioc 0 (T : ℝ))).prod Q
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((RawConstantNoiseContraction.Data.optimizer_continuous Q M U).sub
      (RawConstantNoiseContraction.Data.optimizer_continuous Q M V))
  let R := max 0 C
  have hR : 0 ≤ R := le_max_left _ _
  have hb (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) : ‖U.optimizer r-V.optimizer r‖ ≤ R :=
    (hC r hr).trans (le_max_right _ _)
  have hp (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) (ω : Ω) :
      max (RawConstantNoiseContraction.rawMetricBilinear D
        (RawConstantNoiseContraction.pairState Q M U V r ω)
        (RawConstantNoiseContraction.pairDrift Q M U V r ω)) 0 ≤
      ‖D.optimizerWeight‖ * ‖U.optimizer r-V.optimizer r‖ * (LΨ : ℝ) *
        (‖fluctuation M Q U r ω‖+‖fluctuation M Q V r ω‖) := by
    have hd := positive_work_le M D ρ hρ hmono r hr.1 LΨ (hΨ r hr)
      (U.optimizer r) (V.optimizer r)
      (∫ ω', observation M Q U r ω' ∂Q) (∫ ω', observation M Q V r ω' ∂Q)
      (U.sampler r ω) (V.sampler r ω)
    rw [mean_eq M Q U hF,mean_eq M Q V hF] at hd
    change max (⟪U.optimizer r-V.optimizer r,D.optimizerWeight
        (U.optimizerDrift r-V.optimizerDrift r)⟫_ℝ +
      ⟪U.sampler r ω-V.sampler r ω,D.samplerWeight
        (M.drift (M.parameter (U.optimizer r)) (U.sampler r ω)-
         M.drift (M.parameter (V.optimizer r)) (V.sampler r ω))⟫_ℝ) 0 ≤ _
    rw [U.optimizerDrift_realizes r hr,V.optimizerDrift_realizes r hr]
    simp only [fluctuation]
    rw [mean_eq M Q U hF,mean_eq M Q V hF]
    simpa only [Model.optimizerField,observation,
      RawConstantNoiseContraction.sampler_work_eq_drift M D hσ] using hd
  have hm := (RawConstantNoiseContraction.rawMetricBilinear D).continuous₂.comp_stronglyMeasurable
    ((RawConstantNoiseContraction.pairState_strong Q M U V).prodMk
      (RawConstantNoiseContraction.pairDrift_strong Q M U V))
  apply ((hU.norm.add hV.norm).const_mul (‖D.optimizerWeight‖ * R * (LΨ : ℝ))).mono'
    (continuous_max.comp_aestronglyMeasurable
      (hm.aestronglyMeasurable.prodMk aestronglyMeasurable_const))
  have htime : ∀ᵐ p ∂μ, p.1 ∈ Icc 0 (T : ℝ) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact ae_of_all Q (fun _ => ⟨hr.1.le,hr.2⟩)
  filter_upwards [htime] with p hp'
  rw [Real.norm_of_nonneg (le_max_right _ _)]
  apply (hp p.1 hp' p.2).trans
  change ‖D.optimizerWeight‖ * ‖U.optimizer p.1-V.optimizer p.1‖ * (LΨ : ℝ) *
      (‖fluctuation M Q U p.1 p.2‖+‖fluctuation M Q V p.1 p.2‖) ≤
    ‖D.optimizerWeight‖ * R * (LΨ : ℝ) *
      (‖fluctuation M Q U p.1 p.2‖+‖fluctuation M Q V p.1 p.2‖)
  gcongr
  exact hb p.1 hp'

include hF in
/-- The original reference variance and actual stationary-target
observation L¹ discharge positive work for raw constant-diffusion dynamics.
No parameter-cross drift growth or drift moment is assumed. -/
theorem positive_work_of_reference_variance_stationary_target
    (V : RawConstantNoiseContraction.Data Q M W T K)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hmono : TwistedJointMonotonicity M D ρ)
    (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i)
    (LΨ : ℝ≥0)
    (hΨ : ∀ r ∈ Icc 0 (T : ℝ), ∀ s g g',
      ‖M.optimizer r s g-M.optimizer r s g'‖ ≤ (LΨ : ℝ)*‖g-g'‖)
    (V0 : ℝ)
    (hU2 : ∀ r ∈ Icc 0 (T : ℝ),
      MemLp (fun z => M.observation (M.parameter (U.optimizer r)) (M.position z))
        2 (Q.map (U.sampler r)))
    (hVar : ∀ r ∈ Icc 0 (T : ℝ),
      (∫ z, ‖M.observation (M.parameter (U.optimizer r)) (M.position z)-
        M.meanGradient (Q.map (U.sampler r)) (U.optimizer r)‖ ^ 2 ∂Q.map (U.sampler r)) ≤ V0)
    (sStar : S) (νStar : Measure Z) [IsProbabilityMeasure νStar]
    (hopt : ∀ r ∈ Icc 0 (T : ℝ), V.optimizer r = sStar)
    (hlaw : ∀ r ∈ Icc 0 (T : ℝ), Q.map (V.sampler r) = νStar)
    (hobs : Integrable (fun z => M.observation (M.parameter sStar) (M.position z)) νStar) :
    Integrable (fun p : ℝ × Ω =>
      max (RawConstantNoiseContraction.rawMetricBilinear D
        (RawConstantNoiseContraction.pairState Q M U V p.1 p.2)
        (RawConstantNoiseContraction.pairDrift Q M U V p.1 p.2)) 0)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := by
  apply positive_work_integrable M D Q U hF V ρ hρ hmono hσ LΨ hΨ
  · apply fluctuation_integrable_of_variance M Q U hF V0
    · intro r hr
      exact (hU2 r hr).comp_of_map U.sampler_strong.of_uncurry_left.measurable.aemeasurable
    · intro r hr
      have hvr := hVar r hr
      have hmeas : Measurable (fun z => ‖M.observation (M.parameter (U.optimizer r)) (M.position z)-
          M.meanGradient (Q.map (U.sampler r)) (U.optimizer r)‖ ^ 2) :=
        ((hF.comp (measurable_const.prodMk measurable_id)).sub_const _).norm.pow_const 2
      rw [integral_map U.sampler_strong.of_uncurry_left.measurable.aemeasurable
        hmeas.aestronglyMeasurable] at hvr
      simp only [fluctuation]
      rw [mean_eq M Q U hF]
      exact hvr
  · exact fluctuation_integrable_of_stationarity M Q V hF sStar νStar hopt hlaw hobs

include hF in
/-- Actual raw common-Brownian coupling contracts under the source
constant-diffusion branch and the source parameter theorem's own gradient
response/variance hypotheses. All work, energy and Fubini premises are derived. -/
theorem energy_decay_of_reference_variance_stationary_target
    (V : RawConstantNoiseContraction.Data Q M W T K)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hmono : TwistedJointMonotonicity M D ρ)
    (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i)
    (hb : ∀ θ, Measurable (M.drift θ))
    (LΨ : ℝ≥0)
    (hΨ : ∀ r ∈ Icc 0 (T : ℝ), ∀ s g g',
      ‖M.optimizer r s g-M.optimizer r s g'‖ ≤ (LΨ : ℝ)*‖g-g'‖)
    (V0 : ℝ)
    (hU2 : ∀ r ∈ Icc 0 (T : ℝ),
      MemLp (fun z => M.observation (M.parameter (U.optimizer r)) (M.position z))
        2 (Q.map (U.sampler r)))
    (hVar : ∀ r ∈ Icc 0 (T : ℝ),
      (∫ z, ‖M.observation (M.parameter (U.optimizer r)) (M.position z)-
        M.meanGradient (Q.map (U.sampler r)) (U.optimizer r)‖ ^ 2 ∂Q.map (U.sampler r)) ≤ V0)
    (sStar : S) (νStar : Measure Z) [IsProbabilityMeasure νStar]
    (hopt : ∀ r ∈ Icc 0 (T : ℝ), V.optimizer r = sStar)
    (hlaw : ∀ r ∈ Icc 0 (T : ℝ), Q.map (V.sampler r) = νStar)
    (hobs : Integrable (fun z => M.observation (M.parameter sStar) (M.position z)) νStar) :
    (∫ ω, RawConstantNoiseContraction.rawMetricBilinear D
      (RawConstantNoiseContraction.pairState Q M U V T ω)
      (RawConstantNoiseContraction.pairState Q M U V T ω) ∂Q) ≤
      Real.exp (-2 * ρ * (T : ℝ)) *
        ∫ ω, RawConstantNoiseContraction.rawMetricBilinear D
          (RawConstantNoiseContraction.pairState Q M U V 0 ω)
          (RawConstantNoiseContraction.pairState Q M U V 0 ω) ∂Q := by
  exact RawConstantNoiseContraction.energy_decay Q M D U V ρ hmono hσ hb
    (positive_work_of_reference_variance_stationary_target M D Q U hF V ρ hρ hmono hσ LΨ hΨ
      V0 hU2 hVar sStar νStar hopt hlaw hobs)

open RawConstantNoiseContraction

/-- The original joint RMS follows from actual positive-work Fubini. -/
theorem rms_decay_of_positive_work (U : Data Q M W T L) (V : Data Q M W T K)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hmono : TwistedJointMonotonicity M D ρ)
    (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i)
    (hb : ∀ θ, Measurable (M.drift θ))
    (hp : Integrable (fun p : ℝ × Ω =>
      max (RawConstantNoiseContraction.rawMetricBilinear D
        (RawConstantNoiseContraction.pairState Q M U V p.1 p.2)
        (RawConstantNoiseContraction.pairDrift Q M U V p.1 p.2)) 0)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) :
    Real.sqrt (‖U.optimizer T-V.optimizer T‖ ^ 2+
      ‖ProductLpSections.sectionLp Q U.sampler T-ProductLpSections.sectionLp Q V.sampler T‖ ^ 2) ≤
      Real.sqrt D.conditionNumber * Real.exp (-ρ * (T : ℝ)) *
        Real.sqrt (‖U.optimizer 0-V.optimizer 0‖ ^ 2+
          ‖ProductLpSections.sectionLp Q U.sampler 0-ProductLpSections.sectionLp Q V.sampler 0‖ ^ 2) := by
  have hd := RawConstantNoiseContraction.energy_decay Q M D U V ρ hmono hσ hb hp
  rw [pair_energy_eq_lifted Q M D U V T ⟨T.coe_nonneg,le_rfl⟩,
    pair_energy_eq_lifted Q M D U V 0 ⟨le_rfl,T.coe_nonneg⟩] at hd
  let At := (U.optimizer T-V.optimizer T,ProductLpSections.sectionLp Q U.sampler T-
    ProductLpSections.sectionLp Q V.sampler T)
  let A0 := (U.optimizer 0-V.optimizer 0,ProductLpSections.sectionLp Q U.sampler 0-
    ProductLpSections.sectionLp Q V.sampler 0)
  have hlo := liftedMetricBilinear_lower Q D At
  have hup := liftedMetricBilinear_upper Q D A0
  have hκ : 0 ≤ D.conditionNumber := (by norm_num : (0 : ℝ) ≤ 1).trans D.conditionNumber_ge_one
  have hn (x : S × Lp Z 2 Q) : 0 ≤ liftedEuclideanSq Q x := add_nonneg (sq_nonneg _) (sq_nonneg _)
  change Real.sqrt (liftedEuclideanSq Q At) ≤
    Real.sqrt D.conditionNumber * Real.exp (-ρ * (T : ℝ)) * Real.sqrt (liftedEuclideanSq Q A0)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (hn _),mul_pow,mul_pow,Real.sq_sqrt hκ,Real.sq_sqrt (hn _)]
  have he : Real.exp (-ρ * (T : ℝ)) ^ 2 = Real.exp (-2 * ρ * (T : ℝ)) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  rw [he]
  apply (mul_le_mul_iff_of_pos_left D.lower_pos).mp
  have hupper := mul_le_mul_of_nonneg_left hup (Real.exp_pos (-2 * ρ * (T : ℝ))).le
  have heq : D.lower * (D.conditionNumber * Real.exp (-2 * ρ * (T : ℝ)) * liftedEuclideanSq Q A0) =
      Real.exp (-2 * ρ * (T : ℝ)) * (D.upper * liftedEuclideanSq Q A0) := by
    dsimp [TwistedGeometry.conditionNumber]
    field_simp [ne_of_gt D.lower_pos]
  rw [heq]
  exact hlo.trans (hd.trans hupper)



/-- The actual output law is bounded through its genuine realized coupling. -/
theorem pair_law_distance_decay_of_positive_work
    (U : Data Q M W T L) (V : Data Q M W T K)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hmono : TwistedJointMonotonicity M D ρ)
    (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i)
    (hb : ∀ θ, Measurable (M.drift θ))
    (hp : Integrable (fun p : ℝ × Ω =>
      max (RawConstantNoiseContraction.rawMetricBilinear D
        (RawConstantNoiseContraction.pairState Q M U V p.1 p.2)
        (RawConstantNoiseContraction.pairDrift Q M U V p.1 p.2)) 0)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) :
    optimizerLawDistance (U.optimizer T) (V.optimizer T)
      (Q.map (U.sampler T)) (Q.map (V.sampler T)) ≤
      Real.sqrt D.conditionNumber * Real.exp (-ρ * (T : ℝ)) *
        Real.sqrt (‖U.optimizer 0-V.optimizer 0‖ ^ 2+
          ‖ProductLpSections.sectionLp Q U.sampler 0-ProductLpSections.sectionLp Q V.sampler 0‖ ^ 2) := by
  let A := ProductLpSections.sectionLp Q U.sampler T
  let B := ProductLpSections.sectionLp Q V.sampler T
  have hA : Q.map A = Q.map (U.sampler T) :=
    Measure.map_congr (ProductLpSections.sectionLp_ae Q U.sampler (U.sampler_square T ⟨T.coe_nonneg,le_rfl⟩))
  have hB : Q.map B = Q.map (V.sampler T) :=
    Measure.map_congr (ProductLpSections.sectionLp_ae Q V.sampler (V.sampler_square T ⟨T.coe_nonneg,le_rfl⟩))
  have hν : MemLp (fun z : Z => z) 2 (Q.map A) :=
    (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).mpr (lp_law_second_moment Q A)
  have hν' : MemLp (fun z : Z => z) 2 (Q.map B) :=
    (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).mpr (lp_law_second_moment Q B)
  let c : ULA.Coupling (Q.map A) (Q.map B) :=
    ⟨samplerPairLaw Q A B,(samplerPairLaw_coupling Q A B).1,(samplerPairLaw_coupling Q A B).2⟩
  have hc := coupling_difference_memLp (Q.map A) (Q.map B) hν hν' c
  have hbnd := wasserstein_le_finite_coupling (Q.map A) (Q.map B) c hc.eLpNorm_ne_top
  have hs := couplingCost_sq_eq_integral c.joint hc
  rw [IntegralModelContraction.samplerPairLaw_euclidean_integral] at hs
  apply le_trans _ (rms_decay_of_positive_work M D Q U V ρ hρ hmono hσ hb hp)
  apply Real.sqrt_le_sqrt
  change ‖U.optimizer T-V.optimizer T‖ ^ 2+ULA.wasserstein2Real (Q.map (U.sampler T)) (Q.map (V.sampler T)) ^ 2 ≤
    ‖U.optimizer T-V.optimizer T‖ ^ 2+‖A-B‖ ^ 2
  rw [← hA,← hB]
  apply add_le_add le_rfl
  rw [← hs]
  exact (sq_le_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).mpr hbnd

include hF in
/-- Actual reference and stationary-target raw laws contract from their
realized initial coupling. No abstract weak-generator coupling is supplied. -/
theorem law_decay_of_reference_variance_stationary_target
    (V : RawConstantNoiseContraction.Data Q M W T K)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hmono : TwistedJointMonotonicity M D ρ)
    (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i)
    (hb : ∀ θ, Measurable (M.drift θ))
    (LΨ : ℝ≥0)
    (hΨ : ∀ r ∈ Icc 0 (T : ℝ), ∀ s g g',
      ‖M.optimizer r s g-M.optimizer r s g'‖ ≤ (LΨ : ℝ)*‖g-g'‖)
    (V0 : ℝ)
    (hU2 : ∀ r ∈ Icc 0 (T : ℝ),
      MemLp (fun z => M.observation (M.parameter (U.optimizer r)) (M.position z))
        2 (Q.map (U.sampler r)))
    (hVar : ∀ r ∈ Icc 0 (T : ℝ),
      (∫ z, ‖M.observation (M.parameter (U.optimizer r)) (M.position z)-
        M.meanGradient (Q.map (U.sampler r)) (U.optimizer r)‖ ^ 2 ∂Q.map (U.sampler r)) ≤ V0)
    (sStar : S) (νStar : Measure Z) [IsProbabilityMeasure νStar]
    (hopt : ∀ r ∈ Icc 0 (T : ℝ), V.optimizer r = sStar)
    (hlaw : ∀ r ∈ Icc 0 (T : ℝ), Q.map (V.sampler r) = νStar)
    (hobs : Integrable (fun z => M.observation (M.parameter sStar) (M.position z)) νStar) :
    optimizerLawDistance (U.optimizer T) sStar (Q.map (U.sampler T)) νStar ≤
      Real.sqrt D.conditionNumber * Real.exp (-ρ * (T : ℝ)) *
        Real.sqrt (‖U.optimizer 0-sStar‖ ^ 2+
          ‖ProductLpSections.sectionLp Q U.sampler 0-ProductLpSections.sectionLp Q V.sampler 0‖ ^ 2) := by
  have hd := pair_law_distance_decay_of_positive_work M D Q U V ρ hρ hmono hσ hb
    (positive_work_of_reference_variance_stationary_target M D Q U hF V ρ hρ hmono hσ LΨ hΨ
      V0 hU2 hVar sStar νStar hopt hlaw hobs)
  rwa [hopt T ⟨T.coe_nonneg,le_rfl⟩,hlaw T ⟨T.coe_nonneg,le_rfl⟩,
    hopt 0 ⟨le_rfl,T.coe_nonneg⟩] at hd

end Raw
end PBGSO.ConstantNoiseFluctuation
