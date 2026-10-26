import PBGSO.SeparatedGeometry

/-!
# Separate primitive optimiser/sampler assumptions imply joint monotonicity

The metric estimates below follow from the actual symmetric positive quadratic
weights. The law comparisons use genuine coupling marginals and Bochner
expectations; no optimiser/sampler work inequality is assumed as a substitute
for the primitive separated hypotheses.
-/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal RealInnerProductSpace InnerProductSpace BigOperators
namespace PBGSO




section LawCriteria
variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype I]

/-- A globally Lipschitz observation is Bochner integrable under every P₂
law. The constant offset is retained. -/
theorem observation_integrable_of_lipschitz (ν : Measure Z) [IsProbabilityMeasure ν]
    (f : Z → Θ) {L : ℝ≥0} (hf : LipschitzWith L f) (hν : HasFiniteSecondMoment ν) :
    Integrable f ν := by
  have hid : MemLp (fun z : Z ↦ z) 2 ν :=
    (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).mpr hν
  have hn := (hid.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).norm
  apply ((integrable_const ‖f 0‖).add (hn.const_mul (L : ℝ))).mono'
    hf.continuous.aestronglyMeasurable
  apply ae_of_all
  intro z
  have hl := hf.norm_sub_le z 0
  simp only [sub_zero] at hl
  have hnorm : ‖f z‖ ≤ ‖f z - f 0‖ + ‖f 0‖ := by
    simpa only [sub_add_cancel] using norm_add_le (f z - f 0) (f 0)
  change ‖f z‖ ≤ ‖f 0‖ + (L : ℝ) * ‖z‖
  linarith

/-- A true coupling of probability marginals is itself a probability law. -/
theorem coupling_isProbability (Λ : Measure (Z × Z)) (ν ν' : Measure Z)
    (hc : IsCoupling Λ ν ν') [IsProbabilityMeasure ν] : IsProbabilityMeasure Λ := by
  have hp : IsProbabilityMeasure (Λ.map Prod.fst) := by rw [hc.1]; infer_instance
  exact (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mp hp

/-- The observation expectation discrepancy is derived from the actual
coupling identity, sampler Lipschitz observation, and weighted quadratic cost. -/
theorem meanGradient_coupling_bound (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    (LF : ℝ≥0)
    (hF : ∀ s, LipschitzWith LF (fun z ↦ M.observation (M.parameter s) (M.position z)))
    (s : S) (ν ν' : Measure Z) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hν : HasFiniteSecondMoment ν) (hν' : HasFiniteSecondMoment ν')
    (Λ : Measure (Z × Z)) (hc : IsCoupling Λ ν ν')
    (hcost : Integrable (fun zz : Z × Z ↦ D.samplerSq (zz.1 - zz.2)) Λ) :
    ‖M.meanGradient ν s - M.meanGradient ν' s‖ ≤
      (LF : ℝ) / Real.sqrt D.lower *
        Real.sqrt (∫ zz, D.samplerSq (zz.1 - zz.2) ∂Λ) := by
  letI := coupling_isProbability Λ ν ν' hc
  let f := fun z ↦ M.observation (M.parameter s) (M.position z)
  have hi := observation_integrable_of_lipschitz ν f (hF s) hν
  have hi' := observation_integrable_of_lipschitz ν' f (hF s) hν'
  have hfst : Integrable (fun zz : Z × Z ↦ f zz.1) Λ := by
    rw [← hc.1] at hi
    exact hi.comp_measurable measurable_fst
  have hsnd : Integrable (fun zz : Z × Z ↦ f zz.2) Λ := by
    rw [← hc.2] at hi'
    exact hi'.comp_measurable measurable_snd
  have hm1 : M.meanGradient ν s = ∫ zz : Z × Z, f zz.1 ∂Λ := by
    rw [Model.meanGradient, ← hc.1]
    exact integral_map measurable_fst.aemeasurable (hF s).continuous.aestronglyMeasurable
  have hm2 : M.meanGradient ν' s = ∫ zz : Z × Z, f zz.2 ∂Λ := by
    rw [Model.meanGradient, ← hc.2]
    exact integral_map measurable_snd.aemeasurable (hF s).continuous.aestronglyMeasurable
  let q := fun zz : Z × Z ↦ D.samplerSq (zz.1 - zz.2)
  have hq : AEStronglyMeasurable q Λ := by
    apply Continuous.aestronglyMeasurable
    dsimp [q, TwistedGeometry.samplerSq]
    fun_prop
  have hqpos : ∀ zz, 0 ≤ q zz := fun zz ↦ D.samplerSq_nonneg _
  have hsq := sqrt_energy_memLp Λ q hq hcost hqpos
  have hsqrtInt := hsq.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hbound (zz : Z × Z) : ‖f zz.1 - f zz.2‖ ≤
      ((LF : ℝ) / Real.sqrt D.lower) * Real.sqrt (q zz) := by
    calc
      _ ≤ (LF : ℝ) * ‖zz.1 - zz.2‖ := (hF s).norm_sub_le _ _
      _ ≤ (LF : ℝ) * (Real.sqrt (q zz) / Real.sqrt D.lower) :=
        mul_le_mul_of_nonneg_left (D.sampler_norm_le _) LF.coe_nonneg
      _ = _ := by ring
  rw [hm1, hm2, ← integral_sub hfst hsnd]
  calc
    _ ≤ ∫ zz, ‖f zz.1 - f zz.2‖ ∂Λ := norm_integral_le_integral_norm _
    _ ≤ ∫ zz, ((LF : ℝ) / Real.sqrt D.lower) * Real.sqrt (q zz) ∂Λ :=
      integral_mono (hfst.sub hsnd).norm (hsqrtInt.const_mul _) hbound
    _ = ((LF : ℝ) / Real.sqrt D.lower) * (∫ zz, Real.sqrt (q zz) ∂Λ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_sqrt_energy_le Λ q hq hcost hqpos) (by positivity)

/-- The exact primitive separated conditions from the appendix, stated on
actual optimiser fields, observation maps, frozen sampler drifts and diffusion
columns. No combined work estimate or final monotonicity inequality is a field. -/
structure SeparatedAssumptions (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    (rOptimizer rSampler : ℝ) (LΨ LF Lb Lσ : ℝ≥0) : Prop where
  optimizer_contract : ∀ t, 0 ≤ t → ∀ s s' ν, IsProbabilityMeasure ν →
    HasFiniteSecondMoment ν →
    ⟪s - s', D.optimizerWeight (M.optimizerField t s ν - M.optimizerField t s' ν)⟫_ℝ ≤
      -rOptimizer * D.optimizerSq (s - s')
  optimizer_response : ∀ t, 0 ≤ t → ∀ s ν ν', IsProbabilityMeasure ν → IsProbabilityMeasure ν' →
    HasFiniteSecondMoment ν → HasFiniteSecondMoment ν' →
    ‖M.optimizerField t s ν - M.optimizerField t s ν'‖ ≤
      (LΨ : ℝ) * ‖M.meanGradient ν s - M.meanGradient ν' s‖
  observation_lipschitz : ∀ s,
    LipschitzWith LF (fun z ↦ M.observation (M.parameter s) (M.position z))
  sampler_frozen : ∀ s z z',
    ⟪z - z', D.samplerWeight (M.drift (M.parameter s) z - M.drift (M.parameter s) z')⟫_ℝ ≤
      -rSampler * D.samplerSq (z - z')
  sampler_parameter : ∀ s s' z,
    ‖M.drift (M.parameter s) z - M.drift (M.parameter s') z‖ ≤ (Lb : ℝ) * ‖s - s'‖
  diffusion_lipschitz : ∀ s s' z z',
    (∑ i, ‖M.diffusion (M.parameter s) z i - M.diffusion (M.parameter s') z' i‖ ^ 2) ≤
      (Lσ : ℝ) ^ 2 * (‖s - s'‖ ^ 2 + ‖z - z'‖ ^ 2)

/-- The optimiser part of the actual law-coupling work is controlled by the
primitive frozen-law contraction and observation response. -/
theorem separated_optimizer_work_bound (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    {rO rS : ℝ} {LΨ LF Lb Lσ : ℝ≥0}
    (H : SeparatedAssumptions M D rO rS LΨ LF Lb Lσ)
    (t : ℝ) (ht : 0 ≤ t) (s s' : S) (ν ν' : Measure Z)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hν : HasFiniteSecondMoment ν) (hν' : HasFiniteSecondMoment ν')
    (Λ : Measure (Z × Z)) (hc : IsCoupling Λ ν ν')
    (hcost : Integrable (fun zz : Z × Z ↦ D.samplerSq (zz.1 - zz.2)) Λ) :
    ⟪s - s', D.optimizerWeight
      (M.optimizerField t s ν - M.optimizerField t s' ν')⟫_ℝ ≤
      -rO * D.optimizerSq (s - s') +
      Real.sqrt D.conditionNumber * (LΨ : ℝ) * (LF : ℝ) *
        Real.sqrt (D.optimizerSq (s - s')) *
        Real.sqrt (∫ zz, D.samplerSq (zz.1 - zz.2) ∂Λ) := by
  have hg := meanGradient_coupling_bound M D LF H.observation_lipschitz
    s' ν ν' hν hν' Λ hc hcost
  have hr := H.optimizer_response t ht s' ν ν' inferInstance inferInstance hν hν'
  have he := hr.trans (mul_le_mul_of_nonneg_left hg LΨ.coe_nonneg)
  have hp := D.optimizer_pairing_bound (s - s')
    (M.optimizerField t s' ν - M.optimizerField t s' ν')
  have hp' := hp.trans (mul_le_mul_of_nonneg_left he (by positivity))
  have hs := H.optimizer_contract t ht s s' ν inferInstance hν
  have hid : M.optimizerField t s ν - M.optimizerField t s' ν' =
      (M.optimizerField t s ν - M.optimizerField t s' ν) +
      (M.optimizerField t s' ν - M.optimizerField t s' ν') := by module
  rw [hid, map_add, inner_add_right]
  calc
    _ ≤ -rO * D.optimizerSq (s - s') +
      (Real.sqrt (D.optimizerSq (s - s')) * Real.sqrt D.upper *
       ((LΨ : ℝ) * ((LF : ℝ) / Real.sqrt D.lower *
         Real.sqrt (∫ zz, D.samplerSq (zz.1 - zz.2) ∂Λ)))) := by
      linarith [le_abs_self ⟪s - s', D.optimizerWeight
        (M.optimizerField t s' ν - M.optimizerField t s' ν')⟫_ℝ]
    _ = _ := by rw [← D.sqrt_conditionNumber]; ring

/-- Frozen sampler dissipativity, parameter Lipschitzness, and the actual
finite sum of diffusion columns imply the pointwise sampler work estimate. -/
theorem separated_sampler_work_bound (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    {rO rS : ℝ} {LΨ LF Lb Lσ : ℝ≥0}
    (H : SeparatedAssumptions M D rO rS LΨ LF Lb Lσ)
    (s s' : S) (zz : Z × Z) :
    samplerCouplingWork M D s s' zz ≤
      -rS * D.samplerSq (zz.1 - zz.2) +
      Real.sqrt D.conditionNumber * (Lb : ℝ) * Real.sqrt (D.optimizerSq (s - s')) *
        Real.sqrt (D.samplerSq (zz.1 - zz.2)) +
      (D.conditionNumber * (Lσ : ℝ) ^ 2 / 2) *
        (D.optimizerSq (s - s') + D.samplerSq (zz.1 - zz.2)) := by
  have hu : 0 ≤ D.upper := D.lower_pos.le.trans D.lower_le_upper
  have hp := D.sampler_pairing_bound (zz.1 - zz.2)
    (M.drift (M.parameter s) zz.2 - M.drift (M.parameter s') zz.2)
  have hb := H.sampler_parameter s s' zz.2
  have hb' := hb.trans (mul_le_mul_of_nonneg_left (D.optimizer_norm_le _) Lb.coe_nonneg)
  have hcross := hp.trans (mul_le_mul_of_nonneg_left hb' (by positivity))
  have hcross' : ⟪zz.1 - zz.2, D.samplerWeight
      (M.drift (M.parameter s) zz.2 - M.drift (M.parameter s') zz.2)⟫_ℝ ≤
      Real.sqrt D.conditionNumber * (Lb : ℝ) * Real.sqrt (D.optimizerSq (s - s')) *
        Real.sqrt (D.samplerSq (zz.1 - zz.2)) := by
    calc
      _ ≤ |⟪zz.1 - zz.2, D.samplerWeight
        (M.drift (M.parameter s) zz.2 - M.drift (M.parameter s') zz.2)⟫_ℝ| := le_abs_self _
      _ ≤ _ := hcross
      _ = _ := by rw [← D.sqrt_conditionNumber]; ring
  have hnorm : ‖s - s'‖ ^ 2 + ‖zz.1 - zz.2‖ ^ 2 ≤
      (D.optimizerSq (s - s') + D.samplerSq (zz.1 - zz.2)) / D.lower := by
    apply (le_div_iff₀ D.lower_pos).mpr
    have hs := D.optimizer_lower (s - s')
    have hz := D.sampler_lower (zz.1 - zz.2)
    dsimp [TwistedGeometry.optimizerSq, TwistedGeometry.samplerSq]
    linarith
  have hdiff : (∑ i, D.samplerSq
      (M.diffusion (M.parameter s) zz.1 i - M.diffusion (M.parameter s') zz.2 i)) ≤
      D.conditionNumber * (Lσ : ℝ) ^ 2 *
        (D.optimizerSq (s - s') + D.samplerSq (zz.1 - zz.2)) := by
    calc
      _ ≤ ∑ i, D.upper * ‖M.diffusion (M.parameter s) zz.1 i -
        M.diffusion (M.parameter s') zz.2 i‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          exact D.sampler_upper _
      _ = D.upper * ∑ i, ‖M.diffusion (M.parameter s) zz.1 i -
        M.diffusion (M.parameter s') zz.2 i‖ ^ 2 := (Finset.mul_sum ..).symm
      _ ≤ D.upper * ((Lσ : ℝ) ^ 2 * (‖s - s'‖ ^ 2 + ‖zz.1 - zz.2‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (H.diffusion_lipschitz s s' zz.1 zz.2) hu
      _ ≤ D.upper * ((Lσ : ℝ) ^ 2 *
        ((D.optimizerSq (s - s') + D.samplerSq (zz.1 - zz.2)) / D.lower)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnorm (sq_nonneg _)) hu
      _ = _ := by dsimp [TwistedGeometry.conditionNumber]; ring
  have hf := H.sampler_frozen s zz.1 zz.2
  have hid : M.drift (M.parameter s) zz.1 - M.drift (M.parameter s') zz.2 =
      (M.drift (M.parameter s) zz.1 - M.drift (M.parameter s) zz.2) +
      (M.drift (M.parameter s) zz.2 - M.drift (M.parameter s') zz.2) := by module
  unfold samplerCouplingWork
  rw [hid, map_add, inner_add_right]
  linarith

/-- Integrating the sampler estimate uses Cauchy--Schwarz under the actual
coupling probability measure, not an assumed Wasserstein comparison. -/
theorem separated_sampler_integral_bound (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    {rO rS : ℝ} {LΨ LF Lb Lσ : ℝ≥0}
    (H : SeparatedAssumptions M D rO rS LΨ LF Lb Lσ)
    (s s' : S) (ν ν' : Measure Z) [IsProbabilityMeasure ν]
    (Λ : Measure (Z × Z)) (hc : IsCoupling Λ ν ν')
    (hwork : Integrable (samplerCouplingWork M D s s') Λ)
    (hcost : Integrable (fun zz : Z × Z ↦ D.samplerSq (zz.1 - zz.2)) Λ) :
    (∫ zz, samplerCouplingWork M D s s' zz ∂Λ) ≤
      -rS * (∫ zz, D.samplerSq (zz.1 - zz.2) ∂Λ) +
      Real.sqrt D.conditionNumber * (Lb : ℝ) * Real.sqrt (D.optimizerSq (s - s')) *
        Real.sqrt (∫ zz, D.samplerSq (zz.1 - zz.2) ∂Λ) +
      (D.conditionNumber * (Lσ : ℝ) ^ 2 / 2) *
        (D.optimizerSq (s - s') + ∫ zz, D.samplerSq (zz.1 - zz.2) ∂Λ) := by
  letI := coupling_isProbability Λ ν ν' hc
  let q := fun zz : Z × Z ↦ D.samplerSq (zz.1 - zz.2)
  let A := D.optimizerSq (s - s')
  let C := Real.sqrt D.conditionNumber * (Lb : ℝ) * Real.sqrt A
  let V := D.conditionNumber * (Lσ : ℝ) ^ 2 / 2
  have hq : AEStronglyMeasurable q Λ := by
    apply Continuous.aestronglyMeasurable
    dsimp [q, TwistedGeometry.samplerSq]
    fun_prop
  have hpos : ∀ zz, 0 ≤ q zz := fun zz ↦ D.samplerSq_nonneg _
  have hsqrtInt := (sqrt_energy_memLp Λ q hq hcost hpos).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hg1 := hcost.const_mul (-rS)
  have hg2 := hsqrtInt.const_mul C
  have hg3 := ((integrable_const A).add hcost).const_mul V
  have hw : (∫ zz, samplerCouplingWork M D s s' zz ∂Λ) ≤
      ∫ zz, -rS * q zz + C * Real.sqrt (q zz) + V * (A + q zz) ∂Λ :=
    integral_mono hwork ((hg1.add hg2).add hg3)
      (separated_sampler_work_bound M D H s s')
  have heq : (∫ zz, A + q zz ∂Λ) = A + ∫ zz, q zz ∂Λ := by
    calc
      _ = (∫ _ : Z × Z, A ∂Λ) + ∫ zz, q zz ∂Λ :=
        integral_add (integrable_const A) hcost
      _ = _ := by simp
  have he : (∫ zz, -rS * q zz + C * Real.sqrt (q zz) + V * (A + q zz) ∂Λ) =
      -rS * (∫ zz, q zz ∂Λ) + C * (∫ zz, Real.sqrt (q zz) ∂Λ) +
        V * (A + ∫ zz, q zz ∂Λ) := by
    calc
      _ = (∫ zz, -rS * q zz + C * Real.sqrt (q zz) ∂Λ) +
          ∫ zz, V * (A + q zz) ∂Λ := integral_add (hg1.add hg2) hg3
      _ = (∫ zz, -rS * q zz ∂Λ) + (∫ zz, C * Real.sqrt (q zz) ∂Λ) +
          ∫ zz, V * (A + q zz) ∂Λ := by
            congr 1
            exact integral_add hg1 hg2
      _ = _ := by rw [integral_const_mul, integral_const_mul, integral_const_mul, heq]
  rw [he] at hw
  have hcs := mul_le_mul_of_nonneg_left (integral_sqrt_energy_le Λ q hq hcost hpos)
    (show 0 ≤ C by dsimp [C]; positivity)
  dsimp [C, V, A, q] at hw hcs
  linarith

/-- A conservative explicit small-gain criterion at the full law level.
All coupling work bounds are derived from the primitive separated conditions.
The two displayed diagonal inequalities give the contraction rate directly. -/
theorem separated_joint_monotonicity (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    {rO rS ρ : ℝ} {LΨ LF Lb Lσ : ℝ≥0}
    (H : SeparatedAssumptions M D rO rS LΨ LF Lb Lσ)
    (hO : ρ ≤ rO - D.conditionNumber * (Lσ : ℝ) ^ 2 / 2 -
      Real.sqrt D.conditionNumber * ((LΨ : ℝ) * (LF : ℝ) + (Lb : ℝ)) / 2)
    (hS : ρ ≤ rS - D.conditionNumber * (Lσ : ℝ) ^ 2 / 2 -
      Real.sqrt D.conditionNumber * ((LΨ : ℝ) * (LF : ℝ) + (Lb : ℝ)) / 2) :
    TwistedJointMonotonicity M D ρ := by
  intro t ht s s' ν ν' Λ hc hp hp' hν hν' _ _ hwork hcost
  letI := hp
  letI := hp'
  have ho := separated_optimizer_work_bound M D H t ht s s' ν ν' hν hν' Λ hc hcost
  have hs := separated_sampler_integral_bound M D H s s' ν ν' Λ hc hwork hcost
  have hqO := D.optimizerSq_nonneg (s - s')
  have hqS : 0 ≤ ∫ zz, D.samplerSq (zz.1 - zz.2) ∂Λ :=
    integral_nonneg (fun zz ↦ D.samplerSq_nonneg _)
  have hg := small_gain_diagonal (Real.sqrt (D.optimizerSq (s - s')))
    (Real.sqrt (∫ zz, D.samplerSq (zz.1 - zz.2) ∂Λ)) rO rS
    (Real.sqrt D.conditionNumber * ((LΨ : ℝ) * (LF : ℝ) + (Lb : ℝ)))
    (D.conditionNumber * (Lσ : ℝ) ^ 2 / 2) ρ (by positivity) hO hS
  rw [Real.sq_sqrt hqO, Real.sq_sqrt hqS] at hg
  nlinarith

/-- The minimum of the explicit diagonal margins is always an available
joint rate. Positivity of this displayed number is precisely the additional
strict small-gain condition needed to call it a contraction rate. -/
def separatedDiagonalRate (D : TwistedGeometry S Z) (rO rS : ℝ)
    (LΨ LF Lb Lσ : ℝ≥0) : ℝ :=
  min rO rS - D.conditionNumber * (Lσ : ℝ) ^ 2 / 2 -
    Real.sqrt D.conditionNumber * ((LΨ : ℝ) * (LF : ℝ) + (Lb : ℝ)) / 2

theorem separated_joint_monotonicity_diagonal (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    {rO rS : ℝ} {LΨ LF Lb Lσ : ℝ≥0}
    (H : SeparatedAssumptions M D rO rS LΨ LF Lb Lσ) :
    TwistedJointMonotonicity M D (separatedDiagonalRate D rO rS LΨ LF Lb Lσ) := by
  apply separated_joint_monotonicity M D H
  · dsimp [separatedDiagonalRate]
    linarith [min_le_left rO rS]
  · dsimp [separatedDiagonalRate]
    linarith [min_le_right rO rS]

end LawCriteria

end PBGSO
