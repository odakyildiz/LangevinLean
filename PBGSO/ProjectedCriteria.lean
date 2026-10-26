import PBGSO.PaperTheorems
import PBGSO.Criteria
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The projected-field criterion at the level of actual coupling laws

The projected observation and force satisfy the pointwise monotonicity
condition U4. The two *separate* auxiliary dissipation inequalities U5
remain primitive assumptions on the chosen optimiser and sampler; their
conclusion is not assumed. This file proves the coupling marginal identity,
integrates U4, cancels constant diffusion, and derives the full model's
`TwistedJointMonotonicity`. All score-work integrability is explicit:
finite second moments alone need not control a superlinear force.
-/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace InnerProductSpace
namespace PBGSO

variable {S Θ Z X U V I : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [MeasurableSpace Z] [BorelSpace Z]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fintype I]

/-- Position and auxiliary coordinates are specified by actual linear
projections. The model's optimiser response and sampler drift are arbitrary.
The force is the negative score in the source; conservativity is not needed
by this implication. -/
structure ProjectedData (M : Model S Θ Z X I) where
  parameterProjection : S →L[ℝ] Θ
  positionProjection : Z →L[ℝ] X
  optimizerAuxiliary : S →L[ℝ] U
  samplerAuxiliary : Z →L[ℝ] V
  parameter_eq : M.parameter = parameterProjection
  position_eq : M.position = positionProjection
  force : Θ → X → X
  optimizerAuxWeight : U →L[ℝ] U
  samplerAuxWeight : V →L[ℝ] V

namespace ProjectedData
variable {M : Model S Θ Z X I} (C : ProjectedData (U := U) (V := V) M)

def radius (s s' : S) (Λ : Measure (Z × Z)) : ℝ :=
  ‖C.parameterProjection (s - s')‖ ^ 2 +
    ∫ zz, ‖C.positionProjection (zz.1 - zz.2)‖ ^ 2 ∂Λ

def optimizerAuxSq (d : S) : ℝ :=
  ⟪C.optimizerAuxiliary d, C.optimizerAuxWeight (C.optimizerAuxiliary d)⟫_ℝ

def samplerAuxSq (zz : Z × Z) : ℝ :=
  ⟪C.samplerAuxiliary (zz.1 - zz.2),
    C.samplerAuxWeight (C.samplerAuxiliary (zz.1 - zz.2))⟫_ℝ

def scoreWork (s s' : S) (zz : Z × Z) : ℝ :=
  ⟪C.positionProjection (zz.1 - zz.2),
    C.force (M.parameter s) (M.position zz.1) -
      C.force (M.parameter s') (M.position zz.2)⟫_ℝ

def optimizerProjectedWork (s s' : S) (ν ν' : Measure Z) : ℝ :=
  ⟪C.parameterProjection (s - s'), M.meanGradient ν s - M.meanGradient ν' s'⟫_ℝ

/-- U4 is a pointwise monotonicity statement on the projected field,
before any expectation or coupling is introduced. -/
def StrongMonotonicity (r : ℝ) : Prop :=
  ∀ θ θ' x x', r * (‖θ - θ'‖ ^ 2 + ‖x - x'‖ ^ 2) ≤
    ⟪θ - θ', M.observation θ x - M.observation θ' x'⟫_ℝ +
      ⟪x - x', C.force θ x - C.force θ' x'⟫_ℝ

/-- The additional integrability needed to integrate the source U4/U5
expressions. It is not inferred from finite second moments of the laws. -/
structure Integrability (s s' : S) (Λ : Measure (Z × Z)) : Prop where
  position_sq : Integrable (fun zz => ‖C.positionProjection (zz.1 - zz.2)‖ ^ 2) Λ
  score_work : Integrable (C.scoreWork s s') Λ
  auxiliary_sq : Integrable C.samplerAuxSq Λ

end ProjectedData

/-- The actual mean-gradient difference is the integral of the paired
observations for every genuine coupling. No coupling-gradient identity is
assumed as a separate hypothesis. -/
theorem meanGradient_difference_of_coupling (M : Model S Θ Z X I)
    (s s' : S) {ν ν' : Measure Z} {Λ : Measure (Z × Z)}
    (hΛ : IsCoupling Λ ν ν')
    (hf : Integrable (fun z => M.observation (M.parameter s) (M.position z)) ν)
    (hg : Integrable (fun z => M.observation (M.parameter s') (M.position z)) ν') :
    M.meanGradient ν s - M.meanGradient ν' s' =
      ∫ zz, M.observation (M.parameter s) (M.position zz.1) -
        M.observation (M.parameter s') (M.position zz.2) ∂Λ := by
  have hfm : Integrable (fun z => M.observation (M.parameter s) (M.position z))
      (Λ.map Prod.fst) := hΛ.1.symm ▸ hf
  have hgm : Integrable (fun z => M.observation (M.parameter s') (M.position z))
      (Λ.map Prod.snd) := hΛ.2.symm ▸ hg
  have hfΛ := hfm.comp_measurable measurable_fst
  have hgΛ := hgm.comp_measurable measurable_snd
  simp only [Function.comp_def] at hfΛ hgΛ
  rw [integral_sub hfΛ hgΛ]
  rw [← integral_map measurable_fst.aemeasurable hfm.aestronglyMeasurable,
    ← integral_map measurable_snd.aemeasurable hgm.aestronglyMeasurable,
    hΛ.1, hΛ.2]
  rfl

/-- Pointwise projected monotonicity integrates to the precise law-level
inequality used by the appendix proof. -/
theorem projected_monotonicity_integral (M : Model S Θ Z X I)
    (C : ProjectedData (U := U) (V := V) M) (r : ℝ)
    (hmono : C.StrongMonotonicity r)
    (s s' : S) {ν ν' : Measure Z} {Λ : Measure (Z × Z)}
    (hΛ : IsCoupling Λ ν ν') [IsProbabilityMeasure ν]
    (hf : Integrable (fun z => M.observation (M.parameter s) (M.position z)) ν)
    (hg : Integrable (fun z => M.observation (M.parameter s') (M.position z)) ν')
    (hInt : C.Integrability s s' Λ) :
    r * C.radius s s' Λ ≤
      C.optimizerProjectedWork s s' ν ν' + ∫ zz, C.scoreWork s s' zz ∂Λ := by
  letI : IsProbabilityMeasure (Λ.map Prod.fst) := hΛ.1.symm ▸ inferInstance
  letI : IsProbabilityMeasure Λ :=
    (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mp inferInstance
  have hfΛ : Integrable (fun zz : Z × Z =>
      M.observation (M.parameter s) (M.position zz.1)) Λ :=
    (hΛ.1.symm ▸ hf).comp_measurable measurable_fst
  have hgΛ : Integrable (fun zz : Z × Z =>
      M.observation (M.parameter s') (M.position zz.2)) Λ :=
    (hΛ.2.symm ▸ hg).comp_measurable measurable_snd
  have hobs := hfΛ.sub hgΛ
  have hw : Integrable (fun zz : Z × Z =>
      ⟪C.parameterProjection (s - s'),
        M.observation (M.parameter s) (M.position zz.1) -
          M.observation (M.parameter s') (M.position zz.2)⟫_ℝ) Λ :=
    hobs.const_inner (C.parameterProjection (s - s'))
  have heq : C.optimizerProjectedWork s s' ν ν' =
      ∫ zz, ⟪C.parameterProjection (s - s'),
        M.observation (M.parameter s) (M.position zz.1) -
          M.observation (M.parameter s') (M.position zz.2)⟫_ℝ ∂Λ := by
    unfold ProjectedData.optimizerProjectedWork
    rw [meanGradient_difference_of_coupling M s s' hΛ hf hg]
    exact (integral_inner hobs _).symm
  rw [heq, ← integral_add hw hInt.score_work]
  have hleft : Integrable (fun zz : Z × Z =>
      r * (‖C.parameterProjection (s - s')‖ ^ 2 +
        ‖C.positionProjection (zz.1 - zz.2)‖ ^ 2)) Λ :=
    ((integrable_const _).add hInt.position_sq).const_mul r
  have hbound := integral_mono hleft (hw.add hInt.score_work) (fun zz => ?_)
  · simpa only [Pi.add_apply, integral_const_mul, integral_add (integrable_const _) hInt.position_sq,
      integral_const, probReal_univ, smul_eq_mul, one_mul, ProjectedData.radius] using hbound
  · simpa only [Pi.add_apply, ProjectedData.scoreWork, C.parameter_eq, C.position_eq, map_sub] using
      hmono (C.parameterProjection s) (C.parameterProjection s')
        (C.positionProjection zz.1) (C.positionProjection zz.2)

/-- These are exactly the probabilistic and integrability inputs in the
domain of `TwistedJointMonotonicity`, not an energy inequality. -/
structure ProjectedAdmissibleCoupling (M : Model S Θ Z X I)
    (D : TwistedGeometry S Z) (s s' : S) (ν ν' : Measure Z)
    (Λ : Measure (Z × Z)) : Prop where
  coupling : IsCoupling Λ ν ν'
  left_probability : IsProbabilityMeasure ν
  right_probability : IsProbabilityMeasure ν'
  left_moment : HasFiniteSecondMoment ν
  right_moment : HasFiniteSecondMoment ν'
  left_observation : Integrable (fun z => M.observation (M.parameter s) (M.position z)) ν
  right_observation : Integrable (fun z => M.observation (M.parameter s') (M.position z)) ν'
  sampler_work : Integrable (samplerCouplingWork M D s s') Λ
  sampler_sq : Integrable (fun zz => D.samplerSq (zz.1 - zz.2)) Λ

def samplerDriftWork (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    (s s' : S) (zz : Z × Z) : ℝ :=
  ⟪zz.1 - zz.2, D.samplerWeight
    (M.drift (M.parameter s) zz.1 - M.drift (M.parameter s') zz.2)⟫_ℝ

/-- U5 consists of two separate dissipation requirements on the chosen
optimiser and sampler. Neither field is required to be conservative. -/
structure ProjectedAuxiliaryDissipation (M : Model S Θ Z X I)
    (D : TwistedGeometry S Z) (C : ProjectedData (U := U) (V := V) M)
    (β AOpt ASam : ℝ) : Prop where
  optimizer : ∀ t, 0 ≤ t → ∀ s s' ν ν' Λ,
    ProjectedAdmissibleCoupling M D s s' ν ν' Λ →
    ⟪s - s', D.optimizerWeight
      (M.optimizerField t s ν - M.optimizerField t s' ν')⟫_ℝ ≤
      -β * C.optimizerProjectedWork s s' ν ν' - C.optimizerAuxSq (s - s') +
        AOpt * C.radius s s' Λ
  sampler : ∀ s s' ν ν' Λ,
    ProjectedAdmissibleCoupling M D s s' ν ν' Λ →
    (∫ zz, samplerDriftWork M D s s' zz ∂Λ) ≤
      -β * (∫ zz, C.scoreWork s s' zz ∂Λ) -
        (∫ zz, C.samplerAuxSq zz ∂Λ) + ASam * C.radius s s' Λ

/-- Constant diffusion removes the Hilbert--Schmidt correction exactly. -/
theorem samplerCouplingWork_eq_drift_of_constant (M : Model S Θ Z X I)
    (D : TwistedGeometry S Z) (σ : I → Z)
    (hσ : ∀ θ z, M.diffusion θ z = σ) (s s' : S) :
    samplerCouplingWork M D s s' = samplerDriftWork M D s s' := by
  funext zz
  simp [samplerCouplingWork, samplerDriftWork, hσ, TwistedGeometry.samplerSq]

/-- The pointwise metric domination `rho D ≤ K` integrates to the full
coupling-energy domination. Its premises concern two deterministic quadratic
forms, not a stochastic contraction theorem. -/
theorem projected_metric_integral (M : Model S Θ Z X I)
    (D : TwistedGeometry S Z) (C : ProjectedData (U := U) (V := V) M)
    (c ρ : ℝ)
    (hOpt : ∀ d, ρ * D.optimizerSq d ≤
      c * ‖C.parameterProjection d‖ ^ 2 + C.optimizerAuxSq d)
    (hSam : ∀ zz : Z × Z, ρ * D.samplerSq (zz.1 - zz.2) ≤
      c * ‖C.positionProjection (zz.1 - zz.2)‖ ^ 2 + C.samplerAuxSq zz)
    (s s' : S) (Λ : Measure (Z × Z))
    (hInt : C.Integrability s s' Λ)
    (hSq : Integrable (fun zz => D.samplerSq (zz.1 - zz.2)) Λ) :
    ρ * (D.optimizerSq (s - s') + ∫ zz, D.samplerSq (zz.1 - zz.2) ∂Λ) ≤
      c * C.radius s s' Λ + C.optimizerAuxSq (s - s') +
        ∫ zz, C.samplerAuxSq zz ∂Λ := by
  have hi := integral_mono (hSq.const_mul ρ)
    ((hInt.position_sq.const_mul c).add hInt.auxiliary_sq) hSam
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul, integral_add (hInt.position_sq.const_mul c) hInt.auxiliary_sq,
    integral_const_mul] at hi
  dsimp [ProjectedData.radius]
  linarith [hOpt (s - s')]

/-- The full projected-field sufficient condition in the source appendix.
Pointwise U4 is integrated using the actual marginal identities. U5 is kept
as the separate optimiser and sampler hypothesis. Integrability of the
score work is an explicit analytic requirement. -/
theorem projected_twistedJointMonotonicity (M : Model S Θ Z X I)
    (D : TwistedGeometry S Z) (C : ProjectedData (U := U) (V := V) M)
    (β r AOpt ASam ρ : ℝ) (hβ : 0 ≤ β)
    (hmono : C.StrongMonotonicity r)
    (haux : ProjectedAuxiliaryDissipation M D C β AOpt ASam)
    (σ : I → Z) (hσ : ∀ θ z, M.diffusion θ z = σ)
    (hInt : ∀ s s' ν ν' Λ, ProjectedAdmissibleCoupling M D s s' ν ν' Λ →
      C.Integrability s s' Λ)
    (hOpt : ∀ d, ρ * D.optimizerSq d ≤
      (β * r - AOpt - ASam) * ‖C.parameterProjection d‖ ^ 2 + C.optimizerAuxSq d)
    (hSam : ∀ zz : Z × Z, ρ * D.samplerSq (zz.1 - zz.2) ≤
      (β * r - AOpt - ASam) * ‖C.positionProjection (zz.1 - zz.2)‖ ^ 2 +
        C.samplerAuxSq zz) :
    TwistedJointMonotonicity M D ρ := by
  intro t ht s s' ν ν' Λ hΛ hν hν' hν2 hν2' hf hg hw hs
  let ha : ProjectedAdmissibleCoupling M D s s' ν ν' Λ :=
    ⟨hΛ, hν, hν', hν2, hν2', hf, hg, hw, hs⟩
  letI := hν
  have hmono' := projected_monotonicity_integral M C r hmono s s' hΛ hf hg
    (hInt s s' ν ν' Λ ha)
  have hmetric := projected_metric_integral M D C (β * r - AOpt - ASam) ρ
    hOpt hSam s s' Λ (hInt s s' ν ν' Λ ha) hs
  rw [samplerCouplingWork_eq_drift_of_constant M D σ hσ]
  exact projected_dissipation
    (C.optimizerProjectedWork s s' ν ν') (∫ zz, C.scoreWork s s' zz ∂Λ)
    _ _ (C.radius s s' Λ) (C.optimizerAuxSq (s - s'))
    (∫ zz, C.samplerAuxSq zz ∂Λ) β r AOpt ASam ρ _ hβ hmono'
    (haux.optimizer t ht s s' ν ν' Λ ha) (haux.sampler s s' ν ν' Λ ha) hmetric

/-- An explicit conservative rate avoiding inverse square roots and an
eigenvalue computation. `c=beta*r-AOpt-ASam` in the source criterion. -/
def projectedCertifiedRate (D : TwistedGeometry S Z) (c mLower vLower : ℝ) : ℝ :=
  min c (min mLower vLower) / D.upper

theorem projectedCertifiedRate_pos (D : TwistedGeometry S Z) (c mLower vLower : ℝ)
    (hc : 0 < c) (hm : 0 < mLower) (hv : 0 < vLower) :
    0 < projectedCertifiedRate D c mLower vLower := by
  exact div_pos (lt_min hc (lt_min hm hv)) (D.lower_pos.trans_le D.lower_le_upper)

/-- Coordinate coercivity and a genuine orthogonal norm splitting prove
the optimiser metric comparison at the displayed explicit rate. -/
theorem projected_optimizer_metric_certified (M : Model S Θ Z X I)
    (D : TwistedGeometry S Z) (C : ProjectedData (U := U) (V := V) M)
    (c mLower vLower : ℝ) (hc : 0 < c) (hm : 0 < mLower) (hv : 0 < vLower)
    (hsplit : ∀ d, ‖d‖ ^ 2 =
      ‖C.parameterProjection d‖ ^ 2 + ‖C.optimizerAuxiliary d‖ ^ 2)
    (hlower : ∀ d, mLower * ‖C.optimizerAuxiliary d‖ ^ 2 ≤ C.optimizerAuxSq d)
    (d : S) :
    projectedCertifiedRate D c mLower vLower * D.optimizerSq d ≤
      c * ‖C.parameterProjection d‖ ^ 2 + C.optimizerAuxSq d := by
  let k := min c (min mLower vLower)
  have hρ := projectedCertifiedRate_pos D c mLower vLower hc hm hv
  have hcomp := mul_le_mul_of_nonneg_left (D.optimizer_upper d) hρ.le
  have hcancel : projectedCertifiedRate D c mLower vLower * D.upper = k :=
    div_mul_cancel₀ _ (ne_of_gt (D.lower_pos.trans_le D.lower_le_upper))
  rw [← mul_assoc, hcancel, hsplit d] at hcomp
  have hq := mul_le_mul_of_nonneg_right (min_le_left c (min mLower vLower))
    (sq_nonneg ‖C.parameterProjection d‖)
  have hp := mul_le_mul_of_nonneg_right
    ((min_le_right c (min mLower vLower)).trans (min_le_left mLower vLower))
    (sq_nonneg ‖C.optimizerAuxiliary d‖)
  change projectedCertifiedRate D c mLower vLower * D.optimizerSq d ≤ _
  dsimp [TwistedGeometry.optimizerSq] at *
  linarith [hlower d]

/-- The analogous sampler metric comparison. Auxiliary coercivity is a
pointwise deterministic quadratic-form premise. -/
theorem projected_sampler_metric_certified (M : Model S Θ Z X I)
    (D : TwistedGeometry S Z) (C : ProjectedData (U := U) (V := V) M)
    (c mLower vLower : ℝ) (hc : 0 < c) (hm : 0 < mLower) (hv : 0 < vLower)
    (hsplit : ∀ d, ‖d‖ ^ 2 =
      ‖C.positionProjection d‖ ^ 2 + ‖C.samplerAuxiliary d‖ ^ 2)
    (hlower : ∀ zz, vLower * ‖C.samplerAuxiliary (zz.1 - zz.2)‖ ^ 2 ≤
      C.samplerAuxSq zz) (zz : Z × Z) :
    projectedCertifiedRate D c mLower vLower * D.samplerSq (zz.1 - zz.2) ≤
      c * ‖C.positionProjection (zz.1 - zz.2)‖ ^ 2 + C.samplerAuxSq zz := by
  let k := min c (min mLower vLower)
  have hρ := projectedCertifiedRate_pos D c mLower vLower hc hm hv
  have hcomp := mul_le_mul_of_nonneg_left (D.sampler_upper (zz.1 - zz.2)) hρ.le
  have hcancel : projectedCertifiedRate D c mLower vLower * D.upper = k :=
    div_mul_cancel₀ _ (ne_of_gt (D.lower_pos.trans_le D.lower_le_upper))
  rw [← mul_assoc, hcancel, hsplit (zz.1 - zz.2)] at hcomp
  have hq := mul_le_mul_of_nonneg_right (min_le_left c (min mLower vLower))
    (sq_nonneg ‖C.positionProjection (zz.1 - zz.2)‖)
  have hp := mul_le_mul_of_nonneg_right
    ((min_le_right c (min mLower vLower)).trans (min_le_right mLower vLower))
    (sq_nonneg ‖C.samplerAuxiliary (zz.1 - zz.2)‖)
  dsimp [TwistedGeometry.samplerSq] at *
  linarith [hlower zz]

/-- U4 and U5 imply full twisted joint monotonicity at a strictly positive,
explicit certified rate, once the stated coordinate coercivity and
integrability conditions have been checked. -/
theorem projected_twistedJointMonotonicity_certified (M : Model S Θ Z X I)
    (D : TwistedGeometry S Z) (C : ProjectedData (U := U) (V := V) M)
    (β r AOpt ASam mLower vLower : ℝ) (hβ : 0 ≤ β)
    (hc : 0 < β * r - AOpt - ASam) (hm : 0 < mLower) (hv : 0 < vLower)
    (hmono : C.StrongMonotonicity r)
    (haux : ProjectedAuxiliaryDissipation M D C β AOpt ASam)
    (σ : I → Z) (hσ : ∀ θ z, M.diffusion θ z = σ)
    (hInt : ∀ s s' ν ν' Λ, ProjectedAdmissibleCoupling M D s s' ν ν' Λ →
      C.Integrability s s' Λ)
    (hOptSplit : ∀ d, ‖d‖ ^ 2 =
      ‖C.parameterProjection d‖ ^ 2 + ‖C.optimizerAuxiliary d‖ ^ 2)
    (hSamSplit : ∀ d, ‖d‖ ^ 2 =
      ‖C.positionProjection d‖ ^ 2 + ‖C.samplerAuxiliary d‖ ^ 2)
    (hOptLower : ∀ d, mLower * ‖C.optimizerAuxiliary d‖ ^ 2 ≤ C.optimizerAuxSq d)
    (hSamLower : ∀ zz, vLower * ‖C.samplerAuxiliary (zz.1 - zz.2)‖ ^ 2 ≤
      C.samplerAuxSq zz) :
    let ρ := projectedCertifiedRate D (β * r - AOpt - ASam) mLower vLower
    0 < ρ ∧ TwistedJointMonotonicity M D ρ := by
  dsimp
  refine ⟨projectedCertifiedRate_pos D _ _ _ hc hm hv, ?_⟩
  apply projected_twistedJointMonotonicity M D C β r AOpt ASam _ hβ hmono haux σ hσ hInt
  · exact projected_optimizer_metric_certified M D C _ _ _ hc hm hv hOptSplit hOptLower
  · exact projected_sampler_metric_certified M D C _ _ _ hc hm hv hSamSplit hSamLower

end PBGSO
