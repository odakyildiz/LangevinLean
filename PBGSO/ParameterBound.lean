import PBGSO.ParticleWeakBound
import PBGSO.SeparatedGeometry
import PBGSO.LawContraction

/-! # Actual optimiser and parameter errors

The random optimiser is the first coordinate of the interacting/reference
joint law. Its error to a deterministic target is a genuine L² norm. The
triangle inequality, the projection comparison and the comparison of the
optimiser coordinate with the full particle metric are proved here.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators RealInnerProductSpace Topology
namespace PBGSO

section L2
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (Q : Measure Ω)

/-- The genuine root second norm moment equals the L² seminorm when the
function is square integrable. -/
theorem rms_eq_eLpNorm (f : Ω → E) (hf : MemLp f 2 Q) :
    Real.sqrt (∫ ω, ‖f ω‖ ^ 2 ∂Q) = (eLpNorm f 2 Q).toReal := by
  have hn := ProximalLangevin.lp_norm_sq_eq_integral Q (hf.toLp f)
  rw [Lp.norm_toLp] at hn
  have he : (∫ ω, ‖hf.toLp f ω‖ ^ 2 ∂Q) = ∫ ω, ‖f ω‖ ^ 2 ∂Q := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with ω hω
    rw [hω]
  rw [he] at hn
  rw [← hn, Real.sqrt_sq ENNReal.toReal_nonneg]

variable [IsProbabilityMeasure Q]

/-- Minkowski with a deterministic offset. The second moment of the sum is
proved finite, so no totalised integral is being treated as an error norm. -/
theorem rms_add_constant (f : Ω → E) (hf : MemLp f 2 Q) (c : E) :
    MemLp (fun ω ↦ f ω + c) 2 Q ∧
    Real.sqrt (∫ ω, ‖f ω + c‖ ^ 2 ∂Q) ≤
      Real.sqrt (∫ ω, ‖f ω‖ ^ 2 ∂Q) + ‖c‖ := by
  have hc : MemLp (fun _ : Ω ↦ c) 2 Q := memLp_const c
  have hs : MemLp (fun ω ↦ f ω + c) 2 Q := hf.add hc
  refine ⟨hs, ?_⟩
  rw [rms_eq_eLpNorm Q _ hs, rms_eq_eLpNorm Q f hf]
  have hle := eLpNorm_add_le (μ := Q) (f := f) (g := fun _ : Ω ↦ c)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨hf.eLpNorm_ne_top, hc.eLpNorm_ne_top⟩) hle
  rw [ENNReal.toReal_add hf.eLpNorm_ne_top hc.eLpNorm_ne_top] at hr
  have he : (eLpNorm (fun _ : Ω ↦ c) 2 Q).toReal = ‖c‖ := by
    simp [eLpNorm_const c (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by exact NeZero.ne Q)]
  change (eLpNorm (fun ω ↦ f ω + c) 2 Q).toReal ≤
    (eLpNorm f 2 Q).toReal + (eLpNorm (fun _ : Ω ↦ c) 2 Q).toReal at hr
  simpa only [he] using hr

end L2

section ParticleCoordinate
variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype I]

/-- The optimiser-coordinate error is bounded by the actual joint particle
energy. The deterministic reference coordinate is identified almost surely. -/
theorem optimizer_interaction_rms_bound (D : TwistedGeometry S Z) (N : ℕ)
    (Q : Measure (ParticlePair N S Z)) [IsProbabilityMeasure Q]
    (sbar : S) (hbar : ∀ᵐ p ∂Q, p.2.1 = sbar)
    (hquad : Integrable (fun p ↦ particleQuadraticBilinear D N p p) Q) :
    MemLp (fun p : ParticlePair N S Z ↦ p.1.1 - sbar) 2 Q ∧
    Real.sqrt (∫ p, ‖p.1.1 - sbar‖ ^ 2 ∂Q) ≤
      Real.sqrt (∫ p, particleQuadraticBilinear D N p p ∂Q) / Real.sqrt D.lower := by
  let q := fun p : ParticlePair N S Z ↦ particleQuadraticBilinear D N p p
  have hpos (p : ParticlePair N S Z) : 0 ≤ q p := by
    dsimp only [q]
    rw [particleQuadraticBilinear_diag]
    exact add_nonneg (D.optimizerSq_nonneg _)
      (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ ↦ D.samplerSq_nonneg _))
  have hqp (p : ParticlePair N S Z) : D.optimizerSq (p.1.1 - p.2.1) ≤ q p := by
    dsimp only [q]
    rw [particleQuadraticBilinear_diag]
    exact le_add_of_nonneg_right
      (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ ↦ D.samplerSq_nonneg _))
  have hbound : ∀ᵐ p ∂Q, ‖p.1.1 - sbar‖ ≤ Real.sqrt (q p) / Real.sqrt D.lower := by
    filter_upwards [hbar] with p hp
    rw [← hp]
    exact (D.optimizer_norm_le _).trans
      (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (hqp p)) (Real.sqrt_nonneg _))
  have hq := sqrt_energy_memLp Q q hquad.aestronglyMeasurable hquad hpos
  have hg : MemLp (fun p ↦ Real.sqrt (q p) / Real.sqrt D.lower) 2 Q := by
    convert hq.const_mul (1 / Real.sqrt D.lower) using 1
    ext p
    ring
  have hf : MemLp (fun p : ParticlePair N S Z ↦ p.1.1 - sbar) 2 Q :=
    hg.mono' (by fun_prop) hbound
  refine ⟨hf, ?_⟩
  have hsqbound : ∀ᵐ p ∂Q, ‖p.1.1 - sbar‖ ^ 2 ≤ q p / D.lower := by
    filter_upwards [hbar] with p hp
    rw [← hp]
    apply (le_div_iff₀ D.lower_pos).mpr
    simpa only [mul_comm] using (D.optimizer_lower _).trans (hqp p)
  have hs := integral_mono_ae
    ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf)
    (hquad.div_const D.lower) hsqbound
  have hr := Real.sqrt_le_sqrt hs
  rw [integral_div, Real.sqrt_div (integral_nonneg hpos)] at hr
  exact hr

/-- The optimiser triangle inequality is proved on the actual particle law. -/
theorem optimizer_target_rms_bound (D : TwistedGeometry S Z) (N : ℕ)
    (Q : Measure (ParticlePair N S Z)) [IsProbabilityMeasure Q]
    (sbar sStar : S) (hbar : ∀ᵐ p ∂Q, p.2.1 = sbar)
    (hquad : Integrable (fun p ↦ particleQuadraticBilinear D N p p) Q) :
    MemLp (fun p : ParticlePair N S Z ↦ p.1.1 - sStar) 2 Q ∧
    Real.sqrt (∫ p, ‖p.1.1 - sStar‖ ^ 2 ∂Q) ≤
      Real.sqrt (∫ p, particleQuadraticBilinear D N p p ∂Q) / Real.sqrt D.lower +
        ‖sbar - sStar‖ := by
  obtain ⟨hf, hi⟩ := optimizer_interaction_rms_bound D N Q sbar hbar hquad
  obtain ⟨hs, ht⟩ := rms_add_constant Q _ hf (sbar - sStar)
  have he : (fun p : ParticlePair N S Z ↦ (p.1.1 - sbar) + (sbar - sStar)) =
      (fun p ↦ p.1.1 - sStar) := by funext p; module
  rw [he] at hs
  simp only [sub_add_sub_cancel] at ht
  exact ⟨hs, ht.trans (add_le_add hi (le_refl _))⟩

/-- A one-Lipschitz parameter projection sends the actual random optimiser
error to a no-larger parameter L² error. -/
theorem parameter_target_rms_bound (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    (hProjection : LipschitzWith 1 M.parameter) (N : ℕ)
    (Q : Measure (ParticlePair N S Z)) [IsProbabilityMeasure Q]
    (sbar sStar : S) (hbar : ∀ᵐ p ∂Q, p.2.1 = sbar)
    (hquad : Integrable (fun p ↦ particleQuadraticBilinear D N p p) Q) :
    MemLp (fun p : ParticlePair N S Z ↦ M.parameter p.1.1 - M.parameter sStar) 2 Q ∧
    Real.sqrt (∫ p, ‖M.parameter p.1.1 - M.parameter sStar‖ ^ 2 ∂Q) ≤
      Real.sqrt (∫ p, particleQuadraticBilinear D N p p ∂Q) / Real.sqrt D.lower +
        ‖sbar - sStar‖ := by
  obtain ⟨hf, ht⟩ := optimizer_target_rms_bound D N Q sbar sStar hbar hquad
  have hb (p : ParticlePair N S Z) : ‖M.parameter p.1.1 - M.parameter sStar‖ ≤
      ‖p.1.1 - sStar‖ := by simpa using hProjection.norm_sub_le p.1.1 sStar
  have hm : AEStronglyMeasurable
      (fun p : ParticlePair N S Z ↦ M.parameter p.1.1 - M.parameter sStar) Q := by
    exact ((hProjection.continuous.comp (continuous_fst.comp continuous_fst)).sub
      continuous_const).aestronglyMeasurable
  have hp := hf.norm.mono' hm (ae_of_all Q hb)
  refine ⟨hp, le_trans (Real.sqrt_le_sqrt ?_) ht⟩
  apply integral_mono
    ((memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).mp hp)
    ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf)
  intro p
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hb p)

/-- The deterministic optimiser distance is one component of the actual
optimiser-law product metric. -/
theorem optimizer_norm_le_lawDistance (s s' : S) (ν ν' : Measure Z) :
    ‖s - s'‖ ≤ optimizerLawDistance s s' ν ν' := by
  apply Real.le_sqrt_of_sq_le
  exact le_add_of_nonneg_right (sq_nonneg _)

end ParticleCoordinate

section StationaryTarget
variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype I]

/-- The actual synchronous pair law and its generator equation. Marginal
weak solutions are supplied separately, so stationarity is constructed from
frozen sampler stationarity rather than assumed as a contraction conclusion. -/
structure SynchronousCouplingData (M : Model S Θ Z X I)
    (pairTests : Set (Z × Z → ℝ)) (s s' : ℝ → S)
    (ν ν' : ℝ → Measure Z) (Λ : ℝ → Measure (Z × Z)) : Prop where
  coupling : ∀ t, 0 ≤ t → IsCoupling (Λ t) (ν t) (ν' t)
  test_integrable : ∀ φ ∈ pairTests, ∀ t, 0 ≤ t → Integrable φ (Λ t)
  generator_integrable : ∀ φ ∈ pairTests, ∀ t, 0 ≤ t →
    Integrable (synchronousGenerator M (s t) (s' t) φ) (Λ t)
  forward_equation : ∀ φ ∈ pairTests, ∀ t, 0 ≤ t →
    HasDerivWithinAt (fun r ↦ ∫ zz, φ zz ∂Λ r)
      (∫ zz, synchronousGenerator M (s t) (s' t) φ zz ∂Λ t) (Ici 0) t

theorem SynchronousCouplingData.toCoupledWeakSolution
    {M : Model S Θ Z X I} {tests : Set (Z → ℝ)} {pairTests : Set (Z × Z → ℝ)}
    {s s' : ℝ → S} {ν ν' : ℝ → Measure Z} {Λ : ℝ → Measure (Z × Z)}
    (H : SynchronousCouplingData M pairTests s s' ν ν' Λ)
    (hleft : M.IsWeakSolution tests s ν) (hright : M.IsWeakSolution tests s' ν') :
    IsCoupledWeakSolution M tests pairTests s s' ν ν' Λ where
  left := hleft
  right := hright
  coupling := H.coupling
  test_integrable := H.test_integrable
  generator_integrable := H.generator_integrable
  forward_equation := H.forward_equation

/-- Actual mean-field relaxation to a frozen stationary target. The target
constant weak solution is constructed by `Model.constant_isWeakSolution`.
Synchronous realizability for every genuine initial coupling remains the
explicit analytic process assumption used to reach the transport infimum. -/
theorem stationary_target_law_bound (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    (tests : Set (Z → ℝ)) (pairTests : Set (Z × Z → ℝ))
    (sbar : ℝ → S) (ν : ℝ → Measure Z) (hmean : M.IsWeakSolution tests sbar ν)
    (sStar : S) (νStar : Measure Z)
    (hstationary : M.FrozenStationary tests (M.parameter sStar) νStar)
    (hgradient : Integrable
      (fun z ↦ M.observation (M.parameter sStar) (M.position z)) νStar)
    (hzero : M.meanGradient νStar sStar = 0)
    (hfix : ∀ r, 0 ≤ r → M.optimizer r sStar 0 = 0)
    (hquad : couplingQuadratic D ∈ pairTests)
    (ρ T : ℝ) (hmono : TwistedJointMonotonicity M D ρ)
    (realize : ∀ c : ULA.Coupling (ν 0) νStar,
      ∃ Λ : ℝ → Measure (Z × Z),
        SynchronousCouplingData M pairTests sbar (fun _ ↦ sStar) ν (fun _ ↦ νStar) Λ ∧
          Λ 0 = c.joint)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    optimizerLawDistance (sbar t) sStar (ν t) νStar ≤
      Real.sqrt D.conditionNumber * Real.exp (-ρ * t) *
        optimizerLawDistance (sbar 0) sStar (ν 0) νStar := by
  letI := hmean.probability 0 le_rfl
  letI := hstationary.probability
  have hν : MemLp (fun z : Z ↦ z) 2 (ν 0) :=
    (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).mpr
      (hmean.second_moment 0 le_rfl)
  have hνStar : MemLp (fun z : Z ↦ z) 2 νStar :=
    (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).mpr
      hstationary.second_moment
  have hStar := M.constant_isWeakSolution tests sStar νStar hstationary hgradient hzero hfix
  apply weak_law_contraction M D tests pairTests sbar (fun _ ↦ sStar) ν (fun _ ↦ νStar)
    hν hνStar hquad ρ T hmono ?_ t ht
  intro c
  obtain ⟨Λ, hΛ, hinit⟩ := realize c
  exact ⟨Λ, hΛ.toCoupledWeakSolution hmean hStar, hinit⟩

end StationaryTarget

section SourceParameterBound
variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace Θ] [BorelSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype I]

/-- The paper's parameter bound, for actual random interacting optimiser
coordinates and an actual frozen stationary target. The interaction and
relaxation terms are derived from their respective weak-generator equations;
no parameter triangle, energy differential inequality, variance formula or
transport error bound is an input. The generator domains, iid reference
marginal, synchronous realizability, primitive optimiser response Lipschitz
bound, and uniform observation variance assumptions are all explicit. -/
theorem finite_particle_parameter_bound
    (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    (hProjection : LipschitzWith 1 M.parameter)
    (tests : Set (Z → ℝ)) (pairTests : Set (Z × Z → ℝ))
    (sbar : ℝ → S) (ν : ℝ → Measure Z) (hmean : M.IsWeakSolution tests sbar ν)
    (sStar : S) (νStar : Measure Z)
    (hstationary : M.FrozenStationary tests (M.parameter sStar) νStar)
    (hgradient : Integrable
      (fun z ↦ M.observation (M.parameter sStar) (M.position z)) νStar)
    (hgradientZero : M.meanGradient νStar sStar = 0)
    (hfix : ∀ r, 0 ≤ r → M.optimizer r sStar 0 = 0)
    (hpairQuad : couplingQuadratic D ∈ pairTests)
    (ρ : ℝ) (hρ : 0 < ρ) (hmono : TwistedJointMonotonicity M D ρ)
    (realize : ∀ c : ULA.Coupling (ν 0) νStar,
      ∃ Λ : ℝ → Measure (Z × Z),
        SynchronousCouplingData M pairTests sbar (fun _ ↦ sStar) ν (fun _ ↦ νStar) Λ ∧
          Λ 0 = c.joint)
    (N : ℕ) (hN : 0 < N) (particleTests : Set (ParticlePair N S Z → ℝ))
    (Γ : ℝ → Measure (ParticlePair N S Z))
    (hparticle : IsParticleCopyWeakSolution M N ν particleTests Γ)
    (hparticleQuad : (fun p ↦ particleQuadraticBilinear D N p p) ∈ particleTests)
    (LΨ : ℝ≥0) (V T : ℝ) (hV : 0 ≤ V)
    (hF : ∀ r ∈ Icc 0 T,
      MemLp (fun z ↦ M.observation (M.parameter (sbar r)) (M.position z)) 2 (ν r))
    (hCloud : ∀ r ∈ Icc 0 T,
      (Γ r).map (fun p ↦ p.2.2) = Measure.pi (fun _ : Fin N ↦ ν r))
    (hbar : ∀ r ∈ Icc 0 T, ∀ᵐ p ∂Γ r, p.2.1 = sbar r)
    (hΨ : ∀ r ∈ Icc 0 T, ∀ s g g',
      ‖M.optimizer r s g - M.optimizer r s g'‖ ≤ (LΨ : ℝ) * ‖g - g'‖)
    (hVariance : ∀ r ∈ Icc 0 T,
      (∫ z, ‖M.observation (M.parameter (sbar r)) (M.position z) -
        M.meanGradient (ν r) (sbar r)‖ ^ 2 ∂ν r) ≤ V)
    (hResidual : ∀ r ∈ Icc 0 T,
      AEStronglyMeasurable (particlePopulationResidual M D N (ν r) r) (Γ r))
    (hzero : expectedParticleEnergy D N Γ 0 = 0)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    MemLp (fun p : ParticlePair N S Z ↦ M.parameter p.1.1 - M.parameter sStar) 2 (Γ t) ∧
    Real.sqrt (∫ p, ‖M.parameter p.1.1 - M.parameter sStar‖ ^ 2 ∂Γ t) ≤
      Real.sqrt D.conditionNumber * Real.exp (-ρ * t) *
        optimizerLawDistance (sbar 0) sStar (ν 0) νStar +
      ((LΨ : ℝ) / ρ) * Real.sqrt (D.conditionNumber * V / (N : ℝ)) *
        (1 - Real.exp (-ρ * t)) := by
  letI := hparticle.probability t ht.1
  obtain ⟨hm, htriangle⟩ := parameter_target_rms_bound M D hProjection N (Γ t)
    (sbar t) sStar (hbar t ht) (hparticle.test_integrable _ hparticleQuad t ht.1)
  have hrelax := (optimizer_norm_le_lawDistance (sbar t) sStar (ν t) νStar).trans
    (stationary_target_law_bound M D tests pairTests sbar ν hmean sStar νStar hstationary
      hgradient hgradientZero hfix hpairQuad ρ T hmono realize t ht)
  have hforcing := hparticle.forced_energy_bound D hN hparticleQuad ρ hρ hmono LΨ V T hV
    sbar (fun r hr ↦ hmean.probability r hr.1) hF hCloud hbar hΨ hVariance hResidual hzero t ht
  have hinteract := div_le_div_of_nonneg_right hforcing (Real.sqrt_nonneg D.lower)
  have hκ : 0 ≤ D.conditionNumber := le_trans (by norm_num : (0 : ℝ) ≤ 1)
    D.conditionNumber_ge_one
  have hs : Real.sqrt (D.conditionNumber * V / (N : ℝ)) =
      (Real.sqrt D.upper / Real.sqrt D.lower) * Real.sqrt (V / (N : ℝ)) := by
    rw [show D.conditionNumber * V / (N : ℝ) = D.conditionNumber * (V / (N : ℝ)) by ring,
      Real.sqrt_mul hκ, D.sqrt_conditionNumber]
  have hinteract' : Real.sqrt (expectedParticleEnergy D N Γ t) / Real.sqrt D.lower ≤
      ((LΨ : ℝ) / ρ) * Real.sqrt (D.conditionNumber * V / (N : ℝ)) *
        (1 - Real.exp (-ρ * t)) := by
    apply hinteract.trans_eq
    rw [hs]
    ring
  refine ⟨hm, ?_⟩
  dsimp only [expectedParticleEnergy] at hinteract'
  linarith

/-- Actual weak particle/reference dynamics with uniform-in-time primitive
sampling and response assumptions. This packages process data, not an error
bound. It supports the paper's long-time/population limit statements. -/
structure ParticleParameterApproximation (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    (N : ℕ) (ν : ℝ → Measure Z) (sbar : ℝ → S) (LΨ : ℝ≥0) (V : ℝ) where
  jointLaw : ℝ → Measure (ParticlePair N S Z)
  tests : Set (ParticlePair N S Z → ℝ)
  solution : IsParticleCopyWeakSolution M N ν tests jointLaw
  quadratic_test : (fun p ↦ particleQuadraticBilinear D N p p) ∈ tests
  observation_second_moment : ∀ r, 0 ≤ r →
    MemLp (fun z ↦ M.observation (M.parameter (sbar r)) (M.position z)) 2 (ν r)
  reference_cloud : ∀ r, 0 ≤ r →
    (jointLaw r).map (fun p ↦ p.2.2) = Measure.pi (fun _ : Fin N ↦ ν r)
  reference_optimizer : ∀ r, 0 ≤ r → ∀ᵐ p ∂jointLaw r, p.2.1 = sbar r
  response : ∀ r, 0 ≤ r → ∀ s g g',
    ‖M.optimizer r s g - M.optimizer r s g'‖ ≤ (LΨ : ℝ) * ‖g - g'‖
  observation_variance : ∀ r, 0 ≤ r →
    (∫ z, ‖M.observation (M.parameter (sbar r)) (M.position z) -
      M.meanGradient (ν r) (sbar r)‖ ^ 2 ∂ν r) ≤ V
  residual_measurable : ∀ r, 0 ≤ r →
    AEStronglyMeasurable (particlePopulationResidual M D N (ν r) r) (jointLaw r)
  zero_initial_error : expectedParticleEnergy D N jointLaw 0 = 0

/-- The actual parameter RMS associated with the interacting coordinate of
this joint law. -/
def ParticleParameterApproximation.parameterError
    {M : Model S Θ Z X I} {D : TwistedGeometry S Z} {N : ℕ}
    {ν : ℝ → Measure Z} {sbar : ℝ → S} {LΨ : ℝ≥0} {V : ℝ}
    (H : ParticleParameterApproximation M D N ν sbar LΨ V) (sStar : S) (t : ℝ) : ℝ :=
  Real.sqrt (∫ p, ‖M.parameter p.1.1 - M.parameter sStar‖ ^ 2 ∂H.jointLaw t)

/-- Uniform process data instantiate the actual finite-time parameter
bound at every nonnegative time. -/
theorem ParticleParameterApproximation.parameter_bound
    {M : Model S Θ Z X I} {D : TwistedGeometry S Z}
    (hProjection : LipschitzWith 1 M.parameter)
    (tests : Set (Z → ℝ)) (pairTests : Set (Z × Z → ℝ))
    {sbar : ℝ → S} {ν : ℝ → Measure Z} (hmean : M.IsWeakSolution tests sbar ν)
    (sStar : S) (νStar : Measure Z)
    (hstationary : M.FrozenStationary tests (M.parameter sStar) νStar)
    (hgradient : Integrable
      (fun z ↦ M.observation (M.parameter sStar) (M.position z)) νStar)
    (hgradientZero : M.meanGradient νStar sStar = 0)
    (hfix : ∀ r, 0 ≤ r → M.optimizer r sStar 0 = 0)
    (hpairQuad : couplingQuadratic D ∈ pairTests)
    {ρ : ℝ} (hρ : 0 < ρ) (hmono : TwistedJointMonotonicity M D ρ)
    (realize : ∀ c : ULA.Coupling (ν 0) νStar,
      ∃ Λ : ℝ → Measure (Z × Z),
        SynchronousCouplingData M pairTests sbar (fun _ ↦ sStar) ν (fun _ ↦ νStar) Λ ∧
          Λ 0 = c.joint)
    {N : ℕ} (hN : 0 < N) {LΨ : ℝ≥0} {V : ℝ} (hV : 0 ≤ V)
    (H : ParticleParameterApproximation M D N ν sbar LΨ V) (t : ℝ) (ht : 0 ≤ t) :
    H.parameterError sStar t ≤
      Real.sqrt D.conditionNumber * Real.exp (-ρ * t) *
        optimizerLawDistance (sbar 0) sStar (ν 0) νStar +
      ((LΨ : ℝ) / ρ) * Real.sqrt (D.conditionNumber * V / (N : ℝ)) *
        (1 - Real.exp (-ρ * t)) := by
  exact (finite_particle_parameter_bound M D hProjection tests pairTests sbar ν hmean
    sStar νStar hstationary hgradient hgradientZero hfix hpairQuad ρ hρ hmono realize N hN
    H.tests H.jointLaw H.solution H.quadratic_test LΨ V t hV
    (fun r hr ↦ H.observation_second_moment r hr.1)
    (fun r hr ↦ H.reference_cloud r hr.1)
    (fun r hr ↦ H.reference_optimizer r hr.1)
    (fun r hr ↦ H.response r hr.1)
    (fun r hr ↦ H.observation_variance r hr.1)
    (fun r hr ↦ H.residual_measurable r hr.1)
    H.zero_initial_error t ⟨ht, le_rfl⟩).2

/-- With the primitive assumptions uniform in time and population, the
actual parameter errors vanish as population and time tend to infinity
jointly. The family index n represents the positive particle count n+1.
This is stronger than either sequential upper-limit conclusion. -/
theorem finite_particle_parameter_joint_limit
    (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    (hProjection : LipschitzWith 1 M.parameter)
    (tests : Set (Z → ℝ)) (pairTests : Set (Z × Z → ℝ))
    (sbar : ℝ → S) (ν : ℝ → Measure Z) (hmean : M.IsWeakSolution tests sbar ν)
    (sStar : S) (νStar : Measure Z)
    (hstationary : M.FrozenStationary tests (M.parameter sStar) νStar)
    (hgradient : Integrable
      (fun z ↦ M.observation (M.parameter sStar) (M.position z)) νStar)
    (hgradientZero : M.meanGradient νStar sStar = 0)
    (hfix : ∀ r, 0 ≤ r → M.optimizer r sStar 0 = 0)
    (hpairQuad : couplingQuadratic D ∈ pairTests)
    (ρ : ℝ) (hρ : 0 < ρ) (hmono : TwistedJointMonotonicity M D ρ)
    (realize : ∀ c : ULA.Coupling (ν 0) νStar,
      ∃ Λ : ℝ → Measure (Z × Z),
        SynchronousCouplingData M pairTests sbar (fun _ ↦ sStar) ν (fun _ ↦ νStar) Λ ∧
          Λ 0 = c.joint)
    (LΨ : ℝ≥0) (V : ℝ) (hV : 0 ≤ V)
    (family : ∀ n : ℕ, ParticleParameterApproximation M D (n + 1) ν sbar LΨ V) :
    Tendsto (fun p : ℕ × ℝ ↦ (family p.1).parameterError sStar p.2)
      (atTop ×ˢ atTop) (𝓝 0) := by
  let d0 := optimizerLawDistance (sbar 0) sStar (ν 0) νStar
  let floor := fun n : ℕ ↦ ((LΨ : ℝ) / ρ) *
    Real.sqrt (D.conditionNumber * V / ((n + 1 : ℕ) : ℝ))
  let decay := fun t : ℝ ↦ Real.sqrt D.conditionNumber * Real.exp (-ρ * t) * d0
  have hdiv : Tendsto (fun n : ℕ ↦ D.conditionNumber * V / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
    have hh := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (D.conditionNumber * V)
    simpa only [Nat.cast_add, Nat.cast_one, mul_zero, mul_one_div] using hh
  have hfloor : Tendsto floor atTop (𝓝 0) := by
    have hh := (Real.continuous_sqrt.continuousAt.tendsto.comp hdiv).const_mul
      ((LΨ : ℝ) / ρ)
    simpa only [floor, Real.sqrt_zero, mul_zero, Function.comp_def] using hh
  have hdecay : Tendsto decay atTop (𝓝 0) := by
    simpa only [decay, mul_zero, zero_mul] using
      ((relaxation_tendsto_zero hρ).const_mul (Real.sqrt D.conditionNumber)).mul_const d0
  have hsum : Tendsto (fun p : ℕ × ℝ ↦ decay p.2 + floor p.1)
      (atTop ×ˢ atTop) (𝓝 0) := by
    simpa only [add_zero, Function.comp_def] using (hdecay.comp tendsto_snd).add (hfloor.comp tendsto_fst)
  apply squeeze_zero' (Eventually.of_forall fun p ↦ Real.sqrt_nonneg _) ?_ hsum
  filter_upwards [tendsto_snd.eventually (eventually_ge_atTop (0 : ℝ))] with p hp
  have hb := (family p.1).parameter_bound hProjection tests pairTests hmean sStar νStar
    hstationary hgradient hgradientZero hfix hpairQuad hρ hmono realize
    (Nat.succ_pos p.1) hV p.2 hp
  have hf : 0 ≤ floor p.1 := by dsimp [floor]; positivity
  have he : floor p.1 * (1 - Real.exp (-ρ * p.2)) ≤ floor p.1 := by
    nlinarith [Real.exp_pos (-ρ * p.2)]
  exact hb.trans (add_le_add (le_refl _) he)

end SourceParameterBound
end PBGSO
