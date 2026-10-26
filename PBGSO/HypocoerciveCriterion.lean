import PBGSO.ProjectedCriteria
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Explicit feasible hypocoercive coefficients

The strict source friction threshold is converted into concrete Young,
auxiliary, metric and decay constants. No coefficient feasibility or
positive-definiteness assertion is assumed. The forces need not be gradients.
-/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace NNReal
namespace PBGSO

def hypocoerciveYoung (γ r L : ℝ) : ℝ := (1 + 2 * L ^ 2 / (r * γ ^ 2)) / 2
def hypocoerciveAuxiliary (γ r L : ℝ) : ℝ := 1 - hypocoerciveYoung γ r L
def hypocoerciveLeakage (γ r L : ℝ) : ℝ := L ^ 2 / (hypocoerciveYoung γ r L * γ ^ 2)
def hypocoerciveRemainder (γ r L : ℝ) : ℝ := r - 2 * hypocoerciveLeakage γ r L
def hypocoerciveLower (γ : ℝ) : ℝ := min (γ / 4) (1 / (2 * γ))
def hypocoerciveUpper (γ : ℝ) : ℝ := γ + 1 + 2 / γ
def hypocoerciveRate (γ r L : ℝ) : ℝ :=
  min (hypocoerciveRemainder γ r L) (hypocoerciveAuxiliary γ r L) /
    hypocoerciveUpper γ

/-- The manuscript's displayed square-root friction condition implies
the polynomial threshold used by the coefficient proofs. -/
theorem hypocoercive_threshold_of_source (γ r L : ℝ) (hγ : 0 < γ) (hr : 0 < r)
    (hL : 0 ≤ L) (hsource : Real.sqrt 2 * L / Real.sqrt r < γ) :
    2 * L ^ 2 < r * γ ^ 2 := by
  have hs : Real.sqrt 2 * L < γ * Real.sqrt r :=
    (div_lt_iff₀ (Real.sqrt_pos.mpr hr)).mp hsource
  have hsq := (sq_lt_sq₀ (show 0 ≤ Real.sqrt 2 * L by positivity)
    (show 0 ≤ γ * Real.sqrt r by positivity)).mpr hs
  rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt hr.le] at hsq
  nlinarith

/-- The squared version of the exact source threshold produces an explicit
Young parameter strictly between zero and one. -/
theorem hypocoerciveYoung_bounds (γ r L : ℝ) (hγ : 0 < γ) (hr : 0 < r)
    (hthreshold : 2 * L ^ 2 < r * γ ^ 2) :
    0 < hypocoerciveYoung γ r L ∧ hypocoerciveYoung γ r L < 1 := by
  have hd : 0 < r * γ ^ 2 := by positivity
  have ha : 0 ≤ 2 * L ^ 2 / (r * γ ^ 2) := by positivity
  have hb : 2 * L ^ 2 / (r * γ ^ 2) < 1 := (div_lt_one hd).mpr hthreshold
  dsimp [hypocoerciveYoung]
  constructor <;> linarith

/-- Both auxiliary dissipation and the projected coefficient have strictly
positive room under the source threshold. -/
theorem hypocoercive_coefficients_positive (γ r L : ℝ) (hγ : 0 < γ) (hr : 0 < r)
    (hthreshold : 2 * L ^ 2 < r * γ ^ 2) :
    0 < hypocoerciveAuxiliary γ r L ∧ 0 < hypocoerciveRemainder γ r L := by
  obtain ⟨hη, hη1⟩ := hypocoerciveYoung_bounds γ r L hγ hr hthreshold
  refine ⟨sub_pos.mpr hη1, ?_⟩
  have hden : 0 < hypocoerciveYoung γ r L * γ ^ 2 := by positivity
  have hηid : hypocoerciveYoung γ r L * (r * γ ^ 2) =
      (r * γ ^ 2 + 2 * L ^ 2) / 2 := by
    unfold hypocoerciveYoung
    field_simp
    <;> ring
  have hdiv : 2 * L ^ 2 / (hypocoerciveYoung γ r L * γ ^ 2) < r := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  dsimp [hypocoerciveRemainder, hypocoerciveLeakage]
  rw [mul_div_assoc] at hdiv
  linarith

theorem hypocoerciveLower_pos (γ : ℝ) (hγ : 0 < γ) : 0 < hypocoerciveLower γ := by
  exact lt_min (by positivity) (by positivity)

theorem hypocoerciveUpper_pos (γ : ℝ) (hγ : 0 < γ) : 0 < hypocoerciveUpper γ := by
  dsimp [hypocoerciveUpper]
  positivity

theorem hypocoerciveRate_pos (γ r L : ℝ) (hγ : 0 < γ) (hr : 0 < r)
    (hthreshold : 2 * L ^ 2 < r * γ ^ 2) : 0 < hypocoerciveRate γ r L := by
  obtain ⟨ha, hc⟩ := hypocoercive_coefficients_positive γ r L hγ hr hthreshold
  exact div_pos (lt_min hc ha) (hypocoerciveUpper_pos γ hγ)

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A concrete lower norm constant for the source's actual twisted metric. -/
theorem hypocoerciveEnergy_lower (γ : ℝ) (hγ : 0 < γ) (q p : H) :
    hypocoerciveLower γ * (‖q‖ ^ 2 + ‖p‖ ^ 2) ≤ hypocoerciveEnergy γ q p := by
  have hy := force_cross_young 2 (3 * γ / 4) (by positivity) q p
  have hid : (2 : ℝ) ^ 2 / (4 * (3 * γ / 4)) = 4 / (3 * γ) := by
    field_simp
    <;> ring
  rw [hid] at hy
  have hpcoef : 1 / (2 * γ) ≤ 2 / γ - 4 / (3 * γ) := by
    have hid : 2 / γ - 4 / (3 * γ) - 1 / (2 * γ) = 1 / (6 * γ) := by
      field_simp
      <;> ring
    have : 0 ≤ 1 / (6 * γ) := by positivity
    linarith
  have hq := mul_le_mul_of_nonneg_right
    (min_le_left (γ / 4) (1 / (2 * γ))) (sq_nonneg ‖q‖)
  have hp := mul_le_mul_of_nonneg_right
    ((min_le_right (γ / 4) (1 / (2 * γ))).trans hpcoef) (sq_nonneg ‖p‖)
  dsimp [hypocoerciveLower, hypocoerciveEnergy] at *
  linarith

/-- Young's inequality gives exactly the separate U5 auxiliary estimate
with the explicitly chosen coefficients. -/
theorem hypocoercive_auxiliary_estimate (γ r L R : ℝ) (hγ : 0 < γ) (hr : 0 < r)
    (hthreshold : 2 * L ^ 2 < r * γ ^ 2) (q p f : H)
    (hforce : ‖f‖ ^ 2 ≤ L ^ 2 * R) :
    -⟪q, f⟫_ℝ - ‖p‖ ^ 2 - (2 / γ) * ⟪p, f⟫_ℝ ≤
      -⟪q, f⟫_ℝ - hypocoerciveAuxiliary γ r L * ‖p‖ ^ 2 +
        hypocoerciveLeakage γ r L * R := by
  have hη := (hypocoerciveYoung_bounds γ r L hγ hr hthreshold).1
  have hy := force_cross_young (2 / γ) (hypocoerciveYoung γ r L) hη p f
  have hcoef : (2 / γ) ^ 2 / (4 * hypocoerciveYoung γ r L) =
      1 / (hypocoerciveYoung γ r L * γ ^ 2) := by
    field_simp
    <;> ring
  rw [hcoef] at hy
  have hf := mul_le_mul_of_nonneg_left hforce
    (show 0 ≤ 1 / (hypocoerciveYoung γ r L * γ ^ 2) by positivity)
  have hid : 1 / (hypocoerciveYoung γ r L * γ ^ 2) * (L ^ 2 * R) =
      (L ^ 2 / (hypocoerciveYoung γ r L * γ ^ 2)) * R := by ring
  rw [hid] at hf
  dsimp [hypocoerciveAuxiliary, hypocoerciveLeakage]
  linarith

/-- A globally monotone and Lipschitz joint force has a completely explicit
positive hypocoercive contraction rate under the source friction threshold.
This is a deterministic drift estimate for the actual metric pairing. -/
theorem hypocoercive_dissipation_explicit (γ r L : ℝ) (hγ : 0 < γ) (hr : 0 < r)
    (hthreshold : 2 * L ^ 2 < r * γ ^ 2) (q p f : H)
    (hmono : r * ‖q‖ ^ 2 ≤ ⟪q, f⟫_ℝ)
    (hforce : ‖f‖ ^ 2 ≤ 2 * L ^ 2 * ‖q‖ ^ 2) :
    -⟪q, f⟫_ℝ - ‖p‖ ^ 2 - (2 / γ) * ⟪p, f⟫_ℝ ≤
      -hypocoerciveRate γ r L * hypocoerciveEnergy γ q p := by
  have hη := (hypocoerciveYoung_bounds γ r L hγ hr hthreshold).1
  have hρ := hypocoerciveRate_pos γ r L hγ hr hthreshold
  have hcoef : (2 / γ) ^ 2 / (4 * hypocoerciveYoung γ r L) =
      1 / (hypocoerciveYoung γ r L * γ ^ 2) := by field_simp <;> ring
  have hy := force_cross_young (2 / γ) (hypocoerciveYoung γ r L) hη p f
  rw [hcoef] at hy
  have hf := mul_le_mul_of_nonneg_left hforce
    (show 0 ≤ 1 / (hypocoerciveYoung γ r L * γ ^ 2) by positivity)
  have hcancel : hypocoerciveRate γ r L * hypocoerciveUpper γ =
      min (hypocoerciveRemainder γ r L) (hypocoerciveAuxiliary γ r L) :=
    div_mul_cancel₀ _ (ne_of_gt (hypocoerciveUpper_pos γ hγ))
  have hq := mul_le_mul_of_nonneg_right
    (min_le_left (hypocoerciveRemainder γ r L) (hypocoerciveAuxiliary γ r L))
    (sq_nonneg ‖q‖)
  have hp := mul_le_mul_of_nonneg_right
    (min_le_right (hypocoerciveRemainder γ r L) (hypocoerciveAuxiliary γ r L))
    (sq_nonneg ‖p‖)
  have hu := mul_le_mul_of_nonneg_left (hypocoerciveEnergy_upper γ hγ q p) hρ.le
  change hypocoerciveRate γ r L * hypocoerciveEnergy γ q p ≤
    hypocoerciveRate γ r L * (hypocoerciveUpper γ * (‖q‖ ^ 2 + ‖p‖ ^ 2)) at hu
  rw [← mul_assoc, hcancel] at hu
  dsimp [hypocoerciveRemainder, hypocoerciveAuxiliary, hypocoerciveLeakage] at hu hq hp
  have hid : 1 / (hypocoerciveYoung γ r L * γ ^ 2) * (2 * L ^ 2 * ‖q‖ ^ 2) =
      2 * (L ^ 2 / (hypocoerciveYoung γ r L * γ ^ 2)) * ‖q‖ ^ 2 := by ring
  rw [hid] at hf
  linarith

end Hilbert

/-- Euclidean product of position and momentum coordinates. -/
abbrev HypocoercivePhase (H : Type*) := WithLp 2 (H × H)

section Metric
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The actual source block matrix `[[gamma I,I],[I,2/gamma I]]`
as a bounded linear operator on the Hilbert phase space. -/
def hypocoerciveWeight (γ : ℝ) : HypocoercivePhase H →L[ℝ] HypocoercivePhase H :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ H H).symm.toContinuousLinearMap ∘L
    ((γ • (WithLp.fstL 2 ℝ H H) + WithLp.sndL 2 ℝ H H).prod
      (WithLp.fstL 2 ℝ H H + (2 / γ) • WithLp.sndL 2 ℝ H H))

@[simp] theorem hypocoerciveWeight_apply (γ : ℝ) (z : HypocoercivePhase H) :
    hypocoerciveWeight γ z = WithLp.toLp 2
      (γ • z.fst + z.snd, z.fst + (2 / γ) • z.snd) := rfl

theorem hypocoerciveWeight_pairing (γ : ℝ) (z : HypocoercivePhase H) :
    ⟪z, hypocoerciveWeight γ z⟫_ℝ = hypocoerciveEnergy γ z.fst z.snd := by
  simp only [hypocoerciveWeight_apply, WithLp.prod_inner_apply, WithLp.ofLp_toLp,
    WithLp.fst, WithLp.snd, inner_add_right, inner_smul_right, hypocoerciveEnergy,
    real_inner_self_eq_norm_sq]
  rw [real_inner_comm z.ofLp.2 z.ofLp.1]
  ring

theorem hypocoerciveWeight_symmetric (γ : ℝ) (z w : HypocoercivePhase H) :
    ⟪z, hypocoerciveWeight γ w⟫_ℝ = ⟪hypocoerciveWeight γ z, w⟫_ℝ := by
  simp only [hypocoerciveWeight_apply, WithLp.prod_inner_apply, WithLp.ofLp_toLp,
    WithLp.fst, WithLp.snd, inner_add_left, inner_add_right, real_inner_smul_left, inner_smul_right]
  ring

/-- Multiplication of the actual block operator by the actual heavy-ball
vector field gives the previously proved scalar pairing identity. -/
theorem hypocoerciveWeight_field_pairing (γ : ℝ) (hγ : γ ≠ 0) (q p f : H) :
    ⟪WithLp.toLp 2 (q, p), hypocoerciveWeight γ (WithLp.toLp 2 (p, -f - γ • p))⟫_ℝ =
      -⟪q, f⟫_ℝ - ‖p‖ ^ 2 - (2 / γ) * ⟪p, f⟫_ℝ := by
  simpa only [hypocoerciveWeight_apply, WithLp.prod_inner_apply, WithLp.fst, WithLp.snd,
    WithLp.ofLp_toLp]
    using hypocoercive_pairing γ hγ q p f

end Metric

/-- Both optimiser and sampler metrics are constructed explicitly, with
certified symmetry and quantitative positive definiteness. -/
def hypocoerciveGeometry {A Z : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    (γ : ℝ) (hγ : 0 < γ) :
    TwistedGeometry (HypocoercivePhase A) (HypocoercivePhase Z) where
  optimizerWeight := hypocoerciveWeight γ
  samplerWeight := hypocoerciveWeight γ
  lower := hypocoerciveLower γ
  upper := hypocoerciveUpper γ
  lower_pos := hypocoerciveLower_pos γ hγ
  lower_le_upper := by
    apply (min_le_left (γ / 4) (1 / (2 * γ))).trans
    dsimp [hypocoerciveUpper]
    have : 0 ≤ 2 / γ := by positivity
    linarith
  optimizer_symmetric := hypocoerciveWeight_symmetric γ
  sampler_symmetric := hypocoerciveWeight_symmetric γ
  optimizer_lower := by
    intro z
    rw [hypocoerciveWeight_pairing, WithLp.prod_norm_sq_eq_of_L2]
    exact hypocoerciveEnergy_lower γ hγ z.fst z.snd
  optimizer_upper := by
    intro z
    rw [hypocoerciveWeight_pairing, WithLp.prod_norm_sq_eq_of_L2]
    exact hypocoerciveEnergy_upper γ hγ z.fst z.snd
  sampler_lower := by
    intro z
    rw [hypocoerciveWeight_pairing, WithLp.prod_norm_sq_eq_of_L2]
    exact hypocoerciveEnergy_lower γ hγ z.fst z.snd
  sampler_upper := by
    intro z
    rw [hypocoerciveWeight_pairing, WithLp.prod_norm_sq_eq_of_L2]
    exact hypocoerciveEnergy_upper γ hγ z.fst z.snd

section Jensen
variable {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The square-norm Jensen inequality follows from integrating a
nonnegative squared distance. This supplies the optimiser-force estimate
from its actual Bochner expectation. -/
theorem integral_norm_sq_ge_norm_integral_sq (Q : Measure Ω) [IsProbabilityMeasure Q]
    (f : Ω → H) (hf : Integrable f Q) (hfsq : Integrable (fun ω => ‖f ω‖ ^ 2) Q) :
    ‖∫ ω, f ω ∂Q‖ ^ 2 ≤ ∫ ω, ‖f ω‖ ^ 2 ∂Q := by
  let m := ∫ ω, f ω ∂Q
  have hi : Integrable (fun ω => ⟪m, f ω⟫_ℝ) Q := hf.const_inner m
  have hsub : Integrable (fun ω => ‖f ω‖ ^ 2 - 2 * ⟪m, f ω⟫_ℝ) Q :=
    hfsq.sub (hi.const_mul 2)
  have hn : 0 ≤ ∫ ω, ‖f ω‖ ^ 2 - 2 * ⟪m, f ω⟫_ℝ + ‖m‖ ^ 2 ∂Q := by
    apply integral_nonneg
    intro ω
    have h := sq_nonneg ‖f ω - m‖
    rw [norm_sub_sq_real] at h
    have heq : ⟪f ω, m⟫_ℝ = ⟪m, f ω⟫_ℝ := real_inner_comm _ _
    rw [heq] at h
    exact h
  rw [integral_add hsub (integrable_const _),
    integral_sub hfsq (hi.const_mul 2), integral_const_mul, integral_inner hf m] at hn
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul,
    real_inner_self_eq_norm_sq] at hn
  change 0 ≤ (∫ ω, ‖f ω‖ ^ 2 ∂Q) - 2 * ⟪m, m⟫_ℝ + ‖m‖ ^ 2 at hn
  rw [real_inner_self_eq_norm_sq] at hn
  change ‖m‖ ^ 2 ≤ _
  linarith

end Jensen

section HeavyBall
variable {A X I : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [Fintype I]

/-- The actual unit-mass heavy-ball optimiser and underdamped sampler.
The observation and negative score are independent maps. Constant diffusion
is arbitrary, allowing the exact source column matrix as a special case. -/
def heavyBallModel (γ : ℝ) (F : A → X → A) (H : A → X → X)
    (σ : I → HypocoercivePhase X) :
    Model (HypocoercivePhase A) A (HypocoercivePhase X) X I where
  parameter := WithLp.fst
  position := WithLp.fst
  observation := F
  optimizer := fun _ s g => WithLp.toLp 2 (s.snd, -g - γ • s.snd)
  drift := fun θ z => WithLp.toLp 2 (z.snd, -H θ z.fst - γ • z.snd)
  diffusion := fun _ _ => σ

/-- The source position and momentum projections, with the explicitly
chosen positive auxiliary weights. -/
def heavyBallProjectedData (γ r L : ℝ) (F : A → X → A) (H : A → X → X)
    (σ : I → HypocoercivePhase X) :
    ProjectedData (U := A) (V := X) (heavyBallModel γ F H σ) where
  parameterProjection := WithLp.fstL 2 ℝ A A
  positionProjection := WithLp.fstL 2 ℝ X X
  optimizerAuxiliary := WithLp.sndL 2 ℝ A A
  samplerAuxiliary := WithLp.sndL 2 ℝ X X
  parameter_eq := rfl
  position_eq := rfl
  force := H
  optimizerAuxWeight := hypocoerciveAuxiliary γ r L • ContinuousLinearMap.id ℝ A
  samplerAuxWeight := hypocoerciveAuxiliary γ r L • ContinuousLinearMap.id ℝ X

/-- The optimiser vector-field difference really is the heavy-ball block
applied to the state and actual mean-gradient differences. -/
theorem heavyBall_optimizerField_difference (γ : ℝ) (F : A → X → A) (H : A → X → X)
    (σ : I → HypocoercivePhase X) (t : ℝ) (s s' : HypocoercivePhase A)
    (ν ν' : Measure (HypocoercivePhase X)) :
    (heavyBallModel γ F H σ).optimizerField t s ν -
      (heavyBallModel γ F H σ).optimizerField t s' ν' =
    WithLp.toLp 2 ((s - s').snd,
      -((heavyBallModel γ F H σ).meanGradient ν s -
        (heavyBallModel γ F H σ).meanGradient ν' s') - γ • (s - s').snd) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · rfl
  · simp only [Model.optimizerField, heavyBallModel, WithLp.ofLp_sub,
      WithLp.ofLp_toLp, Prod.snd_sub, WithLp.sub_snd]
    module

/-- The sampler difference is the corresponding negative-score heavy-ball
block, without any conservative-potential assumption. -/
theorem heavyBall_drift_difference (γ : ℝ) (F : A → X → A) (H : A → X → X)
    (σ : I → HypocoercivePhase X) (θ θ' : A) (z z' : HypocoercivePhase X) :
    (heavyBallModel γ F H σ).drift θ z - (heavyBallModel γ F H σ).drift θ' z' =
    WithLp.toLp 2 ((z - z').snd, -(H θ z.fst - H θ' z'.fst) - γ • (z - z').snd) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · rfl
  · simp only [heavyBallModel, WithLp.ofLp_sub, WithLp.ofLp_toLp,
      Prod.snd_sub, WithLp.sub_snd]
    module

/-- The joint Lipschitz bound gives the Jensen estimate for the *actual*
mean-gradient difference through every coupling of the sampler laws. -/
theorem heavyBall_meanGradient_norm_sq_bound (γ r L : ℝ)
    (F : A → X → A) (H : A → X → X) (σ : I → HypocoercivePhase X)
    (hF : ∀ θ θ' x x', ‖F θ x - F θ' x'‖ ^ 2 ≤
      L ^ 2 * (‖θ - θ'‖ ^ 2 + ‖x - x'‖ ^ 2))
    (s s' : HypocoercivePhase A)
    {ν ν' : Measure (HypocoercivePhase X)} {Λ : Measure (HypocoercivePhase X × HypocoercivePhase X)}
    (hΛ : IsCoupling Λ ν ν') [IsProbabilityMeasure ν]
    (hf : Integrable (fun z => F s.fst z.fst) ν)
    (hg : Integrable (fun z => F s'.fst z.fst) ν')
    (hInt : (heavyBallProjectedData γ r L F H σ).Integrability s s' Λ) :
    ‖(heavyBallModel γ F H σ).meanGradient ν s -
        (heavyBallModel γ F H σ).meanGradient ν' s'‖ ^ 2 ≤
      L ^ 2 * (heavyBallProjectedData γ r L F H σ).radius s s' Λ := by
  letI : IsProbabilityMeasure (Λ.map Prod.fst) := hΛ.1.symm ▸ inferInstance
  letI : IsProbabilityMeasure Λ :=
    (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mp inferInstance
  have hfΛ : Integrable (fun zz : HypocoercivePhase X × HypocoercivePhase X =>
      F s.fst zz.1.fst) Λ := (hΛ.1.symm ▸ hf).comp_measurable measurable_fst
  have hgΛ : Integrable (fun zz : HypocoercivePhase X × HypocoercivePhase X =>
      F s'.fst zz.2.fst) Λ := (hΛ.2.symm ▸ hg).comp_measurable measurable_snd
  have hobs : Integrable (fun zz : HypocoercivePhase X × HypocoercivePhase X =>
      F s.fst zz.1.fst - F s'.fst zz.2.fst) Λ := hfΛ.sub hgΛ
  have hpos : Integrable (fun zz : HypocoercivePhase X × HypocoercivePhase X =>
      ‖zz.1.fst - zz.2.fst‖ ^ 2) Λ := by
    simpa [heavyBallProjectedData] using hInt.position_sq
  have hbound : Integrable (fun zz : HypocoercivePhase X × HypocoercivePhase X =>
      L ^ 2 * (‖s.fst - s'.fst‖ ^ 2 + ‖zz.1.fst - zz.2.fst‖ ^ 2)) Λ :=
    ((integrable_const _).add hpos).const_mul _
  have hsq : Integrable (fun zz : HypocoercivePhase X × HypocoercivePhase X =>
      ‖F s.fst zz.1.fst - F s'.fst zz.2.fst‖ ^ 2) Λ := by
    apply hbound.mono' (hobs.aestronglyMeasurable.norm.pow 2)
    exact Filter.Eventually.of_forall (fun zz => by
      simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_sq] using
        hF s.fst s'.fst zz.1.fst zz.2.fst)
  rw [meanGradient_difference_of_coupling _ s s' hΛ hf hg]
  have hj := integral_norm_sq_ge_norm_integral_sq Λ _ hobs hsq
  have hb := integral_mono hsq hbound (fun zz => hF s.fst s'.fst zz.1.fst zz.2.fst)
  apply hj.trans
  convert hb using 1
  simp [ProjectedData.radius, heavyBallProjectedData,
    integral_const_mul, integral_add (integrable_const _) hpos]

theorem heavyBall_auxiliary_dissipation (γ r L : ℝ) (hγ : 0 < γ) (hr : 0 < r)
    (hthreshold : 2 * L ^ 2 < r * γ ^ 2)
    (F : A → X → A) (H : A → X → X) (σ : I → HypocoercivePhase X)
    (hF : ∀ θ θ' x x', ‖F θ x - F θ' x'‖ ^ 2 ≤
      L ^ 2 * (‖θ - θ'‖ ^ 2 + ‖x - x'‖ ^ 2))
    (hH : ∀ θ θ' x x', ‖H θ x - H θ' x'‖ ^ 2 ≤
      L ^ 2 * (‖θ - θ'‖ ^ 2 + ‖x - x'‖ ^ 2))
    (hInt : ∀ s s' ν ν' Λ,
      ProjectedAdmissibleCoupling (heavyBallModel γ F H σ) (hypocoerciveGeometry γ hγ)
        s s' ν ν' Λ → (heavyBallProjectedData γ r L F H σ).Integrability s s' Λ) :
    ProjectedAuxiliaryDissipation (heavyBallModel γ F H σ) (hypocoerciveGeometry γ hγ)
      (heavyBallProjectedData γ r L F H σ) 1
      (hypocoerciveLeakage γ r L) (hypocoerciveLeakage γ r L) := by
  let M := heavyBallModel γ F H σ
  let C := heavyBallProjectedData γ r L F H σ
  let D := hypocoerciveGeometry (A := A) (Z := X) γ hγ
  constructor
  · intro t ht s s' ν ν' Λ ha
    letI := ha.left_probability
    have hf := heavyBall_meanGradient_norm_sq_bound γ r L F H σ hF s s'
      ha.coupling ha.left_observation ha.right_observation (hInt s s' ν ν' Λ ha)
    have hp := hypocoercive_auxiliary_estimate γ r L (C.radius s s' Λ) hγ hr hthreshold
      (s - s').fst (s - s').snd (M.meanGradient ν s - M.meanGradient ν' s') hf
    rw [heavyBall_optimizerField_difference]
    change ⟪s - s', hypocoerciveWeight γ (WithLp.toLp 2 _)⟫_ℝ ≤ _
    have hs : s - s' = WithLp.toLp 2 ((s - s').fst, (s - s').snd) := rfl
    conv_lhs => rw [hs]
    simp only [WithLp.toLp_snd, WithLp.toLp_fst]
    rw [hypocoerciveWeight_field_pairing γ (ne_of_gt hγ)]
    simpa [C, M, ProjectedData.optimizerProjectedWork, ProjectedData.optimizerAuxSq,
      heavyBallProjectedData, real_inner_smul_right, real_inner_self_eq_norm_sq] using hp
  · intro s s' ν ν' Λ ha
    letI := ha.left_probability
    letI : IsProbabilityMeasure (Λ.map Prod.fst) := ha.coupling.1.symm ▸ inferInstance
    letI : IsProbabilityMeasure Λ :=
      (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mp inferInstance
    have hI := hInt s s' ν ν' Λ ha
    have hdrift : Integrable (samplerDriftWork M D s s') Λ := by
      rw [← samplerCouplingWork_eq_drift_of_constant M D σ (fun _ _ => rfl)]
      exact ha.sampler_work
    have hradius : Integrable (fun zz : HypocoercivePhase X × HypocoercivePhase X =>
        ‖(s - s').fst‖ ^ 2 + ‖(zz.1 - zz.2).fst‖ ^ 2) Λ := by
      simpa [C, heavyBallProjectedData] using
        (integrable_const (‖(s - s').fst‖ ^ 2)).add hI.position_sq
    have hright : Integrable (fun zz => -C.scoreWork s s' zz - C.samplerAuxSq zz +
        hypocoerciveLeakage γ r L *
          (‖(s - s').fst‖ ^ 2 + ‖(zz.1 - zz.2).fst‖ ^ 2)) Λ :=
      (hI.score_work.neg.sub hI.auxiliary_sq).add (hradius.const_mul _)
    have hb := integral_mono hdrift hright (fun zz => ?_)
    · have hsub : Integrable (fun zz => -C.scoreWork s s' zz - C.samplerAuxSq zz) Λ :=
        hI.score_work.neg.sub hI.auxiliary_sq
      have hneg : Integrable (fun zz => -C.scoreWork s s' zz) Λ := hI.score_work.neg
      have hpos : Integrable (fun zz : HypocoercivePhase X × HypocoercivePhase X =>
          ‖(zz.1 - zz.2).fst‖ ^ 2) Λ := by
        simpa [C, heavyBallProjectedData] using hI.position_sq
      rw [integral_add hsub (hradius.const_mul _),
        integral_sub hneg hI.auxiliary_sq, integral_neg, integral_const_mul,
        integral_add (integrable_const _) hpos] at hb
      simpa [C, ProjectedData.radius, heavyBallProjectedData] using hb
    · change ⟪zz.1 - zz.2, hypocoerciveWeight γ
        (M.drift s.fst zz.1 - M.drift s'.fst zz.2)⟫_ℝ ≤ _
      rw [heavyBall_drift_difference]
      have hz : zz.1 - zz.2 = WithLp.toLp 2 ((zz.1 - zz.2).fst, (zz.1 - zz.2).snd) := rfl
      conv_lhs => rw [hz]
      simp only [WithLp.toLp_snd, WithLp.toLp_fst]
      rw [hypocoerciveWeight_field_pairing γ (ne_of_gt hγ)]
      have hp := hypocoercive_auxiliary_estimate γ r L
        (‖s.fst - s'.fst‖ ^ 2 + ‖zz.1.fst - zz.2.fst‖ ^ 2) hγ hr hthreshold
        (zz.1 - zz.2).fst (zz.1 - zz.2).snd (H s.fst zz.1.fst - H s'.fst zz.2.fst)
        (hH s.fst s'.fst zz.1.fst zz.2.fst)
      simpa [C, ProjectedData.scoreWork, ProjectedData.samplerAuxSq,
        heavyBallProjectedData, M, heavyBallModel, real_inner_smul_right,
        real_inner_self_eq_norm_sq] using hp

/-- The full source hypocoercive criterion for the actual heavy-ball
optimiser and underdamped sampler. The two component Lipschitz bounds are
primitive projected-field bounds; all U5 constants, metric definiteness and
the positive decay rate are derived. The remaining explicit analytic input
is integrability of the coupling score/auxiliary expressions. -/
theorem heavyBall_twistedJointMonotonicity (γ r L : ℝ) (hγ : 0 < γ) (hr : 0 < r)
    (hthreshold : 2 * L ^ 2 < r * γ ^ 2)
    (F : A → X → A) (H : A → X → X) (σ : I → HypocoercivePhase X)
    (hmono : ∀ θ θ' x x', r * (‖θ - θ'‖ ^ 2 + ‖x - x'‖ ^ 2) ≤
      ⟪θ - θ', F θ x - F θ' x'⟫_ℝ + ⟪x - x', H θ x - H θ' x'⟫_ℝ)
    (hF : ∀ θ θ' x x', ‖F θ x - F θ' x'‖ ^ 2 ≤
      L ^ 2 * (‖θ - θ'‖ ^ 2 + ‖x - x'‖ ^ 2))
    (hH : ∀ θ θ' x x', ‖H θ x - H θ' x'‖ ^ 2 ≤
      L ^ 2 * (‖θ - θ'‖ ^ 2 + ‖x - x'‖ ^ 2))
    (hInt : ∀ s s' ν ν' Λ,
      ProjectedAdmissibleCoupling (heavyBallModel γ F H σ) (hypocoerciveGeometry γ hγ)
        s s' ν ν' Λ → (heavyBallProjectedData γ r L F H σ).Integrability s s' Λ) :
    0 < hypocoerciveRate γ r L ∧
      TwistedJointMonotonicity (heavyBallModel γ F H σ) (hypocoerciveGeometry γ hγ)
        (hypocoerciveRate γ r L) := by
  let M := heavyBallModel γ F H σ
  let C := heavyBallProjectedData γ r L F H σ
  let D := hypocoerciveGeometry (A := A) (Z := X) γ hγ
  obtain ⟨ha, hc⟩ := hypocoercive_coefficients_positive γ r L hγ hr hthreshold
  have hcEq : 1 * r - hypocoerciveLeakage γ r L - hypocoerciveLeakage γ r L =
      hypocoerciveRemainder γ r L := by dsimp [hypocoerciveRemainder]; ring
  have hmonoC : C.StrongMonotonicity r := hmono
  have haux := heavyBall_auxiliary_dissipation γ r L hγ hr hthreshold F H σ hF hH hInt
  have hcert := projected_twistedJointMonotonicity_certified M D C 1 r
    (hypocoerciveLeakage γ r L) (hypocoerciveLeakage γ r L)
    (hypocoerciveAuxiliary γ r L) (hypocoerciveAuxiliary γ r L) (by norm_num)
    (hcEq.symm ▸ hc) ha ha hmonoC haux σ (fun _ _ => rfl) hInt
    (fun d => WithLp.prod_norm_sq_eq_of_L2 d)
    (fun d => WithLp.prod_norm_sq_eq_of_L2 d)
    (fun d => by simp [C, heavyBallProjectedData, ProjectedData.optimizerAuxSq,
      real_inner_smul_right, real_inner_self_eq_norm_sq])
    (fun zz => by simp [C, heavyBallProjectedData, ProjectedData.samplerAuxSq,
      real_inner_smul_right, real_inner_self_eq_norm_sq])
  dsimp only at hcert
  rw [hcEq] at hcert
  simpa only [projectedCertifiedRate, min_self, hypocoerciveRate, M, D,
    hypocoerciveGeometry] using hcert

/-- In the globally Lipschitz heavy-ball example the integrability needed
by the general projected criterion is itself a theorem. The supplied
coupling energy controls both position and momentum squares; Young's
inequality then controls the score work. -/
theorem heavyBall_projected_integrability (γ r L : ℝ) (hγ : 0 < γ)
    (F : A → X → A) (H : A → X → X) (σ : I → HypocoercivePhase X)
    (hH : ∀ θ θ' x x', ‖H θ x - H θ' x'‖ ^ 2 ≤
      L ^ 2 * (‖θ - θ'‖ ^ 2 + ‖x - x'‖ ^ 2))
    (s s' : HypocoercivePhase A)
    (ν ν' : Measure (HypocoercivePhase X))
    (Λ : Measure (HypocoercivePhase X × HypocoercivePhase X))
    (ha : ProjectedAdmissibleCoupling (heavyBallModel γ F H σ) (hypocoerciveGeometry γ hγ)
      s s' ν ν' Λ) :
    (heavyBallProjectedData γ r L F H σ).Integrability s s' Λ := by
  let C := heavyBallProjectedData γ r L F H σ
  let D := hypocoerciveGeometry (A := A) (Z := X) γ hγ
  letI := ha.left_probability
  letI : IsProbabilityMeasure (Λ.map Prod.fst) := ha.coupling.1.symm ▸ inferInstance
  letI : IsProbabilityMeasure Λ :=
    (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mp inferInstance
  have hd : Continuous (fun zz : HypocoercivePhase X × HypocoercivePhase X => zz.1 - zz.2) :=
    continuous_fst.sub continuous_snd
  have hnorm : Integrable (fun zz : HypocoercivePhase X × HypocoercivePhase X =>
      ‖zz.1 - zz.2‖ ^ 2) Λ := by
    apply (ha.sampler_sq.const_mul D.lower⁻¹).mono' (hd.norm.pow 2).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro zz
    rw [Pi.pow_apply, Real.norm_eq_abs, abs_sq]
    have hl := D.sampler_lower (zz.1 - zz.2)
    have hh : ‖zz.1 - zz.2‖ ^ 2 ≤ D.samplerSq (zz.1 - zz.2) / D.lower :=
      (le_div_iff₀ D.lower_pos).mpr (by simpa [TwistedGeometry.samplerSq, mul_comm] using hl)
    simpa only [div_eq_mul_inv, mul_comm] using hh
  have hfst : Continuous (fun z : HypocoercivePhase X => z.fst) := WithLp.continuous_fst 2 X X
  have hsnd : Continuous (fun z : HypocoercivePhase X => z.snd) := WithLp.continuous_snd 2 X X
  have hqcont := (hfst.comp hd).norm.pow 2
  have hpcont := (hsnd.comp hd).norm.pow 2
  have hq : Integrable (fun zz : HypocoercivePhase X × HypocoercivePhase X =>
      ‖(zz.1 - zz.2).fst‖ ^ 2) Λ := by
    apply hnorm.mono' hqcont.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro zz
    rw [Pi.pow_apply, Function.comp_apply, Real.norm_eq_abs, abs_sq, WithLp.prod_norm_sq_eq_of_L2]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hp : Integrable (fun zz : HypocoercivePhase X × HypocoercivePhase X =>
      ‖(zz.1 - zz.2).snd‖ ^ 2) Λ := by
    apply hnorm.mono' hpcont.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro zz
    rw [Pi.pow_apply, Function.comp_apply, Real.norm_eq_abs, abs_sq, WithLp.prod_norm_sq_eq_of_L2]
    exact le_add_of_nonneg_left (sq_nonneg _)
  have hHlip (θ : A) : LipschitzWith ⟨|L|, abs_nonneg L⟩ (H θ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_eq_norm, NNReal.coe_mk]
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (abs_nonneg _) (norm_nonneg _))).mp
    simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add,
      mul_pow, sq_abs] using hH θ θ x y
  have hqmap : Continuous (fun zz : HypocoercivePhase X × HypocoercivePhase X =>
      (zz.1 - zz.2).fst) := hfst.comp hd
  have hforce : Continuous (fun zz : HypocoercivePhase X × HypocoercivePhase X =>
      H s.fst zz.1.fst - H s'.fst zz.2.fst) :=
    ((hHlip s.fst).continuous.comp (hfst.comp continuous_fst)).sub
      ((hHlip s'.fst).continuous.comp (hfst.comp continuous_snd))
  have hscore : Continuous (C.scoreWork s s') := by
    change Continuous (fun zz : HypocoercivePhase X × HypocoercivePhase X =>
      ⟪(zz.1 - zz.2).fst, H s.fst zz.1.fst - H s'.fst zz.2.fst⟫_ℝ)
    exact hqmap.inner hforce
  have hbound : Integrable (fun zz : HypocoercivePhase X × HypocoercivePhase X =>
      (1 / 2 : ℝ) * (‖(zz.1 - zz.2).fst‖ ^ 2 +
        L ^ 2 * (‖s.fst - s'.fst‖ ^ 2 + ‖(zz.1 - zz.2).fst‖ ^ 2))) Λ :=
    (hq.add (((integrable_const (‖s.fst - s'.fst‖ ^ 2)).add hq).const_mul (L ^ 2))).const_mul _
  have hscoreInt : Integrable (C.scoreWork s s') Λ := by
    apply hbound.mono' hscore.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro zz
    change ‖⟪(zz.1 - zz.2).fst, H s.fst zz.1.fst - H s'.fst zz.2.fst⟫_ℝ‖ ≤ _
    have hf : ‖H s.fst zz.1.fst - H s'.fst zz.2.fst‖ ^ 2 ≤
        L ^ 2 * (‖s.fst - s'.fst‖ ^ 2 + ‖(zz.1 - zz.2).fst‖ ^ 2) := by
      simpa only [WithLp.sub_fst] using hH s.fst s'.fst zz.1.fst zz.2.fst
    have hi := norm_inner_le_norm (𝕜 := ℝ) (zz.1 - zz.2).fst
      (H s.fst zz.1.fst - H s'.fst zz.2.fst)
    have hy := sq_nonneg (‖(zz.1 - zz.2).fst‖ - ‖H s.fst zz.1.fst - H s'.fst zz.2.fst‖)
    nlinarith
  refine ⟨?_, hscoreInt, ?_⟩
  · simpa only [C, heavyBallProjectedData, WithLp.fstL_apply] using hq
  · have heq : C.samplerAuxSq = (fun zz : HypocoercivePhase X × HypocoercivePhase X =>
        hypocoerciveAuxiliary γ r L * ‖(zz.1 - zz.2).snd‖ ^ 2) := by
      funext zz
      simp [C, ProjectedData.samplerAuxSq, heavyBallProjectedData,
        real_inner_smul_right, real_inner_self_eq_norm_sq]
    change Integrable C.samplerAuxSq Λ
    rw [heq]
    exact hp.const_mul (hypocoerciveAuxiliary γ r L)

/-- End-to-end verification of the source hypocoercive *criterion*, from
pointwise projected monotonicity, joint force bounds and the displayed
friction threshold. No U5, metric, rate-feasibility, Jensen, coupling-gradient
or score-integrability conclusion is assumed in this theorem. This remains
an algebraic/law criterion, separate from an SDE existence or Itô theorem. -/
theorem heavyBall_twistedJointMonotonicity_of_source (γ r L : ℝ)
    (hγ : 0 < γ) (hr : 0 < r) (hL : 0 ≤ L)
    (hsource : Real.sqrt 2 * L / Real.sqrt r < γ)
    (F : A → X → A) (H : A → X → X) (σ : I → HypocoercivePhase X)
    (hmono : ∀ θ θ' x x', r * (‖θ - θ'‖ ^ 2 + ‖x - x'‖ ^ 2) ≤
      ⟪θ - θ', F θ x - F θ' x'⟫_ℝ + ⟪x - x', H θ x - H θ' x'⟫_ℝ)
    (hF : ∀ θ θ' x x', ‖F θ x - F θ' x'‖ ^ 2 ≤
      L ^ 2 * (‖θ - θ'‖ ^ 2 + ‖x - x'‖ ^ 2))
    (hH : ∀ θ θ' x x', ‖H θ x - H θ' x'‖ ^ 2 ≤
      L ^ 2 * (‖θ - θ'‖ ^ 2 + ‖x - x'‖ ^ 2)) :
    0 < hypocoerciveRate γ r L ∧
      TwistedJointMonotonicity (heavyBallModel γ F H σ) (hypocoerciveGeometry γ hγ)
        (hypocoerciveRate γ r L) := by
  exact heavyBall_twistedJointMonotonicity γ r L hγ hr
    (hypocoercive_threshold_of_source γ r L hγ hr hL hsource) F H σ hmono hF hH
    (heavyBall_projected_integrability γ r L hγ F H σ hH)

/-- The source projected field, as an actual map of the Hilbert product. -/
def heavyBallProjectedField (F : A → X → A) (H : A → X → X)
    (q : WithLp 2 (A × X)) : WithLp 2 (A × X) :=
  WithLp.toLp 2 (F q.fst q.snd, H q.fst q.snd)

/-- A Lipschitz bound for the complete projected field yields the component
square bounds used in the preceding theorem. -/
theorem heavyBallProjectedField_component_bounds (F : A → X → A) (H : A → X → X)
    (L : ℝ≥0) (hLip : LipschitzWith L (heavyBallProjectedField F H))
    (θ θ' : A) (x x' : X) :
    (‖F θ x - F θ' x'‖ ^ 2 ≤ (L : ℝ) ^ 2 * (‖θ - θ'‖ ^ 2 + ‖x - x'‖ ^ 2)) ∧
    (‖H θ x - H θ' x'‖ ^ 2 ≤ (L : ℝ) ^ 2 * (‖θ - θ'‖ ^ 2 + ‖x - x'‖ ^ 2)) := by
  have hn := hLip.norm_sub_le (WithLp.toLp 2 (θ, x)) (WithLp.toLp 2 (θ', x'))
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg L.coe_nonneg (norm_nonneg _))).mpr hn
  simp only [mul_pow, WithLp.prod_norm_sq_eq_of_L2, WithLp.sub_fst,
    WithLp.sub_snd, heavyBallProjectedField, WithLp.toLp_fst, WithLp.toLp_snd] at hs
  exact ⟨(le_add_of_nonneg_right (sq_nonneg _)).trans hs,
    (le_add_of_nonneg_left (sq_nonneg _)).trans hs⟩

/-- The appendix hypocoercive proposition with its original joint
Lipschitz hypothesis and square-root friction threshold, with an explicit
metric and positive rate. Constant sampler diffusion is arbitrary. -/
theorem heavyBall_source_criterion (γ r : ℝ) (L : ℝ≥0)
    (hγ : 0 < γ) (hr : 0 < r)
    (hsource : Real.sqrt 2 * (L : ℝ) / Real.sqrt r < γ)
    (F : A → X → A) (H : A → X → X) (σ : I → HypocoercivePhase X)
    (hmono : ∀ θ θ' x x', r * (‖θ - θ'‖ ^ 2 + ‖x - x'‖ ^ 2) ≤
      ⟪θ - θ', F θ x - F θ' x'⟫_ℝ + ⟪x - x', H θ x - H θ' x'⟫_ℝ)
    (hLip : LipschitzWith L (heavyBallProjectedField F H)) :
    0 < hypocoerciveRate γ r L ∧
      TwistedJointMonotonicity (heavyBallModel γ F H σ) (hypocoerciveGeometry γ hγ)
        (hypocoerciveRate γ r L) := by
  exact heavyBall_twistedJointMonotonicity_of_source γ r L hγ hr L.coe_nonneg hsource
    F H σ hmono
    (fun θ θ' x x' => (heavyBallProjectedField_component_bounds F H L hLip θ θ' x x').1)
    (fun θ θ' x x' => (heavyBallProjectedField_component_bounds F H L hLip θ θ' x x').2)

end HeavyBall
end PBGSO
