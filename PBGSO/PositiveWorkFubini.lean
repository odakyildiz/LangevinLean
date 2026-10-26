import PBGSO.IntegralQuadraticEnergy
import Mathlib.MeasureTheory.Integral.Prod

/-! # Expected quadratic balance from positive work alone
Actual pathwise finite-variation equations give a quadratic identity. Its
nonnegative terminal energy bounds negative work by positive work plus the
initial energy. Thus product-integrable positive work suffices for full
Fubini and expected balance, without square-integrable total variation,
time-L¹(L²) drift, or an endpoint uniform-integrability premise.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.PositiveWorkFubini
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Actual pathwise quadratic FTC for a continuous primitive with merely
Bochner-integrable drift. The identity is proved rather than assumed. -/
theorem path_quadratic (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ x y, B x y = B y x)
    (T : ℝ≥0) (x b : ℝ → E) (hx : ContinuousOn x (Icc 0 (T : ℝ)))
    (hb : IntervalIntegrable b volume 0 (T : ℝ))
    (heq : ∀ r ∈ Icc 0 (T : ℝ), x r = x 0 + ∫ s in 0..r, b s) :
    B (x T) (x T) = B (x 0) (x 0) + 2 * ∫ r in 0..(T : ℝ), B (x r) (b r) := by
  have h := IntegralQuadraticEnergy.quadratic_balance B hB x b (fun _ => 0) (fun _ => 0)
    T.coe_nonneg hb (by simpa using (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 (T : ℝ))) hx
    (fun r hr => by simpa only [add_zero] using heq r hr)
    (by simp) (fun _ _ => by simp) (by simp)
  simpa only [add_zero, intervalIntegral.integral_const_mul] using h

private theorem abs_eq_two_pos_sub (r : ℝ) : ‖r‖ = 2 * max r 0 - r := by
  by_cases hr : 0 ≤ r
  · rw [max_eq_left hr, Real.norm_of_nonneg hr]
    ring
  · have hr' := le_of_lt (lt_of_not_ge hr)
    rw [max_eq_right hr', Real.norm_of_nonpos hr']
    ring

variable {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [SFinite Q]

/-- Positive work and the actual primitive equation control the full expected
absolute work. No expected-energy equation is supplied as a premise. -/
theorem work_integrable (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ x y, B x y = B y x) (hpos : ∀ x, 0 ≤ B x x)
    (T : ℝ≥0) (x b : ℝ → Ω → E)
    (hx : StronglyMeasurable (Function.uncurry x))
    (hb : StronglyMeasurable (Function.uncurry b))
    (hpath : ∀ᵐ ω ∂Q, ContinuousOn (fun r => x r ω) (Icc 0 (T : ℝ)) ∧
      IntervalIntegrable (fun r => b r ω) volume 0 (T : ℝ) ∧
      ∀ r ∈ Icc 0 (T : ℝ), x r ω = x 0 ω + ∫ s in 0..r, b s ω)
    (hzero : Integrable (fun ω => B (x 0 ω) (x 0 ω)) Q)
    (hp : Integrable (fun p : ℝ × Ω => max (B (x p.1 p.2) (b p.1 p.2)) 0)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) :
    Integrable (fun p : ℝ × Ω => B (x p.1 p.2) (b p.1 p.2))
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := by
  let w : ℝ × Ω → ℝ := fun p => B (x p.1 p.2) (b p.1 p.2)
  have hw : StronglyMeasurable w := B.continuous₂.comp_stronglyMeasurable (hx.prodMk hb)
  have hsection : ∀ᵐ ω ∂Q, Integrable (fun r => w (r,ω)) (volume.restrict (Ioc 0 (T : ℝ))) := by
    filter_upwards [hpath] with ω hω
    have hi := IntegralQuadraticEnergy.bilinear_continuous_integrable B
      (fun r => x r ω) (fun r => b r ω) (by simpa only [uIcc_of_le T.coe_nonneg] using hω.1) hω.2.1
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mp hi
  apply (integrable_prod_iff' hw.aestronglyMeasurable).mpr
  refine ⟨hsection, ?_⟩
  apply ((hp.integral_prod_right.const_mul 2).add hzero).mono'
    hw.norm.integral_prod_left'.aestronglyMeasurable
  filter_upwards [hpath, hsection, hp.prod_left_ae] with ω hω hi hpi
  rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  have habs : (∫ r in Ioc 0 (T : ℝ), ‖w (r,ω)‖) =
      2 * (∫ r in Ioc 0 (T : ℝ), max (w (r,ω)) 0) -
        ∫ r in Ioc 0 (T : ℝ), w (r,ω) := by
    simp_rw [abs_eq_two_pos_sub]
    rw [integral_sub (hpi.const_mul 2) hi, integral_const_mul]
  rw [habs]
  have he := path_quadratic B hB T (fun r => x r ω) (fun r => b r ω)
    hω.1 hω.2.1 hω.2.2
  rw [intervalIntegral.integral_of_le T.coe_nonneg] at he
  change B (x T ω) (x T ω) = B (x 0 ω) (x 0 ω) +
    2 * ∫ r in Ioc 0 (T : ℝ), w (r,ω) at he
  have ht := hpos (x T ω)
  have hz := hpos (x 0 ω)
  change 2 * _ - _ ≤ 2 * _ + B (x 0 ω) (x 0 ω)
  linarith

/-- Full product integrability, terminal quadratic integrability and exact
expected balance follow from the actual raw primitive and positive work. -/
theorem expected_quadratic_balance (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ x y, B x y = B y x) (hpos : ∀ x, 0 ≤ B x x)
    (T : ℝ≥0) (x b : ℝ → Ω → E)
    (hx : StronglyMeasurable (Function.uncurry x))
    (hb : StronglyMeasurable (Function.uncurry b))
    (hpath : ∀ᵐ ω ∂Q, ContinuousOn (fun r => x r ω) (Icc 0 (T : ℝ)) ∧
      IntervalIntegrable (fun r => b r ω) volume 0 (T : ℝ) ∧
      ∀ r ∈ Icc 0 (T : ℝ), x r ω = x 0 ω + ∫ s in 0..r, b s ω)
    (hzero : Integrable (fun ω => B (x 0 ω) (x 0 ω)) Q)
    (hp : Integrable (fun p : ℝ × Ω => max (B (x p.1 p.2) (b p.1 p.2)) 0)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) :
    Integrable (fun p : ℝ × Ω => B (x p.1 p.2) (b p.1 p.2))
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) ∧
    Integrable (fun ω => B (x T ω) (x T ω)) Q ∧
    (∫ ω, B (x T ω) (x T ω) ∂Q) = (∫ ω, B (x 0 ω) (x 0 ω) ∂Q) +
      2 * ∫ r in Ioc 0 (T : ℝ), ∫ ω, B (x r ω) (b r ω) ∂Q := by
  have hw := work_integrable Q B hB hpos T x b hx hb hpath hzero hp
  have he : (fun ω => B (x T ω) (x T ω)) =ᵐ[Q]
      (fun ω => B (x 0 ω) (x 0 ω) + 2 * ∫ r in Ioc 0 (T : ℝ), B (x r ω) (b r ω)) := by
    filter_upwards [hpath] with ω hω
    simpa only [intervalIntegral.integral_of_le T.coe_nonneg] using
      path_quadratic B hB T (fun r => x r ω) (fun r => b r ω) hω.1 hω.2.1 hω.2.2
  have hright := hzero.add (hw.integral_prod_right.const_mul 2)
  refine ⟨hw, hright.congr he.symm, ?_⟩
  rw [integral_congr_ae he, integral_add hzero (hw.integral_prod_right.const_mul 2), integral_const_mul,
    integral_integral_swap (μ := volume.restrict (Ioc 0 (T : ℝ))) (ν := Q)
      (f := fun r ω => B (x r ω) (b r ω)) hw]

/-- Constant-input cancellation leaves a raw finite-variation pair. Positive
work and the original full-law work inequality then give exponential expected
energy decay. The energy identity and time absolute continuity are conclusions. -/
theorem expected_energy_decay (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ x y, B x y = B y x) (hpos : ∀ x, 0 ≤ B x x)
    (T : ℝ≥0) (x b : ℝ → Ω → E)
    (hx : StronglyMeasurable (Function.uncurry x))
    (hb : StronglyMeasurable (Function.uncurry b))
    (hpath : ∀ᵐ ω ∂Q, ContinuousOn (fun r => x r ω) (Icc 0 (T : ℝ)) ∧
      IntervalIntegrable (fun r => b r ω) volume 0 (T : ℝ) ∧
      ∀ r ∈ Icc 0 (T : ℝ), x r ω = x 0 ω + ∫ s in 0..r, b s ω)
    (hzero : Integrable (fun ω => B (x 0 ω) (x 0 ω)) Q)
    (hp : Integrable (fun p : ℝ × Ω => max (B (x p.1 p.2) (b p.1 p.2)) 0)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) (ρ : ℝ)
    (hdiss : ∀ᵐ r ∂volume.restrict (Ioc 0 (T : ℝ)),
      (∫ ω, B (x r ω) (b r ω) ∂Q) ≤ -ρ * ∫ ω, B (x r ω) (x r ω) ∂Q) :
    (∫ ω, B (x T ω) (x T ω) ∂Q) ≤
      Real.exp (-2 * ρ * (T : ℝ)) * ∫ ω, B (x 0 ω) (x 0 ω) ∂Q := by
  let e : ℝ → ℝ := fun r => ∫ ω, B (x r ω) (x r ω) ∂Q
  let w : ℝ → ℝ := fun r => 2 * ∫ ω, B (x r ω) (b r ω) ∂Q
  have hw := work_integrable Q B hB hpos T x b hx hb hpath hzero hp
  have hwi : IntervalIntegrable w volume 0 (T : ℝ) := by
    rw [intervalIntegrable_iff, uIoc_of_le T.coe_nonneg]
    exact hw.integral_prod_left.const_mul 2
  have he (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : e t = e 0 + ∫ r in 0..t, w r := by
    let τ : ℝ≥0 := ⟨t,ht.1⟩
    have hsub : Icc 0 t ⊆ Icc 0 (T : ℝ) := Icc_subset_Icc le_rfl ht.2
    have hpt : ∀ᵐ ω ∂Q, ContinuousOn (fun r => x r ω) (Icc 0 (τ : ℝ)) ∧
        IntervalIntegrable (fun r => b r ω) volume 0 (τ : ℝ) ∧
        ∀ r ∈ Icc 0 (τ : ℝ), x r ω = x 0 ω + ∫ s in 0..r, b s ω := by
      filter_upwards [hpath] with ω hω
      refine ⟨hω.1.mono hsub, hω.2.1.mono_set ?_, fun r hr => hω.2.2 r (hsub hr)⟩
      change uIcc 0 t ⊆ uIcc 0 (T : ℝ)
      simpa only [uIcc_of_le ht.1, uIcc_of_le T.coe_nonneg] using hsub
    have hle : (volume : Measure ℝ).restrict (Ioc 0 (τ : ℝ)) ≤
        volume.restrict (Ioc 0 (T : ℝ)) := Measure.restrict_mono_set _ (Ioc_subset_Ioc le_rfl ht.2)
    have hpp := hp.mono_measure (Measure.prod_mono hle le_rfl)
    have hbalance := (expected_quadratic_balance Q B hB hpos τ x b hx hb hpt hzero hpp).2.2
    change e t = e 0 + ∫ r in 0..t, 2 * (∫ ω, B (x r ω) (b r ω) ∂Q)
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le ht.1]
    exact hbalance
  exact IntegralQuadraticEnergy.integral_gronwall e w T.coe_nonneg hwi he
    (hdiss.mono (fun r hr => by dsimp [w,e]; nlinarith))

end PBGSO.PositiveWorkFubini
