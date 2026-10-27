import AverageLMC.SGLDLaw
import AverageLMC.SmoothnessScaling
import AverageLMC.SGLDRecurrence
import AverageLMC.InitialMoment
import AverageLMC.Theorem
import AverageLMC.ExtendedTransport

set_option linter.style.header false
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace AverageLMC
open ULA ULA.Hilbert

/-- Proposition 3, first claim, for the actual Gaussian and uniform-index
transition. The estimator energy is retained without a variance bound. -/
theorem sgld_one_step {p n : ℕ} (hp : 0 < p) (hn : 0 < n)
    (f : Fin n → State p → ℝ) (hf : ∀ i, Differentiable ℝ (f i))
    (L : Fin n → ℝ≥0) (hLip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (m h : ℝ) (M : ℝ≥0) (hm : 0 < m) (hh : 0 ≤ h)
    (hsc : StrongConvexOn univ m (componentPotential f))
    (hfull : LipschitzWith M (gradient (componentPotential f)))
    (anchor : State p) (hstar : gradient (componentPotential f) anchor = 0)
    (μ : Measure (State p)) [IsProbabilityMeasure μ]
    (hfinite : wasserstein2 μ (gibbsMeasure (componentPotential f)) ≠ ⊤) :
    wasserstein2Real (sgldLawStep f anchor h μ) (gibbsMeasure (componentPotential f)) ^ 2 ≤
      (1 - m * h) / (1 + m * h) * wasserstein2Real μ (gibbsMeasure (componentPotential f)) ^ 2 +
      (averageSmoothness (componentPotential f) + m) * h ^ 2 * p / (1 + m * h) +
      h ^ 2 * (h * (M : ℝ) - 2) / (1 + m * h) *
        (∫ x, ‖gradient (componentPotential f) x‖ ^ 2 ∂μ) +
      h ^ 2 * ∫ q : State p × Fin n, ‖controlVariateEstimator f anchor q.1 q.2‖ ^ 2
        ∂μ.prod (uniformIndexLaw n) := by
  have hdiff : Differentiable ℝ (componentPotential f) :=
    Differentiable.fun_sum (fun i _ ↦ hf i)
  have := isProbabilityMeasure_gibbsMeasure _ m hm hdiff hsc
  have hπ := memLp_id_gibbsMeasure _ m hm hdiff hsc
  have hμ := memLp_id_of_wasserstein2_ne_top _ _ hfinite hπ
  have hvar := sgld_variance_addition hn f hf L hLip M hfull anchor hstar h μ
    (gibbsMeasure (componentPotential f)) hμ hπ
  rw [sgld_error_variance_identity hn f hf L hLip M hfull anchor hstar μ hμ] at hvar
  have hlmc := lmc_one_step hp (componentPotential f) m h M hm hh hdiff hsc hfull μ hfinite
  have hG : 0 ≤ ∫ x, ‖gradient (componentPotential f) x‖ ^ 2 ∂μ :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hd : 0 < 1 + m * h := by positivity
  have hc : h ^ 2 * (h * (M : ℝ) - 1) / (1 + m * h) - h ^ 2 ≤
      h ^ 2 * (h * (M : ℝ) - 2) / (1 + m * h) := by
    apply (le_div_iff₀ hd).mpr
    field_simp
    nlinarith [mul_nonneg hm.le hh, sq_nonneg h]
  have hg := mul_le_mul_of_nonneg_right hc hG
  nlinarith

/-- Proposition 3, second claim: the exact RMS-controlled one-step recursion. -/
theorem sgld_one_step_rms {p n : ℕ} (hp : 0 < p) (hn : 0 < n)
    (f : Fin n → State p → ℝ) (hf : ∀ i, Differentiable ℝ (f i))
    (L : Fin n → ℝ≥0) (hLip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (m h : ℝ) (M : ℝ≥0) (hm : 0 < m) (hh : 0 ≤ h)
    (hsc : StrongConvexOn univ m (componentPotential f))
    (hfull : LipschitzWith M (gradient (componentPotential f)))
    (hstep : h * (M : ℝ) ≤ 2)
    (anchor : State p) (hanchor : ∀ x, componentPotential f anchor ≤ componentPotential f x)
    (hstar : gradient (componentPotential f) anchor = 0)
    (μ : Measure (State p)) [IsProbabilityMeasure μ]
    (hfinite : wasserstein2 μ (gibbsMeasure (componentPotential f)) ≠ ⊤) :
    let R := (n : ℝ) * rmsComponentSmoothness f
    wasserstein2Real (sgldLawStep f anchor h μ) (gibbsMeasure (componentPotential f)) ^ 2 ≤
      ((1 - m * h) / (1 + m * h) + 2 * R ^ 2 * h ^ 2) *
        wasserstein2Real μ (gibbsMeasure (componentPotential f)) ^ 2 +
      ((averageSmoothness (componentPotential f) + m) / (1 + m * h) + 2 * R ^ 2 / m) *
        h ^ 2 * p := by
  have hdiff : Differentiable ℝ (componentPotential f) :=
    Differentiable.fun_sum (fun i _ ↦ hf i)
  have hπ := memLp_id_gibbsMeasure _ m hm hdiff hsc
  have hμ := memLp_id_of_wasserstein2_ne_top _ _ hfinite hπ
  have hs := sgld_one_step hp hn f hf L hLip m h M hm hh hsc hfull anchor hstar μ hfinite
  have hneg : h ^ 2 * (h * (M : ℝ) - 2) / (1 + m * h) *
      (∫ x, ‖gradient (componentPotential f) x‖ ^ 2 ∂μ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)) (by positivity))
      (integral_nonneg fun _ ↦ sq_nonneg _)
  have he := (controlVariateEstimator_product_memLp μ f L hLip anchor id hμ).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)
  have hr := (hμ.sub (memLp_const anchor)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  simp only [id_eq] at he
  simp only [Pi.sub_def] at hr
  have hmoment : (∫ q : State p × Fin n, ‖controlVariateEstimator f anchor q.1 q.2‖ ^ 2
      ∂μ.prod (uniformIndexLaw n)) ≤
      ((n : ℝ) * rmsComponentSmoothness f) ^ 2 * ∫ x, ‖x - anchor‖ ^ 2 ∂μ := by
    rw [integral_prod _ he]
    have hi := integral_mono he.integral_prod_left
      (hr.const_mul ((n : ℝ) ^ 2 * rmsComponentSmoothness f ^ 2))
      (fun x ↦ controlVariateEstimator_second_moment_le hp hn f L hLip anchor x)
    rw [integral_const_mul] at hi
    simpa only [mul_pow] using hi
  have hradius := initial_radius_le (componentPotential f) m hm hdiff hsc anchor hanchor μ hfinite
  have hmoment' := hmoment.trans (mul_le_mul_of_nonneg_left hradius (sq_nonneg _))
  have hscaled := mul_le_mul_of_nonneg_left hmoment' (sq_nonneg h)
  dsimp only
  simp only [div_eq_mul_inv] at hs hneg hscaled ⊢
  nlinarith

/-- Finite transport propagates along the actual SGLD laws. -/
theorem sgldLaws_finite {p n : ℕ} (hn : 0 < n)
    (f : Fin n → State p → ℝ) (hf : ∀ i, Differentiable ℝ (f i))
    (L : Fin n → ℝ≥0) (hLip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (m : ℝ) (M : ℝ≥0) (hm : 0 < m)
    (hsc : StrongConvexOn univ m (componentPotential f))
    (hfull : LipschitzWith M (gradient (componentPotential f)))
    (anchor : State p) (h : ℝ) (μ : Measure (State p)) [IsProbabilityMeasure μ]
    (hfinite : wasserstein2 μ (gibbsMeasure (componentPotential f)) ≠ ⊤) (k : ℕ) :
    wasserstein2 (sgldLaws f anchor h μ k) (gibbsMeasure (componentPotential f)) ≠ ⊤ := by
  have : NeZero n := ⟨hn.ne'⟩
  have hdiff : Differentiable ℝ (componentPotential f) :=
    Differentiable.fun_sum (fun i _ ↦ hf i)
  have := isProbabilityMeasure_gibbsMeasure _ m hm hdiff hsc
  have hπ := memLp_id_gibbsMeasure _ m hm hdiff hsc
  induction k with
  | zero => exact hfinite
  | succ k ih =>
    exact wasserstein2_ne_top_of_memLp _ _
      (sgldLawStep_memLp f hf L hLip M hfull anchor h _
        (memLp_id_of_wasserstein2_ne_top _ _ ih hπ)) hπ

/-- Theorem 3 and Proposition 3's final claim in full-potential units.
All second moments, laws and recurrences are derived from the component
potentials and their actual Gaussian/index transition. -/
theorem sgld_constant_step {p n : ℕ} (hp : 0 < p) (hn : 0 < n)
    (f : Fin n → State p → ℝ) (hf : ∀ i, Differentiable ℝ (f i))
    (L : Fin n → ℝ≥0) (hLip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (m h : ℝ) (hm : 0 < m) (hh : 0 ≤ h)
    (hsc : StrongConvexOn univ m (componentPotential f))
    (hstep : 3 * ((n : ℝ) * rmsComponentSmoothness f) ^ 2 * h ≤ m)
    (anchor : State p) (hanchor : ∀ x, componentPotential f anchor ≤ componentPotential f x)
    (μ : Measure (State p)) [IsProbabilityMeasure μ]
    (hfinite : wasserstein2 μ (gibbsMeasure (componentPotential f)) ≠ ⊤) (k : ℕ) :
    let R := (n : ℝ) * rmsComponentSmoothness f
    wasserstein2Real (sgldLaws f anchor h μ k) (gibbsMeasure (componentPotential f)) ^ 2 ≤
      (1 + m * h)⁻¹ ^ k * wasserstein2Real μ (gibbsMeasure (componentPotential f)) ^ 2 +
      (averageSmoothness (componentPotential f) + 2 * m + 2 * R ^ 2 / m) * h * p / m := by
  have : NeZero n := ⟨hn.ne'⟩
  let R := (n : ℝ) * rmsComponentSmoothness f
  let M : ℝ≥0 := ⟨R, mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)⟩
  have hfull : LipschitzWith M (gradient (componentPotential f)) :=
    componentPotential_gradient_lipschitz_rms hp hn f hf L hLip
  have hdiff : Differentiable ℝ (componentPotential f) :=
    Differentiable.fun_sum (fun i _ ↦ hf i)
  have hmR : m ≤ R := strongConvex_le_n_mul_rms hp hn f hf L hLip m hsc
  have hR : m ^ 2 ≤ R ^ 2 := (sq_le_sq₀ hm.le (hm.le.trans hmR)).mpr hmR
  have hRh : h * R ≤ 1 / 3 := by
    have hRpos : 0 < R := hm.trans_le hmR
    have hmul : R * (3 * R * h - 1) ≤ 0 := by nlinarith [hstep]
    by_contra hnot
    have hpos : 0 < 3 * R * h - 1 := by linarith
    exact (not_lt_of_ge hmul) (mul_pos hRpos hpos)
  have hstar : gradient (componentPotential f) anchor = 0 := by
    have hlocal : IsLocalMin (componentPotential f) anchor := Filter.Eventually.of_forall hanchor
    simp [gradient, hlocal.fderiv_eq_zero]
  let r := fun j ↦ wasserstein2Real (sgldLaws f anchor h μ j) (gibbsMeasure (componentPotential f)) ^ 2
  have hA : 0 ≤ averageSmoothness (componentPotential f) :=
    hm.le.trans (strongConvex_le_averageSmoothness hp _ m M hdiff hsc hfull)
  have hrec (j : ℕ) : r (j + 1) ≤
      ((1 - m * h) / (1 + m * h) + 2 * R ^ 2 * h ^ 2) * r j +
      ((averageSmoothness (componentPotential f) + m) / (1 + m * h) + 2 * R ^ 2 / m) * h ^ 2 * p := by
    exact sgld_one_step_rms hp hn f hf L hLip m h M hm hh hsc hfull
      (by change h * R ≤ 2; linarith) anchor hanchor hstar _
      (sgldLaws_finite hn f hf L hLip m M hm hsc hfull anchor h μ hfinite j)
  exact sgld_recurrence_bound r m R (averageSmoothness (componentPotential f)) h p hm hh
    (Nat.cast_nonneg _) hA hR hstep (fun _ ↦ sq_nonneg _) hrec k

/-- Theorem 3 in the manuscript's average-potential units. Its average
smoothness is exactly the full potential's coordinate average divided by n. -/
theorem sgld_constant_step_average {p n : ℕ} (hp : 0 < p) (hn : 0 < n)
    (f : Fin n → State p → ℝ) (hf : ∀ i, Differentiable ℝ (f i))
    (L : Fin n → ℝ≥0) (hLip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (mbar h : ℝ) (hmbar : 0 < mbar) (hh : 0 ≤ h)
    (hsc : StrongConvexOn univ ((n : ℝ) * mbar) (componentPotential f))
    (hstep : h ≤ mbar / (3 * n * rmsComponentSmoothness f ^ 2))
    (anchor : State p) (hanchor : ∀ x, componentPotential f anchor ≤ componentPotential f x)
    (μ : Measure (State p)) [IsProbabilityMeasure μ]
    (hfinite : wasserstein2 μ (gibbsMeasure (componentPotential f)) ≠ ⊤) (k : ℕ) :
    wasserstein2Real (sgldLaws f anchor h μ k) (gibbsMeasure (componentPotential f)) ^ 2 ≤
      (1 + (n : ℝ) * mbar * h)⁻¹ ^ k * wasserstein2Real μ (gibbsMeasure (componentPotential f)) ^ 2 +
      (averageSmoothness (componentPotential f) / n + 2 * mbar +
        2 * rmsComponentSmoothness f ^ 2 / mbar) * h * p / mbar := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : 0 < (n : ℝ) * mbar := mul_pos hn' hmbar
  have hmR := strongConvex_le_n_mul_rms hp hn f hf L hLip ((n : ℝ) * mbar) hsc
  have hR : 0 < rmsComponentSmoothness f := by nlinarith
  have hd : 0 < 3 * (n : ℝ) * rmsComponentSmoothness f ^ 2 := by positivity
  have hsmall := (le_div_iff₀ hd).mp hstep
  have hnorm : 3 * ((n : ℝ) * rmsComponentSmoothness f) ^ 2 * h ≤ (n : ℝ) * mbar := by
    have hx := mul_le_mul_of_nonneg_left hsmall hn'.le
    nlinarith
  have hb := sgld_constant_step hp hn f hf L hLip ((n : ℝ) * mbar) h hm hh hsc hnorm
    anchor hanchor μ hfinite k
  dsimp only at hb
  convert hb using 1
  field_simp [hn'.ne', hmbar.ne']

/-- The main SGLD theorem for every probability initialization, with no
additional finite-second-moment premise. Infinite initial transport is
interpreted in the extended nonnegative reals. -/
theorem sgld_constant_step_extended {p n : ℕ} (hp : 0 < p) (hn : 0 < n)
    (f : Fin n → State p → ℝ) (hf : ∀ i, Differentiable ℝ (f i))
    (L : Fin n → ℝ≥0) (hLip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (mbar h : ℝ) (hmbar : 0 < mbar) (hh : 0 ≤ h)
    (hsc : StrongConvexOn univ ((n : ℝ) * mbar) (componentPotential f))
    (hstep : h ≤ mbar / (3 * n * rmsComponentSmoothness f ^ 2))
    (anchor : State p) (hanchor : ∀ x, componentPotential f anchor ≤ componentPotential f x)
    (μ : Measure (State p)) [IsProbabilityMeasure μ] (k : ℕ) :
    wasserstein2 (sgldLaws f anchor h μ k) (gibbsMeasure (componentPotential f)) ^ 2 ≤
      ENNReal.ofReal ((1 + (n : ℝ) * mbar * h)⁻¹ ^ k) *
        wasserstein2 μ (gibbsMeasure (componentPotential f)) ^ 2 +
      ENNReal.ofReal ((averageSmoothness (componentPotential f) / n + 2 * mbar +
        2 * rmsComponentSmoothness f ^ 2 / mbar) * h * p / mbar) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : 0 < (n : ℝ) * mbar := mul_pos hn' hmbar
  let M : ℝ≥0 := ⟨(n : ℝ) * rmsComponentSmoothness f,
    mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)⟩
  have hfull : LipschitzWith M (gradient (componentPotential f)) :=
    componentPotential_gradient_lipschitz_rms hp hn f hf L hLip
  have hdiff : Differentiable ℝ (componentPotential f) :=
    Differentiable.fun_sum (fun i _ ↦ hf i)
  have hA : 0 ≤ averageSmoothness (componentPotential f) :=
    hm.le.trans (strongConvex_le_averageSmoothness hp _ _ M hdiff hsc hfull)
  apply squared_transport_extended μ (gibbsMeasure (componentPotential f))
    (sgldLaws f anchor h μ k) (gibbsMeasure (componentPotential f))
    ((1 + (n : ℝ) * mbar * h)⁻¹ ^ k) _ (by positivity) (by positivity)
  · intro hi
    exact sgldLaws_finite hn f hf L hLip ((n : ℝ) * mbar) M hm hsc hfull anchor h μ hi k
  · intro hi
    exact sgld_constant_step_average hp hn f hf L hLip mbar h hmbar hh hsc hstep anchor hanchor μ hi k

/-- The manuscript SGLD theorem with its barred constant defined literally
from the average potential `f/n`, and every probability initialization. -/
theorem sgld_constant_step_paper {p n : ℕ} (hp : 0 < p) (hn : 0 < n)
    (f : Fin n → State p → ℝ) (hf : ∀ i, Differentiable ℝ (f i))
    (L : Fin n → ℝ≥0) (hLip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (mbar h : ℝ) (hmbar : 0 < mbar) (hh : 0 ≤ h)
    (hsc : StrongConvexOn univ ((n : ℝ) * mbar) (componentPotential f))
    (hstep : h ≤ mbar / (3 * n * rmsComponentSmoothness f ^ 2))
    (anchor : State p) (hanchor : ∀ x, componentPotential f anchor ≤ componentPotential f x)
    (μ : Measure (State p)) [IsProbabilityMeasure μ] (k : ℕ) :
    wasserstein2 (sgldLaws f anchor h μ k) (gibbsMeasure (componentPotential f)) ^ 2 ≤
      ENNReal.ofReal ((1 + (n : ℝ) * mbar * h)⁻¹ ^ k) *
        wasserstein2 μ (gibbsMeasure (componentPotential f)) ^ 2 +
      ENNReal.ofReal ((averageSmoothness (fun x ↦ componentPotential f x / n) +
        2 * mbar + 2 * rmsComponentSmoothness f ^ 2 / mbar) * h * p / mbar) := by
  rw [averageSmoothness_div_nat (componentPotential f)
    (Differentiable.fun_sum (fun i _ ↦ hf i)) (∑ i, L i)
    (componentPotential_gradient_lipschitz f hf L hLip) n]
  exact sgld_constant_step_extended hp hn f hf L hLip mbar h hmbar hh hsc hstep
    anchor hanchor μ k

end AverageLMC
