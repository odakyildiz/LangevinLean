import AverageLMC.LaplacianCanonical

set_option linter.style.header false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace AverageLMC
open ULA ULA.Hilbert

/-- An increasing quadratic-plus-linear coupling estimate passes to the true
transport infimum, without an optimal coupling assumption. -/
theorem quadratic_linear_bound_of_finite_couplings {E : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] (μ π : Measure E) (r a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hfinite : wasserstein2 μ π ≠ ⊤)
    (hfamily : ∀ γ : Coupling μ π, couplingCost γ.joint ≠ ⊤ →
      r ≤ a * (couplingCost γ.joint).toReal ^ 2 + b * (couplingCost γ.joint).toReal + c) :
    r ≤ a * wasserstein2Real μ π ^ 2 + b * wasserstein2Real μ π + c := by
  have hw : 0 ≤ wasserstein2Real μ π := ENNReal.toReal_nonneg
  have heps (ε : ℝ) (hε : 0 < ε) :
      r ≤ a * (wasserstein2Real μ π + ε) ^ 2 + b * (wasserstein2Real μ π + ε) + c := by
    have hi : wasserstein2 μ π < ENNReal.ofReal (wasserstein2Real μ π + ε) := by
      rw [← ENNReal.ofReal_toReal hfinite]
      apply (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < wasserstein2Real μ π + ε)).mpr
      change (wasserstein2 μ π).toReal < (wasserstein2 μ π).toReal + ε
      linarith
    obtain ⟨γ, hγ⟩ := iInf_lt_iff.mp hi
    have hc : couplingCost γ.joint ≠ ⊤ := ne_top_of_lt hγ
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hγ.le
    rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ wasserstein2Real μ π + ε)] at hr
    have hs := (sq_le_sq₀ ENNReal.toReal_nonneg (by linarith)).mpr hr
    exact (hfamily γ hc).trans (add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hs ha) (mul_le_mul_of_nonneg_left hr hb)) le_rfl)
  have hlim : Tendsto (fun ε : ℝ ↦
      a * (wasserstein2Real μ π + ε) ^ 2 + b * (wasserstein2Real μ π + ε) + c)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (a * wasserstein2Real μ π ^ 2 + b * wasserstein2Real μ π + c)) := by
    have hc : Continuous (fun ε : ℝ ↦
      a * (wasserstein2Real μ π + ε) ^ 2 + b * (wasserstein2Real μ π + ε) + c) := by fun_prop
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (by filter_upwards [self_mem_nhdsWithin] with ε hε using heps ε hε)

/-- Laplacian theorem (source th:3) with the actual Gaussian LMC marginal laws and the exact
paper constant. Only finite transport is required to interpret its real bound. -/
theorem lmc_laplacian {p : ℕ} (hp : 0 < p) (f : State p → ℝ)
    (m h : ℝ) (L : ℝ≥0) (hm : 0 < m) (hh : 0 < h)
    (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith L (gradient f))
    (hsmall : h * (L : ℝ) < 1) (Mdelta : ℝ) (hMdelta : 0 ≤ Mdelta)
    (hδ : LaplacianSmooth f Mdelta) (μ : Measure (State p)) [IsProbabilityMeasure μ]
    (hfinite : wasserstein2 μ (gibbsMeasure f) ≠ ⊤) (k : ℕ) :
    wasserstein2Real ((ulaLawStep f h)^[k] μ) (gibbsMeasure f) ≤
      (1 - m * h) ^ k * wasserstein2Real μ (gibbsMeasure f) +
      (2 * (L : ℝ) * Real.sqrt (averageSmoothness f) + Mdelta) * h * Real.sqrt p / m := by
  have hf : Differentiable ℝ f := hδ.1.differentiable (by norm_num)
  have hM := strongConvex_le_averageSmoothness hp f m L hf hsc hLip
  have hmL := hM.trans (averageSmoothness_le_global_bound hp f L hf hLip)
  have hMnonneg : 0 ≤ averageSmoothness f := hm.le.trans hM
  have hmh : m * h ≤ 1 := by nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hmL)]
  have hq : 0 ≤ 1 - m * h := sub_nonneg.mpr hmh
  let e := fun j ↦ wasserstein2Real (lmcLaws f (fun _ ↦ h) μ j) (gibbsMeasure f)
  have hstep (j : ℕ) : (e (j + 1)) ^ 2 ≤
      (1 - m * h) ^ 2 * (e j) ^ 2 +
      (1 - m * h) * h ^ 2 * ((L : ℝ) * Real.sqrt (averageSmoothness f) + Mdelta) * Real.sqrt p * e j +
      ((3 / 2 : ℝ) * (L : ℝ) * h * Real.sqrt h * Real.sqrt p) ^ 2 := by
    have hj := lmcLaws_finite f m L hm hf hsc hLip (fun _ ↦ h) (fun _ ↦ hh.le) μ hfinite j
    have hb := quadratic_linear_bound_of_finite_couplings
      (lmcLaws f (fun _ ↦ h) μ j) (gibbsMeasure f)
      (wasserstein2Real (ulaLawStep f h (lmcLaws f (fun _ ↦ h) μ j)) (gibbsMeasure f) ^ 2)
      ((1 - m * h) ^ 2)
      (h ^ 2 * (1 - m * h) * ((L : ℝ) * Real.sqrt (averageSmoothness f * p) + Mdelta * Real.sqrt p))
      (((3 / 2 : ℝ) * (L : ℝ) * h * Real.sqrt h * Real.sqrt p) ^ 2)
      (sq_nonneg _) (by positivity) hj (fun γ hγ ↦ by
        have hb := laplacian_coupling_step hp f m h L hm hh hf hsc hLip hsmall.le
          Mdelta hMdelta hδ _ γ hγ
        convert hb using 1 <;> ring)
    rw [Real.sqrt_mul hMnonneg] at hb
    convert hb using 1 <;> dsimp [e] <;> ring
  have hb := laplacian_recurrence_bound_of_global_defect e m (L : ℝ) h
    (Real.sqrt (averageSmoothness f)) Mdelta (Real.sqrt p)
    (fun _ ↦ ENNReal.toReal_nonneg) hm hmL hh.le hsmall.le (Real.sqrt_nonneg _)
    (by simpa only [Real.sq_sqrt hMnonneg] using hM) hMdelta (Real.sqrt_nonneg _) hstep k
  dsimp [e] at hb
  rw [lmcLaws_const] at hb
  exact hb

/-- Laplacian theorem (source th:3) for every probability initialization, using extended nonnegative
transport for possibly infinite initial second moment. -/
theorem lmc_laplacian_extended {p : ℕ} (hp : 0 < p) (f : State p → ℝ)
    (m h : ℝ) (L : ℝ≥0) (hm : 0 < m) (hh : 0 < h)
    (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith L (gradient f))
    (hsmall : h * (L : ℝ) < 1) (Mdelta : ℝ) (hMdelta : 0 ≤ Mdelta)
    (hδ : LaplacianSmooth f Mdelta) (μ : Measure (State p)) [IsProbabilityMeasure μ] (k : ℕ) :
    wasserstein2 ((ulaLawStep f h)^[k] μ) (gibbsMeasure f) ≤
      ENNReal.ofReal ((1 - m * h) ^ k) * wasserstein2 μ (gibbsMeasure f) +
      ENNReal.ofReal ((2 * (L : ℝ) * Real.sqrt (averageSmoothness f) + Mdelta) * h * Real.sqrt p / m) := by
  have hf : Differentiable ℝ f := hδ.1.differentiable (by norm_num)
  have hM := strongConvex_le_averageSmoothness hp f m L hf hsc hLip
  have hmL := hM.trans (averageSmoothness_le_global_bound hp f L hf hLip)
  have hq : 0 < 1 - m * h := by nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hmL)]
  by_cases hi : wasserstein2 μ (gibbsMeasure f) = ⊤
  · simp [hi, ENNReal.ofReal_pos.mpr (pow_pos hq k) |>.ne']
  · have ho := lmcLaws_finite f m L hm hf hsc hLip (fun _ ↦ h) (fun _ ↦ hh.le) μ hi k
    rw [lmcLaws_const] at ho
    have hb := ENNReal.ofReal_le_ofReal
      (lmc_laplacian hp f m h L hm hh hsc hLip hsmall Mdelta hMdelta hδ μ hi k)
    have hconst : 0 ≤ (2 * (L : ℝ) * Real.sqrt (averageSmoothness f) + Mdelta) * h * Real.sqrt (p : ℝ) / m := by positivity
    have hprod : 0 ≤ (1 - m * h) ^ k * wasserstein2Real μ (gibbsMeasure f) :=
      mul_nonneg (pow_pos hq k).le ENNReal.toReal_nonneg
    rw [ENNReal.ofReal_add hprod hconst,
      ENNReal.ofReal_mul (pow_pos hq k).le] at hb
    simpa only [wasserstein2Real, ENNReal.ofReal_toReal hi, ENNReal.ofReal_toReal ho] using hb

end AverageLMC
