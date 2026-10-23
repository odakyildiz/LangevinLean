import AverageLMC.GaussianPerturbation

set_option linter.style.header false
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal RealInnerProductSpace
namespace AverageLMC

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- Future Brownian noise has zero vector expectation. -/
theorem brownian_future_mean_zero
    (B : ι → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P) (t h : ℝ) :
    (∫ ω, (ULA.brownianLangevinNoise P B hB 0 h -
      ULA.brownianLangevinNoise P B hB 0 t : Lp (EuclideanSpace ℝ ι) 2 P) ω ∂P) = 0 := by
  rw [integral_congr_ae (Lp.coeFn_sub _ _)]
  change (∫ ω, ULA.brownianLangevinNoise P B hB 0 h ω -
    ULA.brownianLangevinNoise P B hB 0 t ω ∂P) = 0
  rw [integral_sub ((Lp.memLp _).integrable (by norm_num))
    ((Lp.memLp _).integrable (by norm_num))]
  rw [ProximalLangevin.brownianNoise_integral_zero P B hB h,
    ProximalLangevin.brownianNoise_integral_zero P B hB t, sub_self]

/-- The actual Brownian increment's exact second moment. -/
theorem brownian_future_norm_sq
    (B : ι → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P)
    (t h : ℝ) (ht : 0 ≤ t) (hth : t ≤ h) :
    ‖ULA.brownianLangevinNoise P B hB 0 h -
      ULA.brownianLangevinNoise P B hB 0 t‖ ^ 2 =
      2 * (h - t) * (Fintype.card ι : ℝ) := by
  have he : ULA.brownianLangevinNoise P B hB 0 h -
      ULA.brownianLangevinNoise P B hB 0 t =
      ULA.brownianLangevinNoise P B hB t (h - t) := by
    unfold ULA.brownianLangevinNoise
    simp only [zero_add, show t + (h - t) = h by ring]
    module
  rw [he, ULA.brownianLangevinNoise_norm P B hB t (h - t) ht (sub_nonneg.mpr hth),
    mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * (Fintype.card ι : ℝ)),
    Real.sq_sqrt (sub_nonneg.mpr hth)]
  ring

/-- The Brownian orthogonality needed by the energy proof follows from genuine
independence, the integral equation, and its derived adaptedness. -/
theorem gaussian_error_future_inner_zero
    (f : EuclideanSpace ℝ ι → ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient f))
    (X Z : Lp (EuclideanSpace ℝ ι) 2 P)
    (B : ι → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hmeas : ∀ i s, Measurable (B i s))
    (hpaths : iIndepFun (fun i ω s ↦ B i s ω) P)
    (hX : IndepFun X (fun ω (i : ι) (s : ℝ≥0) ↦ B i s ω) P)
    (hZ : IndepFun Z (fun ω (i : ι) (s : ℝ≥0) ↦ B i s ω) P)
    (Y : ℝ → Lp (EuclideanSpace ℝ ι) 2 P) (hY : Continuous Y)
    (t h : ℝ) (ht : 0 ≤ t) (hth : t ≤ h)
    (hYe : ∀ s ∈ Icc 0 h, Y s - Z =
      -(∫ r in 0..s, ULA.lpDrift P (gradient f) hLip (Y r)) +
        ULA.brownianLangevinNoise P B hB 0 s) :
    ⟪X + ULA.brownianLangevinNoise P B hB 0 t - Y t,
      ULA.brownianLangevinNoise P B hB 0 h -
        ULA.brownianLangevinNoise P B hB 0 t⟫ = 0 := by
  let N := ULA.brownianLangevinNoise P B hB 0
  have hind := ProximalLangevin.brownian_future_independent_initial_past P B hB hmeas
    hpaths X hX t h ht hth
  have hIX : IndepFun X (N h - N t) P := by
    exact hind.comp (measurable_pi_apply none) measurable_id
  have hIB : IndepFun (N t) (N h - N t) P := by
    exact hind.comp (measurable_pi_apply (some (⟨t, ht, le_rfl⟩ : Icc (0 : ℝ) t))) measurable_id
  have hmean := brownian_future_mean_zero P B hB t h
  have hx := ProximalLangevin.independent_centered_lp_inner_zero P X (N h - N t) hIX hmean
  have hb := ProximalLangevin.independent_centered_lp_inner_zero P (N t) (N h - N t) hIB hmean
  have hy := ProximalLangevin.lp_langevin_future_inner_zero P f L hLip Z B hB hmeas hpaths
    hZ Y hY t h ht hth hYe (fun x ↦ x) 1 (LipschitzWith.id)
  have he : ULA.lpDrift P (fun x : EuclideanSpace ℝ ι ↦ x) LipschitzWith.id (Y t) = Y t := by
    apply Lp.ext
    exact ULA.lpDrift_coe P _ LipschitzWith.id (Y t)
  rw [he] at hy
  change ⟪X + N t - Y t, N h - N t⟫ = 0
  rw [inner_sub_left, inner_add_left, hx, hb, hy]
  ring

end AverageLMC
