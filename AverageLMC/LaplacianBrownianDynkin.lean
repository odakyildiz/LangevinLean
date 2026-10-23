import AverageLMC.LaplacianDynkinLimit
import AverageLMC.LaplacianCompactTest
import AverageLMC.LaplacianWeakChain
import UnadjustedLangevin.GibbsStationarity

set_option linter.style.header false

/-!
# Dynkin's identity for the constructed Brownian Langevin solution

The reference is the actual continuous `L²` solution driven by Brownian
coordinates. Matching-noise Euler chains supply the independent Gaussian
increments, and uniform grid bounds control their accumulated weak errors.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace AverageLMC

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- All sufficiently fine actual Brownian Euler approximations have a single
uniform score norm bound, at every point in the time partition. -/
theorem brownian_euler_score_grid_eventually_bounded
    (f : EuclideanSpace ℝ ι → ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient f))
    (initial : Lp (EuclideanSpace ℝ ι) 2 P)
    (B : ι → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P)
    (Y : ℝ → Lp (EuclideanSpace ℝ ι) 2 P) (hY : Continuous Y)
    (T : ℝ) (hT : 0 < T)
    (hYe : ∀ t ∈ Icc 0 T, Y t - initial =
      -(∫ s in 0..t, ULA.lpDrift P (gradient f) hLip (Y s)) +
        ULA.brownianLangevinNoise P B hB 0 t) :
    ∃ R : ℝ, 0 ≤ R ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ k ≤ n + 1,
      ‖ULA.lpDrift P (gradient f) hLip
        (ULA.Hilbert.lpChain P f (T / ((n + 1 : ℕ) : ℝ)) hLip initial
          (ULA.Hilbert.brownianEulerNoise P B hB (T / ((n + 1 : ℕ) : ℝ))) k)‖ ≤ R := by
  obtain ⟨R, hR, N, hN⟩ := additiveEulerChain_drift_grid_eventually_bounded
    (ULA.lpDrift P (gradient f) hLip) L (ULA.lpDrift_lipschitz P (gradient f) hLip)
    initial (ULA.brownianLangevinNoise P B hB 0) Y
    (ULA.brownianLangevinNoise_zero P B hB 0) hY T hT.le hYe
  refine ⟨R, hR, N, fun n hn k hk ↦ ?_⟩
  rw [← ULA.brownian_additiveEulerChain_eq_lpChain P f
    (T / ((n + 1 : ℕ) : ℝ)) L hLip initial B hB (by positivity) k]
  exact hN n hn k hk

/-- The exact weighted Dynkin identity for every compact `C²` test on the
constructed Brownian Langevin solution. The independence hypotheses concern
only the initialization and actual Brownian innovations, not a stochastic
calculus formula or a generator identity. -/
theorem lp_langevin_weighted_dynkin_compact
    (f : EuclideanSpace ℝ ι → ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient f))
    (initial : Lp (EuclideanSpace ℝ ι) 2 P)
    (B : ι → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P)
    (w : Ω → ℝ) (hw : Measurable w) (A : ℝ) (hA : 0 ≤ A)
    (hwA : ∀ᵐ a ∂P, |w a| ≤ A)
    (hscalar : ∀ r : ℝ, 0 < r → iIndepFun (fun q : ℕ × ι ↦ fun a ↦
      ULA.Hilbert.brownianEulerNoise P B hB r q.1 a q.2) P)
    (hind : ∀ r : ℝ, 0 < r → IndepFun (fun a ↦ (w a, initial a))
      (fun a k ↦ ULA.Hilbert.brownianEulerNoise P B hB r k a) P)
    (Y : ℝ → Lp (EuclideanSpace ℝ ι) 2 P) (hY : Continuous Y)
    (T : ℝ) (hT : 0 ≤ T)
    (hYe : ∀ t ∈ Icc 0 T, Y t - initial =
      -(∫ s in 0..t, ULA.lpDrift P (gradient f) hLip (Y s)) +
        ULA.brownianLangevinNoise P B hB 0 t)
    (φ : EuclideanSpace ℝ ι → ℝ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    lpWeightedTest P w φ (Y T) - lpWeightedTest P w φ initial =
      ∫ t in 0..T, lpWeightedTest P w (ULA.langevinGenerator f φ) (Y t) := by
  by_cases hTzero : T = 0
  · subst T
    have hY0 : Y 0 = initial := by
      simpa only [intervalIntegral.integral_same, neg_zero,
        ULA.brownianLangevinNoise_zero, add_zero, sub_eq_zero] using hYe 0 ⟨le_rfl, le_rfl⟩
    simp only [hY0, sub_self, intervalIntegral.integral_same]
  have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hTzero)
  obtain ⟨R, hR, N₀, hN₀⟩ := brownian_euler_score_grid_eventually_bounded P
    f L hLip initial B hB Y hY T hTpos hYe
  obtain ⟨hUCφ, Cφ, hCφ, hboundφ⟩ := compact_test_bounded_uniformContinuous φ hφ hc
  obtain ⟨hUCg, Cg, hCg, hboundg⟩ :=
    compact_test_generator_bounded_uniformContinuous f L hLip φ hφ hc
  have htest := lpWeightedTest_uniformContinuous P w hw A hA hwA φ hUCφ Cφ hCφ hboundφ
  have hgen := lpWeightedTest_uniformContinuous P w hw A hA hwA _ hUCg Cg hCg hboundg
  apply weighted_dynkin_of_weak_euler_consistency
    (ULA.lpDrift P (gradient f) hLip) L (ULA.lpDrift_lipschitz P (gradient f) hLip)
    initial (ULA.brownianLangevinNoise P B hB 0) Y
    (ULA.brownianLangevinNoise_zero P B hB 0) hY T hT hYe
    (lpWeightedTest P w φ) (lpWeightedTest P w (ULA.langevinGenerator f φ))
    htest hgen (A * T * (1 + R ^ 2)) (by positivity)
  intro ε hε
  obtain ⟨K, hK, hbound⟩ := compactC2_gaussian_weak_step φ hφ hc ε hε
  have hmesh : Tendsto (fun n : ℕ ↦ T / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_const_div_atTop_nhds_zero_nat T)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hmesh.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  refine ⟨K, hK, max N₀ N₁, fun n hn ↦ ?_⟩
  let h := T / ((n + 1 : ℕ) : ℝ)
  have hh : 0 < h := by dsimp [h]; positivity
  have hh1 : h ≤ 1 := (hN₁ n ((le_max_right _ _).trans hn)).le
  obtain ⟨hiid, hlaw⟩ := ULA.brownianEulerNoise_vectorGaussian P B hB h hh (hscalar h hh)
  have hb := hilbert_lpChain_weak_sum_of_bound P f h L hLip initial
    (ULA.Hilbert.brownianEulerNoise P B hB h) w hw (hind h hh) hiid hlaw
    φ hφ Cφ Cg hboundφ hboundg A hA hwA ε hε K hK hbound hh.le hh1
    (n + 1) R hR (hN₀ n ((le_max_left _ _).trans hn))
  have hpartition : (((n + 1 : ℕ) : ℝ)) * h = T := by dsimp [h]; field_simp
  rw [hpartition] at hb
  have he (k : ℕ) := ULA.brownian_additiveEulerChain_eq_lpChain P f h L hLip initial B hB hh k
  simp_rw [← he] at hb
  convert hb using 1 <;> dsimp [h] <;> ring

end AverageLMC
