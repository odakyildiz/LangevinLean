import AverageLMC.LaplacianBrownianDynkin
import AverageLMC.LaplacianPairingLimit
import AverageLMC.LaplacianStationaryTest
import AverageLMC.GibbsScoreCutoff

set_option linter.style.header false

/-!
# The actual gradient cross-term bound

Compact `C²` coordinate tests satisfy the proved Brownian Dynkin identity.
Their genuine generators converge in Gibbs `L²` to the actual gradient
generator. Stationarity makes the error uniform in time. Radial clipping
removes boundedness of the initial vector and preserves its exact `L²` norm.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace AverageLMC

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- Actual-law observations inherit convergence in Gibbs `L²`. -/
theorem stationaryObservation_tendsto_of_sq_error {p : ℕ}
    (π : Measure (State p)) (F : ℕ → State p → State p) (G : State p → State p)
    (hFc : ∀ n, Continuous (F n)) (hGc : Continuous G)
    (hF : ∀ n, MemLp (F n) 2 π) (hG : MemLp G 2 π)
    (Y : Lp (State p) 2 P) (hlaw : P.map Y = π)
    (herr : Tendsto (fun n ↦ ∫ x, ‖F n x - G x‖ ^ 2 ∂π) atTop (𝓝 0)) :
    Tendsto (fun n ↦ stationaryObservation P π (F n) (hF n) Y hlaw) atTop
      (𝓝 (stationaryObservation P π G hG Y hlaw)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have he (n : ℕ) :
      ‖stationaryObservation P π (F n) (hF n) Y hlaw - stationaryObservation P π G hG Y hlaw‖ =
        Real.sqrt (∫ x, ‖F n x - G x‖ ^ 2 ∂π) := by
    rw [← stationaryObservation_sub_norm_sq P π (F n) G (hFc n) hGc (hF n) hG Y hlaw,
      Real.sqrt_sq (norm_nonneg _)]
  simp_rw [he]
  simpa only [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp herr

/-- The actual stationary gradient increment has the paper's sharp dual
bound against every square-integrable independent initial vector. Every
stochastic-calculus identity used here was derived from Gaussian Euler
approximations; no desired Wasserstein recurrence is a hypothesis. -/
theorem lp_stationary_gradient_pairing_bound {p : ℕ} (hp : 0 < p)
    (f : State p → ℝ) (m : ℝ) (L : ℝ≥0) (hm : 0 < m)
    (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith L (gradient f))
    (Mdelta : ℝ) (hMdelta : 0 ≤ Mdelta) (hδ : LaplacianSmooth f Mdelta)
    (initial : Lp (State p) 2 P)
    (B : Fin p → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hscalar : ∀ r : ℝ, 0 < r → iIndepFun (fun q : ℕ × Fin p ↦ fun a ↦
      ULA.Hilbert.brownianEulerNoise P B hB r q.1 a q.2) P)
    (Ψ : Lp (State p) 2 P)
    (hind : ∀ r : ℝ, 0 < r → IndepFun (fun a ↦ (Ψ a, initial a))
      (fun a k ↦ ULA.Hilbert.brownianEulerNoise P B hB r k a) P)
    (Y : ℝ → Lp (State p) 2 P) (hY : Continuous Y)
    (T : ℝ) (hT : 0 ≤ T)
    (hYe : ∀ t ∈ Icc 0 T, Y t - initial =
      -(∫ s in 0..t, ULA.lpDrift P (gradient f) hLip (Y s)) +
        ULA.brownianLangevinNoise P B hB 0 t)
    (hstationary : ∀ t ∈ Icc 0 T, P.map (Y t) = ULA.gibbsMeasure f) :
    inner ℝ Ψ (ULA.lpDrift P (gradient f) hLip (Y T) -
      ULA.lpDrift P (gradient f) hLip initial) ≤
        T * ‖Ψ‖ * ((L : ℝ) * Real.sqrt (averageSmoothness f * (p : ℝ)) +
          Mdelta * Real.sqrt (p : ℝ)) := by
  classical
  have hf : Differentiable ℝ f := hδ.1.differentiable (by norm_num)
  have hZ := ULA.gibbsPartition_ne_top f m hm hf hsc
  let π := ULA.gibbsMeasure f
  haveI : IsProbabilityMeasure π := ULA.isProbabilityMeasure_gibbsMeasure f m hm hf hsc
  have hY0 : Y 0 = initial := by
    simpa only [intervalIntegral.integral_same, neg_zero,
      ULA.brownianLangevinNoise_zero, add_zero, sub_eq_zero] using hYe 0 ⟨le_rfl, hT⟩
  have hinitlaw : P.map initial = π := by
    simpa only [hY0] using hstationary 0 ⟨le_rfl, hT⟩
  have hTlaw : P.map (Y T) = π := hstationary T ⟨hT, le_rfl⟩
  obtain ⟨φ, hφ, hFn, hGFn, hscore, hgen, hscoreLim, hgenLim⟩ :=
    score_vector_compact_approximation f L hLip hZ Mdelta hMdelta hδ
  let Fn : ℕ → State p → State p := fun n x ↦ WithLp.toLp 2 (fun j ↦ φ n j x)
  let GFn : ℕ → State p → State p := fun n x ↦
    WithLp.toLp 2 (fun j ↦ ULA.langevinGenerator f (φ n j) x)
  have hFc (n : ℕ) : Continuous (Fn n) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin p ↦ ℝ)).comp
      (continuous_pi (fun j ↦ (hφ n j).1.continuous))
  have hGc (n : ℕ) : Continuous (GFn n) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin p ↦ ℝ)).comp (continuous_pi (fun j ↦
      continuous_langevinGenerator_compact_test f L hLip (φ n j) (hφ n j).1))
  have htargetc := continuous_gradientGenerator f hδ.1
  let R := (L : ℝ) * Real.sqrt (averageSmoothness f * (p : ℝ)) + Mdelta * Real.sqrt (p : ℝ)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  let err : ℕ → ℝ := fun n ↦ Real.sqrt (∫ x, ‖GFn n x - gradientGenerator f x‖ ^ 2 ∂π)
  have herr (n : ℕ) : 0 ≤ err n := Real.sqrt_nonneg _
  have herrlim : Tendsto err atTop (𝓝 0) := by
    simpa only [err, GFn, π, Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hgenLim
  have hscoreObs (Z : Lp (State p) 2 P) (hZlaw : P.map Z = π) :
      stationaryObservation P π (gradient f) hscore Z hZlaw =
        ULA.lpDrift P (gradient f) hLip Z := by
    apply Lp.ext
    exact (stationaryObservation_coe P π _ hscore Z hZlaw).trans
      (ULA.lpDrift_coe P _ hLip Z).symm
  let Xn := fun n ↦ stationaryObservation P π (Fn n) (hFn n) (Y T) hTlaw
  let Yn := fun n ↦ stationaryObservation P π (Fn n) (hFn n) initial hinitlaw
  have hXlim : Tendsto Xn atTop (𝓝 (ULA.lpDrift P (gradient f) hLip (Y T))) := by
    have hl := stationaryObservation_tendsto_of_sq_error P π Fn (gradient f) hFc
      hLip.continuous hFn hscore (Y T) hTlaw hscoreLim
    rwa [hscoreObs] at hl
  have hYlim : Tendsto Yn atTop (𝓝 (ULA.lpDrift P (gradient f) hLip initial)) := by
    have hl := stationaryObservation_tendsto_of_sq_error P π Fn (gradient f) hFc
      hLip.continuous hFn hscore initial hinitlaw hscoreLim
    rwa [hscoreObs] at hl
  apply pairing_bound_of_clipped_weights P Ψ _ T R hT hR
  intro r
  let Ψr := lpClippedWeight P Ψ r
  have hΨr : ∀ᵐ a ∂P, ‖Ψr a‖ ≤ (r : ℝ) + 1 := by
    filter_upwards [lpClippedWeight_coe P Ψ r] with a ha
    rw [ha]
    exact norm_clipWeight_le_radius r (Ψ a)
  have hindr : ∀ s : ℝ, 0 < s → IndepFun (fun a ↦ (Ψr a, initial a))
      (fun a k ↦ ULA.Hilbert.brownianEulerNoise P B hB s k a) P := by
    intro s hs
    have hi := (hind s hs).comp
      (φ := fun q : State p × State p ↦ (clipWeight r q.1, q.2)) (ψ := id)
      (((measurable_clipWeight r).comp measurable_fst).prodMk measurable_snd) measurable_id
    apply hi.congr _ (ae_eq_refl _)
    filter_upwards [lpClippedWeight_coe P Ψ r] with a ha
    exact congrArg (fun z ↦ (z, initial a)) ha.symm
  have hgenNorm (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) :
      ‖stationaryObservation P π (GFn n) (hGFn n) (Y t) (hstationary t ht)‖ ≤ R + err n := by
    let H := stationaryObservation P π (gradientGenerator f) hgen (Y t) (hstationary t ht)
    have he : H = (gradientGenerator_memLp P f L hLip Mdelta hMdelta hδ (Y t)).toLp
        (fun a ↦ gradientGenerator f (Y t a)) := by
      apply Lp.ext
      exact (stationaryObservation_coe P π _ hgen (Y t) (hstationary t ht)).trans
        (gradientGenerator_memLp P f L hLip Mdelta hMdelta hδ (Y t)).coeFn_toLp.symm
    have hH : ‖H‖ ≤ R := by
      rw [he]
      exact lp_gradientGenerator_gibbs_norm_le P hp f m L hm hsc hLip Mdelta hMdelta hδ
        (Y t) (hstationary t ht)
    have hd : ‖stationaryObservation P π (GFn n) (hGFn n) (Y t) (hstationary t ht) - H‖ =
        err n := by
      dsimp [err, H]
      rw [← stationaryObservation_sub_norm_sq P π (GFn n) (gradientGenerator f)
        (hGc n) htargetc (hGFn n) hgen (Y t) (hstationary t ht),
        Real.sqrt_sq (norm_nonneg _)]
    exact (norm_le_norm_sub_add _ H).trans (by rw [hd]; linarith)
  let Gn' : ℕ → ℝ → Lp (State p) 2 P := fun n t ↦
    if ht : t ∈ Icc 0 T then
      stationaryObservation P π (GFn n) (hGFn n) (Y t) (hstationary t ht) else 0
  have hweightMeas (j : Fin p) : Measurable (fun a ↦ Ψr a j) :=
    (PiLp.continuous_apply 2 (fun _ : Fin p ↦ ℝ) j).measurable.comp
      (Lp.stronglyMeasurable Ψr).measurable
  have hcoordBound (j : Fin p) : ∀ᵐ a ∂P, |Ψr a j| ≤ (r : ℝ) + 1 := by
    filter_upwards [hΨr] with a ha
    exact (show |Ψr a j| ≤ ‖Ψr a‖ by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (Ψr a) j).trans ha
  have hidentity (n : ℕ) : inner ℝ Ψr (Xn n - Yn n) =
      ∫ t in 0..T, inner ℝ Ψr (Gn' n t) := by
    have hscalarIdentity (j : Fin p) :
        lpWeightedTest P (fun a ↦ Ψr a j) (φ n j) (Y T) -
          lpWeightedTest P (fun a ↦ Ψr a j) (φ n j) initial =
            ∫ t in 0..T, lpWeightedTest P (fun a ↦ Ψr a j)
              (ULA.langevinGenerator f (φ n j)) (Y t) := by
      apply lp_langevin_weighted_dynkin_compact P f L hLip initial B hB
        (fun a ↦ Ψr a j) (hweightMeas j)
        ((r : ℝ) + 1) (by positivity) _ hscalar _ Y hY T hT hYe
        (φ n j) (hφ n j).1 (hφ n j).2
      · exact hcoordBound j
      · intro s hs
        exact (hindr s hs).comp
          (φ := fun q : State p × State p ↦ (q.1 j, q.2)) (ψ := id)
          (((PiLp.continuous_apply 2 (fun _ : Fin p ↦ ℝ) j).measurable.comp
            measurable_fst).prodMk measurable_snd) measurable_id
    have hInt (j : Fin p) : IntervalIntegrable (fun t ↦ lpWeightedTest P
        (fun a ↦ Ψr a j) (ULA.langevinGenerator f (φ n j)) (Y t)) volume 0 T := by
      obtain ⟨huc, C, hC, hb⟩ := compact_test_generator_bounded_uniformContinuous f L hLip
        (φ n j) (hφ n j).1 (hφ n j).2
      exact ((lpWeightedTest_uniformContinuous P _ (hweightMeas j)
        ((r : ℝ) + 1) (by positivity) (hcoordBound j) _ huc C hC hb).continuous.comp hY
        ).intervalIntegrable 0 T
    rw [inner_sub_right,
      stationaryObservation_inner_eq_sum P π (Fn n) (hFc n) (hFn n) (Y T) hTlaw Ψr,
      stationaryObservation_inner_eq_sum P π (Fn n) (hFc n) (hFn n) initial hinitlaw Ψr,
      ← Finset.sum_sub_distrib]
    calc
      _ = ∑ j : Fin p, ∫ t in 0..T, lpWeightedTest P (fun a ↦ Ψr a j)
          (ULA.langevinGenerator f (φ n j)) (Y t) := by
        apply Finset.sum_congr rfl
        intro j _
        exact hscalarIdentity j
      _ = ∫ t in 0..T, ∑ j : Fin p, lpWeightedTest P (fun a ↦ Ψr a j)
          (ULA.langevinGenerator f (φ n j)) (Y t) :=
        (intervalIntegral.integral_finsetSum (fun j _ ↦ hInt j)).symm
      _ = _ := by
        apply intervalIntegral.integral_congr_ae_restrict
        filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with t ht
        have ht' : t ∈ Icc 0 T := by
          rw [uIoc_of_le hT] at ht
          exact ⟨ht.1.le, ht.2⟩
        dsimp [Gn']
        rw [dite_eq_left ht', stationaryObservation_inner_eq_sum P π (GFn n) (hGc n)
          (hGFn n) (Y t) (hstationary t ht') Ψr]
  exact pairing_bound_of_compact_dynkin_approximations Ψr _ _ Xn Yn Gn' T R hT hR
    err herr herrlim hXlim hYlim
    (fun n t ht ↦ by dsimp [Gn']; rw [dite_eq_left ht]; exact hgenNorm n t ht) hidentity

end AverageLMC
