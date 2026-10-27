import AverageLMC.CompactC2Taylor
import AverageLMC.LaplacianIndependentSteps
import AverageLMC.LaplacianWeightedTest
import UnadjustedLangevin.GibbsStationarity

set_option linter.style.header false
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace AverageLMC

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

/-- A bounded weight times a bounded measurable observation is integrable. -/
theorem integrable_bounded_weight_observation
    (P : Measure Ω) [IsProbabilityMeasure P] (w F : Ω → ℝ)
    (hw : Measurable w) (hF : Measurable F) (A C : ℝ) (hA : 0 ≤ A)
    (hwA : ∀ᵐ a ∂P, |w a| ≤ A) (hFC : ∀ a, |F a| ≤ C) :
    Integrable (fun a ↦ w a * F a) P := by
  apply (integrable_const (A * C)).mono' (hw.mul hF).aestronglyMeasurable
  filter_upwards [hwA] with a ha
  simpa only [Real.norm_eq_abs, Pi.mul_apply, abs_mul] using
    mul_le_mul ha (hFC a) (abs_nonneg _) hA

omit [CompleteSpace H] in
/-- The product joint law of a retained past weight, Euler state and fresh
Gaussian innovation gives the actual weighted conditional Gaussian integral. -/
theorem fresh_weighted_gaussian_integral
    (P : Measure Ω) [IsProbabilityMeasure P]
    (φ : H → ℝ) (hφ : Continuous φ) (C : ℝ) (hφC : ∀ x, |φ x| ≤ C)
    (b : H → H) (hb : Measurable b) (x z : Ω → H) (w : Ω → ℝ)
    (hx : Measurable x) (hz : Measurable z) (hw : Measurable w)
    (A : ℝ) (hA : 0 ≤ A) (hwA : ∀ᵐ a ∂P, |w a| ≤ A)
    (hfresh : P.map (fun a ↦ ((w a, x a), z a)) =
      (P.map (fun a ↦ (w a, x a))).prod (stdGaussian H)) (h : ℝ) :
    (∫ a, w a * φ (x a + h • b (x a) + Real.sqrt (2 * h) • z a) ∂P) =
      ∫ a, w a * (∫ y : H, φ (x a + h • b (x a) + Real.sqrt (2 * h) • y)
        ∂stdGaussian H) ∂P := by
  let F : (ℝ × H) × H → ℝ := fun q ↦
    q.1.1 * φ (q.1.2 + h • b q.1.2 + Real.sqrt (2 * h) • q.2)
  have hFm : Measurable F := by dsimp [F]; fun_prop
  have hmap := Measure.map_prod_map P (stdGaussian H) (hw.prodMk hx) measurable_id
  rw [Measure.map_id] at hmap
  have heq : (∫ a, w a * φ (x a + h • b (x a) + Real.sqrt (2 * h) • z a) ∂P) =
      ∫ q : Ω × H, w q.1 * φ (x q.1 + h • b (x q.1) + Real.sqrt (2 * h) • q.2)
        ∂P.prod (stdGaussian H) := by
    calc
      _ = ∫ q, F q ∂P.map (fun a ↦ ((w a, x a), z a)) :=
        (integral_map ((hw.prodMk hx).prodMk hz).aemeasurable hFm.aestronglyMeasurable).symm
      _ = ∫ q, F q ∂(P.map (fun a ↦ (w a, x a))).prod (stdGaussian H) := by rw [hfresh]
      _ = _ := by
        rw [hmap, integral_map ((hw.prodMk hx).prodMap measurable_id).aemeasurable
          hFm.aestronglyMeasurable]
        rfl
  rw [heq]
  have hi : Integrable (fun q : Ω × H ↦
      w q.1 * φ (x q.1 + h • b (x q.1) + Real.sqrt (2 * h) • q.2))
      (P.prod (stdGaussian H)) := by
    apply integrable_bounded_weight_observation _ _ _ (hw.comp measurable_fst)
      (by fun_prop) A C hA _ (fun q ↦ hφC _)
    exact measurePreserving_fst.quasiMeasurePreserving.ae hwA
  rw [integral_prod _ hi]
  apply integral_congr_ae
  apply ae_of_all
  intro a
  change (∫ y : H, w a * φ (x a + h • b (x a) + Real.sqrt (2 * h) • y)
    ∂stdGaussian H) = _
  exact integral_const_mul _ _

/-- The uniform compact-C² consistency estimate applies to an actual fresh
Gaussian Euler step while retaining its bounded past weight. Its constant K
is the same at every mesh point. -/
theorem fresh_weighted_weak_step_of_bound
    (P : Measure Ω) [IsProbabilityMeasure P]
    (φ : H → ℝ) (hφ : ContDiff ℝ 2 φ) (C : ℝ) (hφC : ∀ x, |φ x| ≤ C)
    (b : H → H) (hb : Measurable b) (x z : Ω → H) (w : Ω → ℝ)
    (hx : Measurable x) (hz : Measurable z) (hw : Measurable w)
    (hb₂ : MemLp (fun a ↦ b (x a)) 2 P)
    (hgen : Integrable (fun a ↦ w a *
      (fderiv ℝ φ (x a) (b (x a)) + Laplacian.laplacian φ (x a))) P)
    (A : ℝ) (hA : 0 ≤ A) (hwA : ∀ᵐ a ∂P, |w a| ≤ A)
    (hfresh : P.map (fun a ↦ ((w a, x a), z a)) =
      (P.map (fun a ↦ (w a, x a))).prod (stdGaussian H))
    (ε : ℝ) (hε : 0 < ε) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ (x v : H) (h : ℝ), 0 ≤ h → h ≤ 1 →
      |(∫ z : H, φ (x + h • v + Real.sqrt (2 * h) • z) ∂stdGaussian H) -
        φ x - h * (fderiv ℝ φ x v + Laplacian.laplacian φ x)| ≤
          h * (ε + K * Real.sqrt h) * (1 + ‖v‖ ^ 2))
    (h : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    |(∫ a, w a * φ (x a + h • b (x a) + Real.sqrt (2 * h) • z a) ∂P) -
      (∫ a, w a * φ (x a) ∂P) -
      h * (∫ a, w a * (fderiv ℝ φ (x a) (b (x a)) + Laplacian.laplacian φ (x a)) ∂P)| ≤
      A * h * (ε + K * Real.sqrt h) * (1 + ∫ a, ‖b (x a)‖ ^ 2 ∂P) := by
  have hweak := gaussian_weighted_weak_step_of_bound P φ hφ x (fun a ↦ b (x a)) w A
    hx (hb.comp hx) hw hb₂ hA hwA ε hε K hK hbound h hh hh1
  have hprod : Integrable (fun q : Ω × H ↦
      w q.1 * φ (x q.1 + h • b (x q.1) + Real.sqrt (2 * h) • q.2))
      (P.prod (stdGaussian H)) := by
    apply integrable_bounded_weight_observation _ _ _ (hw.comp measurable_fst)
      (by have := hφ.continuous.measurable; fun_prop) A C hA
      (measurePreserving_fst.quasiMeasurePreserving.ae hwA) (fun q ↦ hφC _)
  have hmean := hprod.integral_prod_left
  simp_rw [integral_const_mul] at hmean
  have hbase := integrable_bounded_weight_observation P w (fun a ↦ φ (x a)) hw
    (hφ.continuous.measurable.comp hx) A C hA hwA (fun a ↦ hφC _)
  have heq : (fun a ↦ w a * ((∫ z : H,
      φ (x a + h • b (x a) + Real.sqrt (2 * h) • z) ∂stdGaussian H) -
      φ (x a) - h * (fderiv ℝ φ (x a) (b (x a)) + Laplacian.laplacian φ (x a)))) =
      (fun a ↦ (w a * (∫ z : H,
        φ (x a + h • b (x a) + Real.sqrt (2 * h) • z) ∂stdGaussian H) -
        w a * φ (x a)) - h * (w a *
          (fderiv ℝ φ (x a) (b (x a)) + Laplacian.laplacian φ (x a)))) := by
    funext a
    ring
  rw [heq] at hweak
  rw [integral_sub
    (f := fun a ↦ w a * (∫ y : H, φ (x a + h • b (x a) + Real.sqrt (2 * h) • y)
      ∂stdGaussian H) - w a * φ (x a))
    (g := fun a ↦ h * (w a *
      (fderiv ℝ φ (x a) (b (x a)) + Laplacian.laplacian φ (x a))))
    (hmean.sub hbase) (hgen.const_mul h),
    integral_sub hmean hbase, integral_const_mul] at hweak
  rw [fresh_weighted_gaussian_integral P φ hφ.continuous C hφC b hb x z w hx hz hw A hA hwA hfresh h]
  exact hweak

/-- A sum of actual one-step residual bounds gives the full finite-horizon
weighted consistency estimate by telescoping. -/
theorem sum_weighted_weak_residual (a c : ℕ → ℝ) (h E : ℝ) (n : ℕ)
    (_hE : 0 ≤ E) (hlocal : ∀ k < n, |a (k + 1) - a k - h * c k| ≤ E) :
    |a n - a 0 - ∑ k ∈ Finset.range n, h * c k| ≤ (n : ℝ) * E := by
  have ht : ∑ k ∈ Finset.range n, (a (k + 1) - a k - h * c k) =
      a n - a 0 - ∑ k ∈ Finset.range n, h * c k := by
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub]
  rw [← ht]
  calc
    _ ≤ ∑ k ∈ Finset.range n, |a (k + 1) - a k - h * c k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, E := Finset.sum_le_sum fun k hk ↦ hlocal k (Finset.mem_range.mp hk)
    _ = _ := by simp

/-- Passive-coordinate recursion proves freshness jointly with every bounded
function of the initialization, for the actual L² Euler chain. -/
theorem hilbert_lpChain_weighted_fresh
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : H → ℝ) (h : ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (initial : Lp H 2 P) (W : ℕ → Lp H 2 P) (w : Ω → ℝ) (hw : Measurable w)
    (hind : IndepFun (fun a ↦ (w a, initial a)) (fun a k ↦ W k a) P)
    (hiid : iIndepFun (fun k a ↦ W k a) P)
    (hlaw : ∀ k, P.map (W k) = stdGaussian H) (k : ℕ) :
    P.map (fun a ↦ ((w a, ULA.Hilbert.lpChain P U h hLip initial W k a), W k a)) =
      (P.map (fun a ↦ (w a, ULA.Hilbert.lpChain P U h hLip initial W k a))).prod
        (stdGaussian H) := by
  let F := ULA.Hilbert.pointwiseUpdate U h
  let Fp : ℝ × H → H → ℝ × H := fun q z ↦ (q.1, F q.2 z)
  have hFm := ULA.Hilbert.pointwiseUpdate_measurable U h L hLip
  have hFpm : Measurable (Function.uncurry Fp) := by
    exact measurable_fst.fst.prodMk (hFm.comp (measurable_fst.snd.prodMk measurable_snd))
  have hj := noiseDrivenChain_joint_fresh_of_iid P Fp hFpm
    (fun a ↦ (w a, initial a)) (fun k a ↦ W k a)
    (hw.prodMk (Lp.stronglyMeasurable initial).measurable).aemeasurable
    (fun k ↦ (Lp.aestronglyMeasurable (W k)).aemeasurable) hind hiid (stdGaussian H) hlaw k
  simp only [Fp, noiseDrivenChain_passive] at hj
  have hc := ULA.hilbert_lpChain_coe P U h L hLip initial W k
  have hm₁ : P.map (fun a ↦ ((w a, ULA.Hilbert.lpChain P U h hLip initial W k a), W k a)) =
      P.map (fun a ↦ ((w a, ULA.noiseDrivenChain F (initial a) (fun j ↦ W j a) k), W k a)) :=
    Measure.map_congr (hc.mono fun a ha ↦
    show ((w a, ULA.Hilbert.lpChain P U h hLip initial W k a), W k a) =
      ((w a, ULA.noiseDrivenChain F (initial a) (fun j ↦ W j a) k), W k a) by rw [ha])
  have hm₂ : P.map (fun a ↦ (w a, ULA.Hilbert.lpChain P U h hLip initial W k a)) =
      P.map (fun a ↦ (w a, ULA.noiseDrivenChain F (initial a) (fun j ↦ W j a) k)) :=
    Measure.map_congr (hc.mono fun a ha ↦
    show (w a, ULA.Hilbert.lpChain P U h hLip initial W k a) =
      (w a, ULA.noiseDrivenChain F (initial a) (fun j ↦ W j a) k) by rw [ha])
  rw [hm₁, hm₂]
  exact hj

/-- The proved one-step residual for the genuine quotient-valued Euler
recursion. The only stochastic inputs are its actual iid Gaussian laws. -/
theorem hilbert_lpChain_weak_step_of_bound
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : H → ℝ) (h : ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (initial : Lp H 2 P) (W : ℕ → Lp H 2 P) (w : Ω → ℝ) (hw : Measurable w)
    (hind : IndepFun (fun a ↦ (w a, initial a)) (fun a k ↦ W k a) P)
    (hiid : iIndepFun (fun k a ↦ W k a) P)
    (hlaw : ∀ k, P.map (W k) = stdGaussian H)
    (φ : H → ℝ) (hφ : ContDiff ℝ 2 φ)
    (C D : ℝ) (hφC : ∀ x, |φ x| ≤ C) (hGD : ∀ x, |ULA.langevinGenerator U φ x| ≤ D)
    (A : ℝ) (hA : 0 ≤ A) (hwA : ∀ᵐ a ∂P, |w a| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ (x v : H) (h : ℝ), 0 ≤ h → h ≤ 1 →
      |(∫ z : H, φ (x + h • v + Real.sqrt (2 * h) • z) ∂stdGaussian H) -
        φ x - h * (fderiv ℝ φ x v + Laplacian.laplacian φ x)| ≤
          h * (ε + K * Real.sqrt h) * (1 + ‖v‖ ^ 2))
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (k : ℕ) :
    |lpWeightedTest P w φ (ULA.Hilbert.lpChain P U h hLip initial W (k + 1)) -
      lpWeightedTest P w φ (ULA.Hilbert.lpChain P U h hLip initial W k) -
      h * lpWeightedTest P w (ULA.langevinGenerator U φ) (ULA.Hilbert.lpChain P U h hLip initial W k)| ≤
      A * h * (ε + K * Real.sqrt h) *
        (1 + ‖ULA.lpDrift P (gradient U) hLip (ULA.Hilbert.lpChain P U h hLip initial W k)‖ ^ 2) := by
  let X := ULA.Hilbert.lpChain P U h hLip initial W k
  have hx : Measurable X := (Lp.stronglyMeasurable X).measurable
  have hG (x : H) : fderiv ℝ φ x (-gradient U x) + Laplacian.laplacian φ x =
      ULA.langevinGenerator U φ x := by
    rw [ULA.langevinGenerator_eq_laplacian_sub_inner U φ hφ]
    simp only [map_neg, ← inner_gradient_left, real_inner_comm (gradient φ x)]
    ring
  have hGc : Continuous (ULA.langevinGenerator U φ) :=
    continuous_finsetSum _ (fun i _ ↦ ULA.continuous_directionalGenerator U L hLip φ hφ _)
  have hgen : Integrable (fun a ↦ w a *
      (fderiv ℝ φ (X a) (-gradient U (X a)) + Laplacian.laplacian φ (X a))) P := by
    simp_rw [hG]
    exact integrable_bounded_weight_observation P w _ hw (hGc.measurable.comp hx)
      A D hA hwA (fun a ↦ hGD _)
  have hweak := fresh_weighted_weak_step_of_bound P φ hφ C hφC
    (fun x ↦ -gradient U x) hLip.continuous.measurable.neg X (W k) w hx
    (Lp.stronglyMeasurable (W k)).measurable hw (ULA.lpDrift_memLp P _ hLip X).neg hgen
    A hA hwA (hilbert_lpChain_weighted_fresh P U h L hLip initial W w hw hind hiid hlaw k)
    ε hε K hK hbound h hh hh1
  have hnext : (∫ a, w a * φ (ULA.Hilbert.lpChain P U h hLip initial W (k + 1) a) ∂P) =
      ∫ a, w a * φ (X a + h • (-gradient U (X a)) + Real.sqrt (2 * h) • W k a) ∂P := by
    apply integral_congr_ae
    filter_upwards [ULA.lpUlaUpdate_coe P U h hLip X (W k)] with a ha
    change w a * φ (ULA.lpUlaUpdate P U h hLip X (W k) a) = _
    rw [ha]
    simp only [smul_neg, sub_eq_add_neg]
  have hnorm : ‖ULA.lpDrift P (gradient U) hLip X‖ ^ 2 =
      ∫ a, ‖gradient U (X a)‖ ^ 2 ∂P := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ULA.lpDrift_coe P _ hLip X] with a ha
    rw [ha, real_inner_self_eq_norm_sq]
  dsimp only [lpWeightedTest]
  rw [hnext]
  simp only [hG, norm_neg] at hweak
  rw [← hnorm] at hweak
  exact hweak

/-- Summed weak consistency for the actual iid Euler chain with one common
L² drift bound. This is the stochastic input to the deterministic Dynkin
limit, and does not assume a martingale or generator identity. -/
theorem hilbert_lpChain_weak_sum_of_bound
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : H → ℝ) (h : ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (initial : Lp H 2 P) (W : ℕ → Lp H 2 P) (w : Ω → ℝ) (hw : Measurable w)
    (hind : IndepFun (fun a ↦ (w a, initial a)) (fun a k ↦ W k a) P)
    (hiid : iIndepFun (fun k a ↦ W k a) P)
    (hlaw : ∀ k, P.map (W k) = stdGaussian H)
    (φ : H → ℝ) (hφ : ContDiff ℝ 2 φ)
    (C D : ℝ) (hφC : ∀ x, |φ x| ≤ C) (hGD : ∀ x, |ULA.langevinGenerator U φ x| ≤ D)
    (A : ℝ) (hA : 0 ≤ A) (hwA : ∀ᵐ a ∂P, |w a| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ (x v : H) (h : ℝ), 0 ≤ h → h ≤ 1 →
      |(∫ z : H, φ (x + h • v + Real.sqrt (2 * h) • z) ∂stdGaussian H) -
        φ x - h * (fderiv ℝ φ x v + Laplacian.laplacian φ x)| ≤
          h * (ε + K * Real.sqrt h) * (1 + ‖v‖ ^ 2))
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (n : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hboundR : ∀ k ≤ n,
      ‖ULA.lpDrift P (gradient U) hLip (ULA.Hilbert.lpChain P U h hLip initial W k)‖ ≤ R) :
    |lpWeightedTest P w φ (ULA.Hilbert.lpChain P U h hLip initial W n) -
      lpWeightedTest P w φ initial - ∑ k ∈ Finset.range n,
        h * lpWeightedTest P w (ULA.langevinGenerator U φ)
          (ULA.Hilbert.lpChain P U h hLip initial W k)| ≤
      A * ((n : ℝ) * h) * (ε + K * Real.sqrt h) * (1 + R ^ 2) := by
  have hlocal (k : ℕ) (hk : k < n) :
      |lpWeightedTest P w φ (ULA.Hilbert.lpChain P U h hLip initial W (k + 1)) -
        lpWeightedTest P w φ (ULA.Hilbert.lpChain P U h hLip initial W k) -
        h * lpWeightedTest P w (ULA.langevinGenerator U φ)
          (ULA.Hilbert.lpChain P U h hLip initial W k)| ≤
      A * h * (ε + K * Real.sqrt h) * (1 + R ^ 2) := by
    have hb := hilbert_lpChain_weak_step_of_bound P U h L hLip initial W w hw hind hiid hlaw
      φ hφ C D hφC hGD A hA hwA ε hε K hK hbound hh hh1 k
    have hs := (sq_le_sq₀ (norm_nonneg _) hR).mpr (hboundR k hk.le)
    exact hb.trans (mul_le_mul_of_nonneg_left (by linarith : 1 + _ ≤ 1 + R ^ 2) (by positivity))
  have hb := sum_weighted_weak_residual
    (fun k ↦ lpWeightedTest P w φ (ULA.Hilbert.lpChain P U h hLip initial W k))
    (fun k ↦ lpWeightedTest P w (ULA.langevinGenerator U φ)
      (ULA.Hilbert.lpChain P U h hLip initial W k))
    h (A * h * (ε + K * Real.sqrt h) * (1 + R ^ 2)) n (by positivity) hlocal
  change |lpWeightedTest P w φ (ULA.Hilbert.lpChain P U h hLip initial W n) -
    lpWeightedTest P w φ initial - _| ≤ _ at hb
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hb

end AverageLMC
