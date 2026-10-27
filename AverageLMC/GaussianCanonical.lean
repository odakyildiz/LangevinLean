import AverageLMC.GaussianBrownian
import AverageLMC.ExpectedGradientStep
import AverageLMC.SquaredTransport

set_option linter.style.header false
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal RealInnerProductSpace
namespace AverageLMC
open ULA ULA.Hilbert
variable {ι : Type*} [Fintype ι]

/-- The paper's one-step bound for the actual independent Gaussian LMC update.
The sole auxiliary premise is the coordinate smoothing conclusion, proved
from the exact coordinate constants in `Smoothing.lean`. All diffusion,
stationarity, moment and orthogonality facts are constructed internally. -/
theorem lmc_coupling_step (f : EuclideanSpace ℝ ι → ℝ) (m h Mav : ℝ) (L : ℝ≥0)
    (hm : 0 < m) (hh : 0 < h) (hf : Differentiable ℝ f)
    (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith L (gradient f))
    (hsm : ∀ x s, 0 ≤ s → (∫ z, f (x + Real.sqrt (2 * s) • z) - f x
      ∂stdGaussian (EuclideanSpace ℝ ι)) ≤ Mav * (Fintype.card ι : ℝ) * s)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (c : Coupling μ (gibbsMeasure f)) (hc : couplingCost c.joint ≠ ⊤) :
    wasserstein2 (ulaLawStep f h μ) (gibbsMeasure f) ≠ ⊤ ∧
    (1 + m * h) * wasserstein2Real (ulaLawStep f h μ) (gibbsMeasure f) ^ 2 ≤
      (1 - m * h) * (couplingCost c.joint).toReal ^ 2 +
      (Mav + m) * h ^ 2 * (Fintype.card ι : ℝ) +
      h ^ 2 * (h * (L : ℝ) - 1) * (∫ x, ‖gradient f x‖ ^ 2 ∂μ) := by
  let Q := CanonicalBrownian.vectorProbability ι
  let P := initialExtension c Q
  have : IsProbabilityMeasure P := initialExtension_isProbabilityMeasure c Q
  have : IsProbabilityMeasure c.joint := c.isProbabilityMeasure
  let hπ := productGibbsMemLp f m hm hf hsc
  let X := initialExtension_lpInitial c Q hc hπ
  let Z := initialExtension_lpReference c Q hπ
  let W := fun i t (p : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ×
      CanonicalBrownian.VectorSample ι) => CanonicalBrownian.coordinate i t p.2
  have hW : ∀ i, IsPreBrownianReal (W i) P :=
    productPreBrownian Q c CanonicalBrownian.coordinate CanonicalBrownian.coordinate_isPreBrownian
  have hcoord (i : ι) (t : ℝ≥0) :
      Measurable (fun ω : CanonicalBrownian.VectorSample ι => CanonicalBrownian.coordinate i t ω) :=
    (CanonicalBrownian.process_measurable t).comp (measurable_pi_apply i)
  have hfull : Measurable (fun ω : CanonicalBrownian.VectorSample ι =>
      fun (i : ι) (t : ℝ≥0) => CanonicalBrownian.coordinate i t ω) :=
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun t => hcoord i t
  have hWmeas : ∀ i t, Measurable (W i t) := by
    intro i t
    exact (hcoord i t).comp measurable_snd
  have hWpaths : iIndepFun (fun i ω t => W i t ω) P := by
    apply (iIndepFun_iff_map_fun_eq_infinitePi_map
      (fun i => measurable_pi_iff.mpr fun t => hWmeas i t)).mpr
    have hs := (CanonicalBrownian.coordinate_paths_independent ι).map_fun_eq_infinitePi_map
      (fun i => measurable_pi_iff.mpr fun t => hcoord i t)
    have hmap : P.map (fun ω i t => W i t ω) =
        Q.map (fun ω i t => CanonicalBrownian.coordinate i t ω) := by
      change P.map ((fun ω i t => CanonicalBrownian.coordinate i t ω) ∘ Prod.snd) = _
      rw [← Measure.map_map hfull measurable_snd, initialExtension_noise]
    rw [hmap, hs]
    congr 1
    funext i
    change Q.map (fun ω t => CanonicalBrownian.coordinate i t ω) =
      P.map ((fun ω t => CanonicalBrownian.coordinate i t ω) ∘ Prod.snd)
    rw [← Measure.map_map (measurable_pi_iff.mpr fun t => hcoord i t) measurable_snd,
      initialExtension_noise]
  have hZpaths : IndepFun Z (fun ω (i : ι) (t : ℝ≥0) => W i t ω) P := by
    have hi := (initialExtension_independent c Q).comp measurable_snd
      hfull
    exact hi.congr (initialExtension_memLp_reference c Q hπ).coeFn_toLp.symm
      (ae_of_all _ fun _ => rfl)
  have hscalar : ∀ r : ℝ, 0 < r → iIndepFun (fun p : ℕ × ι => fun ω =>
      brownianEulerNoise P W hW r p.1 ω p.2) P := by
    intro r hr
    have hs := productEulerNoise_independent Q c CanonicalBrownian.coordinate
      CanonicalBrownian.coordinate_isPreBrownian r hr
      (CanonicalBrownian.coordinate_grid_paths_independent ι r.toNNReal)
    simpa only [productNoise_eq_brownianEulerNoise] using hs
  have hind : ∀ r : ℝ, 0 < r → IndepFun Z
      (fun ω n => brownianEulerNoise P W hW r n ω) P := by
    intro r _hr
    have hs := productEulerNoise_independentReference Q c hπ CanonicalBrownian.coordinate
      CanonicalBrownian.coordinate_isPreBrownian r
    simpa only [productNoise_eq_brownianEulerNoise] using hs
  have hZlaw : P.map Z = gibbsMeasure f := initialExtension_lpReference_law c Q hπ
  obtain ⟨Y, hY, hY0, hYe, _hnoise⟩ := exists_lp_langevin_integral_of_brownian
    P f L hLip Z W hW 0 h le_rfl hh.le
  have hYlaw (t : ℝ) (ht : t ∈ Icc 0 h) : P.map (Y t) = gibbsMeasure f :=
    lp_langevin_gibbs_stationary P f m L hm hf hsc hLip Z hZlaw W hW
      hscalar hind Y hY t ht.1 (fun s hs => hYe s ⟨hs.1, hs.2.trans ht.2⟩)
  let B := brownianLangevinNoise P W hW 0
  let A := X - h • lpDrift P (gradient f) hLip X
  let V := fun r ↦ brownianEulerNoise P W hW r 0
  let T := fun x ↦ x - h • gradient f x
  have hTm : Measurable T := measurable_id.sub (hLip.continuous.measurable.const_smul h)
  have hAcoe : A =ᵐ[P] fun ω ↦ T (X ω) := by
    filter_upwards [Lp.coeFn_sub X (h • lpDrift P (gradient f) hLip X),
      Lp.coeFn_smul h (lpDrift P (gradient f) hLip X), lpDrift_coe P (gradient f) hLip X]
      with ω hs hsm hg
    change (X - h • lpDrift P (gradient f) hLip X) ω = T (X ω)
    simp only [hs, Pi.sub_apply, hsm, Pi.smul_apply, hg, T]
  have hXlaw : P.map X = μ := initialExtension_lpInitial_law c Q hc hπ
  have hXpath : IndepFun X (fun ω (i : ι) (t : ℝ≥0) ↦ W i t ω) P := by
    have hi := (initialExtension_independent c Q).comp measurable_fst hfull
    exact hi.congr (initialExtension_memLp_initial c Q hc hπ).coeFn_toLp.symm
      (ae_of_all _ fun _ ↦ rfl)
  have hApaths : IndepFun A (fun ω (i : ι) (t : ℝ≥0) ↦ W i t ω) P :=
    (hXpath.comp hTm measurable_id).congr hAcoe.symm Filter.EventuallyEq.rfl
  have hVlaw (r : ℝ) (hr : 0 < r) : P.map (V r) = stdGaussian (EuclideanSpace ℝ ι) :=
    (brownianEulerNoise_vectorGaussian P W hW r hr (hscalar r hr)).2 0
  have hXV (r : ℝ) : IndepFun X (V r) P := by
    have hi := productEulerNoise_independentInitial Q c hc hπ CanonicalBrownian.coordinate
      CanonicalBrownian.coordinate_isPreBrownian r
    have hi' : IndepFun X (fun ω n ↦ brownianEulerNoise P W hW r n ω) P := by
      simpa only [productNoise_eq_brownianEulerNoise] using hi
    exact hi'.comp measurable_id (measurable_pi_apply 0)
  have hAV (r : ℝ) : IndepFun A (V r) P :=
    ((hXV r).comp hTm measurable_id).congr hAcoe.symm Filter.EventuallyEq.rfl
  have hBr (r : ℝ) (hr : 0 < r) : B r = Real.sqrt (2 * r) • V r := by
    simpa only [Nat.cast_zero, zero_mul] using brownianEulerNoise_endpoint P W hW r hr 0
  have houtcoe : A + B h =ᵐ[P] fun ω ↦ pointwiseUpdate f h (X ω) (V h ω) := by
    rw [hBr h hh]
    exact lpUlaUpdate_coe P f h hLip X (V h)
  have hout : P.map (A + B h) = ulaLawStep f h μ := by
    have hj := (hXV h).map_prod_eq_prod_map_map
      (Lp.aestronglyMeasurable X).aemeasurable (Lp.aestronglyMeasurable (V h)).aemeasurable
    rw [hXlaw, hVlaw h hh] at hj
    rw [Measure.map_congr houtcoe]
    have he := AEMeasurable.map_map_of_aemeasurable
      (pointwiseUpdate_measurable f h L hLip).aemeasurable
      ((Lp.aestronglyMeasurable X).aemeasurable.prodMk
        (Lp.aestronglyMeasurable (V h)).aemeasurable)
    calc
      _ = (P.map (fun ω ↦ (X ω, V h ω))).map
          (Function.uncurry (pointwiseUpdate f h)) := he.symm
      _ = ulaLawStep f h μ := by rw [hj]; rfl
  have hcost (t : ℝ) (ht : t ∈ Icc 0 h) :
      wasserstein2Real (ulaLawStep f h μ) (gibbsMeasure f) ^ 2 ≤ ‖A + B h - Y t‖ ^ 2 := by
    have htr := wasserstein2_le_Lp_cost P (A + B h) (Y t)
    rw [hout, hYlaw t ht] at htr
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top htr
    rw [ENNReal.toReal_ofReal (norm_nonneg _)] at hr
    exact (sq_le_sq₀ ENNReal.toReal_nonneg (norm_nonneg _)).mpr hr
  have hfinite : wasserstein2 (ulaLawStep f h μ) (gibbsMeasure f) ≠ ⊤ := by
    have htr := wasserstein2_le_Lp_cost P (A + B h) (Y h)
    rw [hout, hYlaw h ⟨hh.le, le_rfl⟩] at htr
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top htr
  have henergy (t : ℝ) (ht : t ∈ Icc 0 h) :
      (∫ ω, f ((A + B t) ω) ∂P) - ∫ ω, f (Y t ω) ∂P ≤
      ((∫ ω, f (A ω) ∂P) - ∫ ω, f (Z ω) ∂P) +
        (Mav * (Fintype.card ι : ℝ)) * t := by
    have hstat : (∫ ω, f (Y t ω) ∂P) = ∫ ω, f (Z ω) ∂P := by
      rw [← integral_map (Lp.aestronglyMeasurable (Y t)).aemeasurable
        hf.continuous.aestronglyMeasurable,
        ← integral_map (Lp.aestronglyMeasurable Z).aemeasurable hf.continuous.aestronglyMeasurable,
        hYlaw t ht, hZlaw]
    rw [hstat]
    rcases eq_or_lt_of_le ht.1 with ht0 | htpos
    · subst t
      simp [B]
    · have hi := independent_smoothing P f L hf hLip A (V t)
        (stdGaussian (EuclideanSpace ℝ ι)) (hVlaw t htpos) (hAV t)
        (Real.sqrt (2 * t)) (Mav * (Fintype.card ι : ℝ) * t)
        (fun x ↦ hsm x t ht.1)
      rw [← hBr t htpos] at hi
      linarith
  have heq (t : ℝ) (ht : t ∈ Icc 0 h) : Y t - Y 0 =
      -(∫ s in 0..t, lpDrift P (gradient f) hLip (Y s)) + B t := by
    rw [hY0]
    exact hYe t ht
  have horth (t : ℝ) (ht : t ∈ Icc 0 h) : ⟪A + B t - Y t, B h - B t⟫ = 0 :=
    gaussian_error_future_inner_zero P f L hLip A Z W hW hWmeas hWpaths hApaths hZpaths
      Y hY t h ht.1 ht.2 hYe
  have hg := gaussian_energy_bound P f m h (Fintype.card ι : ℝ)
    ((∫ ω, f (A ω) ∂P) - ∫ ω, f (Z ω) ∂P) (Mav * (Fintype.card ι : ℝ))
    (wasserstein2Real (ulaLawStep f h μ) (gibbsMeasure f) ^ 2) L
    hf hsc hLip hm.le hh.le A Y B hY (brownianLangevinNoise_continuous P W hW 0)
    heq horth (fun t ht ↦ brownian_future_norm_sq P W hW t h ht.1 ht.2) hcost henergy
  rw [hY0] at hg
  have hgd := lp_gradient_step P f m h L hf hsc hLip hh.le X Z
  have hdesc := lp_gradient_descent P f h L hf hLip hh.le X
  have hscaled := mul_le_mul_of_nonneg_left hdesc hh.le
  rw [initialExtension_lp_cost c Q hc hπ] at hgd
  have hscore : ‖lpDrift P (gradient f) hLip X‖ ^ 2 = ∫ x, ‖gradient f x‖ ^ 2 ∂μ := by
    calc
      _ = ∫ ω, ‖gradient f (X ω)‖ ^ 2 ∂P := lpDrift_norm_sq P (gradient f) hLip X
      _ = ∫ x, ‖gradient f x‖ ^ 2 ∂(P.map X) :=
        (integral_map (Lp.aestronglyMeasurable X).aemeasurable
          (hLip.continuous.norm.pow 2).aestronglyMeasurable).symm
      _ = _ := by rw [hXlaw]
  change ‖A - Z‖ ^ 2 ≤ _ at hgd
  change 2 * ((∫ ω, f (A ω) ∂P) - ∫ ω, f (X ω) ∂P) ≤ _ at hdesc
  rw [hscore] at hgd hscaled
  refine ⟨hfinite, ?_⟩
  nlinarith

end AverageLMC
