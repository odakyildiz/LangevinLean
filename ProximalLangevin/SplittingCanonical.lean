import ProximalLangevin.SplittingOneStep
import ProximalLangevin.SplittingMoments
import ProximalLangevin.SplittingTransport
import UnadjustedLangevin.CanonicalULA

set_option linter.style.header false

/-! # A canonical stationary coupling for the actual splitting transition

Each coupling of an input law with the Gibbs law is extended by the explicit
canonical Brownian probability space. The integral solution, its stationary
law, its bounded moments, and its future-noise orthogonality are all derived.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal RealInnerProductSpace
namespace ProximalLangevin
open ULA ULA.Hilbert

variable {ι : Type*} [Fintype ι]

/-- The actual forward, noise, backward splitting transition. -/
def splittingUpdate (f₁ : EuclideanSpace ℝ ι → ℝ)
    (T : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (h : ℝ)
    (x z : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  T (x - h • gradient f₁ x + Real.sqrt (2 * h) • z)

theorem splittingUpdate_measurable {f₁ : EuclideanSpace ℝ ι → ℝ}
    {T : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {L LT : ℝ≥0}
    (hLip : LipschitzWith L (gradient f₁)) (hT : LipschitzWith LT T) (h : ℝ) :
    Measurable (Function.uncurry (splittingUpdate f₁ T h)) :=
  hT.continuous.measurable.comp (pointwiseUpdate_measurable f₁ h L hLip)

section Drift
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]

/-- The lifted drift of an actual sum is the sum of its lifted gradients. -/
theorem lpDrift_gradient_add {f e : EuclideanSpace ℝ ι → ℝ} {Lf Le : ℝ≥0}
    (hf : Differentiable ℝ f) (he : Differentiable ℝ e)
    (hLf : LipschitzWith Lf (gradient f)) (hLe : LipschitzWith Le (gradient e))
    (hF : LipschitzWith (Lf + Le) (gradient (fun x => f x + e x)))
    (X : Lp (EuclideanSpace ℝ ι) 2 P) :
    lpDrift P (gradient (fun x => f x + e x)) hF X =
      lpDrift P (gradient f) hLf X + lpDrift P (gradient e) hLe X := by
  apply Lp.ext
  filter_upwards [lpDrift_coe P _ hF X, lpDrift_coe P _ hLf X,
    lpDrift_coe P _ hLe X, Lp.coeFn_add (lpDrift P _ hLf X) (lpDrift P _ hLe X)]
    with ω hsum hf' he' hadd
  simp only [hsum, hadd, Pi.add_apply, hf', he', gradient_add_of_differentiable hf he]

end Drift

/-- A genuine canonical coupling estimate for one actual independent Gaussian
splitting step. All stochastic inputs of the analytic one-step theorem are
constructed here from the potential assumptions. -/
theorem splitting_markov_step_coupling_bound
    {f₁ f e : EuclideanSpace ℝ ι → ℝ}
    {T : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {L₁ Le Kf Ke LT K : ℝ≥0}
    (hf₁ : Differentiable ℝ f₁) (he : Differentiable ℝ e)
    (m h : ℝ) (hm : 0 < m) (hh : 0 < h)
    (hsc : StrongConvexOn univ m f₁)
    (hLip₁ : LipschitzWith L₁ (gradient f₁)) (hmL : m ≤ (L₁ : ℝ))
    (hsmall : h ≤ 2 / (m + (L₁ : ℝ)))
    (heconv : ConvexOn ℝ univ e) (hegrad : LipschitzWith Le (gradient e))
    (heLip : LipschitzWith Ke e) (hfLip : LipschitzWith Kf f)
    (hbounded : ∀ x, ‖gradient e x‖ ≤ (K : ℝ))
    (hT : LipschitzWith LT T)
    (henergy : ∀ x y, ‖T x - y‖ ^ 2 ≤
      ‖x - y‖ ^ 2 - 2 * h * (f x - f y) + h ^ 2 * (K : ℝ) ^ 2)
    (delta : ℝ) (hgap : ∀ x, e x ≤ f x ∧ f x ≤ e x + delta)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (c : Coupling μ (gibbsMeasure (fun x => f₁ x + e x)))
    (hc : couplingCost c.joint ≠ ⊤) :
    let G := Real.sqrt (2 * (L₁ : ℝ) ^ 2 * ((Module.finrank ℝ (EuclideanSpace ℝ ι) : ℝ) / m) +
      2 * (K : ℝ) ^ 2) + (K : ℝ)
    let noise := Real.sqrt (2 * (Fintype.card ι : ℝ))
    wasserstein2 (markovStep (splittingUpdate f₁ T h) (stdGaussian (EuclideanSpace ℝ ι)) μ)
      (gibbsMeasure (fun x => f₁ x + e x)) ≠ ⊤ ∧
    wasserstein2Real (markovStep (splittingUpdate f₁ T h) (stdGaussian (EuclideanSpace ℝ ι)) μ)
      (gibbsMeasure (fun x => f₁ x + e x)) ^ 2 ≤
      (1 - m * h) * (couplingCost c.joint).toReal ^ 2 +
        splittingCouplingForcing m h (L₁ : ℝ) G noise (K : ℝ) delta := by
  let F := fun x => f₁ x + e x
  have hF : Differentiable ℝ F := hf₁.add he
  have hscF : StrongConvexOn univ m F := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    have h₁ := hsc.2 hx hy ha hb hab
    have h₂ := heconv.2 hx hy ha hb hab
    simp only [F, smul_eq_mul] at h₁ h₂ ⊢
    linarith
  have hLipF : LipschitzWith (L₁ + Le) (gradient F) := by
    convert hLip₁.add hegrad using 1
    funext x
    exact gradient_add_of_differentiable hf₁ he x
  let Q := CanonicalBrownian.vectorProbability ι
  let P := initialExtension c Q
  have : IsProbabilityMeasure P := initialExtension_isProbabilityMeasure c Q
  have : IsProbabilityMeasure c.joint := c.isProbabilityMeasure
  let hπ := productGibbsMemLp F m hm hF hscF
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
  have hZlaw : P.map Z = gibbsMeasure F := initialExtension_lpReference_law c Q hπ
  obtain ⟨Y, hY, hY0, hYe, _hnoise⟩ := exists_lp_langevin_integral_of_brownian
    P F (L₁ + Le) hLipF Z W hW 0 h le_rfl hh.le
  have hYlaw (t : ℝ) (ht : t ∈ Icc 0 h) : P.map (Y t) = gibbsMeasure F :=
    lp_langevin_gibbs_stationary P F m (L₁ + Le) hm hF hscF hLipF Z hZlaw W hW
      hscalar hind Y hY t ht.1 (fun s hs => hYe s ⟨hs.1, hs.2.trans ht.2⟩)
  let B := brownianLangevinNoise P W hW 0
  let G := Real.sqrt (2 * (L₁ : ℝ) ^ 2 *
    ((Module.finrank ℝ (EuclideanSpace ℝ ι) : ℝ) / m) + 2 * (K : ℝ) ^ 2) + (K : ℝ)
  let noise := Real.sqrt (2 * (Fintype.card ι : ℝ))
  have hbBound (t : ℝ) (_ht : t ∈ Icc 0 h) :
      ‖lpDrift P (gradient e) hegrad (Y t)‖ ≤ (K : ℝ) :=
    lpDrift_norm_le_of_bounded P hegrad hbounded (Y t)
  have hgBound (t : ℝ) (ht : t ∈ Icc 0 h) :
      ‖lpDrift P (gradient f₁) hLip₁ (Y t) + lpDrift P (gradient e) hegrad (Y t)‖ ≤ G := by
    exact (norm_add_le _ _).trans (add_le_add
      (lpDrift_smooth_gradient_norm_le P m hm hf₁ he hscF hLip₁ hbounded (Y t) (hYlaw t ht))
      (hbBound t ht))
  have hBbound (t : ℝ) (ht : t ∈ Icc 0 h) : ‖B t‖ ≤ noise * Real.sqrt t :=
    (brownianLangevinNoise_norm P W hW 0 t le_rfl ht.1).le
  have hYe' (t : ℝ) (ht : t ∈ Icc 0 h) : Y t - Y 0 =
      -(∫ s in 0..t, lpDrift P (gradient f₁) hLip₁ (Y s) +
        lpDrift P (gradient e) hegrad (Y s)) + B t := by
    rw [hY0]
    have hd (A : Lp (EuclideanSpace ℝ ι) 2 P) : lpDrift P (gradient F) hLipF A =
        lpDrift P (gradient f₁) hLip₁ A + lpDrift P (gradient e) hegrad A :=
      lpDrift_gradient_add P hf₁ he hLip₁ hegrad hLipF A
    simpa only [hd] using hYe t ht
  have horth (t : ℝ) (ht : t ∈ Icc 0 h) :
      ⟪lpDrift P (gradient e) hegrad (Y t), B h - B t⟫ = 0 :=
    lp_langevin_future_inner_zero P F (L₁ + Le) hLipF Z W hW hWmeas hWpaths hZpaths
      Y hY t h ht.1 ht.2 hYe (gradient e) Le hegrad
  have hstationary (t : ℝ) (ht : t ∈ Icc 0 h) :
      (∫ ω, e (Y t ω) ∂P) = ∫ ω, e (Y h ω) ∂P := by
    rw [← integral_map (Lp.aestronglyMeasurable (Y t)).aemeasurable
        he.continuous.aestronglyMeasurable,
      ← integral_map (Lp.aestronglyMeasurable (Y h)).aemeasurable
        he.continuous.aestronglyMeasurable,
      hYlaw t ht, hYlaw h ⟨hh.le, le_rfl⟩]
  let X' := lpDrift P T hT (X - h • lpDrift P (gradient f₁) hLip₁ X + B h)
  have hbound := splitting_one_step_of_integral_solution P hf₁ he m h hm hh hsc hLip₁ hmL
    hsmall heconv hegrad heLip hfLip hT henergy delta hgap Y B hY G noise
    (by dsimp [G]; positivity) (Real.sqrt_nonneg _) hgBound hbBound hBbound hYe'
    horth hstationary X
  rw [hY0, initialExtension_lp_cost] at hbound
  have hXlaw : P.map X = μ := initialExtension_lpInitial_law c Q hc hπ
  let V := brownianEulerNoise P W hW h 0
  have hVlaw : P.map V = stdGaussian (EuclideanSpace ℝ ι) :=
    (brownianEulerNoise_vectorGaussian P W hW h hh (hscalar h hh)).2 0
  have hXV : IndepFun X V P := by
    have hs := productEulerNoise_independentInitial Q c hc hπ CanonicalBrownian.coordinate
      CanonicalBrownian.coordinate_isPreBrownian h
    have hs' : IndepFun X (fun ω n => brownianEulerNoise P W hW h n ω) P := by
      simpa only [productNoise_eq_brownianEulerNoise] using hs
    exact hs'.comp measurable_id (measurable_pi_apply 0)
  have hX'coe : X' =ᵐ[P] fun ω => splittingUpdate f₁ T h (X ω) (V ω) := by
    have hBh : B h = Real.sqrt (2 * h) • V := by
      simpa only [Nat.cast_zero, zero_mul] using brownianEulerNoise_endpoint P W hW h hh 0
    dsimp [X']
    rw [hBh]
    filter_upwards [lpDrift_coe P T hT
        (X - h • lpDrift P (gradient f₁) hLip₁ X + Real.sqrt (2 * h) • V),
      Lp.coeFn_add (X - h • lpDrift P (gradient f₁) hLip₁ X) (Real.sqrt (2 * h) • V),
      Lp.coeFn_sub X (h • lpDrift P (gradient f₁) hLip₁ X),
      Lp.coeFn_smul h (lpDrift P (gradient f₁) hLip₁ X),
      Lp.coeFn_smul (Real.sqrt (2 * h)) V, lpDrift_coe P (gradient f₁) hLip₁ X]
      with ω hT' ha hs hsm hn hg
    simp only [hT', ha, Pi.add_apply, hs, Pi.sub_apply, hsm, Pi.smul_apply, hn, hg,
      splittingUpdate]
  have hX'law : P.map X' = markovStep (splittingUpdate f₁ T h)
      (stdGaussian (EuclideanSpace ℝ ι)) μ := by
    have hjoint := hXV.map_prod_eq_prod_map_map (Lp.aestronglyMeasurable X).aemeasurable
      (Lp.aestronglyMeasurable V).aemeasurable
    rw [hXlaw, hVlaw] at hjoint
    calc
      P.map X' = P.map (fun ω => splittingUpdate f₁ T h (X ω) (V ω)) :=
        Measure.map_congr hX'coe
      _ = (P.map (fun ω => (X ω, V ω))).map (Function.uncurry (splittingUpdate f₁ T h)) := by
        rw [AEMeasurable.map_map_of_aemeasurable
          (splittingUpdate_measurable hLip₁ hT h).aemeasurable
          ((Lp.aestronglyMeasurable X).aemeasurable.prodMk
            (Lp.aestronglyMeasurable V).aemeasurable)]
        rfl
      _ = _ := by rw [hjoint]; rfl
  have htransport := wasserstein2_le_Lp_cost P X' (Y h)
  rw [hX'law, hYlaw h ⟨hh.le, le_rfl⟩] at htransport
  have hfinite : wasserstein2 (markovStep (splittingUpdate f₁ T h)
      (stdGaussian (EuclideanSpace ℝ ι)) μ) (gibbsMeasure F) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top htransport
  refine ⟨hfinite, ?_⟩
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top htransport
  rw [ENNReal.toReal_ofReal (norm_nonneg _)] at hr
  have hsq : wasserstein2Real (markovStep (splittingUpdate f₁ T h)
      (stdGaussian (EuclideanSpace ℝ ι)) μ) (gibbsMeasure F) ^ 2 ≤ ‖X' - Y h‖ ^ 2 := by
    exact (sq_le_sq₀ ENNReal.toReal_nonneg (norm_nonneg _)).mpr hr
  exact hsq.trans hbound

end ProximalLangevin
