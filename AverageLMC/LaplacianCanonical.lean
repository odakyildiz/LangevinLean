import AverageLMC.LaplacianOneStep
import AverageLMC.LaplacianPairing
import AverageLMC.Theorem
import UnadjustedLangevin.CanonicalULA

set_option linter.style.header false
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal RealInnerProductSpace Topology
namespace AverageLMC
open ULA ULA.Hilbert

/-- One actual Gaussian step under the paper's third-order assumptions,
compared through any finite-cost initial coupling. The dual pairing is derived
from the actual diffusion and its independent canonical Brownian source. -/
theorem laplacian_coupling_step {p : ℕ} (hp : 0 < p)
    (f : State p → ℝ) (m h : ℝ) (L : ℝ≥0) (hm : 0 < m) (hh : 0 < h)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith L (gradient f)) (hsmall : h * (L : ℝ) ≤ 1)
    (Mdelta : ℝ) (hMdelta : 0 ≤ Mdelta) (hδ : LaplacianSmooth f Mdelta)
    (μ : Measure (State p)) [IsProbabilityMeasure μ]
    (c : Coupling μ (gibbsMeasure f)) (hc : couplingCost c.joint ≠ ⊤) :
    wasserstein2Real (ulaLawStep f h μ) (gibbsMeasure f) ^ 2 ≤
      (1 - m * h) ^ 2 * (couplingCost c.joint).toReal ^ 2 +
      h ^ 2 * (1 - m * h) * (couplingCost c.joint).toReal *
        ((L : ℝ) * Real.sqrt (averageSmoothness f * p) + Mdelta * Real.sqrt p) +
      ((3 / 2 : ℝ) * (L : ℝ) * h * Real.sqrt h * Real.sqrt p) ^ 2 := by
  let Q := CanonicalBrownian.vectorProbability (Fin p)
  let P := initialExtension c Q
  have : IsProbabilityMeasure P := initialExtension_isProbabilityMeasure c Q
  have : IsProbabilityMeasure c.joint := c.isProbabilityMeasure
  let hπ := productGibbsMemLp f m hm hf hsc
  let X := initialExtension_lpInitial c Q hc hπ
  let Z := initialExtension_lpReference c Q hπ
  let W := fun i t (p : (State p × State p) ×
      CanonicalBrownian.VectorSample (Fin p)) => CanonicalBrownian.coordinate i t p.2
  have hW : ∀ i, IsPreBrownianReal (W i) P :=
    productPreBrownian Q c CanonicalBrownian.coordinate CanonicalBrownian.coordinate_isPreBrownian
  have hcoord (i : Fin p) (t : ℝ≥0) :
      Measurable (fun ω : CanonicalBrownian.VectorSample (Fin p) => CanonicalBrownian.coordinate i t ω) :=
    (CanonicalBrownian.process_measurable t).comp (measurable_pi_apply i)
  have hfull : Measurable (fun ω : CanonicalBrownian.VectorSample (Fin p) =>
      fun (i : Fin p) (t : ℝ≥0) => CanonicalBrownian.coordinate i t ω) :=
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun t => hcoord i t
  have hWmeas : ∀ i t, Measurable (W i t) := by
    intro i t
    exact (hcoord i t).comp measurable_snd
  have hWpaths : iIndepFun (fun i ω t => W i t ω) P := by
    apply (iIndepFun_iff_map_fun_eq_infinitePi_map
      (fun i => measurable_pi_iff.mpr fun t => hWmeas i t)).mpr
    have hs := (CanonicalBrownian.coordinate_paths_independent (Fin p)).map_fun_eq_infinitePi_map
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
  have hZpaths : IndepFun Z (fun ω (i : Fin p) (t : ℝ≥0) => W i t ω) P := by
    have hi := (initialExtension_independent c Q).comp measurable_snd
      hfull
    exact hi.congr (initialExtension_memLp_reference c Q hπ).coeFn_toLp.symm
      (ae_of_all _ fun _ => rfl)
  have hscalar : ∀ r : ℝ, 0 < r → iIndepFun (fun p : ℕ × Fin p => fun ω =>
      brownianEulerNoise P W hW r p.1 ω p.2) P := by
    intro r hr
    have hs := productEulerNoise_independent Q c CanonicalBrownian.coordinate
      CanonicalBrownian.coordinate_isPreBrownian r hr
      (CanonicalBrownian.coordinate_grid_paths_independent (Fin p) r.toNNReal)
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
  let g := lpDrift P (gradient f) hLip
  let Ψ := (X - h • g X) - (Z - h • g Z)
  let T := fun x : State p ↦ x - h • gradient f x
  have hTm : Measurable T := measurable_id.sub (hLip.continuous.measurable.const_smul h)
  have hTcoe (V : Lp (State p) 2 P) : V - h • g V =ᵐ[P] fun ω ↦ T (V ω) := by
    filter_upwards [Lp.coeFn_sub V (h • g V), Lp.coeFn_smul h (g V),
      lpDrift_coe P (gradient f) hLip V] with ω hs hsm hg
    simp only [hs, Pi.sub_apply, hsm, Pi.smul_apply, hg, T, g]
  have hPair : (fun ω ↦ (Ψ ω, Z ω)) =ᵐ[P] fun ω ↦ (T ω.1.1 - T ω.1.2, ω.1.2) := by
    filter_upwards [Lp.coeFn_sub (X - h • g X) (Z - h • g Z), hTcoe X, hTcoe Z,
      (initialExtension_memLp_initial c Q hc hπ).coeFn_toLp,
      (initialExtension_memLp_reference c Q hπ).coeFn_toLp] with ω hsub hx hz hX hZ
    change X ω = ω.1.1 at hX
    change Z ω = ω.1.2 at hZ
    change ((X - h • g X - (Z - h • g Z)) ω, Z ω) = _
    simp only [hsub, Pi.sub_apply, hx, hz, hX, hZ]
  have hinit (r : ℝ) (_hr : 0 < r) : IndepFun (fun ω ↦ (Ψ ω, Z ω))
      (fun ω k ↦ brownianEulerNoise P W hW r k ω) P := by
    have hraw : IndepFun (fun ω ↦ (T ω.1.1 - T ω.1.2, ω.1.2))
        (fun ω k ↦ sourceEulerNoise Q CanonicalBrownian.coordinate
          CanonicalBrownian.coordinate_isPreBrownian r k ω.2) P :=
      indepFun_prod₀
        (((hTm.comp measurable_fst).sub (hTm.comp measurable_snd)).prodMk measurable_snd).aemeasurable
        (aemeasurable_pi_iff.mpr fun k ↦ (sourceEulerNoise_memLp Q CanonicalBrownian.coordinate
          CanonicalBrownian.coordinate_isPreBrownian r k).aestronglyMeasurable.aemeasurable)
    have hn (k : ℕ) : brownianEulerNoise P W hW r k =ᵐ[P] fun ω ↦
        sourceEulerNoise Q CanonicalBrownian.coordinate
          CanonicalBrownian.coordinate_isPreBrownian r k ω.2 := by
      rw [← productNoise_eq_brownianEulerNoise Q c CanonicalBrownian.coordinate
        CanonicalBrownian.coordinate_isPreBrownian r k]
      exact productNoise_coe Q c _ _ k
    have hne : (fun ω k ↦ brownianEulerNoise P W hW r k ω) =ᵐ[P]
        fun ω k ↦ sourceEulerNoise Q CanonicalBrownian.coordinate
          CanonicalBrownian.coordinate_isPreBrownian r k ω.2 := by
      filter_upwards [ae_all_iff.mpr hn] with ω hω
      funext k
      exact hω k
    exact hraw.congr hPair.symm hne.symm
  have hpair (t : ℝ) (ht : t ∈ Icc 0 h) :
      ⟪(X - h • g X) - (Y 0 - h • g (Y 0)), g (Y t) - g (Y 0)⟫ ≤
      t * ‖(X - h • g X) - (Y 0 - h • g (Y 0))‖ *
        ((L : ℝ) * Real.sqrt (averageSmoothness f * p) + Mdelta * Real.sqrt p) := by
    rw [hY0]
    exact lp_stationary_gradient_pairing_bound P hp f m L hm hsc hLip Mdelta hMdelta hδ
      Z W hW hscalar Ψ hinit Y hY t ht.1
      (fun s hs ↦ hYe s ⟨hs.1, hs.2.trans ht.2⟩)
      (fun s hs ↦ hYlaw s ⟨hs.1, hs.2.trans ht.2⟩)
  have hmL := (strongConvex_le_averageSmoothness hp f m L hf hsc hLip).trans
    (averageSmoothness_le_global_bound hp f L hf hLip)
  have hYe' (t : ℝ) (ht : t ∈ Icc 0 h) : Y t - Y 0 = -(∫ s in 0..t, g (Y s)) + B t := by
    rw [hY0]
    exact hYe t ht
  have hG (t : ℝ) (ht : t ∈ Icc 0 h) : ‖g (Y t)‖ ≤ Real.sqrt ((L : ℝ) * p) := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using
      lpDrift_norm_le_of_strongConvex_gibbs_law P f m L hm hf hsc hLip (Y t) (hYlaw t ht)
  have hb := lp_laplacian_one_step_bound P f m h (p : ℝ)
    ((L : ℝ) * Real.sqrt (averageSmoothness f * p) + Mdelta * Real.sqrt p) L
    hf hsc hLip hm hmL hh.le (Nat.cast_nonneg p) hsmall (by positivity)
    X Y B hY hG (fun t ht ↦ by simpa only [Fintype.card_fin] using
      (brownianLangevinNoise_norm P W hW 0 t le_rfl ht.1).le)
    hYe' hpair
  rw [hY0, initialExtension_lp_cost c Q hc hπ] at hb
  let V := brownianEulerNoise P W hW h 0
  have hVlaw : P.map V = stdGaussian (State p) :=
    (brownianEulerNoise_vectorGaussian P W hW h hh (hscalar h hh)).2 0
  have hXV : IndepFun X V P := by
    have hi := productEulerNoise_independentInitial Q c hc hπ CanonicalBrownian.coordinate
      CanonicalBrownian.coordinate_isPreBrownian h
    have hi' : IndepFun X (fun ω n ↦ brownianEulerNoise P W hW h n ω) P := by
      simpa only [productNoise_eq_brownianEulerNoise] using hi
    exact hi'.comp measurable_id (measurable_pi_apply 0)
  have hXlaw : P.map X = μ := initialExtension_lpInitial_law c Q hc hπ
  have hBh : B h = Real.sqrt (2 * h) • V := by
    simpa only [Nat.cast_zero, zero_mul] using brownianEulerNoise_endpoint P W hW h hh 0
  have hout : P.map (X - h • g X + B h) = ulaLawStep f h μ := by
    rw [hBh]
    have hc' := lpUlaUpdate_coe P f h hLip X V
    change P.map (lpUlaUpdate P f h hLip X V) = _
    rw [Measure.map_congr hc']
    have hj := hXV.map_prod_eq_prod_map_map (Lp.aestronglyMeasurable X).aemeasurable
      (Lp.aestronglyMeasurable V).aemeasurable
    rw [hXlaw, hVlaw] at hj
    calc
      _ = (P.map (fun ω ↦ (X ω, V ω))).map (Function.uncurry (pointwiseUpdate f h)) :=
        (AEMeasurable.map_map_of_aemeasurable (pointwiseUpdate_measurable f h L hLip).aemeasurable
          ((Lp.aestronglyMeasurable X).aemeasurable.prodMk
            (Lp.aestronglyMeasurable V).aemeasurable)).symm
      _ = _ := by rw [hj]; rfl
  have htr := wasserstein2_le_Lp_cost P (X - h • g X + B h) (Y h)
  rw [hout, hYlaw h ⟨hh.le, le_rfl⟩] at htr
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top htr
  rw [ENNReal.toReal_ofReal (norm_nonneg _)] at hr
  exact ((sq_le_sq₀ ENNReal.toReal_nonneg (norm_nonneg _)).mpr hr).trans hb

end AverageLMC
