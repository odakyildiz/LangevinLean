import KineticLangevin.ExactOBABO
import KineticLangevin.OBABOLocalCost
import KineticLangevin.RandomMapPerturbation
import KineticLangevin.OBABOLaw
import KineticLangevin.OBABOBiasScalar

noncomputable section
set_option linter.style.header false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace KineticLangevin
variable {ι : Type*} [Fintype ι]
local instance obaboPhaseLp_measurable : MeasurableSpace (WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) := borel _
local instance obaboPhaseLp_borel : BorelSpace (WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) := ⟨rfl⟩

def weightedExactObaboStep (f : EuclideanSpace ℝ ι → ℝ) (M : ℝ≥0) (hLip : LipschitzWith M (gradient f))
    (γ h : ℝ) (hh : 0 ≤ h) (δ σ : ℝ) (y : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι))
    (ξ : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :=
  weightedPhaseTransform (1 / (M : ℝ)) (1 / γ)
    (exactObaboStep f M hLip h hh δ σ (weightedPhaseInverse (1 / (M : ℝ)) (1 / γ) y) ξ)

theorem weightedExactObaboStep_continuous (f : EuclideanSpace ℝ ι → ℝ) (M : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (γ h : ℝ) (hh : 0 ≤ h) (δ σ : ℝ) :
    Continuous (Function.uncurry (weightedExactObaboStep f M hLip γ h hh δ σ)) := by
  have hi : Continuous (fun p : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ×
      (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
        (weightedPhaseInverse (1 / (M : ℝ)) (1 / γ) p.1,p.2)) :=
    (((weightedPhaseInverse_continuous (E := EuclideanSpace ℝ ι) (1 / (M : ℝ)) (1 / γ)).comp continuous_fst).prodMk continuous_snd)
  have hr : Continuous (fun p : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ×
      (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
        exactObaboStep f M hLip h hh δ σ (weightedPhaseInverse (1 / (M : ℝ)) (1 / γ) p.1) p.2) := by
    convert (exactObaboStep_continuous f M hLip h hh δ σ).comp hi using 1
    funext p
    rfl
  change Continuous (fun p : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ×
      (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
        weightedPhaseTransform (1 / (M : ℝ)) (1 / γ)
          (exactObaboStep f M hLip h hh δ σ (weightedPhaseInverse (1 / (M : ℝ)) (1 / γ) p.1) p.2))
  exact (weightedPhaseTransform_continuous (E := EuclideanSpace ℝ ι) (1 / (M : ℝ)) (1 / γ)).comp hr

theorem obaboGaussian_local_cost
    (f : EuclideanSpace ℝ ι → ℝ) (m γ h δ σ : ℝ) (M : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith M (gradient f))
    (hm : 0 < m) (hγ : 0 < γ) (hM : 0 < (M : ℝ)) (hh : 0 ≤ h)
    (hfriction : 4 * (M : ℝ) ≤ γ ^ 2) (hδ : |δ| ≤ 1) (hvariance : δ ^ 2 + σ ^ 2 = 1) :
    eLpNorm (fun p ↦ weightedPhaseTransform (1 / (M : ℝ)) (1 / γ)
      (obaboStep (gradient f) h δ σ p.1 p.2.1 p.2.2 - exactObaboStep f M hLip h hh δ σ p.1 p.2)) 2
      ((kineticGibbsTarget f).prod ((stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ ι)))) ≤
        ENNReal.ofReal (obaboLocalBudget M h (Fintype.card ι : ℝ)) := by
  haveI := kineticGibbsTarget_probability f m hm hf hsc
  let P := (kineticGibbsTarget f).prod ((stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ ι)))
  obtain ⟨Z,Ξ,Ξ',hZ,hΞ,hΞ',hlaw⟩ := exactObabo_lp_source f m hm hf hsc δ σ hvariance
  have hc := lp_obabo_hamiltonian_local_cost P f m γ h δ σ M hf hsc hLip hm hγ hM hh hfriction hδ Z Ξ Ξ' hlaw
  have he : (fun ω ↦ weightedPhaseTransform (1 / (M : ℝ)) (1 / γ)
      (obaboStep (gradient f) h δ σ (lpPhaseCoe P Z ω) (Ξ ω) (Ξ' ω) -
        ornsteinStep δ σ (Ξ' ω)
          (hamiltonianFlow f M hLip h hh (ornsteinStep δ σ (Ξ ω) (lpPhaseCoe P Z ω)) h))) =ᵐ[P]
      fun p ↦ weightedPhaseTransform (1 / (M : ℝ)) (1 / γ)
        (obaboStep (gradient f) h δ σ p.1 p.2.1 p.2.2 - exactObaboStep f M hLip h hh δ σ p.1 p.2) := by
    filter_upwards [hZ,hΞ,hΞ'] with p hz hξ hξ'
    rw [hz,hξ,hξ']
    rfl
  rwa [eLpNorm_congr_ae he] at hc

theorem weightedExactObaboStep_preserves_target
    (f : EuclideanSpace ℝ ι → ℝ) (m γ h δ σ : ℝ) (M : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith M (gradient f))
    (hm : 0 < m) (hγ : 0 < γ) (hM : 0 < (M : ℝ)) (hh : 0 ≤ h)
    (hfriction : 4 * (M : ℝ) ≤ γ ^ 2) (hvariance : δ ^ 2 + σ ^ 2 = 1) :
    randomMapLaw (Function.uncurry (weightedExactObaboStep f M hLip γ h hh δ σ))
      ((kineticGibbsTarget f).map (weightedPhaseTransform (1 / (M : ℝ)) (1 / γ)))
      ((stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ ι))) =
        (kineticGibbsTarget f).map (weightedPhaseTransform (1 / (M : ℝ)) (1 / γ)) := by
  haveI := kineticGibbsTarget_probability f m hm hf hsc
  let T := weightedPhaseTransform (E := EuclideanSpace ℝ ι) (1 / (M : ℝ)) (1 / γ)
  have hT : Measurable T := (weightedPhaseTransform_continuous _ _).measurable
  have hc := markovLaws_map_conjugacy (exactObaboStep f M hLip h hh δ σ)
    (weightedExactObaboStep f M hLip γ h hh δ σ) T
    (exactObaboStep_continuous f M hLip h hh δ σ).measurable
    (weightedExactObaboStep_continuous f M hLip γ h hh δ σ).measurable hT
    (fun z ξ ↦ by
      unfold weightedExactObaboStep
      rw [weightedPhaseInverse_transform _ _ (obabo_metric_strict γ M hγ hM hfriction)])
    (kineticGibbsTarget f) ((stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ ι))) 1
  simp only [ULA.markovLaws, ULA.markovStep] at hc
  rw [exactObaboStep_preserves_target f m hm M hf hsc hLip h hh δ σ hvariance] at hc
  exact hc.symm

theorem weightedObaboGaussian_local_cost
    (f : EuclideanSpace ℝ ι → ℝ) (m γ h σ : ℝ) (M : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith M (gradient f))
    (hm : 0 < m) (hγ : 0 < γ) (hM : 0 < (M : ℝ)) (hh : 0 ≤ h)
    (hfriction : 4 * (M : ℝ) ≤ γ ^ 2) (hvariance : obaboDamping γ h ^ 2 + σ ^ 2 = 1) :
    eLpNorm (fun p ↦ weightedExactObaboStep f M hLip γ h hh (obaboDamping γ h) σ p.1 p.2 -
      weightedObaboStep (gradient f) γ M h σ p.1 p.2) 2
      (((kineticGibbsTarget f).map (weightedPhaseTransform (1 / (M : ℝ)) (1 / γ))).prod
        ((stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ ι)))) ≤
          ENNReal.ofReal (obaboLocalBudget M h (Fintype.card ι : ℝ)) := by
  haveI := kineticGibbsTarget_probability f m hm hf hsc
  let T := weightedPhaseTransform (E := EuclideanSpace ℝ ι) (1 / (M : ℝ)) (1 / γ)
  let π := kineticGibbsTarget f
  let η := (stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ ι))
  let P := π.prod η
  have hT : Measurable T := (weightedPhaseTransform_continuous _ _).measurable
  have hpair : Measurable (fun p : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ×
      (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦ (T p.1,p.2)) := (hT.comp measurable_fst).prodMk measurable_snd
  have hp : P.map (fun p ↦ (T p.1,p.2)) = (π.map T).prod η := by
    simpa only [Measure.map_id,Prod.map_def,id_eq] using (Measure.map_prod_map π η hT measurable_id).symm
  let G := Function.uncurry (weightedExactObaboStep f M hLip γ h hh (obaboDamping γ h) σ)
  let F := Function.uncurry (weightedObaboStep (gradient f) γ M h σ)
  have hG : Measurable G := (weightedExactObaboStep_continuous f M hLip γ h hh (obaboDamping γ h) σ).measurable
  have hF : Measurable F := (weightedObaboStep_continuous (gradient f) hLip.continuous γ M h σ).measurable
  have hmapped := eLpNorm_map_measure (μ := P) (p := 2) (g := fun p ↦ G p - F p)
    (hG.sub hF).aestronglyMeasurable hpair.aemeasurable
  rw [hp] at hmapped
  have hraw := obaboGaussian_local_cost f m γ h (obaboDamping γ h) σ M hf hsc hLip hm hγ hM hh hfriction
    (by rw [abs_of_pos (obaboDamping_pos γ h)];exact (obabo_damping_bounds γ h hγ.le hh).2.1) hvariance
  change eLpNorm (fun p ↦ G p - F p) 2 ((π.map T).prod η) ≤ _
  rw [hmapped]
  change eLpNorm ((fun p ↦ G (T p.1,p.2)) - (fun p ↦ F (T p.1,p.2))) 2 P ≤ _
  rw [eLpNorm_sub_comm]
  have hid : (fun p ↦ F (T p.1,p.2) - G (T p.1,p.2)) =
      fun p : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
        T (obaboStep (gradient f) h (obaboDamping γ h) σ p.1 p.2.1 p.2.2 -
          exactObaboStep f M hLip h hh (obaboDamping γ h) σ p.1 p.2) := by
    funext p
    dsimp [F,G,weightedObaboStep,weightedExactObaboStep,Function.uncurry]
    rw [weightedPhaseInverse_transform _ _ (obabo_metric_strict γ M hγ hM hfriction)]
    exact (weightedPhaseTransform_sub _ _ _ _).symm
  change eLpNorm (fun p ↦ F (T p.1,p.2) - G (T p.1,p.2)) 2 P ≤ _
  rw [hid]
  exact hraw

theorem obabo_wasserstein_bound
    (f : EuclideanSpace ℝ ι → ℝ) (m γ h σ : ℝ) (M : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith M (gradient f))
    (hm : 0 < m) (hmM : m ≤ (M : ℝ)) (hγ : 0 < γ) (hh : 0 < h)
    (hfriction : 4 * (M : ℝ) ≤ γ ^ 2) (hstep : 33 * γ ^ 3 * h ≤ m)
    (hvariance : obaboDamping γ h ^ 2 + σ ^ 2 = 1)
    (μ : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hfinite : ULA.wasserstein2 (μ.map (weightedPhaseTransform (1 / (M : ℝ)) (1 / γ)))
      ((kineticGibbsTarget f).map (weightedPhaseTransform (1 / (M : ℝ)) (1 / γ))) ≠ ⊤) (n : ℕ) :
    ULA.wasserstein2Real
      ((obaboLaws (gradient f) γ h σ
        ((stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ ι))) μ n).map
          (weightedPhaseTransform (1 / (M : ℝ)) (1 / γ)))
      ((kineticGibbsTarget f).map (weightedPhaseTransform (1 / (M : ℝ)) (1 / γ))) ≤
        (obaboContractionRate m γ h : ℝ) ^ n *
          ULA.wasserstein2Real (μ.map (weightedPhaseTransform (1 / (M : ℝ)) (1 / γ)))
            ((kineticGibbsTarget f).map (weightedPhaseTransform (1 / (M : ℝ)) (1 / γ))) +
          (6 * γ / m) * h * Real.sqrt (Fintype.card ι : ℝ) * (4 * Real.sqrt (M : ℝ) + (M : ℝ) * h / 2) := by
  have hM : 0 < (M : ℝ) := hm.trans_le hmM
  haveI := kineticGibbsTarget_probability f m hm hf hsc
  let T := weightedPhaseTransform (E := EuclideanSpace ℝ ι) (1 / (M : ℝ)) (1 / γ)
  let η := (stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ ι))
  let π := (kineticGibbsTarget f).map T
  let F := Function.uncurry (weightedObaboStep (gradient f) γ M h σ)
  let G := Function.uncurry (weightedExactObaboStep f M hLip γ h hh.le (obaboDamping γ h) σ)
  let q := obaboContractionRate m γ h
  let b : ℝ≥0 := ⟨obaboLocalBudget M h (Fintype.card ι : ℝ),obaboLocalBudget_nonneg M h _ hh.le⟩
  have hT : Measurable T := (weightedPhaseTransform_continuous _ _).measurable
  letI : IsProbabilityMeasure π := (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).mpr inferInstance
  letI : IsProbabilityMeasure (μ.map T) := (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).mpr inferInstance
  have hF : Measurable F := (weightedObaboStep_continuous (gradient f) hLip.continuous γ M h σ).measurable
  have hG : Measurable G := (weightedExactObaboStep_continuous f M hLip γ h hh.le (obaboDamping γ h) σ).measurable
  have hcontract : ∀ x y ξ, ‖F (x,ξ) - F (y,ξ)‖ ≤ (q : ℝ) * ‖x-y‖ :=
    weightedObaboStep_contract f m γ h σ M hf hsc hLip hm.le hmM hγ hM hh.le hfriction hstep
  have hinvariant : randomMapLaw G π η = π := weightedExactObaboStep_preserves_target
    f m γ h (obaboDamping γ h) σ M hf hsc hLip hm hγ hM hh.le hfriction hvariance
  have hlocal : eLpNorm (fun p ↦ G p - F p) 2 (π.prod η) ≤ (b : ℝ≥0∞) := by
    have hc := weightedObaboGaussian_local_cost f m γ h σ M hf hsc hLip hm hγ hM hh.le hfriction hvariance
    have he : ENNReal.ofReal (obaboLocalBudget M h (Fintype.card ι : ℝ)) = (b : ℝ≥0∞) := by
      change ENNReal.ofReal (b : ℝ) = (b : ℝ≥0∞)
      exact ENNReal.ofReal_coe_nnreal
    rw [he] at hc
    exact hc
  have hb := markovLaws_bias_of_invariant_comparator F G hF hG q b
    (obaboContractionRate_lt_one m γ h hm hγ hh) hcontract (μ.map T) π η hinvariant hlocal hfinite n
  have hb' : ULA.wasserstein2Real (weightedObaboLaws (gradient f) γ M h σ η (μ.map T) n) π ≤
      (q : ℝ) ^ n * ULA.wasserstein2Real (μ.map T) π + (b : ℝ) / (1 - (q : ℝ)) := hb
  rw [← obaboLaws_weighted_map (gradient f) hLip.continuous γ M h σ hγ hM hfriction η μ n] at hb'
  have hs := obabo_step_size_consequences γ M m h hγ hh.le hmM hfriction hstep
  have hq := obabo_contraction_factor_nonneg γ M m h hγ hh.le hmM hfriction hs.1
  exact hb'.trans (add_le_add le_rfl (obaboLocalBudget_div_gap m M γ h hm M.coe_nonneg hγ hh hq _))

theorem obabo_wasserstein_ne_top
    (f : EuclideanSpace ℝ ι → ℝ) (m γ h σ : ℝ) (M : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith M (gradient f))
    (hm : 0 < m) (hmM : m ≤ (M : ℝ)) (hγ : 0 < γ) (hh : 0 < h)
    (hfriction : 4 * (M : ℝ) ≤ γ ^ 2) (hstep : 33 * γ ^ 3 * h ≤ m)
    (hvariance : obaboDamping γ h ^ 2 + σ ^ 2 = 1)
    (μ : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hfinite : ULA.wasserstein2 (μ.map (weightedPhaseTransform (1 / (M : ℝ)) (1 / γ)))
      ((kineticGibbsTarget f).map (weightedPhaseTransform (1 / (M : ℝ)) (1 / γ))) ≠ ⊤) (n : ℕ) :
    ULA.wasserstein2
      ((obaboLaws (gradient f) γ h σ
        ((stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ ι))) μ n).map
          (weightedPhaseTransform (1 / (M : ℝ)) (1 / γ)))
      ((kineticGibbsTarget f).map (weightedPhaseTransform (1 / (M : ℝ)) (1 / γ))) ≠ ⊤ := by
  have hM : 0 < (M : ℝ) := hm.trans_le hmM
  haveI := kineticGibbsTarget_probability f m hm hf hsc
  let T := weightedPhaseTransform (E := EuclideanSpace ℝ ι) (1 / (M : ℝ)) (1 / γ)
  let η := (stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ ι))
  let π := (kineticGibbsTarget f).map T
  let F := Function.uncurry (weightedObaboStep (gradient f) γ M h σ)
  let G := Function.uncurry (weightedExactObaboStep f M hLip γ h hh.le (obaboDamping γ h) σ)
  let q := obaboContractionRate m γ h
  let b : ℝ≥0 := ⟨obaboLocalBudget M h (Fintype.card ι : ℝ),obaboLocalBudget_nonneg M h _ hh.le⟩
  have hT : Measurable T := (weightedPhaseTransform_continuous _ _).measurable
  letI : IsProbabilityMeasure π := (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).mpr inferInstance
  letI : IsProbabilityMeasure (μ.map T) := (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).mpr inferInstance
  have hF : Measurable F := (weightedObaboStep_continuous (gradient f) hLip.continuous γ M h σ).measurable
  have hG : Measurable G := (weightedExactObaboStep_continuous f M hLip γ h hh.le (obaboDamping γ h) σ).measurable
  have hcontract : ∀ x y ξ, ‖F (x,ξ) - F (y,ξ)‖ ≤ (q : ℝ) * ‖x-y‖ :=
    weightedObaboStep_contract f m γ h σ M hf hsc hLip hm.le hmM hγ hM hh.le hfriction hstep
  have hinvariant : randomMapLaw G π η = π := weightedExactObaboStep_preserves_target
    f m γ h (obaboDamping γ h) σ M hf hsc hLip hm hγ hM hh.le hfriction hvariance
  have hlocal : eLpNorm (fun p ↦ G p - F p) 2 (π.prod η) ≤ (b : ℝ≥0∞) := by
    have hc := weightedObaboGaussian_local_cost f m γ h σ M hf hsc hLip hm hγ hM hh.le hfriction hvariance
    have he : ENNReal.ofReal (obaboLocalBudget M h (Fintype.card ι : ℝ)) = (b : ℝ≥0∞) := by
      change ENNReal.ofReal (b : ℝ) = (b : ℝ≥0∞)
      exact ENNReal.ofReal_coe_nnreal
    rw [he] at hc
    exact hc
  have hb := markovLaws_ne_top_of_invariant_comparator F G hF hG q b hcontract
    (μ.map T) π η hinvariant hlocal hfinite n
  change ULA.wasserstein2 (weightedObaboLaws (gradient f) γ M h σ η (μ.map T) n) π ≠ ⊤ at hb
  rwa [← obaboLaws_weighted_map (gradient f) hLip.continuous γ M h σ hγ hM hfriction η μ n] at hb

end KineticLangevin
