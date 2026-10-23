import KineticLangevin.OBABOBias
import KineticLangevin.TransportMap

/-! # The actual OBABO position-law endpoint

Gaussian initial velocities are coupled identically at no initial position
transport cost. The explicit inverse metric projects the actual weighted
sampling theorem to position with factor sqrt2, retaining output finiteness.
-/

noncomputable section
set_option linter.style.header false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace KineticLangevin
variable {ι : Type*} [Fintype ι]
local instance obaboPositionPhase_measurable : MeasurableSpace (WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) := borel _
local instance obaboPositionPhase_borel : BorelSpace (WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) := ⟨rfl⟩

def obaboPositionProjection (γ M : ℝ) (y : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) :=
  (weightedPhaseInverse (1 / M) (1 / γ) y).2

theorem obaboPositionProjection_lipschitz (γ M : ℝ) (hγ : 0 < γ) (hM : 0 < M)
    (hfriction : 4 * M ≤ γ ^ 2) (y z : WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) :
    ‖obaboPositionProjection γ M y - obaboPositionProjection γ M z‖ ≤ Real.sqrt 2 * ‖y-z‖ := by
  have hab := (obabo_metric_strict γ M hγ hM hfriction).le
  let r := weightedPhaseInverse (1 / M) (1 / γ) y - weightedPhaseInverse (1 / M) (1 / γ) z
  have hlo := (weightedPhaseEnergy_equiv (1 / M) (1 / γ) (by positivity)
    (obabo_metric_condition γ M hγ hM hfriction) r).1
  have he : weightedPhaseEnergy (1 / M) (1 / γ) r = ‖y-z‖ ^ 2 := by
    rw [← weightedPhaseNorm_sq _ _ hab]
    unfold weightedPhaseNorm
    dsimp [r]
    rw [weightedPhaseTransform_sub,weightedPhaseTransform_inverse _ _ (obabo_metric_strict γ M hγ hM hfriction) y,
      weightedPhaseTransform_inverse _ _ (obabo_metric_strict γ M hγ hM hfriction) z]
  have hp : 0 ≤ (1 / M) * ‖r.1‖ ^ 2 := by positivity
  change (1 / 2 : ℝ) * (‖r.2‖ ^ 2 + (1 / M) * ‖r.1‖ ^ 2) ≤ _ at hlo
  change ‖r.2‖ ≤ Real.sqrt 2 * ‖y-z‖
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith only [hlo,he,hp]

theorem obaboPositionProjection_transform (γ M : ℝ) (hγ : 0 < γ) (hM : 0 < M)
    (hfriction : 4 * M ≤ γ ^ 2) (z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    obaboPositionProjection γ M (weightedPhaseTransform (1 / M) (1 / γ) z) = z.2 := by
  unfold obaboPositionProjection
  rw [weightedPhaseInverse_transform _ _ (obabo_metric_strict γ M hγ hM hfriction)]

theorem gaussianVelocity_weighted_wasserstein2 (γ M : ℝ) (hγ : 0 < γ) (hM : 0 < M)
    (hfriction : 4 * M ≤ γ ^ 2)
    (μ ν : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ULA.wasserstein2 (((stdGaussian (EuclideanSpace ℝ ι)).prod μ).map (weightedPhaseTransform (1 / M) (1 / γ)))
      (((stdGaussian (EuclideanSpace ℝ ι)).prod ν).map (weightedPhaseTransform (1 / M) (1 / γ))) ≤ ULA.wasserstein2 μ ν := by
  let T := weightedPhaseTransform (E := EuclideanSpace ℝ ι) (1 / M) (1 / γ)
  let F : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι → WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :=
    fun p ↦ T (p.2,p.1)
  have hT : Measurable T := (weightedPhaseTransform_continuous _ _).measurable
  have hF : Measurable F := hT.comp (measurable_snd.prodMk measurable_fst)
  have hcontract (x y v : EuclideanSpace ℝ ι) : ‖F (x,v) - F (y,v)‖ ≤ (1 : ℝ≥0) * ‖x-y‖ := by
    have hab := (obabo_metric_strict γ M hγ hM hfriction).le
    have hid : T (v,x) - T (v,y) = T (0,x-y) := by
      rw [← weightedPhaseTransform_sub]
      congr 1
      ext <;> simp
    change ‖T (v,x) - T (v,y)‖ ≤ _
    rw [hid]
    have hs : ‖T (0,x-y)‖ ^ 2 = ‖x-y‖ ^ 2 := by
      simpa [weightedPhaseNorm,weightedPhaseEnergy,T] using
        weightedPhaseNorm_sq (1 / M) (1 / γ) hab (0,x-y)
    norm_num only [NNReal.coe_one,one_mul]
    nlinarith only [hs,norm_nonneg (T (0,x-y)),norm_nonneg (x-y)]
  have hmap (ρ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure ρ] :
      (ρ.prod (stdGaussian (EuclideanSpace ℝ ι))).map F = ((stdGaussian (EuclideanSpace ℝ ι)).prod ρ).map T := by
    have hswap := (Measure.measurePreserving_swap (μ := ρ) (ν := stdGaussian (EuclideanSpace ℝ ι))).map_eq
    calc
      _ = ((ρ.prod (stdGaussian (EuclideanSpace ℝ ι))).map Prod.swap).map T := by
        rw [Measure.map_map hT measurable_swap]
        rfl
      _ = _ := by rw [hswap]
  have hw := wasserstein2_randomMap_lipschitz F hF 1 hcontract μ ν (stdGaussian (EuclideanSpace ℝ ι))
  rw [hmap μ,hmap ν] at hw
  simpa only [ENNReal.coe_one,one_mul] using hw

theorem obabo_position_sampling_bound
    (f : EuclideanSpace ℝ ι → ℝ) (m γ h σ : ℝ) (M : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith M (gradient f))
    (hm : 0 < m) (hmM : m ≤ (M : ℝ)) (hγ : 0 < γ) (hh : 0 < h)
    (hfriction : 4 * (M : ℝ) ≤ γ ^ 2) (hstep : 33 * γ ^ 3 * h ≤ m)
    (hvariance : obaboDamping γ h ^ 2 + σ ^ 2 = 1)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hfinite : ULA.wasserstein2 μ (ULA.gibbsMeasure f) ≠ ⊤) (n : ℕ) :
    let ν := (obaboLaws (gradient f) γ h σ
      ((stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ ι)))
      ((stdGaussian (EuclideanSpace ℝ ι)).prod μ) n).map Prod.snd
    ULA.wasserstein2 ν (ULA.gibbsMeasure f) ≠ ⊤ ∧
      ULA.wasserstein2Real ν (ULA.gibbsMeasure f) ≤
        Real.sqrt 2 * (obaboContractionRate m γ h : ℝ) ^ n * ULA.wasserstein2Real μ (ULA.gibbsMeasure f) +
          (6 * Real.sqrt 2 * γ / m) * h * Real.sqrt (Fintype.card ι : ℝ) *
            (4 * Real.sqrt (M : ℝ) + (M : ℝ) * h / 2) := by
  intro ν
  have hM : 0 < (M : ℝ) := hm.trans_le hmM
  haveI := ULA.isProbabilityMeasure_gibbsMeasure f m hm hf hsc
  haveI := kineticGibbsTarget_probability f m hm hf hsc
  let T := weightedPhaseTransform (E := EuclideanSpace ℝ ι) (1 / (M : ℝ)) (1 / γ)
  let proj := obaboPositionProjection (ι := ι) γ M
  let μ0 := (stdGaussian (EuclideanSpace ℝ ι)).prod μ
  let η := (stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ ι))
  let ρ := obaboLaws (gradient f) γ h σ η μ0 n
  let π := kineticGibbsTarget f
  have hT : Measurable T := (weightedPhaseTransform_continuous _ _).measurable
  have hprojMeas : Measurable proj := (weightedPhaseInverse_continuous (E := EuclideanSpace ℝ ι) (1 / (M : ℝ)) (1 / γ)).snd.measurable
  have hprojLip : ∀ x y, ‖proj x - proj y‖ ≤ (⟨Real.sqrt 2,Real.sqrt_nonneg _⟩ : ℝ≥0) * ‖x-y‖ :=
    obaboPositionProjection_lipschitz γ M hγ hM hfriction
  have hinitial : ULA.wasserstein2 (μ0.map T) (π.map T) ≤ ULA.wasserstein2 μ (ULA.gibbsMeasure f) :=
    gaussianVelocity_weighted_wasserstein2 γ M hγ hM hfriction μ (ULA.gibbsMeasure f)
  have hinitfinite : ULA.wasserstein2 (μ0.map T) (π.map T) ≠ ⊤ := ne_top_of_le_ne_top hfinite hinitial
  have hweighted := obabo_wasserstein_bound f m γ h σ M hf hsc hLip hm hmM hγ hh hfriction hstep hvariance μ0 hinitfinite n
  have hweightedfinite := obabo_wasserstein_ne_top f m γ h σ M hf hsc hLip hm hmM hγ hh hfriction hstep hvariance μ0 hinitfinite n
  have hstepMeas : Measurable (Function.uncurry (fun z (ξ : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
      obaboStep (gradient f) h (obaboDamping γ h) σ z ξ.1 ξ.2)) := by
    apply Continuous.measurable
    unfold Function.uncurry obaboStep ornsteinStep kickStep driftStep
    have hg := hLip.continuous
    fun_prop
  letI : IsProbabilityMeasure ρ := ULA.markovLaws_isProbability _ hstepMeas μ0 η n
  letI : IsProbabilityMeasure (ρ.map T) := (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).mpr inferInstance
  letI : IsProbabilityMeasure (π.map T) := (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).mpr inferInstance
  have hproj (χ : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) : (χ.map T).map proj = χ.map Prod.snd := by
    rw [Measure.map_map hprojMeas hT]
    congr 1
    funext z
    exact obaboPositionProjection_transform γ M hγ hM hfriction z
  have hprojBound := wasserstein2_map_lipschitz proj hprojMeas ⟨Real.sqrt 2,Real.sqrt_nonneg _⟩ hprojLip (ρ.map T) (π.map T)
  rw [hproj ρ,hproj π,kineticGibbsTarget_position f m hm hf hsc] at hprojBound
  have hposfinite : ULA.wasserstein2 ν (ULA.gibbsMeasure f) ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.coe_ne_top hweightedfinite) hprojBound
  have hprojReal := wasserstein2Real_map_lipschitz proj hprojMeas ⟨Real.sqrt 2,Real.sqrt_nonneg _⟩ hprojLip
    (ρ.map T) (π.map T) hweightedfinite
  rw [hproj ρ,hproj π,kineticGibbsTarget_position f m hm hf hsc] at hprojReal
  have hinitialReal : ULA.wasserstein2Real (μ0.map T) (π.map T) ≤ ULA.wasserstein2Real μ (ULA.gibbsMeasure f) :=
    ENNReal.toReal_mono hfinite hinitial
  refine ⟨hposfinite,?_⟩
  calc
    _ ≤ Real.sqrt 2 * ULA.wasserstein2Real (ρ.map T) (π.map T) := hprojReal
    _ ≤ Real.sqrt 2 * ((obaboContractionRate m γ h : ℝ) ^ n *
        ULA.wasserstein2Real (μ0.map T) (π.map T) +
          (6 * γ / m) * h * Real.sqrt (Fintype.card ι : ℝ) * (4 * Real.sqrt (M : ℝ) + (M : ℝ) * h / 2)) :=
      mul_le_mul_of_nonneg_left hweighted (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt 2 * ((obaboContractionRate m γ h : ℝ) ^ n * ULA.wasserstein2Real μ (ULA.gibbsMeasure f) +
          (6 * γ / m) * h * Real.sqrt (Fintype.card ι : ℝ) * (4 * Real.sqrt (M : ℝ) + (M : ℝ) * h / 2)) := by
      gcongr
    _ = _ := by simp only [div_eq_mul_inv];ring

end KineticLangevin
