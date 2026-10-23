import KineticLangevin.CanonicalGlobalSegments
import KineticLangevin.CanonicalProduct

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 2000
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace KineticLangevin.CanonicalCoupling
open BrownianConvolution
variable {d : ℕ} {μ π : Measure (H d)} [IsProbabilityMeasure μ]

/-- The explicit phase/Brownian projection of each initial coupling has the independent canonical product law. -/
theorem initialPhase_brownian_jointLaw (c : ULA.Coupling μ π) :
    HasLaw (fun p : Sample d => ((p.2.1,p.1.2),p.2.2))
      (((stdGaussian (H d)).prod π).prod (ULA.CanonicalBrownian.vectorProbability (Fin d))) (probability c) := by
  haveI : IsProbabilityMeasure c.joint := c.isProbabilityMeasure
  haveI : IsProbabilityMeasure π := by
    have hl : HasLaw Prod.snd π c.joint := ⟨measurable_snd.aemeasurable,c.snd⟩
    exact hl.isProbabilityMeasure_iff.mp inferInstance
  have hproj : HasLaw (fun p : Sample d => (p.1.2,p.2)) (π.prod (canonicalSourceProbability d)) (probability c) := by
    refine ⟨(measurable_fst.snd.prodMk measurable_snd).aemeasurable,?_⟩
    change (c.joint.prod (canonicalSourceProbability d)).map (Prod.map Prod.snd id) = _
    simpa only [c.snd,Measure.map_id] using
      (Measure.map_prod_map c.joint (canonicalSourceProbability d) measurable_snd measurable_id).symm
  have hassoc : HasLaw (MeasurableEquiv.prodAssoc : ((H d×H d)×ULA.CanonicalBrownian.VectorSample (Fin d)) ≃ᵐ _).symm
      ((π.prod (stdGaussian (H d))).prod (ULA.CanonicalBrownian.vectorProbability (Fin d)))
      (π.prod (canonicalSourceProbability d)) :=
    (MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc π (stdGaussian (H d)) (ULA.CanonicalBrownian.vectorProbability (Fin d)))).hasLaw
  have hswap : HasLaw (Prod.map Prod.swap id : (H d×H d)×ULA.CanonicalBrownian.VectorSample (Fin d) → _)
      (((stdGaussian (H d)).prod π).prod (ULA.CanonicalBrownian.vectorProbability (Fin d)))
      ((π.prod (stdGaussian (H d))).prod (ULA.CanonicalBrownian.vectorProbability (Fin d))) :=
    ((Measure.measurePreserving_swap (μ := π) (ν := stdGaussian (H d))).prod
      (MeasurePreserving.id (ULA.CanonicalBrownian.vectorProbability (Fin d)))).hasLaw
  exact hswap.comp (hassoc.comp hproj)

/-- The global forcing's actual OU increment equals the already constructed filtered velocity response. -/
theorem ouInputIncrement_globalInput (c : ULA.Coupling μ π) (γ : ℝ) (hγ : 0 ≤ γ)
    (h : ℝ≥0) (n : ℕ) :
    ouInputIncrement γ (globalInput c γ) ((n : ℝ)*(h : ℝ)) h = filtered c γ h n h := by
  have hc : Continuous (fun s : ℝ => Real.exp (-γ*((h : ℝ)-s)) •
      vectorBrownianIncrementLp (Fin d) ((n : ℝ≥0)*h) s.toNNReal) :=
    (by fun_prop : Continuous (fun s : ℝ => Real.exp (-γ*((h : ℝ)-s)))).smul
      ((continuous_vectorBrownianIncrementLp (Fin d) _).comp continuous_real_toNNReal)
  unfold filtered
  rw [Real.toNNReal_coe,vectorSegmentLp_velocity_eq_brownian_sub_convolution (Fin d) γ hγ,
    map_sub,map_smul,← (inputLift c γ).intervalIntegral_comp_comm (f := fun s : ℝ =>
      Real.exp (-γ*((h : ℝ)-s)) • vectorBrownianIncrementLp (Fin d) ((n : ℝ≥0)*h) s.toNNReal)
      (hc.intervalIntegrable _ _)]
  unfold ouInputIncrement
  rw [← input_eq_globalInput_increment c γ h n h h.coe_nonneg]
  change input c γ h n h - γ • (∫ s in 0..(h : ℝ), Real.exp (-γ*((h : ℝ)-s)) •
      (globalInput c γ ((n : ℝ)*(h : ℝ)+s)-globalInput c γ ((n : ℝ)*(h : ℝ)))) = _
  have hend : inputLift c γ (vectorBrownianIncrementLp (Fin d) ((n : ℝ≥0)*h) h) = input c γ h n h := by
    simp only [input,Real.toNNReal_coe]
  rw [hend]
  apply congrArg (fun z : Lp (H d) 2 (probability c) => input c γ h n h - γ • z)
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le h.coe_nonneg] at hs
  dsimp only
  rw [← input_eq_globalInput_increment c γ h n s hs.1,map_smul]
  rfl

/-- The actual OU response on the extension has the original source representative. -/
theorem ouInputIncrement_globalInput_coe (c : ULA.Coupling μ π) (γ : ℝ) (hγ : 0 ≤ γ)
    (h : ℝ≥0) (n : ℕ) :
    ouInputIncrement γ (globalInput c γ) ((n : ℝ)*(h : ℝ)) h =ᵐ[probability c]
      fun p : Sample d => (Real.sqrt (2*γ) • vectorSegmentLp (Fin d) (psi γ 0)
        (continuous_psi γ 0) ((n : ℝ≥0)*h) h) p.2.2 := by
  rw [ouInputIncrement_globalInput c γ hγ]
  have he : filtered c γ h n h = brownianLift c (Real.sqrt (2*γ) •
      vectorSegmentLp (Fin d) (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) h) := by
    unfold filtered inputLift
    simp only [Real.toNNReal_coe,smul_apply,map_smul]
  rw [he]
  exact brownianLift_coe c _

/-- The initial reference and the whole actual OU innovation stream have the exact independent thermal product law. -/
theorem initial_ouInput_jointLaw (c : ULA.Coupling μ π) (hπ : MemLp (id : H d → H d) 2 π)
    (γ : ℝ) (hγ : 0 ≤ γ) (h : ℝ≥0) :
    HasLaw (fun p : Sample d => (lpPhaseCoe (probability c) (referenceInitial c hπ) p,
      fun k : ℕ => ouInputIncrement γ (globalInput c γ) ((k : ℝ)*(h : ℝ)) h p))
      (((stdGaussian (H d)).prod π).prod (Measure.infinitePi (fun _ : ℕ =>
        (stdGaussian (H d)).map (fun x => Real.sqrt (1-(psi γ 0 h)^2) • x)))) (probability c) := by
  haveI : IsProbabilityMeasure π := by
    have hl : HasLaw (fun p : Sample d => p.1.2) π (probability c) :=
      ⟨(measurable_fst.snd).aemeasurable,ULA.initialExtension_reference c (canonicalSourceProbability d)⟩
    exact hl.isProbabilityMeasure_iff.mp inferInstance
  let η := (stdGaussian (H d)).map (fun x => Real.sqrt (1-(psi γ 0 h)^2) • x)
  letI : IsProbabilityMeasure η := (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  let W : ULA.CanonicalBrownian.VectorSample (Fin d) → ℕ → H d := fun ω k =>
    (Real.sqrt (2*γ) • vectorSegmentLp (Fin d) (psi γ 0) (continuous_psi γ 0) ((k : ℝ≥0)*h) h) ω
  have hW : Measurable W := measurable_pi_iff.mpr fun _ => (Lp.stronglyMeasurable _).measurable
  have hj := jointLaw_product_source ((stdGaussian (H d)).prod π)
    (ULA.CanonicalBrownian.vectorProbability (Fin d)) η W hW (vectorOU_grid_hasLaw d γ hγ h)
  have hp := hj.comp (initialPhase_brownian_jointLaw c)
  apply hp.congr
  filter_upwards [referenceInitial_coe c hπ,ae_all_iff.mpr (ouInputIncrement_globalInput_coe c γ hγ h)]
    with p hinit hnoise
  exact Prod.ext hinit (funext hnoise)

end KineticLangevin.CanonicalCoupling
