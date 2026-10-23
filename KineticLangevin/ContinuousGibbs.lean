import KineticLangevin.CanonicalContinuousMixing
import KineticLangevin.GenericCanonicalKLMC

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace KineticLangevin.CanonicalContinuous
variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- Reassociate the independent position, Gaussian velocity, and genuine Brownian source. -/
def phaseSourceProjection (p : H ι × Sample ι) : (H ι × H ι) × ULA.CanonicalBrownian.VectorSample ι :=
  ((p.2.1,p.1),p.2.2)

theorem phaseSourceProjection_preserving (π : Measure (H ι)) [IsProbabilityMeasure π] :
    MeasurePreserving (phaseSourceProjection ι)
      (π.prod (((stdGaussian (H ι)).prod (ULA.CanonicalBrownian.vectorProbability ι))))
      (((stdGaussian (H ι)).prod π).prod (ULA.CanonicalBrownian.vectorProbability ι)) := by
  have ha := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc π (stdGaussian (H ι)) (ULA.CanonicalBrownian.vectorProbability ι))
  exact (MeasurePreserving.prod (Measure.measurePreserving_swap (μ := π) (ν := stdGaussian (H ι)))
    (MeasurePreserving.id (ULA.CanonicalBrownian.vectorProbability ι))).comp ha

/-- The actual thermal OU increment is pulled back from the independent Brownian coordinate. -/
theorem ouInputIncrement_coe (π : Measure (H ι)) [IsProbabilityMeasure π]
    (γ : ℝ) (hγ : 0 ≤ γ) (h : ℝ≥0) (n : ℕ) :
    ouInputIncrement γ (ProductContinuous.input (((stdGaussian (H ι)).prod (ULA.CanonicalBrownian.vectorProbability ι))) π
        (input ι (stdGaussian (H ι)) γ)) ((n : ℝ)*h) h =ᵐ[π.prod (((stdGaussian (H ι)).prod (ULA.CanonicalBrownian.vectorProbability ι)))]
      fun p : H ι × Sample ι => (Real.sqrt (2*γ) • BrownianConvolution.vectorSegmentLp ι
        (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) h) p.2.2 := by
  let L := sourcePullback (H := H ι) (Prod.snd : H ι × Sample ι → Sample ι)
    (measurePreserving_snd : MeasurePreserving Prod.snd
      (π.prod (((stdGaussian (H ι)).prod (ULA.CanonicalBrownian.vectorProbability ι)))) (((stdGaussian (H ι)).prod (ULA.CanonicalBrownian.vectorProbability ι))))
  let R := sourcePullback (H := H ι) (Prod.snd : Sample ι → ULA.CanonicalBrownian.VectorSample ι)
    (measurePreserving_snd : MeasurePreserving Prod.snd (((stdGaussian (H ι)).prod (ULA.CanonicalBrownian.vectorProbability ι)))
      (ULA.CanonicalBrownian.vectorProbability ι))
  change ouInputIncrement γ (fun t => L (R (Real.sqrt (2*γ) • BrownianConvolution.canonicalVectorInput ι t)))
    ((n : ℝ)*h) h =ᵐ[_] _
  have hc : Continuous (fun t => Real.sqrt (2*γ) • BrownianConvolution.canonicalVectorInput ι t) :=
    (BrownianConvolution.continuous_canonicalVectorInput ι).const_smul (Real.sqrt (2*γ))
  have heL := ouInputIncrement_map L γ
    (fun t => R (Real.sqrt (2*γ) • BrownianConvolution.canonicalVectorInput ι t))
    (R.continuous.comp hc) ((n : ℝ)*h) h
  have heR := ouInputIncrement_map R γ
    (fun t => Real.sqrt (2*γ) • BrownianConvolution.canonicalVectorInput ι t) hc ((n : ℝ)*h) h
  rw [heL,heR,
    show (n : ℝ)*(h : ℝ)=(((n : ℝ≥0)*h : ℝ≥0) : ℝ) by rfl,
    BrownianConvolution.canonicalVectorInput_scaled_ouIncrement ι γ _ hγ]
  change sourcePullback _ _ (sourcePullback _ _ _) =ᵐ[_] _
  rw [sourcePullback_comp]
  exact sourcePullback_coe _ _ _

/-- Actual initial phase and the complete actual OU stream have the independent target-times-iid law. -/
theorem initial_ouInput_jointLaw (π : Measure (H ι)) [IsProbabilityMeasure π]
    (hπ : MemLp (id : H ι → H ι) 2 π) (γ : ℝ) (hγ : 0 ≤ γ) (h : ℝ≥0) :
    HasLaw (fun p => (lpPhaseCoe (π.prod (((stdGaussian (H ι)).prod (ULA.CanonicalBrownian.vectorProbability ι))))
        (ProductContinuous.initial (((stdGaussian (H ι)).prod (ULA.CanonicalBrownian.vectorProbability ι))) π hπ
          (velocity ι (stdGaussian (H ι)) IsGaussian.memLp_two_id)) p,
      fun k : ℕ => ouInputIncrement γ (ProductContinuous.input (((stdGaussian (H ι)).prod (ULA.CanonicalBrownian.vectorProbability ι))) π
        (input ι (stdGaussian (H ι)) γ)) ((k : ℝ)*h) h p))
      (((stdGaussian (H ι)).prod π).prod
        (Measure.infinitePi (fun _ : ℕ => ouThermalLaw (E := H ι) γ h)))
      (π.prod (((stdGaussian (H ι)).prod (ULA.CanonicalBrownian.vectorProbability ι)))) := by
  let W := fun ω (n : ℕ) => (Real.sqrt (2*γ) • BrownianConvolution.vectorSegmentLp ι
    (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) h) ω
  have hW : Measurable W := measurable_pi_iff.mpr (fun _ => (Lp.stronglyMeasurable _).measurable)
  have hη : IsProbabilityMeasure (ouThermalLaw (E := H ι) γ h) := by
    unfold ouThermalLaw
    exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  letI := hη
  have hsource := jointLaw_product_source ((stdGaussian (H ι)).prod π)
    (ULA.CanonicalBrownian.vectorProbability ι) (ouThermalLaw (E := H ι) γ h) W hW
    (GenericCanonicalSource.vectorOU_grid_hasLaw ι γ hγ h)
  have hj := hsource.comp (phaseSourceProjection_preserving ι π).hasLaw
  have hV : velocity ι (stdGaussian (H ι)) IsGaussian.memLp_two_id =ᵐ[((stdGaussian (H ι)).prod (ULA.CanonicalBrownian.vectorProbability ι))]
      (Prod.fst : Sample ι → H ι) :=
    (IsGaussian.memLp_two_id.comp_measurePreserving
      (measurePreserving_fst : MeasurePreserving Prod.fst (((stdGaussian (H ι)).prod (ULA.CanonicalBrownian.vectorProbability ι)))
        (stdGaussian (H ι)))).coeFn_toLp
  have hv := (measurePreserving_snd : MeasurePreserving Prod.snd
    (π.prod (((stdGaussian (H ι)).prod (ULA.CanonicalBrownian.vectorProbability ι)))) (((stdGaussian (H ι)).prod (ULA.CanonicalBrownian.vectorProbability ι)))).quasiMeasurePreserving.ae_eq_comp hV
  apply hj.congr
  have hall := ae_all_iff.mpr (ouInputIncrement_coe ι π γ hγ h)
  filter_upwards [ProductContinuous.initial_coe (((stdGaussian (H ι)).prod (ULA.CanonicalBrownian.vectorProbability ι))) π hπ
    (velocity ι (stdGaussian (H ι)) IsGaussian.memLp_two_id),hv,hall] with p hi hv hn
  exact Prod.ext (hi.trans (Prod.ext hv rfl)) (funext hn)

/-- The actual full phase flow started at the independent Gaussian-times-Gibbs target stays stationary. -/
theorem phaseFlow_gibbs_stationary (f : H ι → ℝ) (m : ℝ) (hm : 0 < m) (M γ : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith M (gradient f))
    (T : ℝ) (hT : 0 ≤ T) :
    letI := ULA.isProbabilityMeasure_gibbsMeasure f m hm hf hsc
    HasLaw (lpPhaseCoe ((ULA.gibbsMeasure f).prod (probability ι (stdGaussian (H ι))))
      (ProductContinuous.flow (probability ι (stdGaussian (H ι))) (ULA.gibbsMeasure f)
        (ULA.memLp_id_gibbsMeasure f m hm hf hsc) (velocity ι (stdGaussian (H ι)) IsGaussian.memLp_two_id)
        (input ι (stdGaussian (H ι)) γ) (continuous_input ι (stdGaussian (H ι)) γ)
        (gradient f) M γ hLip T hT T))
      (kineticGibbsTarget f) ((ULA.gibbsMeasure f).prod (probability ι (stdGaussian (H ι)))) := by
  letI := ULA.isProbabilityMeasure_gibbsMeasure f m hm hf hsc
  let π := ULA.gibbsMeasure f
  let hπ := ULA.memLp_id_gibbsMeasure f m hm hf hsc
  let Q := ((stdGaussian (H ι)).prod (ULA.CanonicalBrownian.vectorProbability ι))
  let V := velocity ι (stdGaussian (H ι)) IsGaussian.memLp_two_id
  let B := input ι (stdGaussian (H ι)) γ
  let Y := ProductContinuous.flow Q π hπ V B (continuous_input ι (stdGaussian (H ι)) γ)
    (gradient f) M γ hLip T hT
  have hs := ProductContinuous.flow_spec Q π hπ V B (continuous_input ι (stdGaussian (H ι)) γ)
    (input_zero ι (stdGaussian (H ι)) γ) (gradient f) M γ hLip T hT
  have hjoint := initial_ouInput_jointLaw ι π hπ γ γ.coe_nonneg
  have hstat := kinetic_integral_stationary_of_jointNoise (π.prod Q) f m hm M γ hf hsc hLip
    (ProductContinuous.initial Q π hπ V) (ProductContinuous.input Q π B)
    ((sourcePullback (H := H ι) (Prod.snd : H ι × Sample ι → Sample ι)
      measurePreserving_snd).continuous.comp (continuous_input ι (stdGaussian (H ι)) γ))
    (by simp only [ProductContinuous.input,B,input_zero];exact map_zero _)
    hjoint Y hs.1 (⟨T,hT⟩ : ℝ≥0) (fun t ht => by simpa only [hs.2.1] using hs.2.2 t ht)
  have hl : HasLaw (lpPhaseCoe (π.prod Q) (Y T)) (kineticGibbsTarget f) (π.prod Q) :=
    ⟨(measurable_lpPhaseCoe _ _).aemeasurable,hstat⟩
  exact hl

/-- The actual continuous canonical diffusion started at the Gibbs position law is stationary. -/
theorem positionLaw_gibbs (f : H ι → ℝ) (m : ℝ) (hm : 0 < m) (M γ : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith M (gradient f))
    (T : ℝ) (hT : 0 ≤ T) :
    letI := ULA.isProbabilityMeasure_gibbsMeasure f m hm hf hsc
    positionLaw ι (stdGaussian (H ι)) IsGaussian.memLp_two_id (ULA.gibbsMeasure f)
      (ULA.memLp_id_gibbsMeasure f m hm hf hsc) f M γ hLip T hT = ULA.gibbsMeasure f := by
  letI := ULA.isProbabilityMeasure_gibbsMeasure f m hm hf hsc
  have hl := phaseFlow_gibbs_stationary ι f m hm M γ hf hsc hLip T hT
  have hp := (measurePreserving_snd : MeasurePreserving Prod.snd (kineticGibbsTarget f) (ULA.gibbsMeasure f)).hasLaw.comp hl
  exact hp.map_eq

/-- The actual Brownian diffusion mixes toward its proved Gibbs target with the full arbitrary-shift rate. -/
theorem wasserstein2_gibbs_general (μ : Measure (H ι)) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : H ι → H ι) 2 μ) (f : H ι → ℝ) (m a : ℝ) (M γ : ℝ≥0)
    (hm : 0 < m) (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ)) (hd : 0 < (γ : ℝ)-2*a)
    (T : ℝ) (hT : 0 ≤ T) :
    ULA.wasserstein2Real (positionLaw ι (stdGaussian (H ι)) IsGaussian.memLp_two_id μ hμ f M γ hLip T hT)
      (ULA.gibbsMeasure f) ≤
      (Real.sqrt (2*(((γ : ℝ)-a)^2+a^2))/((γ : ℝ)-2*a) *
        Real.exp (max (a^2-m) ((M : ℝ)-((γ : ℝ)-a)^2)/((γ : ℝ)-2*a)*T)) *
          ULA.wasserstein2Real μ (ULA.gibbsMeasure f) := by
  letI := ULA.isProbabilityMeasure_gibbsMeasure f m hm hf hsc
  have hb := wasserstein2_general ι (stdGaussian (H ι)) IsGaussian.memLp_two_id μ (ULA.gibbsMeasure f)
    hμ (ULA.memLp_id_gibbsMeasure f m hm hf hsc) f m a M γ hf hsc hLip hmM hd T hT
  rw [positionLaw_gibbs ι f m hm M γ hf hsc hLip T hT] at hb
  exact hb

/-- The paper's simple friction-regime continuous mixing estimate for the actual Gibbs-target diffusion. -/
theorem wasserstein2_gibbs (μ : Measure (H ι)) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : H ι → H ι) 2 μ) (f : H ι → ℝ) (m : ℝ) (M γ : ℝ≥0)
    (hm : 0 < m) (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ)) (hγ : 0 < (γ : ℝ))
    (hfriction : m+(M : ℝ) ≤ (γ : ℝ)^2) (T : ℝ) (hT : 0 ≤ T) :
    ULA.wasserstein2Real (positionLaw ι (stdGaussian (H ι)) IsGaussian.memLp_two_id μ hμ f M γ hLip T hT)
      (ULA.gibbsMeasure f) ≤ Real.sqrt 2 * Real.exp ((-m/(γ : ℝ))*T) *
        ULA.wasserstein2Real μ (ULA.gibbsMeasure f) := by
  have hb := wasserstein2_gibbs_general ι μ hμ f m 0 M γ hm hf hsc hLip hmM (by simpa using hγ) T hT
  have hmax : max (-m) ((M : ℝ)-(γ : ℝ)^2) = -m := max_eq_left (by linarith)
  have hpref : Real.sqrt (2*(γ : ℝ)^2)/(γ : ℝ)=Real.sqrt 2 := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),Real.sqrt_sq_eq_abs,abs_of_pos hγ]
    field_simp
  simpa only [sub_zero,mul_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),add_zero,zero_sub,hmax,hpref]
    using hb

/-- Finite initial second moment gives a finite actual diffusion-to-target transport distance. -/
theorem wasserstein2_gibbs_ne_top (μ : Measure (H ι)) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : H ι → H ι) 2 μ) (f : H ι → ℝ) (m : ℝ) (M γ : ℝ≥0)
    (hm : 0 < m) (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (T : ℝ) (hT : 0 ≤ T) :
    ULA.wasserstein2 (positionLaw ι (stdGaussian (H ι)) IsGaussian.memLp_two_id μ hμ f M γ hLip T hT)
      (ULA.gibbsMeasure f) ≠ ⊤ := by
  letI := ULA.isProbabilityMeasure_gibbsMeasure f m hm hf hsc
  letI : IsProbabilityMeasure (positionLaw ι (stdGaussian (H ι)) IsGaussian.memLp_two_id μ hμ f M γ hLip T hT) :=
    ProductContinuous.positionLaw_probability _ μ hμ _ _ _ _ M γ hLip T hT
  exact ULA.wasserstein2_ne_top_of_memLp _ _
    (ProductContinuous.positionLaw_memLp _ μ hμ _ _ _ _ M γ hLip T hT)
    (ULA.memLp_id_gibbsMeasure f m hm hf hsc)

end KineticLangevin.CanonicalContinuous
