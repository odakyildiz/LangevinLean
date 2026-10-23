import KineticLangevin.HamiltonianStationarity
import UnadjustedLangevin.GaussianProposalDensity
import KineticLangevin.Thermostat

/-! # Canonical Gaussian-times-Gibbs Hamiltonian target -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal ENNReal
namespace KineticLangevin
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- The standard Gaussian is the explicitly normalized thermal velocity weight. -/
theorem stdGaussian_hamiltonian_density :
    stdGaussian E = ENNReal.ofReal (ULA.radialGaussianNormalizer (H := E) (1/2)) •
      (volume : Measure E).withDensity (fun v ↦ ENNReal.ofReal (Real.exp (-‖v‖^2/2))) := by
  have hm := ULA.gaussian_proposal_radial_density (H := E) (1/2) (by norm_num) 0
  have hprecision : (1 / (4 * (1/2 : ℝ))) = (1/2 : ℝ) := by norm_num
  rw [hprecision] at hm
  have hfun : (fun ξ : E ↦ (0 : E)+Real.sqrt (2*(1/2:ℝ)) • ξ) = id := by
    funext ξ
    norm_num
  rw [hfun,Measure.map_id] at hm
  rw [hm,← withDensity_smul _ (by fun_prop)]
  congr 1
  funext v
  unfold ULA.radialGaussianDensity
  rw [Pi.smul_apply,smul_eq_mul,← ENNReal.ofReal_mul
    (ULA.radialGaussianNormalizer_pos (H := E) (1/2) (by norm_num)).le]
  rw [sub_zero]
  congr 1
  congr 1
  congr 1
  ring

/-- The canonical target has standard thermal Gaussian velocity independent
of the normalized potential Gibbs position. -/
def kineticGibbsTarget (f : E → ℝ) : Measure (E×E) :=
  (stdGaussian E).prod (ULA.gibbsMeasure f)

/-- The canonical target is an explicit scalar normalization of the actual
Hamiltonian weighted measure, with no distributional identification premise. -/
theorem kineticGibbsTarget_eq_scaled (f : E → ℝ) (hf : Measurable f) :
    kineticGibbsTarget f =
      (ENNReal.ofReal (ULA.radialGaussianNormalizer (H := E) (1/2)) *
        (ULA.gibbsPartition f)⁻¹) • hamiltonianGibbs (volume : Measure E) f := by
  rw [kineticGibbsTarget,stdGaussian_hamiltonian_density,ULA.gibbsMeasure,
    Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,
    hamiltonianGibbs_factor volume f hf]
  rfl

/-- The target's probability normalization is derived from the potential assumptions. -/
theorem kineticGibbsTarget_probability (f : E → ℝ) (m : ℝ) (hm : 0<m)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) :
    IsProbabilityMeasure (kineticGibbsTarget f) := by
  haveI := ULA.isProbabilityMeasure_gibbsMeasure f m hm hf hsc
  unfold kineticGibbsTarget
  infer_instance

/-- The actual Hamiltonian flow preserves the canonical independent
Gaussian-times-Gibbs target under the paper's first-order assumptions. -/
theorem hamiltonianFlow_preserves_target
    (f : E → ℝ) (m : ℝ) (hm : 0<m) (M : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (T : ℝ) (hT : 0 ≤ T) :
    (kineticGibbsTarget f).map (fun z ↦ hamiltonianFlow f M hLip T hT z T) =
      kineticGibbsTarget f := by
  rw [kineticGibbsTarget_eq_scaled f hf.continuous.measurable,
    Measure.map_smul _ (hamiltonianFlow_endpoint_continuous f M hLip T hT).measurable.aemeasurable,
    hamiltonianFlow_preserves_gibbs f m hm M hf hsc hLip T hT]

/-- An exact Gaussian thermostat preserves any independent position law.
The source is explicitly the old phase state times a fresh Gaussian velocity. -/
theorem thermostat_preserves_independent_position (π : Measure E) [IsProbabilityMeasure π]
    (a b : ℝ) (hab : a^2+b^2 = 1) :
    (((stdGaussian E).prod π).prod (stdGaussian E)).map
      (fun p ↦ (a • p.1.1+b • p.2,p.1.2)) = (stdGaussian E).prod π := by
  have hperm : MeasurePreserving (fun p : (E×E)×E ↦ ((p.1.1,p.2),p.1.2))
      (((stdGaussian E).prod π).prod (stdGaussian E))
      (((stdGaussian E).prod (stdGaussian E)).prod π) := by
    convert (MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc (stdGaussian E) (stdGaussian E) π)).comp
      (((MeasurePreserving.id (stdGaussian E)).prod
        (Measure.measurePreserving_swap (μ := π) (ν := stdGaussian E))).comp
        (measurePreserving_prodAssoc (stdGaussian E) π (stdGaussian E))) using 1
    rfl
  have hO : (((stdGaussian E).prod (stdGaussian E)).prod π).map
      (fun p ↦ (a • p.1.1+b • p.1.2,p.2)) = (stdGaussian E).prod π := by
    have hp := Measure.map_prod_map ((stdGaussian E).prod (stdGaussian E)) π
      (show Measurable (fun z : E×E ↦ a • z.1+b • z.2) by fun_prop) measurable_id
    rw [stdGaussian_linear_combination a b hab,Measure.map_id] at hp
    exact hp.symm
  calc
    _ = ((((stdGaussian E).prod π).prod (stdGaussian E)).map
      (fun p : (E×E)×E ↦ ((p.1.1,p.2),p.1.2))).map
        (fun p ↦ (a • p.1.1+b • p.1.2,p.2)) := by
      rw [Measure.map_map (by fun_prop) hperm.measurable]
      rfl
    _ = _ := by rw [hperm.map_eq,hO]

/-- The canonical kinetic Gibbs target is invariant under the actual
independent Gaussian thermostat, before any discretization limit is taken. -/
theorem thermostat_preserves_target (f : E → ℝ) (m : ℝ) (hm : 0<m)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (a b : ℝ) (hab : a^2+b^2=1) :
    ((kineticGibbsTarget f).prod (stdGaussian E)).map
      (fun p ↦ (a • p.1.1+b • p.2,p.1.2)) = kineticGibbsTarget f := by
  haveI := ULA.isProbabilityMeasure_gibbsMeasure f m hm hf hsc
  exact thermostat_preserves_independent_position (ULA.gibbsMeasure f) a b hab

/-- The target's position marginal is exactly the intended normalized Gibbs law. -/
theorem kineticGibbsTarget_position (f : E → ℝ) (m : ℝ) (hm : 0<m)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) :
    (kineticGibbsTarget f).map Prod.snd = ULA.gibbsMeasure f := by
  haveI := ULA.isProbabilityMeasure_gibbsMeasure f m hm hf hsc
  simpa only [kineticGibbsTarget,measure_univ,one_smul] using
    (Measure.map_snd_prod (μ := stdGaussian E) (ν := ULA.gibbsMeasure f))

/-- The target's velocity marginal is the actual standard Gaussian law. -/
theorem kineticGibbsTarget_velocity (f : E → ℝ) (m : ℝ) (hm : 0<m)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) :
    (kineticGibbsTarget f).map Prod.fst = stdGaussian E := by
  haveI := ULA.isProbabilityMeasure_gibbsMeasure f m hm hf hsc
  simpa only [kineticGibbsTarget,measure_univ,one_smul] using
    (Measure.map_fst_prod (μ := stdGaussian E) (ν := ULA.gibbsMeasure f))

end KineticLangevin
