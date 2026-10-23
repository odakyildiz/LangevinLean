import KineticLangevin.CanonicalSplitting
import KineticLangevin.Thermostat

/-! # The actual canonical OU innovation has the exact thermal Gaussian law -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace KineticLangevin.BrownianConvolution
variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- Independent spatial copies of an actual scalar variable have the
corresponding finite product law, transported to Euclidean coordinates. -/
theorem spatialLift_hasLaw (Z : Lp ℝ 2 probability) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hZ : HasLaw Z ν probability) :
    HasLaw (spatialLift ι Z) ((Measure.pi (fun _ : ι ↦ ν)).map (WithLp.toLp 2))
      (ULA.CanonicalBrownian.vectorProbability ι) := by
  have hm : Measurable Z := (Lp.stronglyMeasurable Z).measurable
  have hi : iIndepFun (fun i (ω : ULA.CanonicalBrownian.VectorSample ι) ↦ Z (ω i))
      (ULA.CanonicalBrownian.vectorProbability ι) :=
    iIndepFun_infinitePi (X := fun _ x ↦ Z x) (fun _ ↦ hm)
  have hl (i : ι) : HasLaw (fun ω : ULA.CanonicalBrownian.VectorSample ι ↦ Z (ω i)) ν
      (ULA.CanonicalBrownian.vectorProbability ι) :=
    hZ.comp (measurePreserving_eval_infinitePi (fun _ : ι ↦ probability) i).hasLaw
  have hp := hi.hasLaw_infinitePi hl
    (measurable_pi_iff.mpr (fun i ↦ hm.comp (measurable_pi_apply i))).aemeasurable
  rw [Measure.infinitePi_eq_pi] at hp
  have ht : HasLaw (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι)
      ((Measure.pi (fun _ : ι ↦ ν)).map (WithLp.toLp 2)) (Measure.pi (fun _ : ι ↦ ν)) :=
    ⟨(WithLp.measurable_toLp 2 _).aemeasurable,rfl⟩
  exact (ht.comp hp).congr (spatialLift_coe ι Z)

/-- Independent spatial copies of a scaled real standard Gaussian give
precisely the scaled Euclidean standard Gaussian. -/
theorem spatialLift_hasLaw_scaledStandard (Z : Lp ℝ 2 probability) (σ : ℝ)
    (hZ : HasLaw Z ((gaussianReal 0 1).map (fun x ↦ σ*x)) probability) :
    HasLaw (spatialLift ι Z)
      ((stdGaussian (EuclideanSpace ℝ ι)).map (fun x ↦ σ • x))
      (ULA.CanonicalBrownian.vectorProbability ι) := by
  have hprod : ((Measure.pi (fun _ : ι ↦ (gaussianReal 0 1).map (fun x ↦ σ*x))).map
      (WithLp.toLp 2)) = (stdGaussian (EuclideanSpace ℝ ι)).map (fun x ↦ σ • x) := by
    rw [← Measure.pi_map_pi (fun _ : ι ↦ (show Measurable (fun x : ℝ ↦ σ*x) by fun_prop).aemeasurable),
      Measure.map_map (WithLp.measurable_toLp 2 _) (by fun_prop),
      ← map_pi_eq_stdGaussian,Measure.map_map (by fun_prop) (WithLp.measurable_toLp 2 _)]
    congr 1
  rw [← hprod]
  exact spatialLift_hasLaw ι Z _ hZ

/-- The actual scalar OU convolution, with fluctuation-dissipation scaling,
has the law of the exact thermal-variance Gaussian. -/
theorem scalarOU_hasLaw (γ : ℝ) (hγ : 0≤γ) (a t : ℝ≥0) :
    HasLaw (Real.sqrt (2*γ) • segmentConvolutionLp (psi γ 0) (continuous_psi γ 0) a t)
      ((gaussianReal 0 1).map
        (fun x ↦ Real.sqrt (1-(psi γ 0 t)^2)*x)) probability := by
  let K := segmentKernelLp (psi γ 0) (continuous_psi γ 0) a t
  let c := Real.sqrt (2*γ)
  let σ := Real.sqrt (1-(psi γ 0 t)^2)
  have hvariance : 0≤1-(psi γ 0 t)^2 := by
    have hp := psi_nonneg γ 0 t.coe_nonneg
    have hq := psi_zero_le_one hγ t.coe_nonneg
    nlinarith
  have hnorm : ‖K‖^2=klmcCovariance γ t 0 0 := by
    rw [← real_inner_self_eq_norm_sq,segmentKernelLp_inner]
    rfl
  have hnormc : ‖c • K‖^2=σ^2 := by
    rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
    change (Real.sqrt (2*γ))^2*‖K‖^2=(Real.sqrt (1-(psi γ 0 t)^2))^2
    rw [Real.sq_sqrt (by positivity),Real.sq_sqrt hvariance,hnorm]
    nlinarith [velocity_variance_balance γ t]
  have hz := ULA.GaussianHilbert.isonormal_hasLaw ULA.CanonicalBrownian.basis (c • K)
  change HasLaw (ULA.GaussianHilbert.isonormal ULA.CanonicalBrownian.basis (c • K))
    (gaussianReal 0 (‖c • K‖^2).toNNReal) probability at hz
  rw [hnormc] at hz
  rw [gaussianReal_map_const_mul]
  simp only [mul_zero,mul_one]
  have hv : (σ^2).toNNReal=⟨σ^2,sq_nonneg σ⟩ := by
    apply NNReal.eq
    exact Real.coe_toNNReal _ (sq_nonneg σ)
  change HasLaw (c • segmentConvolutionLp (psi γ 0) (continuous_psi γ 0) a t)
    (gaussianReal 0 ⟨σ^2,sq_nonneg σ⟩) probability
  simpa only [segmentConvolutionLp,K,map_smul,hv] using hz

/-- The actual canonical vector OU innovation has exactly the law required
by the thermal Gaussian step, including every spatial coordinate. -/
theorem vectorOU_hasLaw (γ : ℝ) (hγ : 0≤γ) (a t : ℝ≥0) :
    HasLaw (Real.sqrt (2*γ) • vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) a t)
      ((stdGaussian (EuclideanSpace ℝ ι)).map
        (fun x ↦ Real.sqrt (1-(psi γ 0 t)^2) • x))
      (ULA.CanonicalBrownian.vectorProbability ι) := by
  have hz := spatialLift_hasLaw_scaledStandard ι
    (Real.sqrt (2*γ) • segmentConvolutionLp (psi γ 0) (continuous_psi γ 0) a t)
    (Real.sqrt (1-(psi γ 0 t)^2)) (scalarOU_hasLaw γ hγ a t)
  simpa only [map_smul,vectorSegmentLp] using hz

/-- The actual scaled OU innovations on disjoint time-grid intervals are
independent as full spatial vectors, by the constructed Brownian source. -/
theorem vectorOU_grid_independent (d : ℕ) (γ c : ℝ) (h : ℝ≥0) :
    iIndepFun (fun n : ℕ ↦ c • vectorSegmentLp (Fin d) (psi γ 0) (continuous_psi γ 0)
      ((n : ℝ≥0)*h) h) (ULA.CanonicalBrownian.vectorProbability (Fin d)) := by
  have hi := (canonicalKLMCInnovation_independent d γ h).comp
    (fun _ z ↦ c • z.1) (by intro n; fun_prop)
  apply hi.congr
  intro n
  filter_upwards [Lp.coeFn_smul c
      (vectorSegmentLp (Fin d) (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) h),
    vectorSegmentLp_klmcInnovation_coe d γ h n] with ω hsm hp
  simp only [Pi.smul_apply] at hsm
  exact (hsm.trans (congrArg (fun v ↦ c • v) (congrArg Prod.fst hp))).symm

/-- The full actual OU innovation stream has the independent thermal
Gaussian stream law needed by a Markov-chain law transfer. -/
theorem vectorOU_grid_hasLaw (d : ℕ) (γ : ℝ) (hγ : 0≤γ) (h : ℝ≥0) :
    HasLaw (fun ω (n : ℕ) ↦ (Real.sqrt (2*γ) •
      vectorSegmentLp (Fin d) (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) h) ω)
      (Measure.infinitePi (fun _ : ℕ ↦
        (stdGaussian (EuclideanSpace ℝ (Fin d))).map
          (fun x ↦ Real.sqrt (1-(psi γ 0 h)^2) • x)))
      (ULA.CanonicalBrownian.vectorProbability (Fin d)) := by
  apply (vectorOU_grid_independent d γ (Real.sqrt (2*γ)) h).hasLaw_infinitePi
  · intro n
    exact vectorOU_hasLaw (Fin d) γ hγ ((n : ℝ≥0)*h) h
  · apply Measurable.aemeasurable
    apply measurable_pi_iff.mpr
    intro n
    exact (Lp.stronglyMeasurable _).measurable

end KineticLangevin.BrownianConvolution
