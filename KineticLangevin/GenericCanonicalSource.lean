import KineticLangevin.OUMarginal

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace KineticLangevin.GenericCanonicalSource
open BrownianConvolution
variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- Independent Gaussian velocity and the existing canonical spatial Brownian source on arbitrary finite coordinates. -/
def canonicalSourceProbability : Measure (EuclideanSpace ℝ ι × ULA.CanonicalBrownian.VectorSample ι) :=
  (stdGaussian (EuclideanSpace ℝ ι)).prod (ULA.CanonicalBrownian.vectorProbability ι)
instance canonicalSourceProbability_isProbabilityMeasure : IsProbabilityMeasure (canonicalSourceProbability ι) := by
  unfold canonicalSourceProbability
  infer_instance

def canonicalKLMCInnovation (γ : ℝ) (h : ℝ≥0) (n : ℕ)
    (ω : ULA.CanonicalBrownian.VectorSample ι) : PhaseSpace (EuclideanSpace ℝ ι) :=
  (WithLp.toLp 2 (fun i => gridConvolutionLp (klmcKernels γ) (continuous_klmcKernels γ) h n 0 (ω i)),
   WithLp.toLp 2 (fun i => gridConvolutionLp (klmcKernels γ) (continuous_klmcKernels γ) h n 1 (ω i)))

theorem measurable_canonicalKLMCInnovation (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    Measurable (canonicalKLMCInnovation ι γ h n) := by
  have hm : Measurable (fun x : ι → EuclideanSpace ℝ (Fin 2) =>
      (WithLp.toLp 2 (fun i => x i 0),WithLp.toLp 2 (fun i => x i 1))) := by fun_prop
  exact hm.comp (measurable_vectorGridBlock ι (klmcKernels γ) (continuous_klmcKernels γ) h n)

theorem canonicalKLMCInnovation_independent (γ : ℝ) (h : ℝ≥0) :
    iIndepFun (canonicalKLMCInnovation ι γ h) (ULA.CanonicalBrownian.vectorProbability ι) :=
  (vectorGridBlock_time_independent ι (klmcKernels γ) (continuous_klmcKernels γ) h).comp
    (fun _ x => (WithLp.toLp 2 (fun i => x i 0),WithLp.toLp 2 (fun i => x i 1))) (by intros;fun_prop)

/-- The actual phase innovation has precisely the spatial product of the paper's correlated Gaussian blocks. -/
theorem canonicalKLMCInnovation_law (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    HasLaw (canonicalKLMCInnovation ι γ h n)
      ((Measure.pi (fun _ : ι => klmcGaussian γ h)).map
        (fun x => (WithLp.toLp 2 (fun i => x i 0),WithLp.toLp 2 (fun i => x i 1))))
      (ULA.CanonicalBrownian.vectorProbability ι) := by
  let R := Measure.infinitePi (fun _ : ι => klmcGaussian γ h)
  have hblock : HasLaw (vectorGridBlock ι (klmcKernels γ) (continuous_klmcKernels γ) h n)
      R (ULA.CanonicalBrownian.vectorProbability ι) :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => R) n).hasLaw.comp
      (vectorGridBlock_path_law ι (klmcKernels γ) (continuous_klmcKernels γ) h)
  change HasLaw _ (Measure.infinitePi (fun _ : ι => klmcGaussian γ h)) _ at hblock
  rw [Measure.infinitePi_eq_pi] at hblock
  have hp : HasLaw
      (fun x : ι → EuclideanSpace ℝ (Fin 2) =>
        (WithLp.toLp 2 (fun i => x i 0),WithLp.toLp 2 (fun i => x i 1)))
      ((Measure.pi (fun _ : ι => klmcGaussian γ h)).map
        (fun x => (WithLp.toLp 2 (fun i => x i 0),WithLp.toLp 2 (fun i => x i 1))))
      (Measure.pi (fun _ : ι => klmcGaussian γ h)) := ⟨(by fun_prop),rfl⟩
  exact hp.comp hblock

/-- The whole implemented innovation stream has the actual iid packed Gaussian law. -/
theorem canonicalKLMCInnovation_streamLaw (γ : ℝ) (h : ℝ≥0) :
    HasLaw (fun ω n => canonicalKLMCInnovation ι γ h n ω)
      (Measure.infinitePi (fun _ : ℕ => (Measure.pi (fun _ : ι => klmcGaussian γ h)).map
        (fun x => (WithLp.toLp 2 (fun i => x i 0),WithLp.toLp 2 (fun i => x i 1)))))
      (ULA.CanonicalBrownian.vectorProbability ι) :=
  (canonicalKLMCInnovation_independent ι γ h).hasLaw_infinitePi
    (canonicalKLMCInnovation_law ι γ h)
    (measurable_pi_iff.mpr (measurable_canonicalKLMCInnovation ι γ h)).aemeasurable

theorem canonicalKLMCInnovation_memLp (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    MemLp (fun ω => (canonicalKLMCInnovation ι γ h n ω).1) 2 (ULA.CanonicalBrownian.vectorProbability ι) ∧
    MemLp (fun ω => (canonicalKLMCInnovation ι γ h n ω).2) 2 (ULA.CanonicalBrownian.vectorProbability ι) := by
  constructor
  all_goals apply MemLp.of_eval_piLp
  all_goals intro i
  all_goals exact (Lp.memLp _).comp_measurePreserving (measurePreserving_eval_infinitePi _ i)

theorem canonicalSourceVelocity_law : HasLaw Prod.fst (stdGaussian (EuclideanSpace ℝ ι)) (canonicalSourceProbability ι) :=
  measurePreserving_fst.hasLaw

theorem canonicalSourceVelocity_memLp :
    MemLp (Prod.fst : EuclideanSpace ℝ ι × ULA.CanonicalBrownian.VectorSample ι → EuclideanSpace ℝ ι)
      2 (canonicalSourceProbability ι) :=
  IsGaussian.memLp_two_id.comp_measurePreserving measurePreserving_fst

theorem canonicalSourceInnovation_memLp (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    MemLp (fun p : EuclideanSpace ℝ ι × ULA.CanonicalBrownian.VectorSample ι =>
      (canonicalKLMCInnovation ι γ h n p.2).1) 2 (canonicalSourceProbability ι) ∧
    MemLp (fun p : EuclideanSpace ℝ ι × ULA.CanonicalBrownian.VectorSample ι =>
      (canonicalKLMCInnovation ι γ h n p.2).2) 2 (canonicalSourceProbability ι) :=
  ⟨(canonicalKLMCInnovation_memLp ι γ h n).1.comp_measurePreserving measurePreserving_snd,
    (canonicalKLMCInnovation_memLp ι γ h n).2.comp_measurePreserving measurePreserving_snd⟩

theorem vectorSegmentLp_klmcInnovation_coe (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    (fun ω : ULA.CanonicalBrownian.VectorSample ι =>
      (vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) h ω,
       vectorSegmentLp ι (psi γ 1) (continuous_psi γ 1) ((n : ℝ≥0)*h) h ω))
      =ᵐ[ULA.CanonicalBrownian.vectorProbability ι] canonicalKLMCInnovation ι γ h n := by
  filter_upwards [vectorSegmentLp_coe ι (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) h,
    vectorSegmentLp_coe ι (psi γ 1) (continuous_psi γ 1) ((n : ℝ≥0)*h) h] with ω hv hx
  exact Prod.ext hv hx

theorem vectorOU_grid_independent (γ c : ℝ) (h : ℝ≥0) :
    iIndepFun (fun n : ℕ => c • vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) h)
      (ULA.CanonicalBrownian.vectorProbability ι) := by
  have hi := (canonicalKLMCInnovation_independent ι γ h).comp (fun _ z => c • z.1) (by intros;fun_prop)
  apply hi.congr
  intro n
  filter_upwards [Lp.coeFn_smul c (vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) h),
    vectorSegmentLp_klmcInnovation_coe ι γ h n] with ω hsm hp
  simp only [Pi.smul_apply] at hsm
  exact (hsm.trans (congrArg (fun v => c • v) (congrArg Prod.fst hp))).symm

theorem vectorOU_grid_hasLaw (γ : ℝ) (hγ : 0 ≤ γ) (h : ℝ≥0) :
    HasLaw (fun ω (n : ℕ) => (Real.sqrt (2*γ) •
      vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) h) ω)
      (Measure.infinitePi (fun _ : ℕ => (stdGaussian (EuclideanSpace ℝ ι)).map
        (fun x => Real.sqrt (1-(psi γ 0 h)^2) • x))) (ULA.CanonicalBrownian.vectorProbability ι) := by
  apply (vectorOU_grid_independent ι γ (Real.sqrt (2*γ)) h).hasLaw_infinitePi
  · intro n
    exact vectorOU_hasLaw ι γ hγ ((n : ℝ≥0)*h) h
  · apply Measurable.aemeasurable
    apply measurable_pi_iff.mpr
    intro n
    exact (Lp.stronglyMeasurable _).measurable

end KineticLangevin.GenericCanonicalSource
