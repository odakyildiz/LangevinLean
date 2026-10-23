import KineticLangevin.GenericCanonicalKLMC

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace KineticLangevin.SecondOrderSource
open BrownianConvolution
variable (ι : Type*) [Fintype ι] [DecidableEq ι]
abbrev H := EuclideanSpace ℝ ι

/-- Assemble the four correlated scalar kernel responses in every spatial coordinate. -/
def pack (x : ι → EuclideanSpace ℝ (Fin 4)) : Fin 4 → H ι :=
  fun j => WithLp.toLp 2 (fun i => x i j)

theorem measurable_pack : Measurable (pack ι) := by
  apply measurable_pi_iff.mpr
  intro j
  exact (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.mpr (fun i =>
    (EuclideanSpace.proj j).continuous.measurable.comp (measurable_pi_apply i)))

/-- The exact paper covariance in each spatial coordinate, with all four correlations retained. -/
def gaussianInnovationLaw (γ h : ℝ) : Measure (Fin 4 → H ι) :=
  (Measure.pi (fun _ : ι => klmc2Gaussian γ h)).map (pack ι)

instance gaussianInnovationLaw_isProbabilityMeasure (γ h : ℝ) :
    IsProbabilityMeasure (gaussianInnovationLaw ι γ h) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_pack ι).aemeasurable).mpr inferInstance

/-- The actual four-kernel Brownian innovation used at numerical step n. -/
def innovation (γ : ℝ) (h : ℝ≥0) (n : ℕ) (ω : ULA.CanonicalBrownian.VectorSample ι) : Fin 4 → H ι :=
  pack ι (vectorGridBlock ι (klmc2Kernels γ) (continuous_klmc2Kernels γ) h n ω)

theorem measurable_innovation (γ : ℝ) (h : ℝ≥0) (n : ℕ) : Measurable (innovation ι γ h n) :=
  (measurable_pack ι).comp (measurable_vectorGridBlock ι (klmc2Kernels γ) (continuous_klmc2Kernels γ) h n)

/-- Disjoint Brownian intervals make the full four-response vectors independent across numerical steps. -/
theorem innovation_independent (γ : ℝ) (h : ℝ≥0) :
    iIndepFun (innovation ι γ h) (ULA.CanonicalBrownian.vectorProbability ι) :=
  (vectorGridBlock_time_independent ι (klmc2Kernels γ) (continuous_klmc2Kernels γ) h).comp
    (fun _ => pack ι) (fun _ => measurable_pack ι)

/-- Each actual Brownian four-kernel response has exactly the specified packed correlated Gaussian law. -/
theorem innovation_law (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    HasLaw (innovation ι γ h n) (gaussianInnovationLaw ι γ h) (ULA.CanonicalBrownian.vectorProbability ι) := by
  let R := Measure.infinitePi (fun _ : ι => klmc2Gaussian γ h)
  have hb : HasLaw (vectorGridBlock ι (klmc2Kernels γ) (continuous_klmc2Kernels γ) h n)
      R (ULA.CanonicalBrownian.vectorProbability ι) :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => R) n).hasLaw.comp
      (vectorGridBlock_path_law ι (klmc2Kernels γ) (continuous_klmc2Kernels γ) h)
  change HasLaw _ (Measure.infinitePi (fun _ : ι => klmc2Gaussian γ h)) _ at hb
  rw [Measure.infinitePi_eq_pi] at hb
  have hp : HasLaw (pack ι) (gaussianInnovationLaw ι γ h) (Measure.pi (fun _ : ι => klmc2Gaussian γ h)) :=
    ⟨(measurable_pack ι).aemeasurable,rfl⟩
  exact hp.comp hb

/-- The whole implemented four-kernel stream has its actual iid Gaussian product law. -/
theorem innovation_streamLaw (γ : ℝ) (h : ℝ≥0) :
    HasLaw (fun ω n => innovation ι γ h n ω)
      (Measure.infinitePi (fun _ : ℕ => gaussianInnovationLaw ι γ h))
      (ULA.CanonicalBrownian.vectorProbability ι) :=
  (innovation_independent ι γ h).hasLaw_infinitePi (innovation_law ι γ h)
    (measurable_pi_iff.mpr (measurable_innovation ι γ h)).aemeasurable

/-- The same actual noise is represented directly by its four L² Brownian convolutions. -/
def innovationLp (γ : ℝ) (h : ℝ≥0) (n : ℕ) (j : Fin 4) :
    Lp (H ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) :=
  vectorSegmentLp ι (klmc2Kernels γ j) (continuous_klmc2Kernels γ j) ((n : ℝ≥0)*h) h

/-- Every L² noise coordinate is the corresponding actual implemented vector response almost everywhere. -/
theorem innovationLp_coe (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    (fun ω j => innovationLp ι γ h n j ω) =ᵐ[ULA.CanonicalBrownian.vectorProbability ι] innovation ι γ h n := by
  have hs := ae_all_iff.mpr (fun j : Fin 4 => vectorSegmentLp_coe ι
    (klmc2Kernels γ j) (continuous_klmc2Kernels γ j) ((n : ℝ≥0)*h) h)
  filter_upwards [hs] with ω hω
  funext j
  exact hω j

/-- Every original innovation coordinate has a finite second moment on the genuine Brownian source. -/
theorem innovation_memLp (γ : ℝ) (h : ℝ≥0) (n : ℕ) (j : Fin 4) :
    MemLp (fun ω => innovation ι γ h n ω j) 2 (ULA.CanonicalBrownian.vectorProbability ι) :=
  MemLp.ae_eq ((innovationLp_coe ι γ h n).mono (fun ω hω => congrFun hω j))
    (Lp.memLp (innovationLp ι γ h n j))

section Extension
open GenericCanonicalCoupling
variable {ι} {μ π : Measure (H ι)} [IsProbabilityMeasure μ] (c : ULA.Coupling μ π)
local instance couplingProbability : IsProbabilityMeasure c.joint := c.isProbabilityMeasure

/-- The actual four Brownian convolutions lifted to an arbitrary initial coupling extension. -/
def extensionInnovation (γ : ℝ) (h : ℝ≥0) (n : ℕ) (j : Fin 4) :
    Lp (H ι) 2 (GenericCanonicalCoupling.probability c) :=
  brownianLift c (innovationLp ι γ h n j)

/-- The source lift retains the actual implemented four-response noise values. -/
theorem extensionInnovation_coe (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    (fun p j => extensionInnovation c γ h n j p) =ᵐ[GenericCanonicalCoupling.probability c]
      fun p : GenericCanonicalCoupling.Sample ι => innovation ι γ h n p.2.2 := by
  have hp : MeasurePreserving (fun p : GenericCanonicalCoupling.Sample ι => p.2.2)
      (GenericCanonicalCoupling.probability c) (ULA.CanonicalBrownian.vectorProbability ι) :=
    (measurePreserving_snd : MeasurePreserving Prod.snd (GenericCanonicalSource.canonicalSourceProbability ι)
      (ULA.CanonicalBrownian.vectorProbability ι)).comp measurePreserving_snd
  have he := hp.quasiMeasurePreserving.ae_eq_comp (innovationLp_coe ι γ h n)
  have hs := ae_all_iff.mpr (fun j : Fin 4 => brownianLift_coe c (innovationLp ι γ h n j))
  filter_upwards [he,hs] with p he hs
  funext j
  exact (hs j).trans (congrFun he j)

/-- On every actual initial coupling extension, the full L² four-kernel stream retains its exact iid law. -/
theorem extensionInnovation_streamLaw (γ : ℝ) (h : ℝ≥0) :
    HasLaw (fun p n j => extensionInnovation c γ h n j p)
      (Measure.infinitePi (fun _ : ℕ => gaussianInnovationLaw ι γ h))
      (GenericCanonicalCoupling.probability c) := by
  have hp : MeasurePreserving (fun p : GenericCanonicalCoupling.Sample ι => p.2.2)
      (GenericCanonicalCoupling.probability c) (ULA.CanonicalBrownian.vectorProbability ι) :=
    (measurePreserving_snd : MeasurePreserving Prod.snd (GenericCanonicalSource.canonicalSourceProbability ι)
      (ULA.CanonicalBrownian.vectorProbability ι)).comp measurePreserving_snd
  have hl := (innovation_streamLaw ι γ h).comp hp.hasLaw
  apply hl.congr
  have hs := ae_all_iff.mpr (extensionInnovation_coe c γ h)
  filter_upwards [hs] with p hs
  exact funext hs

end Extension
end KineticLangevin.SecondOrderSource
