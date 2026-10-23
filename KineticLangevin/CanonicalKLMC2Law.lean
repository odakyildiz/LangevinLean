import KineticLangevin.KLMC2ProductLaw
import KineticLangevin.CanonicalKLMC2Noise
import KineticLangevin.ContinuousGibbs

noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace KineticLangevin.SecondOrderSource
variable (ι : Type*) [Fintype ι] [DecidableEq ι]
abbrev SourceSample := H ι × ULA.CanonicalBrownian.VectorSample ι

/-- The original source innovation reads the independent Brownian coordinate after the initial velocity. -/
def sourceInnovation (γ : ℝ) (h : ℝ≥0) (n : ℕ) (p : SourceSample ι) : Fin 4 → H ι :=
  innovation ι γ h n p.2

theorem sourceInnovation_memLp (γ : ℝ) (h : ℝ≥0) (n : ℕ) (j : Fin 4) :
    MemLp (fun p => sourceInnovation ι γ h n p j) 2 (GenericCanonicalSource.canonicalSourceProbability ι) :=
  (innovation_memLp ι γ h n j).comp_measurePreserving measurePreserving_snd

/-- The canonical second-order position law is defined independently of every initial transport coupling. -/
def law (g : H ι → H ι) (Hess : H ι → H ι →L[ℝ] H ι) (γ : ℝ) (h : ℝ≥0)
    (μ : Measure (H ι)) (n : ℕ) : Measure (H ι) :=
  productKLMC2Law (GenericCanonicalSource.canonicalSourceProbability ι) g Hess γ h μ Prod.fst
    (fun k => sourceInnovation ι γ h k) n

theorem law_probability (g : H ι → H ι) (Hess : H ι → H ι →L[ℝ] H ι)
    (hG : Continuous g) (hH : Continuous Hess) (γ : ℝ) (h : ℝ≥0)
    (μ : Measure (H ι)) [IsProbabilityMeasure μ] (n : ℕ) : IsProbabilityMeasure (law ι g Hess γ h μ n) :=
  productKLMC2Law_probability (GenericCanonicalSource.canonicalSourceProbability ι) g Hess hG hH γ h
    Prod.fst (GenericCanonicalSource.canonicalSourceVelocity_memLp ι)
    (fun k => sourceInnovation ι γ h k) (sourceInnovation_memLp ι γ h) n

/-- The actual independent initial phase and complete four-kernel noise stream have the required full Gaussian product law. -/
theorem initial_innovation_jointLaw (μ : Measure (H ι)) [IsProbabilityMeasure μ] (γ : ℝ) (h : ℝ≥0) :
    HasLaw (fun p : H ι × SourceSample ι => ((p.2.1,p.1),fun n => innovation ι γ h n p.2.2))
      (((stdGaussian (H ι)).prod μ).prod (Measure.infinitePi (fun _ : ℕ => gaussianInnovationLaw ι γ h)))
      (μ.prod (GenericCanonicalSource.canonicalSourceProbability ι)) := by
  have hj := jointLaw_product_source ((stdGaussian (H ι)).prod μ)
    (ULA.CanonicalBrownian.vectorProbability ι) (gaussianInnovationLaw ι γ h)
    (fun ω n => innovation ι γ h n ω) (measurable_pi_iff.mpr (measurable_innovation ι γ h))
    (innovation_streamLaw ι γ h)
  exact hj.comp (CanonicalContinuous.phaseSourceProjection_preserving ι μ).hasLaw

/-- The actual canonical Brownian KLMC2 output is exactly the implemented correlated-Gaussian Markov output. -/
theorem law_eq_markovLaws (g : H ι → H ι) (Hess : H ι → H ι →L[ℝ] H ι)
    (hG : Continuous g) (hH : Continuous Hess) (γ : ℝ) (h : ℝ≥0)
    (μ : Measure (H ι)) [IsProbabilityMeasure μ] (n : ℕ) :
    law ι g Hess γ h μ n =
      (ULA.markovLaws (klmc2Step g Hess γ h) (gaussianInnovationLaw ι γ h)
        ((stdGaussian (H ι)).prod μ) n).map Prod.snd := by
  let P := μ.prod (GenericCanonicalSource.canonicalSourceProbability ι)
  have hs := klmc2Step_measurable g Hess hG hH γ h
  have hc : Measurable (fun p : H ι × SourceSample ι =>
      ULA.noiseDrivenChain (klmc2Step g Hess γ h) (p.2.1,p.1)
        (fun k => innovation ι γ h k p.2.2) n) :=
    (ULA.noiseDrivenChain_measurable _ hs n).comp
      ((measurable_snd.fst.prodMk measurable_fst).prodMk
        (measurable_pi_iff.mpr (fun k => (measurable_innovation ι γ h k).comp measurable_snd.snd)))
  have hl := noiseDrivenChain_law_of_jointLaw P (klmc2Step g Hess γ h) hs
    ((stdGaussian (H ι)).prod μ) (gaussianInnovationLaw ι γ h) _ _
    (initial_innovation_jointLaw ι μ γ h) n
  have hp := congrArg (fun ν : Measure (H ι×H ι) => ν.map Prod.snd) hl
  rw [Measure.map_map measurable_snd hc] at hp
  unfold law productKLMC2Law productKLMC2Map
  simp_rw [klmc2Chain_eq_noiseDrivenChain]
  simpa only [P,Function.comp_def,sourceInnovation] using hp

section Coupling
open GenericCanonicalCoupling
variable {ι} {μ π : Measure (H ι)} [IsProbabilityMeasure μ]

/-- The directly lifted canonical convolution is the same L² noise as the generic independent-source extension. -/
theorem extensionInnovation_eq_generic (c : ULA.Coupling μ π) (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    extensionInnovation c γ h n =
      extensionKLMC2Noise (GenericCanonicalSource.canonicalSourceProbability ι) c
        (fun k => sourceInnovation ι γ h k) (sourceInnovation_memLp ι γ h) n := by
  funext j
  apply Lp.ext
  filter_upwards [extensionInnovation_coe c γ h n,
    extensionKLMC2Noise_coe (GenericCanonicalSource.canonicalSourceProbability ι) c
      (fun k => sourceInnovation ι γ h k) (sourceInnovation_memLp ι γ h) n] with p h1 h2
  exact (congrFun h1 j).trans (congrFun h2 j).symm

/-- The actual canonical second-order L² chain on an arbitrary finite-cost initial coupling. -/
def numericalChain (c : ULA.Coupling μ π) (hc : ULA.couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (id : H ι → H ι) 2 π)
    (g : H ι → H ι) (Hess : H ι → H ι →L[ℝ] H ι) (M M2 : ℝ≥0)
    (hG : LipschitzWith M g) (hH : LipschitzWith M2 Hess) (hg : ∀ x,HasFDerivAt g (Hess x) x)
    (γ : ℝ) (h : ℝ≥0) : ℕ → Lp (H ι) 2 (GenericCanonicalCoupling.probability c) ×
      Lp (H ι) 2 (GenericCanonicalCoupling.probability c) :=
  klmc2Chain (ULA.lpDrift (GenericCanonicalCoupling.probability c) g hG)
    (lpHessian (GenericCanonicalCoupling.probability c) g Hess M M2 hG hH hg) γ h
    (GenericCanonicalCoupling.numericalInitial c hc hπ) (extensionInnovation c γ h)

/-- The actual L² second-order output has one coupling-independent canonical Gaussian Markov law. -/
theorem numericalChain_outputLaw (c : ULA.Coupling μ π) (hc : ULA.couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (id : H ι → H ι) 2 π)
    (g : H ι → H ι) (Hess : H ι → H ι →L[ℝ] H ι) (M M2 : ℝ≥0)
    (hG : LipschitzWith M g) (hH : LipschitzWith M2 Hess) (hg : ∀ x,HasFDerivAt g (Hess x) x)
    (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    (GenericCanonicalCoupling.probability c).map (numericalChain c hc hπ g Hess M M2 hG hH hg γ h n).2 =
      law ι g Hess γ h μ n := by
  unfold numericalChain
  have hN := funext (extensionInnovation_eq_generic c γ h)
  rw [hN]
  exact product_klmc2Chain_outputLaw (GenericCanonicalSource.canonicalSourceProbability ι) c hc hπ
    g Hess M M2 hG hH hg γ h Prod.fst (GenericCanonicalSource.canonicalSourceVelocity_memLp ι)
    (fun k => sourceInnovation ι γ h k) (sourceInnovation_memLp ι γ h) n

/-- The actual numerical chain starts at the shared Gaussian velocity and first coupling position. -/
@[simp] theorem numericalChain_zero (c : ULA.Coupling μ π) (hc : ULA.couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (id : H ι → H ι) 2 π)
    (g : H ι → H ι) (Hess : H ι → H ι →L[ℝ] H ι) (M M2 : ℝ≥0)
    (hG : LipschitzWith M g) (hH : LipschitzWith M2 Hess) (hg : ∀ x,HasFDerivAt g (Hess x) x)
    (γ : ℝ) (h : ℝ≥0) :
    numericalChain c hc hπ g Hess M M2 hG hH hg γ h 0=GenericCanonicalCoupling.numericalInitial c hc hπ := rfl

/-- Its exact recurrence uses the original four-kernel Hessian-corrected update. -/
theorem numericalChain_succ (c : ULA.Coupling μ π) (hc : ULA.couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (id : H ι → H ι) 2 π)
    (g : H ι → H ι) (Hess : H ι → H ι →L[ℝ] H ι) (M M2 : ℝ≥0)
    (hG : LipschitzWith M g) (hH : LipschitzWith M2 Hess) (hg : ∀ x,HasFDerivAt g (Hess x) x)
    (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    numericalChain c hc hπ g Hess M M2 hG hH hg γ h (n+1)=
      klmc2Step (ULA.lpDrift (GenericCanonicalCoupling.probability c) g hG)
        (lpHessian (GenericCanonicalCoupling.probability c) g Hess M M2 hG hH hg) γ h
        (numericalChain c hc hπ g Hess M M2 hG hH hg γ h n) (extensionInnovation c γ h n) := rfl

/-- Every actual second-order output law has a finite second moment whenever one finite initial coupling exists. -/
theorem law_memLp_of_finiteCost (c : ULA.Coupling μ π) (hc : ULA.couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (id : H ι → H ι) 2 π)
    (g : H ι → H ι) (Hess : H ι → H ι →L[ℝ] H ι) (M M2 : ℝ≥0)
    (hG : LipschitzWith M g) (hH : LipschitzWith M2 Hess) (hg : ∀ x,HasFDerivAt g (Hess x) x)
    (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    MemLp (id : H ι → H ι) 2 (law ι g Hess γ h μ n) := by
  rw [← numericalChain_outputLaw c hc hπ g Hess M M2 hG hH hg γ h n]
  exact (memLp_map_measure_iff (by fun_prop) (Lp.aestronglyMeasurable _).aemeasurable).mpr (Lp.memLp _)

/-- The real-valued second-order endpoint cannot conceal an infinite output transport distance. -/
theorem law_wasserstein2_ne_top [IsProbabilityMeasure π]
    (hπ : MemLp (id : H ι → H ι) 2 π)
    (g : H ι → H ι) (Hess : H ι → H ι →L[ℝ] H ι) (M M2 : ℝ≥0)
    (hG : LipschitzWith M g) (hH : LipschitzWith M2 Hess) (hg : ∀ x,HasFDerivAt g (Hess x) x)
    (γ : ℝ) (h : ℝ≥0) (hfinite : ULA.wasserstein2 μ π ≠ ⊤) (n : ℕ) :
    ULA.wasserstein2 (law ι g Hess γ h μ n) π ≠ ⊤ := by
  letI := law_probability ι g Hess hG.continuous hH.continuous γ h μ n
  obtain ⟨c,hc⟩ := ULA.exists_finiteCost_coupling μ π hfinite
  exact ULA.wasserstein2_ne_top_of_memLp _ _
    (law_memLp_of_finiteCost c hc.ne hπ g Hess M M2 hG hH hg γ h n) hπ

/-- The actual initial numerical/reference position discrepancy is exactly the cost of the supplied initial plan. -/
theorem initial_position_cost (c : ULA.Coupling μ π) (hc : ULA.couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (id : H ι → H ι) 2 π)
    (g : H ι → H ι) (Hess : H ι → H ι →L[ℝ] H ι) (M M2 : ℝ≥0)
    (hG : LipschitzWith M g) (hH : LipschitzWith M2 Hess) (hg : ∀ x,HasFDerivAt g (Hess x) x)
    (γ : ℝ) (h : ℝ≥0) :
    ‖(numericalChain c hc hπ g Hess M M2 hG hH hg γ h 0).2-(GenericCanonicalCoupling.referenceInitial c hπ).2‖=
      (ULA.couplingCost c.joint).toReal :=
  ULA.initialExtension_lp_cost c (GenericCanonicalSource.canonicalSourceProbability ι) hc hπ

end Coupling
end KineticLangevin.SecondOrderSource
