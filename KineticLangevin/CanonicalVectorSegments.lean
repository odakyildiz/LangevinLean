import KineticLangevin.BrownianSegmentEquations

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace KineticLangevin.BrownianConvolution

/-- Pull an independent measurable family back along an actual probability law. -/
theorem iIndepFun_comp_hasLaw {Ω Ξ α : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {Q : Measure Ξ} [IsProbabilityMeasure Q]
    {S : α → Type*} [∀ i, MeasurableSpace (S i)]
    (X : ∀ i, Ξ → S i) (hX : ∀ i, Measurable (X i))
    (Y : Ω → Ξ) (hY : Measurable Y) (hlaw : HasLaw Y Q P) (hind : iIndepFun X Q) :
    iIndepFun (fun i ω => X i (Y ω)) P := by
  letI : IsProbabilityMeasure P := hlaw.isProbabilityMeasure
  change iIndepFun (fun i => X i ∘ Y) P
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (fun i => (hX i).comp hY)]
  have hmap := hind.map_fun_eq_infinitePi_map hX
  rw [← hlaw.map_eq] at hmap
  rw [Measure.map_map (measurable_pi_iff.mpr hX) hY] at hmap
  change P.map ((fun x i => X i x) ∘ Y) = _
  rw [hmap]
  congr 1
  funext i
  rw [Measure.map_map (hX i) hY]

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The jointly correlated kernel responses on a scalar Brownian grid interval. -/
def scalarGridBlock (kernels : κ → ℝ → ℝ) (hc : ∀ j, Continuous (kernels j))
    (h : ℝ≥0) (n : ℕ) (ω : Sample) : EuclideanSpace ℝ κ :=
  WithLp.toLp 2 (fun j => gridConvolutionLp kernels hc h n j ω)

theorem measurable_scalarGridBlock (kernels : κ → ℝ → ℝ)
    (hc : ∀ j, Continuous (kernels j)) (h : ℝ≥0) (n : ℕ) :
    Measurable (scalarGridBlock kernels hc h n) := by
  apply (WithLp.measurable_toLp 2 _).comp
  exact measurable_pi_iff.mpr fun j => (Lp.stronglyMeasurable _).measurable

/-- The canonical vector noise uses the existing product of independent scalar Brownian sources. -/
def vectorGridBlock (ι : Type*) (kernels : κ → ℝ → ℝ)
    (hc : ∀ j, Continuous (kernels j)) (h : ℝ≥0) (n : ℕ)
    (ω : ULA.CanonicalBrownian.VectorSample ι) (i : ι) : EuclideanSpace ℝ κ :=
  scalarGridBlock kernels hc h n (ω i)

theorem measurable_vectorGridBlock (ι : Type*) (kernels : κ → ℝ → ℝ)
    (hc : ∀ j, Continuous (kernels j)) (h : ℝ≥0) (n : ℕ) :
    Measurable (vectorGridBlock ι kernels hc h n) := by
  exact measurable_pi_iff.mpr fun i =>
    (measurable_scalarGridBlock kernels hc h n).comp (measurable_pi_apply i)

/-- Independence holds jointly over iteration and spatial coordinate, retaining the correlations inside a block. -/
theorem vectorGridBlock_array_independent (ι : Type*) (kernels : κ → ℝ → ℝ)
    (hc : ∀ j, Continuous (kernels j)) (h : ℝ≥0) :
    iIndepFun (fun p : (n : ℕ) × ι => fun ω : ULA.CanonicalBrownian.VectorSample ι =>
      vectorGridBlock ι kernels hc h p.1 ω p.2) (ULA.CanonicalBrownian.vectorProbability ι) := by
  have hind : iIndepFun (fun p : ι × ℕ => fun ω : ULA.CanonicalBrownian.VectorSample ι =>
      scalarGridBlock kernels hc h p.2 (ω p.1)) (ULA.CanonicalBrownian.vectorProbability ι) := by
    refine iIndepFun_uncurry' (Ω := ULA.CanonicalBrownian.VectorSample ι)
      (P := ULA.CanonicalBrownian.vectorProbability ι)
      (X := fun (i : ι) (n : ℕ) (ω : ULA.CanonicalBrownian.VectorSample ι) => scalarGridBlock kernels hc h n (ω i))
      (fun i n => (measurable_scalarGridBlock kernels hc h n).comp (measurable_pi_apply i)) ?_ ?_
    · exact iIndepFun_infinitePi (X := fun _ ω n => scalarGridBlock kernels hc h n ω)
        (fun _ => measurable_pi_iff.mpr (measurable_scalarGridBlock kernels hc h))
    · intro i
      exact iIndepFun_comp_hasLaw (scalarGridBlock kernels hc h)
        (measurable_scalarGridBlock kernels hc h) (fun ω : ULA.CanonicalBrownian.VectorSample ι => ω i) (measurable_pi_apply i)
        ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval (fun _ : ι => probability) i⟩
        (gridConvolutionLp_euclidean_independent kernels hc h)
  exact hind.precomp (g := fun p : (n : ℕ) × ι => (p.2,p.1))
    (by intro p q hp; cases p; cases q; simp_all)

/-- The complete array has the exact independent Gram-Gaussian product law. -/
theorem vectorGridBlock_array_law (ι : Type*) (kernels : κ → ℝ → ℝ)
    (hc : ∀ j, Continuous (kernels j)) (h : ℝ≥0) :
    HasLaw (fun ω : ULA.CanonicalBrownian.VectorSample ι =>
      fun p : (n : ℕ) × ι => vectorGridBlock ι kernels hc h p.1 ω p.2)
      (Measure.infinitePi (fun _ : (n : ℕ) × ι => kernelGaussian kernels h))
      (ULA.CanonicalBrownian.vectorProbability ι) := by
  apply (vectorGridBlock_array_independent ι kernels hc h).hasLaw_infinitePi
  · intro p
    exact (gridConvolutionLp_jointLaw kernels hc h p.1).comp
      (⟨(measurable_pi_apply p.2).aemeasurable, Measure.infinitePi_map_eval (fun _ : ι => probability) p.2⟩ :
        HasLaw (fun ω : ULA.CanonicalBrownian.VectorSample ι => ω p.2) probability
          (ULA.CanonicalBrownian.vectorProbability ι))
  · apply Measurable.aemeasurable
    apply measurable_pi_iff.mpr
    intro p
    exact (measurable_scalarGridBlock kernels hc h p.1).comp (measurable_pi_apply p.2)

/-- Regrouping spatial blocks gives an independent stream of full vector blocks. -/
theorem vectorGridBlock_path_law (ι : Type*) (kernels : κ → ℝ → ℝ)
    (hc : ∀ j, Continuous (kernels j)) (h : ℝ≥0) :
    HasLaw (fun ω : ULA.CanonicalBrownian.VectorSample ι =>
      fun n i => vectorGridBlock ι kernels hc h n ω i)
      (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ι => kernelGaussian kernels h)))
      (ULA.CanonicalBrownian.vectorProbability ι) := by
  have hcurry : HasLaw (MeasurableEquiv.piCurry (fun (_ : ℕ) (_ : ι) => EuclideanSpace ℝ κ))
      (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ι => kernelGaussian kernels h)))
      (Measure.infinitePi (fun _ : (n : ℕ) × ι => kernelGaussian kernels h)) :=
    ⟨(MeasurableEquiv.piCurry _).measurable.aemeasurable, Measure.infinitePi_map_piCurry (fun (_ : ℕ) (_ : ι) => kernelGaussian kernels h)⟩
  exact hcurry.comp (vectorGridBlock_array_law ι kernels hc h)

/-- Full vector innovation blocks on distinct iterations are independent. -/
theorem vectorGridBlock_time_independent (ι : Type*) (kernels : κ → ℝ → ℝ)
    (hc : ∀ j, Continuous (kernels j)) (h : ℝ≥0) :
    iIndepFun (fun n => vectorGridBlock ι kernels hc h n)
      (ULA.CanonicalBrownian.vectorProbability ι) := by
  exact iIndepFun_comp_hasLaw (fun n ω => ω n) (fun n => measurable_pi_apply n)
    (fun ω n i => vectorGridBlock ι kernels hc h n ω i)
    (measurable_pi_iff.mpr (measurable_vectorGridBlock ι kernels hc h))
    (vectorGridBlock_path_law ι kernels hc h)
    (iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id))

/-- On finite spatial coordinates, the canonical Brownian array has exactly the existing Gaussian stream law. -/
theorem vectorGridBlock_kernelNoisePath_law (d : ℕ) (kernels : κ → ℝ → ℝ)
    (hc : ∀ j, Continuous (kernels j)) (h : ℝ≥0) :
    HasLaw (fun ω : ULA.CanonicalBrownian.VectorSample (Fin d) =>
      fun p : ℕ × Fin d => vectorGridBlock (Fin d) kernels hc h p.1 ω p.2)
      (kernelNoisePath d kernels h) (ULA.CanonicalBrownian.vectorProbability (Fin d)) := by
  have hs := (vectorGridBlock_array_independent (Fin d) kernels hc h).precomp
    (g := fun p : ℕ × Fin d => (⟨p.1,p.2⟩ : (n : ℕ) × Fin d))
    (by intro p q hp; cases p; cases q; simp_all)
  apply hs.hasLaw_infinitePi
  · intro p
    exact (gridConvolutionLp_jointLaw kernels hc h p.1).comp
      (⟨(measurable_pi_apply p.2).aemeasurable, Measure.infinitePi_map_eval (fun _ : Fin d => probability) p.2⟩ :
        HasLaw (fun ω : ULA.CanonicalBrownian.VectorSample (Fin d) => ω p.2) probability
          (ULA.CanonicalBrownian.vectorProbability (Fin d)))
  · apply Measurable.aemeasurable
    apply measurable_pi_iff.mpr
    intro p
    exact (measurable_scalarGridBlock kernels hc h p.1).comp (measurable_pi_apply p.2)

/-- Pack each pair of correlated scalar responses into velocity and position vectors. -/
def canonicalKLMCInnovation (d : ℕ) (γ : ℝ) (h : ℝ≥0) (n : ℕ)
    (ω : ULA.CanonicalBrownian.VectorSample (Fin d)) :
    PhaseSpace (EuclideanSpace ℝ (Fin d)) :=
  (WithLp.toLp 2 (fun i => gridConvolutionLp (klmcKernels γ) (continuous_klmcKernels γ) h n 0 (ω i)),
   WithLp.toLp 2 (fun i => gridConvolutionLp (klmcKernels γ) (continuous_klmcKernels γ) h n 1 (ω i)))

/-- The canonical phase innovation is a measurable function of its Brownian source. -/
theorem measurable_canonicalKLMCInnovation (d : ℕ) (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    Measurable (canonicalKLMCInnovation d γ h n) := by
  have hm : Measurable (fun x : Fin d → EuclideanSpace ℝ (Fin 2) =>
      (WithLp.toLp 2 (fun i => x i 0),WithLp.toLp 2 (fun i => x i 1))) := by fun_prop
  exact hm.comp (measurable_vectorGridBlock (Fin d) (klmcKernels γ) (continuous_klmcKernels γ) h n)

/-- The implemented canonical innovation has exactly the law of the paper's Gaussian innovation. -/
theorem canonicalKLMCInnovation_law (d : ℕ) (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    HasLaw (canonicalKLMCInnovation d γ h n)
      ((kernelNoisePath d (klmcKernels γ) h).map (klmcInnovation d n))
      (ULA.CanonicalBrownian.vectorProbability (Fin d)) := by
  have hp : HasLaw (klmcInnovation d n)
      ((kernelNoisePath d (klmcKernels γ) h).map (klmcInnovation d n))
      (kernelNoisePath d (klmcKernels γ) h) := ⟨(measurable_klmcInnovation d n).aemeasurable,rfl⟩
  exact hp.comp (vectorGridBlock_kernelNoisePath_law d (klmcKernels γ) (continuous_klmcKernels γ) h)

/-- Full canonical KLMC innovations are independent across iterations. -/
theorem canonicalKLMCInnovation_independent (d : ℕ) (γ : ℝ) (h : ℝ≥0) :
    iIndepFun (canonicalKLMCInnovation d γ h) (ULA.CanonicalBrownian.vectorProbability (Fin d)) := by
  exact (vectorGridBlock_time_independent (Fin d) (klmcKernels γ) (continuous_klmcKernels γ) h).comp
    (fun _ x => (WithLp.toLp 2 (fun i => x i 0),WithLp.toLp 2 (fun i => x i 1))) (by intros; fun_prop)

/-- Each phase component is square integrable on the actual vector Brownian source. -/
theorem canonicalKLMCInnovation_memLp (d : ℕ) (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    MemLp (fun ω => (canonicalKLMCInnovation d γ h n ω).1) 2
      (ULA.CanonicalBrownian.vectorProbability (Fin d)) ∧
    MemLp (fun ω => (canonicalKLMCInnovation d γ h n ω).2) 2
      (ULA.CanonicalBrownian.vectorProbability (Fin d)) := by
  constructor
  all_goals apply MemLp.of_eval_piLp
  all_goals intro i
  all_goals exact (Lp.memLp _).comp_measurePreserving (measurePreserving_eval_infinitePi _ i)


/-- Add an independent standard Gaussian initial velocity to the constructed vector Brownian source. -/
def canonicalSourceProbability (d : ℕ) :
    Measure (EuclideanSpace ℝ (Fin d) × ULA.CanonicalBrownian.VectorSample (Fin d)) :=
  (stdGaussian (EuclideanSpace ℝ (Fin d))).prod (ULA.CanonicalBrownian.vectorProbability (Fin d))

instance canonicalSourceProbability_isProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (canonicalSourceProbability d) := by
  unfold canonicalSourceProbability
  infer_instance

/-- The initial velocity has the actual standard Gaussian law on the enlarged source. -/
theorem canonicalSourceVelocity_law (d : ℕ) : HasLaw Prod.fst
    (stdGaussian (EuclideanSpace ℝ (Fin d))) (canonicalSourceProbability d) :=
  measurePreserving_fst.hasLaw

/-- The initial velocity is square integrable on the source. -/
theorem canonicalSourceVelocity_memLp (d : ℕ) :
    MemLp (Prod.fst : EuclideanSpace ℝ (Fin d) × ULA.CanonicalBrownian.VectorSample (Fin d) →
      EuclideanSpace ℝ (Fin d)) 2 (canonicalSourceProbability d) :=
  IsGaussian.memLp_two_id.comp_measurePreserving measurePreserving_fst

/-- Enlarging by initial velocity preserves the exact innovation law. -/
theorem canonicalSourceInnovation_law (d : ℕ) (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    HasLaw (fun p : EuclideanSpace ℝ (Fin d) × ULA.CanonicalBrownian.VectorSample (Fin d) =>
      canonicalKLMCInnovation d γ h n p.2)
      ((kernelNoisePath d (klmcKernels γ) h).map (klmcInnovation d n))
      (canonicalSourceProbability d) :=
  (canonicalKLMCInnovation_law d γ h n).comp measurePreserving_snd.hasLaw

/-- Initial velocity is independent of the entire future innovation stream. -/
theorem canonicalSourceVelocity_innovations_independent (d : ℕ) (γ : ℝ) (h : ℝ≥0) :
    IndepFun (Prod.fst : EuclideanSpace ℝ (Fin d) × ULA.CanonicalBrownian.VectorSample (Fin d) → _)
      (fun p => fun n => canonicalKLMCInnovation d γ h n p.2) (canonicalSourceProbability d) := by
  change IndepFun (fun p => id p.1)
    (fun p => (fun ω n => canonicalKLMCInnovation d γ h n ω) p.2)
    ((stdGaussian (EuclideanSpace ℝ (Fin d))).prod (ULA.CanonicalBrownian.vectorProbability (Fin d)))
  refine indepFun_prod (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))
    (ν := ULA.CanonicalBrownian.vectorProbability (Fin d)) (X := id)
    (Y := fun ω n => canonicalKLMCInnovation d γ h n ω) measurable_id ?_
  apply measurable_pi_iff.mpr
  intro n
  unfold canonicalKLMCInnovation
  apply Measurable.prodMk
  all_goals apply (WithLp.measurable_toLp 2 _).comp
  all_goals apply measurable_pi_iff.mpr
  all_goals intro i
  all_goals exact (Lp.stronglyMeasurable _).measurable.comp (measurable_pi_apply i)

/-- Time-step independence is preserved after adjoining the initial velocity. -/
theorem canonicalSourceInnovation_independent (d : ℕ) (γ : ℝ) (h : ℝ≥0) :
    iIndepFun (fun n p => canonicalKLMCInnovation d γ h n
      (p : EuclideanSpace ℝ (Fin d) × ULA.CanonicalBrownian.VectorSample (Fin d)).2)
      (canonicalSourceProbability d) :=
  iIndepFun_comp_hasLaw (canonicalKLMCInnovation d γ h)
    (measurable_canonicalKLMCInnovation d γ h) Prod.snd measurable_snd
    measurePreserving_snd.hasLaw (canonicalKLMCInnovation_independent d γ h)

/-- Both phase components remain square integrable after adjoining initial velocity. -/
theorem canonicalSourceInnovation_memLp (d : ℕ) (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    MemLp (fun p : EuclideanSpace ℝ (Fin d) × ULA.CanonicalBrownian.VectorSample (Fin d) =>
      (canonicalKLMCInnovation d γ h n p.2).1) 2 (canonicalSourceProbability d) ∧
    MemLp (fun p : EuclideanSpace ℝ (Fin d) × ULA.CanonicalBrownian.VectorSample (Fin d) =>
      (canonicalKLMCInnovation d γ h n p.2).2) 2 (canonicalSourceProbability d) :=
  ⟨(canonicalKLMCInnovation_memLp d γ h n).1.comp_measurePreserving measurePreserving_snd,
    (canonicalKLMCInnovation_memLp d γ h n).2.comp_measurePreserving measurePreserving_snd⟩

end KineticLangevin.BrownianConvolution
