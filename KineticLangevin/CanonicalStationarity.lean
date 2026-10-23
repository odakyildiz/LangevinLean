import KineticLangevin.StationarityTransfer
import KineticLangevin.CanonicalProduct
import KineticLangevin.CoupledSegments

/-! # A constructed stationary kinetic Langevin flow on its actual source

The potential assumptions construct both the initial random phase and an
independent Brownian source. Picard gives the actual continuous solution.
Its Gibbs law at every time is then proved by the concrete splitting limit.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace KineticLangevin

section Moments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual target velocity projection is square integrable. -/
theorem kineticGibbsTarget_velocity_memLp (f : E → ℝ) (m : ℝ) (hm : 0<m)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) :
    MemLp (Prod.fst : E×E → E) 2 (kineticGibbsTarget f) := by
  haveI := ULA.isProbabilityMeasure_gibbsMeasure f m hm hf hsc
  change MemLp (Prod.fst : E×E → E) 2 ((stdGaussian E).prod (ULA.gibbsMeasure f))
  exact (show MemLp (id : E → E) 2 (stdGaussian E) from IsGaussian.memLp_two_id).comp_measurePreserving
    measurePreserving_fst

/-- The actual target position projection is square integrable by strong convexity. -/
theorem kineticGibbsTarget_position_memLp (f : E → ℝ) (m : ℝ) (hm : 0<m)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) :
    MemLp (Prod.snd : E×E → E) 2 (kineticGibbsTarget f) := by
  haveI := ULA.isProbabilityMeasure_gibbsMeasure f m hm hf hsc
  change MemLp (Prod.snd : E×E → E) 2 ((stdGaussian E).prod (ULA.gibbsMeasure f))
  exact (ULA.memLp_id_gibbsMeasure f m hm hf hsc).comp_measurePreserving measurePreserving_snd
end Moments

variable {d : ℕ}
abbrev CanonicalGibbsSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The actual normalized initial phase law times an independent canonical Brownian source. -/
abbrev canonicalGibbsProbability (f : CanonicalGibbsSpace d → ℝ) :=
  CanonicalProduct.probability (kineticGibbsTarget f)

/-- The actual square-integrable initial phase on that product source. -/
def canonicalGibbsInitial (f : CanonicalGibbsSpace d → ℝ) (m : ℝ) (hm : 0<m)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) :
    Lp (CanonicalGibbsSpace d) 2 (canonicalGibbsProbability f) ×
      Lp (CanonicalGibbsSpace d) 2 (canonicalGibbsProbability f) := by
  haveI := kineticGibbsTarget_probability f m hm hf hsc
  exact CanonicalProduct.initial (kineticGibbsTarget f)
    (kineticGibbsTarget_velocity_memLp f m hm hf hsc) (kineticGibbsTarget_position_memLp f m hm hf hsc)

/-- The actual independently pulled-back Brownian input with fluctuation-dissipation scaling. -/
def canonicalGibbsInput (f : CanonicalGibbsSpace d → ℝ) (m : ℝ) (hm : 0<m)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (γ : ℝ) :
    ℝ → Lp (CanonicalGibbsSpace d) 2 (canonicalGibbsProbability f) := by
  haveI := kineticGibbsTarget_probability f m hm hf hsc
  exact CanonicalProduct.input (kineticGibbsTarget f) γ

theorem continuous_canonicalGibbsInput (f : CanonicalGibbsSpace d → ℝ) (m : ℝ) (hm : 0<m)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (γ : ℝ) :
    Continuous (canonicalGibbsInput f m hm hf hsc γ) := by
  haveI := kineticGibbsTarget_probability f m hm hf hsc
  exact CanonicalProduct.continuous_input (kineticGibbsTarget f) γ

@[simp] theorem canonicalGibbsInput_zero (f : CanonicalGibbsSpace d → ℝ) (m : ℝ) (hm : 0<m)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (γ : ℝ) :
    canonicalGibbsInput f m hm hf hsc γ 0=0 := by
  haveI := kineticGibbsTarget_probability f m hm hf hsc
  exact CanonicalProduct.input_zero (kineticGibbsTarget f) γ

/-- The actual potential gradient lifted to the constructed probability source. -/
def canonicalGibbsDrift (f : CanonicalGibbsSpace d → ℝ) (m : ℝ) (hm : 0<m) (M : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) :
    Lp (CanonicalGibbsSpace d) 2 (canonicalGibbsProbability f) →
      Lp (CanonicalGibbsSpace d) 2 (canonicalGibbsProbability f) := by
  haveI := kineticGibbsTarget_probability f m hm hf hsc
  exact ULA.lpDrift (canonicalGibbsProbability f) (gradient f) hLip

/-- The actual selected kinetic integral flow on the independent Gibbs/Brownian product. -/
def canonicalGibbsFlow (f : CanonicalGibbsSpace d → ℝ) (m : ℝ) (hm : 0<m) (M γ : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (T : ℝ) (hT : 0≤T) :
    ℝ → Lp (CanonicalGibbsSpace d) 2 (canonicalGibbsProbability f) ×
      Lp (CanonicalGibbsSpace d) 2 (canonicalGibbsProbability f) := by
  haveI := kineticGibbsTarget_probability f m hm hf hsc
  exact kineticSegmentFlow (ULA.lpDrift (canonicalGibbsProbability f) (gradient f) hLip) M γ 1
    (ULA.lpDrift_lipschitz (canonicalGibbsProbability f) (gradient f) hLip) T hT
    (canonicalGibbsInitial f m hm hf hsc) (canonicalGibbsInput f m hm hf hsc γ)
    (continuous_canonicalGibbsInput f m hm hf hsc γ)

/-- Picard construction gives the actual continuous kinetic equation and initial state. -/
theorem canonicalGibbsFlow_spec (f : CanonicalGibbsSpace d → ℝ) (m : ℝ) (hm : 0<m) (M γ : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (T : ℝ) (hT : 0≤T) :
    Continuous (canonicalGibbsFlow f m hm M γ hf hsc hLip T hT) ∧
    canonicalGibbsFlow f m hm M γ hf hsc hLip T hT 0=canonicalGibbsInitial f m hm hf hsc ∧
    ∀ t ∈ Icc 0 T,
      canonicalGibbsFlow f m hm M γ hf hsc hLip T hT t-canonicalGibbsInitial f m hm hf hsc =
        -(∫ s in 0..t, kineticNegativeDrift
          (canonicalGibbsDrift f m hm M hf hsc hLip) γ 1
          (canonicalGibbsFlow f m hm M γ hf hsc hLip T hT s))+
        (canonicalGibbsInput f m hm hf hsc γ t,0) := by
  haveI := kineticGibbsTarget_probability f m hm hf hsc
  exact kineticSegmentFlow_spec _ M γ 1
    (ULA.lpDrift_lipschitz (canonicalGibbsProbability f) (gradient f) hLip) T hT
    (canonicalGibbsInitial f m hm hf hsc) (canonicalGibbsInput f m hm hf hsc γ)
    (continuous_canonicalGibbsInput f m hm hf hsc γ) (canonicalGibbsInput_zero f m hm hf hsc γ)

/-- Every time marginal of the actual constructed kinetic Langevin flow
has exactly the independent Gaussian-times-Gibbs target law. -/
theorem canonicalGibbsFlow_stationary (f : CanonicalGibbsSpace d → ℝ) (m : ℝ) (hm : 0<m) (M γ : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (T : ℝ) (hT : 0≤T) (t : ℝ) (ht : t∈Icc 0 T) :
    (canonicalGibbsProbability f).map (lpPhaseCoe (canonicalGibbsProbability f)
      (canonicalGibbsFlow f m hm M γ hf hsc hLip T hT t))=kineticGibbsTarget f := by
  haveI := kineticGibbsTarget_probability f m hm hf hsc
  have hs := canonicalGibbsFlow_spec f m hm M γ hf hsc hLip T hT
  have hjoint (h : ℝ≥0) : HasLaw
      (fun ω ↦ (lpPhaseCoe (canonicalGibbsProbability f) (canonicalGibbsInitial f m hm hf hsc) ω,
        fun k : ℕ ↦ ouInputIncrement γ (canonicalGibbsInput f m hm hf hsc γ) ((k : ℝ)*h) h ω))
      ((kineticGibbsTarget f).prod (Measure.infinitePi (fun _ : ℕ ↦ ouThermalLaw (E := CanonicalGibbsSpace d) γ h)))
      (canonicalGibbsProbability f) := by
    have hj := CanonicalProduct.initial_innovation_jointLaw (kineticGibbsTarget f)
      (kineticGibbsTarget_velocity_memLp f m hm hf hsc) (kineticGibbsTarget_position_memLp f m hm hf hsc)
      γ γ.coe_nonneg h
    simpa only [canonicalGibbsInitial,canonicalGibbsInput,ouThermalLaw,
      CanonicalProduct.ouInputIncrement_input _ γ γ.coe_nonneg h] using hj
  apply kinetic_integral_stationary_of_jointNoise (canonicalGibbsProbability f) f m hm M γ hf hsc hLip
    (canonicalGibbsInitial f m hm hf hsc) (canonicalGibbsInput f m hm hf hsc γ)
    (continuous_canonicalGibbsInput f m hm hf hsc γ) (canonicalGibbsInput_zero f m hm hf hsc γ)
    hjoint (canonicalGibbsFlow f m hm M γ hf hsc hLip T hT) hs.1 ⟨t,ht.1⟩
  intro r hr
  exact hs.2.2 r ⟨hr.1,hr.2.trans ht.2⟩

end KineticLangevin
