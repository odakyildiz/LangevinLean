import KineticLangevin.ProductContinuousFlow
import KineticLangevin.CanonicalSplitting

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace KineticLangevin.CanonicalContinuous
variable (ι : Type*) [Fintype ι] [DecidableEq ι]
abbrev H := EuclideanSpace ℝ ι
abbrev Sample := H ι × ULA.CanonicalBrownian.VectorSample ι

/-- The arbitrary common initial velocity distribution is independent of the actual vector Brownian source. -/
def probability (ρ : Measure (H ι)) : Measure (Sample ι) :=
  ρ.prod (ULA.CanonicalBrownian.vectorProbability ι)
instance probability_isProbabilityMeasure (ρ : Measure (H ι)) [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (probability ι ρ) := by unfold probability;infer_instance

/-- The common initial velocity is the actual first projection of the independent source. -/
def velocity (ρ : Measure (H ι)) [IsProbabilityMeasure ρ] (hρ : MemLp (id : H ι → H ι) 2 ρ) :
    Lp (H ι) 2 (probability ι ρ) :=
  (hρ.comp_measurePreserving measurePreserving_fst).toLp Prod.fst

/-- The genuine canonical Brownian forcing, with its kinetic fluctuation-dissipation amplitude. -/
def input (ρ : Measure (H ι)) [IsProbabilityMeasure ρ] (γ t : ℝ) : Lp (H ι) 2 (probability ι ρ) :=
  sourcePullback (Prod.snd : Sample ι → ULA.CanonicalBrownian.VectorSample ι)
    (measurePreserving_snd : MeasurePreserving Prod.snd (probability ι ρ)
      (ULA.CanonicalBrownian.vectorProbability ι))
    (Real.sqrt (2*γ) • BrownianConvolution.canonicalVectorInput ι t)

theorem continuous_input (ρ : Measure (H ι)) [IsProbabilityMeasure ρ] (γ : ℝ) :
    Continuous (input ι ρ γ) :=
  (sourcePullback (H := H ι) (Prod.snd : Sample ι → ULA.CanonicalBrownian.VectorSample ι)
    (measurePreserving_snd : MeasurePreserving Prod.snd (probability ι ρ)
      (ULA.CanonicalBrownian.vectorProbability ι))).continuous.comp
        ((BrownianConvolution.continuous_canonicalVectorInput ι).const_smul (Real.sqrt (2*γ)))

@[simp] theorem input_zero (ρ : Measure (H ι)) [IsProbabilityMeasure ρ] (γ : ℝ) : input ι ρ γ 0=0 := by
  simp only [input,BrownianConvolution.canonicalVectorInput_zero,smul_zero,map_zero]
  rfl

/-- The position law of the actual selected Brownian-driven kinetic solution, with arbitrary common velocity law. -/
def positionLaw (ρ : Measure (H ι)) [IsProbabilityMeasure ρ] (hρ : MemLp (id : H ι → H ι) 2 ρ)
    (μ : Measure (H ι)) [IsProbabilityMeasure μ] (hμ : MemLp (id : H ι → H ι) 2 μ)
    (f : H ι → ℝ) (M γ : ℝ≥0) (hLip : LipschitzWith M (gradient f)) (T : ℝ) (hT : 0 ≤ T) : Measure (H ι) :=
  ProductContinuous.positionLaw (probability ι ρ) μ hμ (velocity ι ρ hρ)
    (input ι ρ γ) (continuous_input ι ρ γ) (gradient f) M γ hLip T hT

/-- Theorem 1's explicit arbitrary-shift mixing estimate for actual canonical Brownian kinetic laws.
The common initial velocity distribution is arbitrary with finite second moment. -/
theorem wasserstein2_general (ρ : Measure (H ι)) [IsProbabilityMeasure ρ]
    (hρ : MemLp (id : H ι → H ι) 2 ρ)
    (μ ν : Measure (H ι)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp (id : H ι → H ι) 2 μ) (hν : MemLp (id : H ι → H ι) 2 ν)
    (f : H ι → ℝ) (m a : ℝ) (M γ : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith M (gradient f))
    (hmM : m ≤ (M : ℝ)) (hd : 0 < (γ : ℝ)-2*a) (T : ℝ) (hT : 0 ≤ T) :
    ULA.wasserstein2Real (positionLaw ι ρ hρ μ hμ f M γ hLip T hT)
      (positionLaw ι ρ hρ ν hν f M γ hLip T hT) ≤
      (Real.sqrt (2*(((γ : ℝ)-a)^2+a^2))/((γ : ℝ)-2*a) *
        Real.exp (max (a^2-m) ((M : ℝ)-((γ : ℝ)-a)^2)/((γ : ℝ)-2*a)*T)) * ULA.wasserstein2Real μ ν :=
  ProductContinuous.positionLaw_wasserstein2_general (probability ι ρ) hμ hν (velocity ι ρ hρ)
    (input ι ρ γ) (continuous_input ι ρ γ) (input_zero ι ρ γ) f m a M γ hf hsc hLip hmM hd T hT

end KineticLangevin.CanonicalContinuous
