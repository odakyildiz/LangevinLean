import KineticLangevin.ContinuousGibbs
import KineticLangevin.TransportMap

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace KineticLangevin
variable {E V : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V]

/-- Adjoining the same independent velocity distribution leaves the exact position transport distance unchanged. -/
theorem wasserstein2_common_velocity_product (ρ : Measure V) (μ ν : Measure E)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ULA.wasserstein2 (ρ.prod μ) (ρ.prod ν)=ULA.wasserstein2 μ ν := by
  apply le_antisymm
  · have hb := wasserstein2_randomMap_lipschitz (fun p : E×V => (p.2,p.1)) measurable_swap 1
      (fun x y v => by simp only [Prod.mk_sub_mk,sub_self,Prod.norm_def,norm_zero,max_eq_right,norm_nonneg,NNReal.coe_one,one_mul];exact le_rfl)
      μ ν ρ
    change ULA.wasserstein2 ((μ.prod ρ).map Prod.swap) ((ν.prod ρ).map Prod.swap) ≤ _ at hb
    simpa only [Measure.prod_swap,ENNReal.coe_one,one_mul] using hb
  · have hb := wasserstein2_map_lipschitz (Prod.snd : V×E → E) measurable_snd 1
      (fun x y => by simpa only [NNReal.coe_one,one_mul,Prod.snd_sub] using norm_snd_le (x-y)) (ρ.prod μ) (ρ.prod ν)
    simpa only [Measure.map_snd_prod,measure_univ,one_smul,ENNReal.coe_one,one_mul] using hb

/-- The real-valued distance has the same exact common-velocity product identity. -/
theorem wasserstein2Real_common_velocity_product (ρ : Measure V) (μ ν : Measure E)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ULA.wasserstein2Real (ρ.prod μ) (ρ.prod ν)=ULA.wasserstein2Real μ ν :=
  congrArg ENNReal.toReal (wasserstein2_common_velocity_product ρ μ ν)

namespace CanonicalContinuous
variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- Theorem 1, equation exp2, with its literal full initial phase-product Wasserstein distance. -/
theorem theorem1_exp2 (ρ : Measure (H ι)) [IsProbabilityMeasure ρ]
    (hρ : MemLp (id : H ι → H ι) 2 ρ)
    (μ ν : Measure (H ι)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp (id : H ι → H ι) 2 μ) (hν : MemLp (id : H ι → H ι) 2 ν)
    (f : H ι → ℝ) (m a : ℝ) (M γ : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith M (gradient f))
    (hmM : m ≤ (M : ℝ)) (ha : 0 ≤ a) (haγ : a < (γ : ℝ)/2) (T : ℝ) (hT : 0 ≤ T) :
    ULA.wasserstein2Real (positionLaw ι ρ hρ μ hμ f M γ hLip T hT)
      (positionLaw ι ρ hρ ν hν f M γ hLip T hT) ≤
      Real.sqrt (2*(((γ : ℝ)-a)^2+a^2))/((γ : ℝ)-2*a) *
        Real.exp (max (a^2-m) ((M : ℝ)-((γ : ℝ)-a)^2)/((γ : ℝ)-2*a)*T) *
          ULA.wasserstein2Real (ρ.prod μ) (ρ.prod ν) := by
  rw [wasserstein2Real_common_velocity_product]
  exact wasserstein2_general ι ρ hρ μ ν hμ hν f m a M γ hf hsc hLip hmM (by linarith) T hT

/-- The friction-regime source corollary with the literal initial Gaussian-times-position phase distance. -/
theorem gibbs_mixing_phase_initial (μ : Measure (H ι)) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : H ι → H ι) 2 μ) (f : H ι → ℝ) (m : ℝ) (M γ : ℝ≥0)
    (hm : 0 < m) (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ)) (hγ : 0 < (γ : ℝ))
    (hfriction : m+(M : ℝ) ≤ (γ : ℝ)^2) (T : ℝ) (hT : 0 ≤ T) :
    ULA.wasserstein2Real (positionLaw ι (stdGaussian (H ι)) IsGaussian.memLp_two_id μ hμ f M γ hLip T hT)
      (ULA.gibbsMeasure f) ≤ Real.sqrt 2 * Real.exp ((-m/(γ : ℝ))*T) *
        ULA.wasserstein2Real ((stdGaussian (H ι)).prod μ) (kineticGibbsTarget f) := by
  letI := ULA.isProbabilityMeasure_gibbsMeasure f m hm hf hsc
  change _ ≤ _*ULA.wasserstein2Real ((stdGaussian (H ι)).prod μ)
    ((stdGaussian (H ι)).prod (ULA.gibbsMeasure f))
  rw [wasserstein2Real_common_velocity_product]
  exact wasserstein2_gibbs ι μ hμ f m M γ hm hf hsc hLip hmM hγ hfriction T hT

end CanonicalContinuous
end KineticLangevin
