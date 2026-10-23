import KineticLangevin.KineticSplittingLp
import KineticLangevin.VectorSegmentEquations

/-! # The concrete splitting uses the actual canonical Brownian increments -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal
namespace KineticLangevin

/-- Filtering a scaled additive input scales the actual OU increment. -/
theorem ouInputIncrement_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (γ c : ℝ) (B : ℝ → E) (a h : ℝ) :
    ouInputIncrement γ (fun t ↦ c • B t) a h = c • ouInputIncrement γ B a h := by
  have hi : (∫ s in 0..h, Real.exp (-γ*(h-s)) • (c • B (a+s)-c • B a)) =
      c • ∫ s in 0..h, Real.exp (-γ*(h-s)) • (B (a+s)-B a) := by
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro s _
    module
  unfold ouInputIncrement
  rw [hi]
  module

/-- The exact OU input construction commutes with continuous linear lifts,
including measure-preserving pullbacks to independent initial-law products. -/
theorem ouInputIncrement_map {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) (γ : ℝ) (B : ℝ → E) (hB : Continuous B) (a h : ℝ) :
    ouInputIncrement γ (fun t ↦ L (B t)) a h = L (ouInputIncrement γ B a h) := by
  have hc : Continuous (fun s ↦ Real.exp (-γ*(h-s)) • (B (a+s)-B a)) := by
    exact (by fun_prop : Continuous (fun s : ℝ ↦ Real.exp (-γ*(h-s)))).smul
      ((hB.comp (continuous_const.add continuous_id)).sub continuous_const)
  have hi := L.intervalIntegral_comp_comm (hc.intervalIntegrable (μ := volume) 0 h)
  unfold ouInputIncrement
  rw [map_sub,map_sub,map_smul]
  congr 1
  congr 1
  rw [← hi]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [map_smul,map_sub]

namespace BrownianConvolution
variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The actual canonical vector Brownian input, extended to real time by
clamping negative times to zero and anchored at its time-zero value. -/
def canonicalVectorInput (t : ℝ) :
    Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) :=
  vectorBrownianIncrementLp ι 0 t.toNNReal

theorem continuous_canonicalVectorInput : Continuous (canonicalVectorInput ι) :=
  (continuous_vectorBrownianIncrementLp ι 0).comp continuous_real_toNNReal

@[simp] theorem canonicalVectorInput_zero : canonicalVectorInput ι 0=0 := by
  simp [canonicalVectorInput,vectorBrownianIncrementLp,segmentBrownianLp]

/-- Increments of the anchored actual input are exactly the already
constructed Brownian segment increments. -/
theorem canonicalVectorInput_increment (a t : ℝ≥0) :
    canonicalVectorInput ι ((a+t : ℝ≥0) : ℝ)-canonicalVectorInput ι (a : ℝ) =
      vectorBrownianIncrementLp ι a t := by
  simp only [canonicalVectorInput,Real.toNNReal_coe,vectorBrownianIncrementLp,
    segmentBrownianLp,zero_add,map_sub]
  module

/-- The actual canonical OU convolution is precisely the filtered input
used by the proved deterministic splitting convergence theorem. -/
theorem canonicalVectorInput_ouIncrement (γ : ℝ) (hγ : 0≤γ) (a t : ℝ≥0) :
    ouInputIncrement γ (canonicalVectorInput ι) a t =
      vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) a t := by
  rw [vectorSegmentLp_velocity_eq_brownian_sub_convolution ι γ hγ]
  unfold ouInputIncrement
  rw [show (a : ℝ)+(t : ℝ)=((a+t : ℝ≥0) : ℝ) by rfl,
    canonicalVectorInput_increment]
  congr 1
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le t.coe_nonneg] at hs
  have he : (a : ℝ)+s=((a+s.toNNReal : ℝ≥0) : ℝ) := by
    simp only [NNReal.coe_add,Real.coe_toNNReal _ hs.1]
  dsimp only
  rw [he,canonicalVectorInput_increment]

/-- The fluctuation-dissipation scaling is retained in the actual input
identity rather than imposed through a matching marginal law. -/
theorem canonicalVectorInput_scaled_ouIncrement (γ c : ℝ) (hγ : 0≤γ) (a t : ℝ≥0) :
    ouInputIncrement γ (fun s ↦ c • canonicalVectorInput ι s) a t =
      c • vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) a t := by
  rw [ouInputIncrement_smul,canonicalVectorInput_ouIncrement ι γ hγ]

/-- On every grid, the entire continuous-input splitting is exactly the
innovation-driven chain on the same constructed Brownian source. -/
theorem canonicalVectorInput_chain (g :
      Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) →
      Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι))
    (γ c : ℝ) (hγ : 0≤γ) (h : ℝ≥0)
    (initial : Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) ×
      Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι)) (n : ℕ) :
    kineticSplitChain g γ h initial (fun s ↦ c • canonicalVectorInput ι s) n =
      kineticSplitNoiseChain g γ h initial
        (fun k ↦ c • vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) ((k : ℝ≥0)*h) h) n := by
  rw [kineticSplitChain_eq_noiseChain]
  congr 1
  funext k
  simpa only [NNReal.coe_mul,NNReal.coe_natCast] using
    canonicalVectorInput_scaled_ouIncrement ι γ c hγ ((k : ℝ≥0)*h) h

/-- The concrete canonical-noise chain converges to every actual continuous
kinetic integral solution on that same L² source. -/
theorem canonicalVectorInput_chain_tendsto (g :
      Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) →
      Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι))
    (M γ : ℝ≥0) (hg : LipschitzWith M g) (c : ℝ)
    (initial : Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) ×
      Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι))
    (Y : ℝ → Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) ×
      Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι))
    (hY : Continuous Y) (T : ℝ≥0)
    (heY : ∀ t ∈ Icc 0 (T : ℝ), Y t-initial =
      -(∫ s in 0..t,kineticNegativeDrift g γ 1 (Y s))+(c • canonicalVectorInput ι t,0)) :
    Tendsto (fun n : ℕ ↦ kineticSplitNoiseChain g γ
      ((T/((n+1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) initial
      (fun k ↦ c • vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0)
        ((k : ℝ≥0)*(T/((n+1 : ℕ) : ℝ≥0))) (T/((n+1 : ℕ) : ℝ≥0))) (n+1))
      atTop (𝓝 (Y T)) := by
  have he := kineticSplitChain_tendsto g M γ hg initial (fun s ↦ c • canonicalVectorInput ι s) Y
    ((continuous_canonicalVectorInput ι).const_smul c) (by simp) hY T T.coe_nonneg heY
  convert he using 1
  funext n
  rw [← canonicalVectorInput_chain ι g γ c γ.coe_nonneg (T/((n+1 : ℕ) : ℝ≥0)) initial (n+1)]
  simp only [NNReal.coe_div,NNReal.coe_natCast]

end BrownianConvolution
end KineticLangevin
