import KineticLangevin.SplittingLaw
import KineticLangevin.CanonicalSplitting
import KineticLangevin.OUMarginal

/-! # The actual independent initial-law/Brownian source for kinetic stationarity -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace KineticLangevin.CanonicalProduct
open BrownianConvolution
abbrev H (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Sample (d : ℕ) := (H d×H d)×ULA.CanonicalBrownian.VectorSample (Fin d)
variable {d : ℕ} (π : Measure (H d×H d)) [IsProbabilityMeasure π]

/-- The initial phase is independent of the actual canonical Brownian source. -/
abbrev probability := π.prod (ULA.CanonicalBrownian.vectorProbability (Fin d))

/-- The genuine initial phase, represented in the L² product source. -/
def initial (hv : MemLp (Prod.fst : H d×H d → H d) 2 π)
    (hx : MemLp (Prod.snd : H d×H d → H d) 2 π) :
    Lp (H d) 2 (probability π) × Lp (H d) 2 (probability π) :=
  ((hv.comp_measurePreserving measurePreserving_fst).toLp (fun p : Sample d ↦ p.1.1),
   (hx.comp_measurePreserving measurePreserving_fst).toLp (fun p : Sample d ↦ p.1.2))

/-- Its representatives are exactly the original first phase coordinate. -/
theorem initial_coe (hv : MemLp (Prod.fst : H d×H d → H d) 2 π)
    (hx : MemLp (Prod.snd : H d×H d → H d) 2 π) :
    lpPhaseCoe (probability π) (initial π hv hx) =ᵐ[probability π] Prod.fst := by
  filter_upwards [(hv.comp_measurePreserving measurePreserving_fst).coeFn_toLp,
    (hx.comp_measurePreserving measurePreserving_fst).coeFn_toLp] with p hv hx
  exact Prod.ext hv hx

/-- The actual source projection, as a continuous linear L² pullback. -/
def brownianLift :
    Lp (H d) 2 (ULA.CanonicalBrownian.vectorProbability (Fin d)) →L[ℝ]
      Lp (H d) 2 (probability π) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (Prod.snd : Sample d → _)
    (measurePreserving_snd : MeasurePreserving Prod.snd (probability π)
      (ULA.CanonicalBrownian.vectorProbability (Fin d)))).toContinuousLinearMap

/-- The actual continuous Brownian forcing includes the fluctuation-dissipation factor. -/
def input (γ t : ℝ) : Lp (H d) 2 (probability π) :=
  brownianLift π (Real.sqrt (2*γ) • canonicalVectorInput (Fin d) t)

theorem continuous_input (γ : ℝ) : Continuous (input π γ) :=
  (brownianLift π).continuous.comp ((continuous_canonicalVectorInput (Fin d)).const_smul (Real.sqrt (2*γ)))

@[simp] theorem input_zero (γ : ℝ) : input π γ 0=0 := by simp [input]

/-- The actual filtered Brownian innovation in interval number n. -/
def innovation (γ : ℝ) (h : ℝ≥0) (n : ℕ) : Lp (H d) 2 (probability π) :=
  brownianLift π (Real.sqrt (2*γ) • vectorSegmentLp (Fin d) (psi γ 0)
    (continuous_psi γ 0) ((n : ℝ≥0)*h) h)

/-- The true source lift does not change the representative's random value. -/
theorem innovation_coe (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    innovation π γ h n =ᵐ[probability π] fun p : Sample d ↦
      (Real.sqrt (2*γ) • vectorSegmentLp (Fin d) (psi γ 0)
        (continuous_psi γ 0) ((n : ℝ≥0)*h) h) p.2 :=
  Lp.coeFn_compMeasurePreserving _ measurePreserving_snd

/-- Exact filtered input agrees with the same canonical innovation. -/
theorem ouInputIncrement_input (γ : ℝ) (hγ : 0≤γ) (h : ℝ≥0) (n : ℕ) :
    ouInputIncrement γ (input π γ) ((n : ℝ)*h) h = innovation π γ h n := by
  unfold input
  have hc : Continuous (fun t : ℝ ↦ Real.sqrt (2*γ) • canonicalVectorInput (Fin d) t) :=
    (continuous_canonicalVectorInput (Fin d)).const_smul (Real.sqrt (2*γ))
  rw [ouInputIncrement_map (brownianLift π) γ _ hc,
    show (n : ℝ)*(h : ℝ)=(((n : ℝ≥0)*h : ℝ≥0) : ℝ) by rfl,
    canonicalVectorInput_scaled_ouIncrement (Fin d) γ _ hγ]
  rfl

/-- The complete actual initial/noise joint law is the independent product
with the full iid thermal Gaussian stream. -/
theorem initial_innovation_jointLaw (hv : MemLp (Prod.fst : H d×H d → H d) 2 π)
    (hx : MemLp (Prod.snd : H d×H d → H d) 2 π)
    (γ : ℝ) (hγ : 0≤γ) (h : ℝ≥0) :
    HasLaw (fun p ↦ (lpPhaseCoe (probability π) (initial π hv hx) p,
      fun k ↦ innovation π γ h k p))
      (π.prod (Measure.infinitePi (fun _ : ℕ ↦
        (stdGaussian (H d)).map (fun x ↦ Real.sqrt (1-(psi γ 0 h)^2) • x))))
      (probability π) := by
  have hW : Measurable (fun ω (k : ℕ) ↦
      (Real.sqrt (2*γ) • vectorSegmentLp (Fin d) (psi γ 0)
        (continuous_psi γ 0) ((k : ℝ≥0)*h) h) ω) := by
    apply measurable_pi_iff.mpr
    intro k
    exact (Lp.stronglyMeasurable _).measurable
  let η := (stdGaussian (H d)).map (fun x ↦ Real.sqrt (1-(psi γ 0 h)^2) • x)
  letI : IsProbabilityMeasure η := (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  have hj := jointLaw_product_source π (ULA.CanonicalBrownian.vectorProbability (Fin d)) η
    _ hW (vectorOU_grid_hasLaw d γ hγ h)
  apply hj.congr
  have hall := ae_all_iff.mpr (innovation_coe π γ h)
  filter_upwards [initial_coe π hv hx,hall] with p hinit hnoise
  exact Prod.ext hinit (funext hnoise)

/-- The actual L² chain on the independent initial/Brownian product has the
specified Markov law, proved from its actual source rather than assumed. -/
theorem splitNoiseChain_law (hv : MemLp (Prod.fst : H d×H d → H d) 2 π)
    (hx : MemLp (Prod.snd : H d×H d → H d) 2 π)
    (g : H d → H d) (M : ℝ≥0) (hg : LipschitzWith M g)
    (γ : ℝ) (hγ : 0≤γ) (h : ℝ≥0) (n : ℕ) :
    (probability π).map (lpPhaseCoe (probability π)
      (kineticSplitNoiseChain (ULA.lpDrift (probability π) g hg) γ h
        (initial π hv hx) (innovation π γ h) n)) =
      ULA.markovLaws (kineticSplitStep g γ h)
        ((stdGaussian (H d)).map (fun x ↦ Real.sqrt (1-(psi γ 0 h)^2) • x)) π n := by
  let η := (stdGaussian (H d)).map (fun x ↦ Real.sqrt (1-(psi γ 0 h)^2) • x)
  letI : IsProbabilityMeasure η := (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  exact lp_kineticSplitNoiseChain_law_of_jointLaw (probability π) g M hg γ h
    (initial π hv hx) (innovation π γ h) π η (initial_innovation_jointLaw π hv hx γ hγ h) n

/-- The continuous-input splitting itself, using its actual Brownian
filter, has the same independent-noise Markov law. -/
theorem splitChain_law (hv : MemLp (Prod.fst : H d×H d → H d) 2 π)
    (hx : MemLp (Prod.snd : H d×H d → H d) 2 π)
    (g : H d → H d) (M : ℝ≥0) (hg : LipschitzWith M g)
    (γ : ℝ) (hγ : 0≤γ) (h : ℝ≥0) (n : ℕ) :
    (probability π).map (lpPhaseCoe (probability π)
      (kineticSplitChain (ULA.lpDrift (probability π) g hg) γ h
        (initial π hv hx) (input π γ) n)) =
      ULA.markovLaws (kineticSplitStep g γ h)
        ((stdGaussian (H d)).map (fun x ↦ Real.sqrt (1-(psi γ 0 h)^2) • x)) π n := by
  rw [kineticSplitChain_eq_noiseChain]
  have he : (fun k : ℕ ↦ ouInputIncrement γ (input π γ) ((k : ℝ)*h) h) =
      innovation π γ h := funext (ouInputIncrement_input π γ hγ h)
  rw [he]
  exact splitNoiseChain_law π hv hx g M hg γ hγ h n

end KineticLangevin.CanonicalProduct
