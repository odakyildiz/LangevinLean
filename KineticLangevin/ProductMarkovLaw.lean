import KineticLangevin.ProductLaw
import KineticLangevin.SplittingLaw
import Mathlib.Probability.Distributions.Gaussian.Multivariate

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace KineticLangevin

section Source
variable {H S Z : Type*} [MeasurableSpace H] [MeasurableSpace S] [MeasurableSpace Z]

/-- Reorganizing independent position, velocity and source coordinates gives their actual product law. -/
theorem independentInitialPhase_source_jointLaw
    (ν κ : Measure H) (Q : Measure S) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure κ] [IsProbabilityMeasure Q] :
    HasLaw (fun p : H×(H×S) ↦ ((p.2.1,p.1),p.2.2)) ((κ.prod ν).prod Q) (ν.prod (κ.prod Q)) := by
  have ha : HasLaw (MeasurableEquiv.prodAssoc : ((H×H)×S) ≃ᵐ _).symm
      ((ν.prod κ).prod Q) (ν.prod (κ.prod Q)) :=
    (MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc ν κ Q)).hasLaw
  have hs : HasLaw (Prod.map Prod.swap id : (H×H)×S → _) ((κ.prod ν).prod Q) ((ν.prod κ).prod Q) :=
    ((Measure.measurePreserving_swap (μ:=ν) (ν:=κ)).prod (MeasurePreserving.id Q)).hasLaw
  exact hs.comp ha

/-- Actual independent initialization and an actual iid source stream give the joint phase/stream law. -/
theorem independentInitialPhase_noise_jointLaw
    (ν κ : Measure H) (Q : Measure S) (η : Measure Z) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure κ] [IsProbabilityMeasure Q] [IsProbabilityMeasure η]
    (W : S→ℕ→Z) (hW : Measurable W)
    (hlaw : HasLaw W (Measure.infinitePi (fun _ : ℕ ↦ η)) Q) :
    HasLaw (fun p : H×(H×S) ↦ ((p.2.1,p.1),W p.2.2))
      ((κ.prod ν).prod (Measure.infinitePi (fun _ : ℕ ↦ η))) (ν.prod (κ.prod Q)) :=
  (jointLaw_product_source (κ.prod ν) Q η W hW hlaw).comp
    (independentInitialPhase_source_jointLaw ν κ Q)
end Source

variable {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace S]

/-- The shared exponential-integrator recursion is the ordinary noise-driven Markov recursion. -/
theorem klmcChain_eq_noiseDrivenChain (g : E→E) (γ h : ℝ) (z : E×E) (W : ℕ→E×E) (n : ℕ) :
    klmcChain g γ h z W n=ULA.noiseDrivenChain (klmcStep g γ h) z W n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [klmcChain_succ,ULA.noiseDrivenChain_succ,ih]

/-- The actual product-source exponential sampler has precisely the independently driven Markov position law. -/
theorem productKLMCLaw_eq_markovLaws
    (Q : Measure S) [IsProbabilityMeasure Q]
    (κ ν : Measure E) [IsProbabilityMeasure κ] [IsProbabilityMeasure ν]
    (f : E→ℝ) (M : ℝ≥0) (hLip : LipschitzWith M (gradient f)) (γ h : ℝ)
    (η : Measure (E×E)) [IsProbabilityMeasure η]
    (W : S→ℕ→E×E) (hW : Measurable W)
    (hlaw : HasLaw W (Measure.infinitePi (fun _ : ℕ ↦ η)) Q) (n : ℕ) :
    productKLMCLaw (κ.prod Q) f γ h ν Prod.fst (fun k p ↦ W p.2 k) n =
      (ULA.markovLaws (klmcStep (gradient f) γ h) η (κ.prod ν) n).map Prod.snd := by
  have hg := hLip.continuous
  have hstep : Measurable (Function.uncurry (klmcStep (gradient f) γ h)) := by
    apply Continuous.measurable
    unfold Function.uncurry klmcStep exponentialStep
    fun_prop
  have hl := noiseDrivenChain_law_of_jointLaw (ν.prod (κ.prod Q)) (klmcStep (gradient f) γ h)
    hstep (κ.prod ν) η (fun p : E×(E×S) ↦ (p.2.1,p.1))
    (fun k p ↦ W p.2.2 k) (independentInitialPhase_noise_jointLaw ν κ Q η W hW hlaw) n
  have hmeas := ULA.noiseDrivenChain_measurable (klmcStep (gradient f) γ h) hstep n
  have hp : Measurable (fun p : E×(E×S) ↦ ((p.2.1,p.1),W p.2.2)) :=
    ((measurable_snd.fst.prodMk measurable_fst).prodMk (hW.comp measurable_snd.snd))
  have hr := congrArg (fun ρ : Measure (E×E) ↦ ρ.map Prod.snd) hl
  have hchain : Measurable (fun p : E×(E×S) ↦
      ULA.noiseDrivenChain (klmcStep (gradient f) γ h) (p.2.1,p.1) (fun k ↦ W p.2.2 k) n) :=
    hmeas.comp hp
  rw [Measure.map_map measurable_snd hchain] at hr
  unfold productKLMCLaw productKLMCMap
  simp_rw [klmcChain_eq_noiseDrivenChain]
  exact hr

end KineticLangevin
