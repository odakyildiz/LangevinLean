import WassersteinMixing.UniformDecision
import WassersteinMixing.ProductNoise
import WassersteinMixing.SemigroupMALAKernel
import UnadjustedLangevin.MarkovLaw

/-! # Synchronous Gaussian ULA and uniformly randomized MALA

The shared Gaussian innovation and a genuine independent uniform decision
realize the existing synchronous MALA coupling measure exactly.
-/
noncomputable section
set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory
open scoped unitInterval ENNReal NNReal

namespace WassersteinMixing.RandomMALA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual independent innovation law, including the acceptance draw. -/
def innovationLaw : Measure (E × I) := (stdGaussian E).prod volume

instance innovationLaw_isProbability : IsProbabilityMeasure (innovationLaw (E := E)) := by
  unfold innovationLaw
  infer_instance

/-- Both proposals share the Gaussian component. Only MALA uses the uniform component. -/
def update (V : E → ℝ) (h : ℝ) (x : E × E) (z : E × I) : E × E :=
  uniformDecision
    (fun p : (E × E) × E ↦ ULA.malaProposalAcceptance V h (p.1.2, p.2))
    (fun p ↦ (ULA.malaProposal V h p.1.1 p.2, ULA.malaProposal V h p.1.2 p.2))
    (fun p ↦ (ULA.malaProposal V h p.1.1 p.2, p.1.2)) ((x, z.1), z.2)

@[simp] theorem update_fst (V : E → ℝ) (h : ℝ) (x : E × E) (z : E × I) :
    (update V h x z).1 = ULA.malaProposal V h x.1 z.1 := by
  unfold update uniformDecision
  split <;> rfl

/-- The first coordinate is exactly the ordinary shared-noise Euler chain. -/
theorem chain_fst (V : E → ℝ) (h : ℝ) (x : E × E) (w : ℕ → E × I) (n : ℕ) :
    (ULA.noiseDrivenChain (update V h) x w n).1 =
      ULA.noiseDrivenChain (fun x z ↦ ULA.malaProposal V h x z) x.1
        (fun k ↦ (w k).1) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ULA.noiseDrivenChain_succ, update_fst, ih]

theorem update_measurable (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) :
    Measurable (Function.uncurry (update V h)) := by
  have hp := ULA.malaProposal_measurable V h L hLip
  have ha := ULA.malaProposalAcceptance_measurable V h L hdiff hLip
  exact (uniformDecision_measurable _ _ _
    (ha.comp (measurable_fst.snd.prodMk measurable_snd))
    ((hp.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk
      (hp.comp (measurable_fst.snd.prodMk measurable_snd)))
    ((hp.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk measurable_fst.snd)).comp
      (by fun_prop)

/-- One actual randomized step has exactly the existing accepted/rejected
synchronous coupling law. -/
theorem markovStep_eq_coupledStep (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V))
    (ρ : Measure (E × E)) [IsProbabilityMeasure ρ] :
    ULA.markovStep (update V h) innovationLaw ρ = ULA.malaCoupledStep V h ρ := by
  have hp := ULA.malaProposal_measurable V h L hLip
  have ha := ULA.malaProposalAcceptance_measurable V h L hdiff hLip
  rw [ULA.markovStep, innovationLaw,
    ← Measure.prodAssoc_prod (μ := ρ) (ν := stdGaussian E) (τ := (volume : Measure I)),
    Measure.map_map (update_measurable V h L hdiff hLip) (by fun_prop)]
  exact uniformDecision_law (ρ.prod (stdGaussian E)) _ _ _
    (ha.comp (measurable_fst.snd.prodMk measurable_snd))
    (fun p ↦ ULA.malaAcceptance_nonneg V h p.1.2 _)
    (fun p ↦ ULA.malaAcceptance_le_one V h p.1.2 _)
    ((hp.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk
      (hp.comp (measurable_fst.snd.prodMk measurable_snd)))
    ((hp.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk measurable_fst.snd)

/-- The iid randomized recursion realizes every finite synchronous coupling. -/
theorem chainLaw_eq_coupledChain (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V))
    (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) :
    ULA.chainLaw (update V h) (μ.map (fun x ↦ (x, x)))
      (Measure.infinitePi (fun _ : ℕ ↦ innovationLaw)) n =
        ULA.malaCoupledChain V h μ n := by
  have hinit : IsProbabilityMeasure (μ.map (fun x ↦ (x, x))) := by
    constructor
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ,
      Set.preimage_univ, measure_univ]
  rw [ULA.chainLaw_eq_markovLaws (update V h) (update_measurable V h L hdiff hLip)]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ULA.markovLaws, ih]
    letI := ULA.malaCoupledChain_isProbability V h L hdiff hLip μ n
    exact markovStep_eq_coupledStep V h L hdiff hLip _

end WassersteinMixing.RandomMALA
