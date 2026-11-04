import WassersteinMixing.SemigroupRandomMALABounds

/-! # Retaining the initial state in the actual randomized MALA chain

The first coordinate is a frozen initial anchor; the second follows the same
uniformly randomized MALA recursion. Its law is the actual finite-step kernel
pair, allowing reversibility to pass to the continuous diffusion limit.
-/
noncomputable section
set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal unitInterval

namespace WassersteinMixing.RandomMALA

section KernelSampling
variable {A Z : Type*} [MeasurableSpace A] [MeasurableSpace Z]

/-- A pointwise exact random sampler induces exactly its transition kernel. -/
theorem sampled_markovStep_eq_comp (F : A → Z → A)
    (hF : Measurable (Function.uncurry F)) (η : Measure Z) [IsProbabilityMeasure η]
    (κ : Kernel A A) (hκ : ∀ x, κ x = η.map (F x))
    (μ : Measure A) [IsProbabilityMeasure μ] :
    ULA.markovStep F η μ = κ ∘ₘ μ := by
  ext s hs
  rw [ULA.markovStep, Measure.map_apply hF hs,
    Measure.prod_apply (hF hs), Measure.bind_apply hs (Kernel.aemeasurable _)]
  apply lintegral_congr
  intro x
  have hx : Measurable (F x) := hF.comp measurable_prodMk_left
  rw [hκ x, Measure.map_apply hx hs]
  rfl

end KernelSampling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual scalar MALA sampler, using the acceptance draw. -/
def malaUpdate (V : E → ℝ) (h : ℝ) (x : E) (z : E × I) : E :=
  (update V h (x, x) z).2

theorem malaUpdate_measurable (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) :
    Measurable (Function.uncurry (malaUpdate V h)) :=
  measurable_snd.comp ((update_measurable V h L hdiff hLip).comp
    ((measurable_fst.prodMk measurable_fst).prodMk measurable_snd))

/-- The sampler's law is exactly the explicit Gaussian acceptance kernel. -/
theorem malaUpdate_law (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) (x : E) :
    (innovationLaw (E := E)).map (malaUpdate V h x) =
      MALAStationaryPair.explicitKernel V h x := by
  have hc := markovStep_eq_coupledStep V h L hdiff hLip (Measure.dirac (x, x))
  have hm := congrArg (fun μ : Measure (E × E) ↦ μ.map Prod.snd) hc
  have hx : Measurable (fun z ↦ update V h (x, x) z) :=
    (update_measurable V h L hdiff hLip).comp measurable_prodMk_left
  rw [ULA.markovStep, Measure.dirac_prod,
    Measure.map_map (update_measurable V h L hdiff hLip) measurable_prodMk_left] at hm
  change ((innovationLaw (E := E)).map (fun z ↦ update V h (x, x) z)).map Prod.snd =
    (ULA.malaCoupledStep V h (Measure.dirac (x, x))).map Prod.snd at hm
  rw [Measure.map_map measurable_snd hx,
    ULA.malaCoupledStep_snd V h L hdiff hLip,
    Measure.map_dirac' measurable_snd] at hm
  rw [MALAStationaryPair.explicitKernel_apply V h L hdiff hLip]
  exact hm

/-- Preserve the actual initial state and update only the current MALA state. -/
def anchoredUpdate (V : E → ℝ) (h : ℝ) (p : E × E) (z : E × I) : E × E :=
  (p.1, malaUpdate V h p.2 z)

theorem anchoredUpdate_measurable (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) :
    Measurable (Function.uncurry (anchoredUpdate V h)) :=
  measurable_fst.fst.prodMk ((malaUpdate_measurable V h L hdiff hLip).comp
    (measurable_fst.snd.prodMk measurable_snd))

theorem anchoredUpdate_law (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) (p : E × E) :
    (innovationLaw (E := E)).map (anchoredUpdate V h p) =
      (Kernel.id ∥ₖ MALAStationaryPair.explicitKernel V h) p := by
  let := MALAStationaryPair.explicitKernel_isMarkov V h L hdiff hLip
  have hm : Measurable (malaUpdate V h p.2) :=
    (malaUpdate_measurable V h L hdiff hLip).comp measurable_prodMk_left
  rw [Kernel.parallelComp_apply, Kernel.id_apply, Measure.dirac_prod,
    ← malaUpdate_law V h L hdiff hLip p.2,
    Measure.map_map measurable_prodMk_left hm]
  rfl

theorem anchored_markovStep (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V))
    (ρ : Measure (E × E)) [IsProbabilityMeasure ρ] :
    ULA.markovStep (anchoredUpdate V h) innovationLaw ρ =
      (Kernel.id ∥ₖ MALAStationaryPair.explicitKernel V h) ∘ₘ ρ :=
  sampled_markovStep_eq_comp _ (anchoredUpdate_measurable V h L hdiff hLip) _ _
    (fun p ↦ (anchoredUpdate_law V h L hdiff hLip p).symm) ρ

/-- The anchored scalar sampler has exactly the same current state as the
MALA coordinate of the synchronous ULA/MALA chain. -/
theorem anchored_chain_eq (V : E → ℝ) (h : ℝ) (x : E) (w : ℕ → E × I) (n : ℕ) :
    ULA.noiseDrivenChain (anchoredUpdate V h) (x, x) w n =
      (x, (ULA.noiseDrivenChain (update V h) (x, x) w n).2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ULA.noiseDrivenChain_succ, ih, ULA.noiseDrivenChain_succ]
    change (x, malaUpdate V h _ (w n)) = (x, (update V h _ (w n)).2)
    unfold malaUpdate update uniformDecision
    split <;> rfl

end WassersteinMixing.RandomMALA
