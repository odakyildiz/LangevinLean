import KineticLangevin.LpDynamics
import UnadjustedLangevin.ProductReference

/-! # Concrete initial-coupling extensions for KLMC

Every initial position coupling is enlarged by the same explicit independent
source of initial velocity and correlated phase innovations. Its L² numerical
chain is proved to have an output law independent of the chosen coupling.
The initial L² position cost is the genuine supplied transport cost.
-/

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace KineticLangevin

variable {H S : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [MeasurableSpace S]
  {μ π : Measure H} [IsProbabilityMeasure μ] (Q : Measure S) [IsProbabilityMeasure Q]

local instance extensionProbability (c : ULA.Coupling μ π) :
    IsProbabilityMeasure (ULA.initialExtension c Q) := ULA.initialExtension_isProbabilityMeasure c Q

/-- The shared initial velocity as an actual L² variable on each extension. -/
def extensionVelocity (c : ULA.Coupling μ π) (V : S → H) (hV : MemLp V 2 Q) :
    Lp H 2 (ULA.initialExtension c Q) :=
  ULA.Hilbert.productNoise Q c (fun _ ↦ V) (fun _ ↦ hV) 0

/-- The shared phase innovation keeps its two correlated components. -/
def extensionInnovation (c : ULA.Coupling μ π) (W : ℕ → S → H × H)
    (hWv : ∀ n, MemLp (fun s ↦ (W n s).1) 2 Q)
    (hWx : ∀ n, MemLp (fun s ↦ (W n s).2) 2 Q) (n : ℕ) :
    Lp H 2 (ULA.initialExtension c Q) × Lp H 2 (ULA.initialExtension c Q) :=
  (ULA.Hilbert.productNoise Q c (fun k s ↦ (W k s).1) hWv n,
   ULA.Hilbert.productNoise Q c (fun k s ↦ (W k s).2) hWx n)

theorem extensionVelocity_coe (c : ULA.Coupling μ π) (V : S → H) (hV : MemLp V 2 Q) :
    extensionVelocity Q c V hV =ᵐ[ULA.initialExtension c Q] fun p ↦ V p.2 :=
  ULA.Hilbert.productNoise_coe Q c (fun _ ↦ V) (fun _ ↦ hV) 0

theorem extensionInnovation_coe (c : ULA.Coupling μ π) (W : ℕ → S → H × H)
    (hWv : ∀ n, MemLp (fun s ↦ (W n s).1) 2 Q)
    (hWx : ∀ n, MemLp (fun s ↦ (W n s).2) 2 Q) (n : ℕ) :
    (fun p ↦ lpPhaseCoe (ULA.initialExtension c Q) (extensionInnovation Q c W hWv hWx n) p)
      =ᵐ[ULA.initialExtension c Q] fun p ↦ W n p.2 := by
  filter_upwards [ULA.Hilbert.productNoise_coe Q c (fun k s ↦ (W k s).1) hWv n,
    ULA.Hilbert.productNoise_coe Q c (fun k s ↦ (W k s).2) hWx n] with p hv hx
  exact Prod.ext hv hx

/-- The pointwise KLMC phase chain, with initial position first in its input. -/
def productKLMCMap (f : H → ℝ) (γ h : ℝ) (V : S → H) (W : ℕ → S → H × H)
    (n : ℕ) (p : H × S) : H :=
  (klmcChain (gradient f) γ h (V p.2,p.1) (fun k ↦ W k p.2) n).2

/-- Its actual output law uses only the initial position law and fixed source. -/
def productKLMCLaw (f : H → ℝ) (γ h : ℝ) (ν : Measure H)
    (V : S → H) (W : ℕ → S → H × H) (n : ℕ) : Measure H :=
  (ν.prod Q).map (productKLMCMap f γ h V W n)

/-- The lifted chain is the original pointwise chain on every coupling
extension; the two velocity starts agree because they are the same variable. -/
theorem product_klmcChain_coe (c : ULA.Coupling μ π) (hc : ULA.couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (fun x : H ↦ x) 2 π) (f : H → ℝ) (M : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (γ h : ℝ)
    (V : S → H) (hV : MemLp V 2 Q) (W : ℕ → S → H × H)
    (hWv : ∀ n, MemLp (fun s ↦ (W n s).1) 2 Q)
    (hWx : ∀ n, MemLp (fun s ↦ (W n s).2) 2 Q) (n : ℕ) :
    (klmcChain (ULA.lpDrift (ULA.initialExtension c Q) (gradient f) hLip) γ h
      (extensionVelocity Q c V hV,ULA.initialExtension_lpInitial c Q hc hπ)
      (extensionInnovation Q c W hWv hWx) n).2
        =ᵐ[ULA.initialExtension c Q] fun p ↦ productKLMCMap f γ h V W n (p.1.1,p.2) := by
  have hchain := lp_klmcChain_coe (ULA.initialExtension c Q) f M hLip γ h
    (extensionVelocity Q c V hV,ULA.initialExtension_lpInitial c Q hc hπ)
    (extensionInnovation Q c W hWv hWx) n
  have hnoise := ae_all_iff.mpr (extensionInnovation_coe Q c W hWv hWx)
  filter_upwards [hchain,hnoise,extensionVelocity_coe Q c V hV,
    (ULA.initialExtension_memLp_initial c Q hc hπ).coeFn_toLp] with p hchain hnoise hvel hpos
  have hini : lpPhaseCoe (ULA.initialExtension c Q)
      (extensionVelocity Q c V hV,ULA.initialExtension_lpInitial c Q hc hπ) p =
        (V p.2,p.1.1) := Prod.ext hvel hpos
  have hn : (fun k ↦ lpPhaseCoe (ULA.initialExtension c Q)
      (extensionInnovation Q c W hWv hWx k) p) = fun k ↦ W k p.2 := funext hnoise
  have hs := congrArg Prod.snd hchain
  rw [hini,hn] at hs
  exact hs

/-- Almost-everywhere measurable output maps also have coupling-independent
laws; the projection's product law is proved explicitly. -/
theorem initialExtension_map_ae (c : ULA.Coupling μ π)
    (F : H × S → H) (hF : AEMeasurable F (μ.prod Q)) :
    (ULA.initialExtension c Q).map (fun p ↦ F (p.1.1,p.2)) = (μ.prod Q).map F := by
  have hproj := ULA.initialExtension_initial_noise c Q
  have hF' : AEMeasurable F ((ULA.initialExtension c Q).map (fun p ↦ (p.1.1,p.2))) := by
    rwa [hproj]
  rw [← hproj, AEMeasurable.map_map_of_aemeasurable hF'
    (measurable_fst.fst.prodMk measurable_snd).aemeasurable]
  rfl

/-- L² source data suffice for the actual pointwise KLMC output to be
almost-everywhere measurable; no measurable path-choice premise is needed. -/
theorem productKLMCMap_aemeasurable (f : H → ℝ) (M : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (γ h : ℝ)
    (V : S → H) (hV : MemLp V 2 Q) (W : ℕ → S → H × H)
    (hWv : ∀ n, MemLp (fun s ↦ (W n s).1) 2 Q)
    (hWx : ∀ n, MemLp (fun s ↦ (W n s).2) 2 Q) (n : ℕ) :
    AEMeasurable (productKLMCMap f γ h V W n) (μ.prod Q) := by
  have hV' : AEMeasurable (fun p : H × S ↦ V p.2) (μ.prod Q) :=
    (hV.comp_measurePreserving measurePreserving_snd).aestronglyMeasurable.aemeasurable
  have hW' (k : ℕ) : AEMeasurable (fun p : H × S ↦ W k p.2) (μ.prod Q) := by
    exact ((hWv k).comp_measurePreserving measurePreserving_snd).aestronglyMeasurable.aemeasurable.prodMk
      (((hWx k).comp_measurePreserving measurePreserving_snd).aestronglyMeasurable.aemeasurable)
  have hstep : Measurable (fun p : (H × H) × (H × H) ↦ klmcStep (gradient f) γ h p.1 p.2) := by
    apply Continuous.measurable
    have hg := hLip.continuous
    unfold klmcStep exponentialStep
    fun_prop
  have hall : ∀ k : ℕ, AEMeasurable (fun p : H × S ↦
      klmcChain (gradient f) γ h (V p.2,p.1) (fun j ↦ W j p.2) k) (μ.prod Q) := by
    intro k
    induction k with
    | zero => exact hV'.prodMk measurable_fst.aemeasurable
    | succ k ih =>
      exact hstep.comp_aemeasurable (ih.prodMk (hW' k))
  exact (hall n).snd

/-- The actual L² analysis has a single numerical output law, independent
of every chosen initial coupling. -/
theorem product_klmcChain_outputLaw (c : ULA.Coupling μ π) (hc : ULA.couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (fun x : H ↦ x) 2 π) (f : H → ℝ) (M : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (γ h : ℝ)
    (V : S → H) (hV : MemLp V 2 Q) (W : ℕ → S → H × H)
    (hWv : ∀ n, MemLp (fun s ↦ (W n s).1) 2 Q)
    (hWx : ∀ n, MemLp (fun s ↦ (W n s).2) 2 Q) (n : ℕ) :
    (ULA.initialExtension c Q).map
      (klmcChain (ULA.lpDrift (ULA.initialExtension c Q) (gradient f) hLip) γ h
        (extensionVelocity Q c V hV,ULA.initialExtension_lpInitial c Q hc hπ)
        (extensionInnovation Q c W hWv hWx) n).2 = productKLMCLaw Q f γ h μ V W n := by
  rw [Measure.map_congr (product_klmcChain_coe Q c hc hπ f M hLip γ h V hV W hWv hWx n)]
  exact initialExtension_map_ae Q c _ (productKLMCMap_aemeasurable Q f M hLip γ h V hV W hWv hWx n)

/-- The fixed-source KLMC output is an actual probability measure. -/
theorem productKLMCLaw_probability (f : H → ℝ) (M : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (γ h : ℝ)
    (V : S → H) (hV : MemLp V 2 Q) (W : ℕ → S → H × H)
    (hWv : ∀ n, MemLp (fun s ↦ (W n s).1) 2 Q)
    (hWx : ∀ n, MemLp (fun s ↦ (W n s).2) 2 Q) (n : ℕ) :
    IsProbabilityMeasure (productKLMCLaw Q f γ h μ V W n) :=
  (Measure.isProbabilityMeasure_map_iff
    (productKLMCMap_aemeasurable Q f M hLip γ h V hV W hWv hWx n)).mpr inferInstance

end KineticLangevin
