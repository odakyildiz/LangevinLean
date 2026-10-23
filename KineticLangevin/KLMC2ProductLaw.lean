import KineticLangevin.LpKLMC2
import KineticLangevin.ProductLaw

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace KineticLangevin
variable {S E : Type*} [MeasurableSpace S] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (Q : Measure S) [IsProbabilityMeasure Q]
  {μ π : Measure E} [IsProbabilityMeasure μ]
local instance secondOrderCouplingProbability (c : ULA.Coupling μ π) : IsProbabilityMeasure c.joint := c.isProbabilityMeasure
local instance secondOrderExtensionProbability (c : ULA.Coupling μ π) : IsProbabilityMeasure (ULA.initialExtension c Q) :=
  ULA.initialExtension_isProbabilityMeasure c Q

/-- The actual four-coordinate noise lifted onto an arbitrary initial coupling extension. -/
def extensionKLMC2Noise (c : ULA.Coupling μ π) (W : ℕ → S → Fin 4 → E)
    (hW : ∀ n j,MemLp (fun s => W n s j) 2 Q) (n : ℕ) (j : Fin 4) :
    Lp E 2 (ULA.initialExtension c Q) :=
  ((hW n j).comp_measurePreserving measurePreserving_snd).toLp (fun p => W n p.2 j)

/-- Every lifted innovation is the original actual four-coordinate source value. -/
theorem extensionKLMC2Noise_coe (c : ULA.Coupling μ π) (W : ℕ → S → Fin 4 → E)
    (hW : ∀ n j,MemLp (fun s => W n s j) 2 Q) (n : ℕ) :
    (fun p j => extensionKLMC2Noise Q c W hW n j p) =ᵐ[ULA.initialExtension c Q]
      fun p => W n p.2 := by
  have hs := ae_all_iff.mpr (fun j : Fin 4 =>
    ((hW n j).comp_measurePreserving (measurePreserving_snd : MeasurePreserving Prod.snd
      (ULA.initialExtension c Q) Q)).coeFn_toLp)
  filter_upwards [hs] with p hp
  exact funext hp

/-- The actual pointwise second-order output from independent initial position and source. -/
def productKLMC2Map (g : E → E) (H : E → E →L[ℝ] E) (γ h : ℝ)
    (V : S → E) (W : ℕ → S → Fin 4 → E) (n : ℕ) (p : E×S) : E :=
  (klmc2Chain g H γ h (V p.2,p.1) (fun k => W k p.2) n).2

/-- The genuine KLMC2 position law is defined on one independent initial-position/noise product. -/
def productKLMC2Law (g : E → E) (H : E → E →L[ℝ] E) (γ h : ℝ) (ν : Measure E)
    (V : S → E) (W : ℕ → S → Fin 4 → E) (n : ℕ) : Measure E :=
  (ν.prod Q).map (productKLMC2Map g H γ h V W n)

/-- The independent-source actual KLMC2 output map is almost everywhere measurable. -/
theorem productKLMC2Map_aemeasurable (g : E → E) (H : E → E →L[ℝ] E)
    (hG : Continuous g) (hH : Continuous H) (γ h : ℝ)
    (V : S → E) (hV : MemLp V 2 Q) (W : ℕ → S → Fin 4 → E)
    (hW : ∀ n j,MemLp (fun s => W n s j) 2 Q) (n : ℕ) :
    AEMeasurable (productKLMC2Map g H γ h V W n) (μ.prod Q) := by
  have hV' : AEMeasurable (fun p : E×S => V p.2) (μ.prod Q) :=
    (hV.comp_measurePreserving measurePreserving_snd).aestronglyMeasurable.aemeasurable
  have hW' (k : ℕ) : AEMeasurable (fun p : E×S => W k p.2) (μ.prod Q) := by
    apply aemeasurable_pi_iff.mpr
    intro j
    exact ((hW k j).comp_measurePreserving measurePreserving_snd).aestronglyMeasurable.aemeasurable
  have hs := klmc2Step_measurable g H hG hH γ h
  have hall : ∀ k,AEMeasurable (fun p : E×S => klmc2Chain g H γ h (V p.2,p.1) (fun j => W j p.2) k) (μ.prod Q) := by
    intro k
    induction k with
    | zero => exact hV'.prodMk measurable_fst.aemeasurable
    | succ k ih => exact hs.comp_aemeasurable (ih.prodMk (hW' k))
  exact (hall n).snd

/-- The actual L² numerical output agrees with the original KLMC2 chain on the initial coupling extension. -/
theorem product_klmc2Chain_coe (c : ULA.Coupling μ π) (hc : ULA.couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (id : E → E) 2 π)
    (g : E → E) (H : E → E →L[ℝ] E) (M M2 : ℝ≥0)
    (hG : LipschitzWith M g) (hH : LipschitzWith M2 H) (hg : ∀ x,HasFDerivAt g (H x) x)
    (γ h : ℝ) (V : S → E) (hV : MemLp V 2 Q) (W : ℕ → S → Fin 4 → E)
    (hW : ∀ n j,MemLp (fun s => W n s j) 2 Q) (n : ℕ) :
    (klmc2Chain (ULA.lpDrift (ULA.initialExtension c Q) g hG)
      (lpHessian (ULA.initialExtension c Q) g H M M2 hG hH hg) γ h
      (extensionVelocity Q c V hV,ULA.initialExtension_lpInitial c Q hc hπ)
      (extensionKLMC2Noise Q c W hW) n).2 =ᵐ[ULA.initialExtension c Q]
        fun p => productKLMC2Map g H γ h V W n (p.1.1,p.2) := by
  letI := ULA.initialExtension_isProbabilityMeasure c Q
  have hc' := lp_klmc2Chain_coe (ULA.initialExtension c Q) g H M M2 hG hH hg γ h
    (extensionVelocity Q c V hV,ULA.initialExtension_lpInitial c Q hc hπ)
    (extensionKLMC2Noise Q c W hW) n
  have hnoise := ae_all_iff.mpr (extensionKLMC2Noise_coe Q c W hW)
  filter_upwards [hc',hnoise,extensionVelocity_coe Q c V hV,
    (ULA.initialExtension_memLp_initial c Q hc hπ).coeFn_toLp] with p hc' hn hv hx
  have hini : lpPhaseCoe (ULA.initialExtension c Q)
      (extensionVelocity Q c V hV,ULA.initialExtension_lpInitial c Q hc hπ) p=(V p.2,p.1.1) := Prod.ext hv hx
  have hn' : (fun k j => extensionKLMC2Noise Q c W hW k j p)=(fun k => W k p.2) := funext hn
  have he := congrArg Prod.snd hc'
  rw [hini,hn'] at he
  exact he

/-- Every actual finite-cost initial coupling gives the same independently defined second-order output law. -/
theorem product_klmc2Chain_outputLaw (c : ULA.Coupling μ π) (hc : ULA.couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (id : E → E) 2 π)
    (g : E → E) (H : E → E →L[ℝ] E) (M M2 : ℝ≥0)
    (hG : LipschitzWith M g) (hH : LipschitzWith M2 H) (hg : ∀ x,HasFDerivAt g (H x) x)
    (γ h : ℝ) (V : S → E) (hV : MemLp V 2 Q) (W : ℕ → S → Fin 4 → E)
    (hW : ∀ n j,MemLp (fun s => W n s j) 2 Q) (n : ℕ) :
    (ULA.initialExtension c Q).map
      (klmc2Chain (ULA.lpDrift (ULA.initialExtension c Q) g hG)
        (lpHessian (ULA.initialExtension c Q) g H M M2 hG hH hg) γ h
        (extensionVelocity Q c V hV,ULA.initialExtension_lpInitial c Q hc hπ)
        (extensionKLMC2Noise Q c W hW) n).2 = productKLMC2Law Q g H γ h μ V W n := by
  rw [Measure.map_congr (product_klmc2Chain_coe Q c hc hπ g H M M2 hG hH hg γ h V hV W hW n)]
  exact initialExtension_map_ae Q c _ (productKLMC2Map_aemeasurable Q g H hG.continuous hH.continuous γ h V hV W hW n)

/-- The actual second-order output law is a probability measure. -/
theorem productKLMC2Law_probability (g : E → E) (H : E → E →L[ℝ] E)
    (hG : Continuous g) (hH : Continuous H) (γ h : ℝ)
    (V : S → E) (hV : MemLp V 2 Q) (W : ℕ → S → Fin 4 → E)
    (hW : ∀ n j,MemLp (fun s => W n s j) 2 Q) (n : ℕ) :
    IsProbabilityMeasure (productKLMC2Law Q g H γ h μ V W n) :=
  (Measure.isProbabilityMeasure_map_iff
    (productKLMC2Map_aemeasurable Q g H hG hH γ h V hV W hW n)).mpr inferInstance

end KineticLangevin
