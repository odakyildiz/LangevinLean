import UnadjustedLangevin.InitialExtension
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Composition.Lemmas

set_option linter.style.header false

/-! # Genuine symmetry, gluing, and triangle inequality for Wasserstein transport

The gluing measure is constructed by disintegrating its second input coupling.
No optimal-coupling assumption or abstract triangle hypothesis is used.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace WassersteinMixing

variable {H : Type*} [NormedAddCommGroup H] [MeasurableSpace H]
  [BorelSpace H] [SecondCountableTopology H]

/-- Reverse the two marginals of an actual coupling. -/
def couplingSwap {μ ν : Measure H} (c : ULA.Coupling μ ν) : ULA.Coupling ν μ where
  joint := c.joint.map Prod.swap
  fst := by rw [Measure.map_map measurable_fst measurable_swap]; exact c.snd
  snd := by rw [Measure.map_map measurable_snd measurable_swap]; exact c.fst

/-- Swapping endpoints preserves the exact quadratic transport cost. -/
theorem couplingCost_swap {μ ν : Measure H} (c : ULA.Coupling μ ν) :
    ULA.couplingCost (couplingSwap c).joint = ULA.couplingCost c.joint := by
  rw [ULA.couplingCost, couplingSwap,
    eLpNorm_map_measure (by fun_prop) measurable_swap.aemeasurable]
  change eLpNorm (fun p : H × H ↦ p.2 - p.1) 2 c.joint = _
  apply eLpNorm_congr_norm_ae (by fun_prop) (by fun_prop)
  exact Filter.Eventually.of_forall fun p : H × H ↦ norm_sub_rev p.2 p.1

/-- The transport infimum is symmetric, including infinite distances. -/
theorem wasserstein2_symm (μ ν : Measure H) : ULA.wasserstein2 μ ν = ULA.wasserstein2 ν μ := by
  apply le_antisymm
  · apply le_iInf
    intro c
    exact (ULA.wasserstein2_le_couplingCost (couplingSwap c)).trans_eq (couplingCost_swap c)
  · apply le_iInf
    intro c
    exact (ULA.wasserstein2_le_couplingCost (couplingSwap c)).trans_eq (couplingCost_swap c)

/-- Symmetry of the finite-distance real convention. -/
theorem wasserstein2Real_symm (μ ν : Measure H) :
    ULA.wasserstein2Real μ ν = ULA.wasserstein2Real ν μ := by
  unfold ULA.wasserstein2Real
  rw [wasserstein2_symm]

section Gluing
variable [StandardBorelSpace H]
  {μ ν ξ : Measure H} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  [IsProbabilityMeasure ξ]

/-- Glue `XY` and `YZ` by sampling `Z` from the actual conditional kernel of
the second coupling given the shared `Y` coordinate. -/
def glueCouplings (cXY : ULA.Coupling μ ν) (cYZ : ULA.Coupling ν ξ) : Measure ((H × H) × H) := by
  have := cYZ.isProbabilityMeasure
  exact cXY.joint ⊗ₘ (cYZ.joint.condKernel.comap Prod.snd measurable_snd)

omit [BorelSpace H] [IsProbabilityMeasure ξ] in
/-- The constructed triple measure preserves its first pair marginal exactly. -/
theorem glueCouplings_left (cXY : ULA.Coupling μ ν) (cYZ : ULA.Coupling ν ξ) :
    (glueCouplings cXY cYZ).map Prod.fst = cXY.joint := by
  have := cXY.isProbabilityMeasure
  have := cYZ.isProbabilityMeasure
  exact Measure.fst_compProd cXY.joint _

omit [BorelSpace H] [IsProbabilityMeasure ξ] in
/-- The shared-second-coordinate projection of the glued measure is the
second input coupling, as proved from disintegration. -/
theorem glueCouplings_right (cXY : ULA.Coupling μ ν) (cYZ : ULA.Coupling ν ξ) :
    (glueCouplings cXY cYZ).map (fun p ↦ (p.1.2, p.2)) = cYZ.joint := by
  have := cXY.isProbabilityMeasure
  have := cYZ.isProbabilityMeasure
  let K := cYZ.joint.condKernel
  have hd : ν ⊗ₘ K = cYZ.joint := by
    calc
      _ = cYZ.joint.fst ⊗ₘ K := congrArg (fun m : Measure H ↦ m ⊗ₘ K) cYZ.fst.symm
      _ = _ := cYZ.joint.disintegrate K
  rw [← hd]
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs, Measure.compProd_apply hs]
  change (cXY.joint ⊗ₘ K.comap Prod.snd measurable_snd)
    ((fun p : (H × H) × H ↦ (p.1.2, p.2)) ⁻¹' s) = _
  rw [Measure.compProd_apply ((measurable_fst.snd.prodMk measurable_snd) hs)]
  simp only [Kernel.comap_apply]
  have hm : Measurable (fun y ↦ K y (Prod.mk y ⁻¹' s)) :=
    Kernel.measurable_kernel_prodMk_left hs
  have hlin := lintegral_map (μ := cXY.joint) hm measurable_snd
  rw [cXY.snd] at hlin
  exact hlin.symm

omit [BorelSpace H] [IsProbabilityMeasure ξ] in
/-- Gluing two probability couplings produces a probability measure. -/
theorem glueCouplings_isProbability (cXY : ULA.Coupling μ ν) (cYZ : ULA.Coupling ν ξ) :
    IsProbabilityMeasure (glueCouplings cXY cYZ) := by
  have := cXY.isProbabilityMeasure
  have := cYZ.isProbabilityMeasure
  constructor
  rw [glueCouplings, Measure.compProd_apply_univ, measure_univ]

omit [IsProbabilityMeasure ξ] in
/-- Minkowski on the actual glued triple bounds endpoint transport by the
sum of the two supplied coupling costs.  Infinite costs are retained. -/
theorem wasserstein2_le_couplingCost_add
    (cXY : ULA.Coupling μ ν) (cYZ : ULA.Coupling ν ξ) :
    ULA.wasserstein2 μ ξ ≤ ULA.couplingCost cXY.joint + ULA.couplingCost cYZ.joint := by
  let R := glueCouplings cXY cYZ
  have hleft : R.map Prod.fst = cXY.joint := glueCouplings_left cXY cYZ
  have hright : R.map (fun p ↦ (p.1.2, p.2)) = cYZ.joint := glueCouplings_right cXY cYZ
  have hX : R.map (fun p ↦ p.1.1) = μ := by
    calc
      _ = (R.map Prod.fst).map Prod.fst := by rw [Measure.map_map (by fun_prop) (by fun_prop)]; rfl
      _ = μ := by rw [hleft, cXY.fst]
  have hZ : R.map Prod.snd = ξ := by
    calc
      _ = (R.map (fun p ↦ (p.1.2, p.2))).map Prod.snd := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]; rfl
      _ = ξ := by rw [hright, cYZ.snd]
  have hcostXY : eLpNorm (fun p : (H × H) × H ↦ p.1.1 - p.1.2) 2 R =
      ULA.couplingCost cXY.joint := by
    rw [ULA.couplingCost, ← hleft,
      eLpNorm_map_measure (by fun_prop) measurable_fst.aemeasurable]
    rfl
  have hcostYZ : eLpNorm (fun p : (H × H) × H ↦ p.1.2 - p.2) 2 R =
      ULA.couplingCost cYZ.joint := by
    rw [ULA.couplingCost, ← hright,
      eLpNorm_map_measure (by fun_prop) (by fun_prop)]
    rfl
  have hb := ULA.wasserstein2_le_random_cost R (fun p ↦ p.1.1) Prod.snd
    (by fun_prop) measurable_snd
  rw [hX, hZ] at hb
  have hsplit : (fun p : (H × H) × H ↦ p.1.1 - p.2) =
      (fun p ↦ p.1.1 - p.1.2) + (fun p ↦ p.1.2 - p.2) := by
    funext p
    simp only [Pi.add_apply]
    abel
  calc
    _ ≤ eLpNorm (fun p : (H × H) × H ↦ p.1.1 - p.2) 2 R := hb
    _ ≤ eLpNorm (fun p : (H × H) × H ↦ p.1.1 - p.1.2) 2 R +
        eLpNorm (fun p : (H × H) × H ↦ p.1.2 - p.2) 2 R := by
      rw [hsplit]
      exact eLpNorm_add_le (by norm_num)
    _ = _ := by rw [hcostXY, hcostYZ]

/-- The triangle inequality for the repository's genuine Wasserstein infimum,
derived by disintegration and two infima over arbitrary couplings. -/
theorem wasserstein2_triangle (μ ν ξ : Measure H)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ] :
    ULA.wasserstein2 μ ξ ≤ ULA.wasserstein2 μ ν + ULA.wasserstein2 ν ξ := by
  unfold ULA.wasserstein2
  rw [ENNReal.iInf_add]
  apply le_iInf
  intro cXY
  rw [ENNReal.add_iInf]
  apply le_iInf
  intro cYZ
  exact wasserstein2_le_couplingCost_add cXY cYZ

/-- A finite sum of two transport distances also proves finite endpoint
transport, so conversion to ordinary real distances cannot hide infinity. -/
theorem wasserstein2_triangle_finite (μ ν ξ : Measure H)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ]
    (hμν : ULA.wasserstein2 μ ν ≠ ⊤) (hνξ : ULA.wasserstein2 ν ξ ≠ ⊤) :
    ULA.wasserstein2 μ ξ ≠ ⊤ := by
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hμν, hνξ⟩)
    (wasserstein2_triangle μ ν ξ)

/-- The ordinary real-valued triangle inequality with the required two
finite-distance premises made explicit. -/
theorem wasserstein2Real_triangle (μ ν ξ : Measure H)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ]
    (hμν : ULA.wasserstein2 μ ν ≠ ⊤) (hνξ : ULA.wasserstein2 ν ξ ≠ ⊤) :
    ULA.wasserstein2Real μ ξ ≤ ULA.wasserstein2Real μ ν + ULA.wasserstein2Real ν ξ := by
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hμν, hνξ⟩)
    (wasserstein2_triangle μ ν ξ)
  simpa only [ULA.wasserstein2Real, ENNReal.toReal_add hμν hνξ] using hr

end Gluing

end WassersteinMixing
