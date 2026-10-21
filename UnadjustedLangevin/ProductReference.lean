import UnadjustedLangevin.HilbertDalalyan
import UnadjustedLangevin.InitialExtension

set_option linter.style.header false

/-!
# Dalalyan's initial Wasserstein term on concrete product extensions

The reference diffusion may be realized separately for each initial coupling.
The sample space is always `(H × H) × S`, with probability measure
`c.joint.prod Q`. The noise source `Q` and all noise functions are fixed.
Consequently the algorithm's law is proved to be the same for every `c`.

This analytic interface takes an explicit continuous reference construction.
`UnadjustedLangevin/CanonicalULA.lean` supplies that construction from the
potential assumptions. Initial-law realization, initial cost, square
integrability, output-law independence, and the transport infimum are proved here.
-/

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal

namespace ULA.Hilbert
open ULA

variable {H S : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  [MeasurableSpace S]

/-- The ordinary ULA update in an arbitrary Euclidean presentation. -/
def pointwiseUpdate (U : H → ℝ) (h : ℝ) (x z : H) : H :=
  x - h • gradient U x + Real.sqrt (2 * h) • z

/-- Gradient Lipschitz regularity suffices for update measurability. -/
theorem pointwiseUpdate_measurable (U : H → ℝ) (h : ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U)) :
    Measurable (Function.uncurry (pointwiseUpdate U h)) := by
  have hg : Measurable (gradient U) := hLip.continuous.measurable
  exact (measurable_fst.sub ((hg.comp measurable_fst).const_smul h)).add
    (measurable_snd.const_smul (Real.sqrt (2 * h)))

variable {μ π : Measure H} [IsProbabilityMeasure μ]
  (Q : Measure S) [IsProbabilityMeasure Q]

local instance productProbability (c : Coupling μ π) :
    IsProbabilityMeasure (initialExtension c Q) := initialExtension_isProbabilityMeasure c Q

omit [InnerProductSpace ℝ H] [CompleteSpace H] [BorelSpace H]
  [SecondCountableTopology H] in
/-- A square-integrable noise function lifts to every initial-coupling extension. -/
theorem productNoise_memLp (c : Coupling μ π) (W : ℕ → S → H)
    (hW : ∀ n, MemLp (W n) 2 Q) (n : ℕ) :
    MemLp (fun p : (H × H) × S ↦ W n p.2) 2 (initialExtension c Q) := by
  have := c.isProbabilityMeasure
  exact (hW n).comp_measurePreserving measurePreserving_snd

/-- The common noise, as an actual `L²` random variable on each product space. -/
def productNoise (c : Coupling μ π) (W : ℕ → S → H)
    (hW : ∀ n, MemLp (W n) 2 Q) (n : ℕ) : Lp H 2 (initialExtension c Q) :=
  (productNoise_memLp Q c W hW n).toLp (fun p ↦ W n p.2)

omit [InnerProductSpace ℝ H] [CompleteSpace H] [BorelSpace H]
  [SecondCountableTopology H] in
/-- The chosen `L²` representative agrees with the original noise. -/
theorem productNoise_coe (c : Coupling μ π) (W : ℕ → S → H)
    (hW : ∀ n, MemLp (W n) 2 Q) (n : ℕ) :
    productNoise Q c W hW n =ᵐ[initialExtension c Q] fun p ↦ W n p.2 :=
  (productNoise_memLp Q c W hW n).coeFn_toLp

/-- The algorithm law uses the initial law and the fixed noise source only. -/
def productOutputLaw (U : H → ℝ) (h : ℝ) (μ : Measure H)
    (W : ℕ → S → H) (n : ℕ) : Measure H :=
  (μ.prod Q).map (fun p ↦ noiseDrivenChain (pointwiseUpdate U h) p.1
    (fun k ↦ W k p.2) n)

/-- The `L²` recursion equals the original noise-driven algorithm almost
everywhere on every concrete initial-coupling extension. -/
theorem product_chain_coe (c : Coupling μ π) (hc : couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (fun x : H ↦ x) 2 π)
    (U : H → ℝ) (h : ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (W : ℕ → S → H) (hW : ∀ n, MemLp (W n) 2 Q) (n : ℕ) :
    lpChain (initialExtension c Q) U h hLip
      (initialExtension_lpInitial c Q hc hπ) (productNoise Q c W hW) n
      =ᵐ[initialExtension c Q] fun p ↦
        noiseDrivenChain (pointwiseUpdate U h) p.1.1 (fun k ↦ W k p.2) n := by
  induction n with
  | zero => exact (initialExtension_memLp_initial c Q hc hπ).coeFn_toLp
  | succ n ih =>
      filter_upwards [lpUlaUpdate_coe (initialExtension c Q) U h hLip
          (lpChain (initialExtension c Q) U h hLip
            (initialExtension_lpInitial c Q hc hπ) (productNoise Q c W hW) n)
          (productNoise Q c W hW n), ih, productNoise_coe Q c W hW n]
        with p hupdate hprev hnoise
      simpa only [lpChain_succ, noiseDrivenChain_succ, pointwiseUpdate, hprev, hnoise]
        using hupdate

/-- Equality of the output law is derived; it is never a supplied hypothesis. -/
theorem product_chain_outputLaw (c : Coupling μ π) (hc : couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (fun x : H ↦ x) 2 π)
    (U : H → ℝ) (h : ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (W : ℕ → S → H) (hW : ∀ n, MemLp (W n) 2 Q) (n : ℕ) :
    (initialExtension c Q).map (lpChain (initialExtension c Q) U h hLip
      (initialExtension_lpInitial c Q hc hπ) (productNoise Q c W hW) n) =
      productOutputLaw Q U h μ W n := by
  rw [Measure.map_congr (product_chain_coe Q c hc hπ U h L hLip W hW n)]
  have hpath : AEMeasurable (fun w k ↦ W k w) Q :=
    aemeasurable_pi_iff.mpr fun k ↦ (hW k).aestronglyMeasurable.aemeasurable
  let path : S → ℕ → H := hpath.mk (fun w k ↦ W k w)
  have hpath_eq : (fun w k ↦ W k w) =ᵐ[Q] path := hpath.ae_eq_mk
  have hleft : (fun p : (H × H) × S ↦
      noiseDrivenChain (pointwiseUpdate U h) p.1.1 (fun k ↦ W k p.2) n)
      =ᵐ[initialExtension c Q] fun p ↦
      noiseDrivenChain (pointwiseUpdate U h) p.1.1 (path p.2) n := by
    have := c.isProbabilityMeasure
    have heq := (measurePreserving_snd (μ := c.joint) (ν := Q)).quasiMeasurePreserving.ae_eq_comp
      hpath_eq
    filter_upwards [heq] with p hp
    simp only [Function.comp_apply] at hp
    rw [hp]
  have hright : (fun p : H × S ↦
      noiseDrivenChain (pointwiseUpdate U h) p.1 (fun k ↦ W k p.2) n)
      =ᵐ[μ.prod Q] fun p ↦
      noiseDrivenChain (pointwiseUpdate U h) p.1 (path p.2) n := by
    have heq := (measurePreserving_snd (μ := μ) (ν := Q)).quasiMeasurePreserving.ae_eq_comp hpath_eq
    filter_upwards [heq] with p hp
    simp only [Function.comp_apply] at hp
    rw [hp]
  rw [Measure.map_congr hleft, productOutputLaw, Measure.map_congr hright]
  exact initialExtension_map c Q
    (fun p : H × S ↦ noiseDrivenChain (pointwiseUpdate U h) p.1 (path p.2) n)
    ((noiseDrivenChain_measurable (pointwiseUpdate U h)
      (pointwiseUpdate_measurable U h L hLip) n).comp
        (measurable_fst.prodMk (hpath.measurable_mk.comp measurable_snd)))

/-- A concrete reference constructor for every finite-cost coupling. The
stationary diffusion construction supplies these values; no law-of-algorithm
or convergence estimate is a field of this interface. -/
structure ProductReference (d : ℕ) (U : H → ℝ) (h : ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U)) (μ π : Measure H) [IsProbabilityMeasure μ]
    (hπ : MemLp (fun x : H ↦ x) 2 π)
    (W : ℕ → S → H) (hW : ∀ n, MemLp (W n) 2 Q) where
  reference : ∀ (c : Coupling μ π) (_ : couplingCost c.joint ≠ ⊤),
    L2Reference (initialExtension c Q) d U h L hLip (productNoise Q c W hW) π
  start : ∀ c hc, (reference c hc).segment 0 0 = initialExtension_lpReference c Q hπ

/-- Finiteness of the output transport distance follows from one finite-cost
initial coupling and its constructed reference. -/
theorem ProductReference.output_finite
    {d : ℕ} {U : H → ℝ} {h : ℝ} {L : ℝ≥0} {hLip : LipschitzWith L (gradient U)}
    {hπ : MemLp (fun x : H ↦ x) 2 π}
    {W : ℕ → S → H} {hW : ∀ n, MemLp (W n) 2 Q}
    (ref : ProductReference Q d U h L hLip μ π hπ W hW)
    (hfinite : wasserstein2 μ π ≠ ⊤) (n : ℕ) :
    wasserstein2 (productOutputLaw Q U h μ W n) π ≠ ⊤ := by
  obtain ⟨c, hc⟩ := exists_finiteCost_coupling μ π hfinite
  have hb := wasserstein2_le_Lp_cost (initialExtension c Q)
    (lpChain (initialExtension c Q) U h hLip
      (initialExtension_lpInitial c Q (ne_of_lt hc) hπ) (productNoise Q c W hW) n)
    ((ref.reference c (ne_of_lt hc)).segment n 0)
  rw [product_chain_outputLaw Q c (ne_of_lt hc) hπ U h L hLip W hW n,
    (ref.reference c (ne_of_lt hc)).stationary n] at hb
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb

/-- Dalalyan's bound with the genuine initial Wasserstein distance. Each
initial coupling uses its own explicitly defined product probability measure.
Its output law and initial coupling cost have already been proved above. -/
theorem dalalyan_small_step_of_product_reference
    (d : ℕ) (U : H → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (hLip : LipschitzWith L (gradient U)) (hm : 0 < m) (hmL : m ≤ (L : ℝ))
    (hh : 0 < h) (hsmall : h ≤ 2 / (m + (L : ℝ)))
    (hπ : MemLp (fun x : H ↦ x) 2 π)
    (W : ℕ → S → H) (hW : ∀ n, MemLp (W n) 2 Q)
    (hfinite : wasserstein2 μ π ≠ ⊤)
    (ref : ProductReference Q d U h L hLip μ π hπ W hW) (n : ℕ) :
    wasserstein2Real (productOutputLaw Q U h μ W n) π ≤
      (1 - m * h) ^ n * wasserstein2Real μ π +
        (33 / 20 : ℝ) * ((L : ℝ) / m) * Real.sqrt (h * d) := by
  have hpos : 0 < m + (L : ℝ) := by positivity
  have hproduct := (le_div_iff₀ hpos).mp hsmall
  have hq : 0 ≤ 1 - m * h := by
    nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hmL)]
  let a : ℝ≥0 := ⟨(1 - m * h) ^ n, pow_nonneg hq n⟩
  let b : ℝ≥0 := ⟨(33 / 20 : ℝ) * ((L : ℝ) / m) * Real.sqrt (h * d), by positivity⟩
  apply wasserstein2_affine_bound_real_of_finite_couplings μ π
    (productOutputLaw Q U h μ W n) π a b hfinite (ref.output_finite Q hfinite n)
  intro c hc
  have hb := dalalyan_small_step_of_integral_reference (initialExtension c Q) d
    U m h L hdiff hsc hLip hm hmL hh hsmall
      (initialExtension_lpInitial c Q hc hπ) (productNoise Q c W hW) π
      (ref.reference c hc) n
  rw [product_chain_outputLaw Q c hc hπ U h L hLip W hW n, ref.start c hc,
    initialExtension_lp_cost c Q hc hπ] at hb
  exact hb

/-- The large-step Dalalyan branch with the genuine initial Wasserstein
distance, using the same concrete product extensions as the small-step branch. -/
theorem dalalyan_large_step_of_product_reference
    (d : ℕ) (U : H → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (hLip : LipschitzWith L (gradient U)) (hm : 0 < m) (hmL : m ≤ (L : ℝ))
    (hh : 0 < h) (hlarge : 2 / (m + (L : ℝ)) ≤ h) (hstep : (L : ℝ) * h < 2)
    (hπ : MemLp (fun x : H ↦ x) 2 π)
    (W : ℕ → S → H) (hW : ∀ n, MemLp (W n) 2 Q)
    (hfinite : wasserstein2 μ π ≠ ⊤)
    (ref : ProductReference Q d U h L hLip μ π hπ W hW) (n : ℕ) :
    wasserstein2Real (productOutputLaw Q U h μ W n) π ≤
      ((L : ℝ) * h - 1) ^ n * wasserstein2Real μ π +
        ((33 / 20 : ℝ) * (L : ℝ) * h / (2 - (L : ℝ) * h)) * Real.sqrt (h * d) := by
  have hpos : 0 < m + (L : ℝ) := by positivity
  have hproduct := (div_le_iff₀ hpos).mp hlarge
  have hq : 0 ≤ (L : ℝ) * h - 1 := by
    nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hmL)]
  let a : ℝ≥0 := ⟨((L : ℝ) * h - 1) ^ n, pow_nonneg hq n⟩
  let b : ℝ≥0 := ⟨((33 / 20 : ℝ) * (L : ℝ) * h / (2 - (L : ℝ) * h)) *
    Real.sqrt (h * d), by positivity⟩
  apply wasserstein2_affine_bound_real_of_finite_couplings μ π
    (productOutputLaw Q U h μ W n) π a b hfinite (ref.output_finite Q hfinite n)
  intro c hc
  have hb := dalalyan_large_step_of_integral_reference (initialExtension c Q) d
    U m h L hdiff hsc hLip hm hmL hh hlarge hstep
      (initialExtension_lpInitial c Q hc hπ) (productNoise Q c W hW) π
      (ref.reference c hc) n
  rw [product_chain_outputLaw Q c hc hπ U h L hLip W hW n, ref.start c hc,
    initialExtension_lp_cost c Q hc hπ] at hb
  exact hb

end ULA.Hilbert
