import UnadjustedLangevin.CanonicalBrownian
import UnadjustedLangevin.GibbsStationarity
import UnadjustedLangevin.BrownianSegmentsGlobal
import UnadjustedLangevin.GaussianInnovationVectors

set_option linter.style.header false

/-! # ULA from the potential assumptions and the actual Gaussian algorithm

An explicit independent Brownian source supplies the continuous reference.
Gibbs stationarity is proved by refining the exactly invariant Metropolis
approximation. Initial couplings, moments, Gaussian innovations, and output-law
identification are derived rather than supplied as reference obligations.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace ULA.Hilbert
open ULA

variable {S ι : Type*} [MeasurableSpace S] [Fintype ι]
  (Q : Measure S) [IsProbabilityMeasure Q]

/-- The Brownian realization has the ordinary iterated Gaussian ULA law.
This is independent of the coupling used to realize the initialization. -/
theorem productBrownianOutput_eq_ulaLawStep
    {μ π : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure μ]
    (c : Coupling μ π) (hc : couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (fun x : EuclideanSpace ℝ ι ↦ x) 2 π)
    (U : EuclideanSpace ℝ ι → ℝ) (h : ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U))
    (B : ι → ℝ≥0 → S → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) Q)
    (hh : 0 < h)
    (hpaths : iIndepFun (fun i ω (n : ℕ) ↦ B i ((n : ℝ≥0) * h.toNNReal) ω) Q)
    (k : ℕ) :
    productOutputLaw Q U h μ (sourceEulerNoise Q B hB h) k =
      (ulaLawStep U h)^[k] μ := by
  have := initialExtension_isProbabilityMeasure c Q
  let W := productNoise Q c (sourceEulerNoise Q B hB h) (sourceEulerNoise_memLp Q B hB h)
  have hW : ∀ n, AEMeasurable (W n) (initialExtension c Q) :=
    fun n ↦ (Lp.aestronglyMeasurable (W n)).aemeasurable
  have hcoord := productEulerNoise_coordinateLaw Q c B hB h hh
  have hind := productEulerNoise_independent Q c B hB h hh hpaths
  rw [← product_chain_outputLaw Q c hc hπ U h L hLip
    (sourceEulerNoise Q B hB h) (sourceEulerNoise_memLp Q B hB h) k]
  rw [hilbert_lpChain_law_eq_ulaLawStep (initialExtension c Q) U h L hLip
    (initialExtension_lpInitial c Q hc hπ) W
    (productEulerNoise_independentInitial Q c hc hπ B hB h)
    (gaussianInnovations_vectorIndependent (initialExtension c Q) (fun n ω ↦ W n ω) hW hcoord hind)
    (gaussianInnovations_vectorLaw (initialExtension c Q) (fun n ω ↦ W n ω) hW hcoord hind),
    initialExtension_lpInitial_law]

/-- Independent Brownian coordinates and an independent initialization derive
every field of the reference. In particular Gibbs stationarity is a conclusion. -/
def productReference_of_independent_brownian
    {μ : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure μ]
    (U : EuclideanSpace ℝ ι → ℝ) (m : ℝ) (L : ℝ≥0)
    (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) (hLip : LipschitzWith L (gradient U))
    (B : ι → ℝ≥0 → S → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) Q)
    (hpaths : ∀ r : ℝ, 0 < r → iIndepFun
      (fun i ω (n : ℕ) ↦ B i ((n : ℝ≥0) * r.toNNReal) ω) Q)
    (h : ℝ) (hh : 0 < h) :
    ProductReference Q (Fintype.card ι) U h L hLip μ (gibbsMeasure U)
      (productGibbsMemLp U m hm hdiff hsc)
      (sourceEulerNoise Q B hB h) (sourceEulerNoise_memLp Q B hB h) := by
  apply productReference_of_constructed_brownian Q U m L hm hdiff hsc hLip B hB h hh
  intro c _hc n t ht
  have := initialExtension_isProbabilityMeasure c Q
  let P := initialExtension c Q
  let X := initialExtension_lpReference c Q (productGibbsMemLp U m hm hdiff hsc)
  let W := fun i t (p : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) × S) ↦ B i t p.2
  have hW : ∀ i, IsPreBrownianReal (W i) P := productPreBrownian Q c B hB
  let T := ((n : ℝ) + 1) * h
  have hT : 0 ≤ T := mul_nonneg (by positivity) hh.le
  obtain ⟨Y, hY, _hY0, hYe, _⟩ := exists_lp_langevin_integral_of_brownian
    P U L hLip X W hW 0 T le_rfl hT
  have heq := brownianSegments_eq_global P U L hLip X W hW Y hY T hT hYe
    h hh.le n le_rfl
  change P.map (brownianSegments P U L hLip W hW h hh.le X n t) = _
  rw [heq ht]
  have hscalar : ∀ r : ℝ, 0 < r → iIndepFun
      (fun p : ℕ × ι ↦ fun ω ↦ brownianEulerNoise P W hW r p.1 ω p.2) P := by
    intro r hr
    have hs := productEulerNoise_independent Q c B hB r hr (hpaths r hr)
    simpa only [productNoise_eq_brownianEulerNoise] using hs
  have hind : ∀ r : ℝ, 0 < r → IndepFun X
      (fun ω k ↦ brownianEulerNoise P W hW r k ω) P := by
    intro r _hr
    have hs := productEulerNoise_independentReference Q c
      (productGibbsMemLp U m hm hdiff hsc) B hB r
    simpa only [productNoise_eq_brownianEulerNoise] using hs
  have hinitial : P.map X = gibbsMeasure U :=
    initialExtension_lpReference_law c Q (productGibbsMemLp U m hm hdiff hsc)
  have hs : 0 ≤ (n : ℝ) * h + t :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) hh.le) ht.1
  have hsT : (n : ℝ) * h + t ≤ T := by dsimp [T]; nlinarith [ht.2]
  exact lp_langevin_gibbs_stationary P U m L hm hdiff hsc hLip X hinitial
    W hW hscalar hind Y hY ((n : ℝ) * h + t) hs
    (fun s hs ↦ hYe s ⟨hs.1, hs.2.trans hsT⟩)

/-- The explicit Brownian noise source used by the unconditional theorem. -/
abbrev canonicalEulerNoise (h : ℝ) : ℕ → CanonicalBrownian.VectorSample ι →
    EuclideanSpace ℝ ι :=
  sourceEulerNoise (CanonicalBrownian.vectorProbability ι)
    CanonicalBrownian.coordinate CanonicalBrownian.coordinate_isPreBrownian h

/-- Every reference field, including its stationary law, is derived from the
original potential assumptions on an explicit probability space. -/
def canonicalProductReference
    {μ : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure μ]
    (U : EuclideanSpace ℝ ι → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) (hLip : LipschitzWith L (gradient U))
    (hh : 0 < h) :
    ProductReference (CanonicalBrownian.vectorProbability ι) (Fintype.card ι)
      U h L hLip μ (gibbsMeasure U) (productGibbsMemLp U m hm hdiff hsc)
      (canonicalEulerNoise h) (sourceEulerNoise_memLp
        (CanonicalBrownian.vectorProbability ι) CanonicalBrownian.coordinate
        CanonicalBrownian.coordinate_isPreBrownian h) :=
  productReference_of_independent_brownian (CanonicalBrownian.vectorProbability ι)
    U m L hm hdiff hsc hLip CanonicalBrownian.coordinate
    CanonicalBrownian.coordinate_isPreBrownian
    (fun r _ ↦ CanonicalBrownian.coordinate_grid_paths_independent ι r.toNNReal) h hh

/-- Exact identification of the explicitly constructed source with ordinary
Gaussian ULA, for every finite-second-moment initial law. -/
theorem canonicalOutput_eq_ulaLawStep
    (U : EuclideanSpace ℝ ι → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) (hLip : LipschitzWith L (gradient U))
    (hh : 0 < h) (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hfinite : wasserstein2 μ (gibbsMeasure U) ≠ ⊤) (k : ℕ) :
    productOutputLaw (CanonicalBrownian.vectorProbability ι) U h μ
      (canonicalEulerNoise h) k = (ulaLawStep U h)^[k] μ := by
  obtain ⟨c, hc⟩ := exists_finiteCost_coupling μ (gibbsMeasure U) hfinite
  exact productBrownianOutput_eq_ulaLawStep (CanonicalBrownian.vectorProbability ι)
    c (ne_of_lt hc) (productGibbsMemLp U m hm hdiff hsc) U h L hLip
    CanonicalBrownian.coordinate CanonicalBrownian.coordinate_isPreBrownian hh
    (CanonicalBrownian.coordinate_grid_paths_independent ι h.toNNReal) k

/-- Output second moments and finite transport are conclusions, not additional
inputs needed to interpret the real Wasserstein bound. -/
theorem dalalyan_output_finite
    (U : EuclideanSpace ℝ ι → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) (hLip : LipschitzWith L (gradient U))
    (hh : 0 < h) (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hfinite : wasserstein2 μ (gibbsMeasure U) ≠ ⊤) (k : ℕ) :
    wasserstein2 ((ulaLawStep U h)^[k] μ) (gibbsMeasure U) ≠ ⊤ := by
  have hf := (canonicalProductReference U m h L hm hdiff hsc hLip hh
    (μ := μ)).output_finite (CanonicalBrownian.vectorProbability ι) hfinite k
  rwa [canonicalOutput_eq_ulaLawStep U m h L hm hdiff hsc hLip hh μ hfinite k] at hf

/-- Dalalyan's strongly convex ULA theorem, with all stochastic reference
obligations proved. The only analytic assumptions concern the potential itself. -/
theorem dalalyan [Nonempty ι]
    (U : EuclideanSpace ℝ ι → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) (hLip : LipschitzWith L (gradient U))
    (hh : 0 < h) (hsmall : h ≤ 2 / (m + (L : ℝ)))
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hfinite : wasserstein2 μ (gibbsMeasure U) ≠ ⊤) (k : ℕ) :
    wasserstein2Real ((ulaLawStep U h)^[k] μ) (gibbsMeasure U) ≤
      (1 - m * h) ^ k * wasserstein2Real μ (gibbsMeasure U) +
        (33 / 20 : ℝ) * ((L : ℝ) / m) * Real.sqrt (h * (Fintype.card ι : ℝ)) := by
  have hb := dalalyan_small_step_of_product_reference
    (CanonicalBrownian.vectorProbability ι) (Fintype.card ι) U m h L hdiff hsc hLip
    hm (strongConvex_le_lipschitz hdiff hsc hLip) hh hsmall
    (productGibbsMemLp U m hm hdiff hsc) (canonicalEulerNoise h)
    (sourceEulerNoise_memLp (CanonicalBrownian.vectorProbability ι)
      CanonicalBrownian.coordinate CanonicalBrownian.coordinate_isPreBrownian h)
    hfinite (canonicalProductReference U m h L hm hdiff hsc hLip hh) k
  rwa [canonicalOutput_eq_ulaLawStep U m h L hm hdiff hsc hLip hh μ hfinite k] at hb

/-- The other stable step-size branch of Dalalyan, with the same fully derived
reference and the exact initial Wasserstein distance. -/
theorem dalalyan_large_step [Nonempty ι]
    (U : EuclideanSpace ℝ ι → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) (hLip : LipschitzWith L (gradient U))
    (hh : 0 < h) (hlarge : 2 / (m + (L : ℝ)) ≤ h) (hstep : (L : ℝ) * h < 2)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hfinite : wasserstein2 μ (gibbsMeasure U) ≠ ⊤) (k : ℕ) :
    wasserstein2Real ((ulaLawStep U h)^[k] μ) (gibbsMeasure U) ≤
      ((L : ℝ) * h - 1) ^ k * wasserstein2Real μ (gibbsMeasure U) +
        ((33 / 20 : ℝ) * (L : ℝ) * h / (2 - (L : ℝ) * h)) *
          Real.sqrt (h * (Fintype.card ι : ℝ)) := by
  have hb := dalalyan_large_step_of_product_reference
    (CanonicalBrownian.vectorProbability ι) (Fintype.card ι) U m h L hdiff hsc hLip
    hm (strongConvex_le_lipschitz hdiff hsc hLip) hh hlarge hstep
    (productGibbsMemLp U m hm hdiff hsc) (canonicalEulerNoise h)
    (sourceEulerNoise_memLp (CanonicalBrownian.vectorProbability ι)
      CanonicalBrownian.coordinate CanonicalBrownian.coordinate_isPreBrownian h)
    hfinite (canonicalProductReference U m h L hm hdiff hsc hLip hh) k
  rwa [canonicalOutput_eq_ulaLawStep U m h L hm hdiff hsc hLip hh μ hfinite k] at hb

end ULA.Hilbert
