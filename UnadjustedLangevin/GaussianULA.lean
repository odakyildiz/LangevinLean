import UnadjustedLangevin.CanonicalULA

set_option linter.style.header false

/-! # Dalalyan for the actual Gaussian ULA recursion

All scalar Gaussian laws and all coordinate/time independence are used to
identify the actual `L²` chain law. The initial second moment comes from its
`L²` representation; the Gibbs moment comes from strong convexity. Their
independent product proves finite initial Wasserstein distance. No reference,
stationarity, normalization, or extra potential regularity is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ULA.Hilbert
open ULA

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
  (P : Measure Ω) [IsProbabilityMeasure P]

private theorem initialLaw_probability (initial : Lp (EuclideanSpace ℝ ι) 2 P) :
    IsProbabilityMeasure (P.map initial) := by
  constructor
  rw [Measure.map_apply_of_aemeasurable (Lp.aestronglyMeasurable initial).aemeasurable
    MeasurableSet.univ, Set.preimage_univ, measure_univ]

/-- Finite initial quadratic transport follows from the actual initialization
and the original strongly convex potential assumptions. -/
theorem gaussianULA_initial_transport_finite
    (U : EuclideanSpace ℝ ι → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (initial : Lp (EuclideanSpace ℝ ι) 2 P) :
    wasserstein2 (P.map initial) (gibbsMeasure U) ≠ ⊤ := by
  have := initialLaw_probability P initial
  have := isProbabilityMeasure_gibbsMeasure U m hm hdiff hsc
  have hμ : MemLp (fun x : EuclideanSpace ℝ ι ↦ x) 2 (P.map initial) :=
    (memLp_map_measure_iff (by fun_prop)
      (Lp.aestronglyMeasurable initial).aemeasurable).mpr (Lp.memLp initial)
  exact wasserstein2_ne_top_of_memLp (P.map initial) (gibbsMeasure U) hμ
    (memLp_id_gibbsMeasure U m hm hdiff hsc)

/-- Dalalyan's small-step theorem for the actual Gaussian ULA implementation.
Only the displayed potential/step assumptions and the algorithm's ordinary
Gaussian laws and independence assumptions are inputs. -/
theorem dalalyan_of_gaussian_innovations
    (U : EuclideanSpace ℝ ι → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) (hLip : LipschitzWith L (gradient U))
    (hh : 0 < h) (hsmall : h ≤ 2 / (m + (L : ℝ)))
    (initial : Lp (EuclideanSpace ℝ ι) 2 P)
    (noise : ℕ → Lp (EuclideanSpace ℝ ι) 2 P)
    (hcoord : ∀ n i, HasLaw (fun ω ↦ noise n ω i) (gaussianReal 0 1) P)
    (hind : iIndepFun (fun p : ℕ × ι ↦ fun ω ↦ noise p.1 ω p.2) P)
    (hindinitial : IndepFun initial (fun ω n ↦ noise n ω) P) (k : ℕ) :
    wasserstein2Real (P.map (lpChain P U h hLip initial noise k)) (gibbsMeasure U) ≤
      (1 - m * h) ^ k * wasserstein2Real (P.map initial) (gibbsMeasure U) +
        (33 / 20 : ℝ) * ((L : ℝ) / m) * Real.sqrt (h * (Fintype.card ι : ℝ)) := by
  have := initialLaw_probability P initial
  have hW (n : ℕ) : AEMeasurable (noise n) P :=
    (Lp.aestronglyMeasurable _).aemeasurable
  rw [hilbert_lpChain_law_eq_ulaLawStep P U h L hLip initial noise hindinitial
    (gaussianInnovations_vectorIndependent P (fun n ω ↦ noise n ω) hW hcoord hind)
    (gaussianInnovations_vectorLaw P (fun n ω ↦ noise n ω) hW hcoord hind)]
  exact dalalyan U m h L hm hdiff hsc hLip hh hsmall (P.map initial)
    (gaussianULA_initial_transport_finite P U m hm hdiff hsc initial) k

/-- Dalalyan's other stable step-size branch for the same actual Gaussian
implementation, with all reference obligations already proved. -/
theorem dalalyan_large_step_of_gaussian_innovations
    (U : EuclideanSpace ℝ ι → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) (hLip : LipschitzWith L (gradient U))
    (hh : 0 < h) (hlarge : 2 / (m + (L : ℝ)) ≤ h) (hstep : (L : ℝ) * h < 2)
    (initial : Lp (EuclideanSpace ℝ ι) 2 P)
    (noise : ℕ → Lp (EuclideanSpace ℝ ι) 2 P)
    (hcoord : ∀ n i, HasLaw (fun ω ↦ noise n ω i) (gaussianReal 0 1) P)
    (hind : iIndepFun (fun p : ℕ × ι ↦ fun ω ↦ noise p.1 ω p.2) P)
    (hindinitial : IndepFun initial (fun ω n ↦ noise n ω) P) (k : ℕ) :
    wasserstein2Real (P.map (lpChain P U h hLip initial noise k)) (gibbsMeasure U) ≤
      ((L : ℝ) * h - 1) ^ k * wasserstein2Real (P.map initial) (gibbsMeasure U) +
        ((33 / 20 : ℝ) * (L : ℝ) * h / (2 - (L : ℝ) * h)) *
          Real.sqrt (h * (Fintype.card ι : ℝ)) := by
  have := initialLaw_probability P initial
  have hW (n : ℕ) : AEMeasurable (noise n) P :=
    (Lp.aestronglyMeasurable _).aemeasurable
  rw [hilbert_lpChain_law_eq_ulaLawStep P U h L hLip initial noise hindinitial
    (gaussianInnovations_vectorIndependent P (fun n ω ↦ noise n ω) hW hcoord hind)
    (gaussianInnovations_vectorLaw P (fun n ω ↦ noise n ω) hW hcoord hind)]
  exact dalalyan_large_step U m h L hm hdiff hsc hLip hh hlarge hstep (P.map initial)
    (gaussianULA_initial_transport_finite P U m hm hdiff hsc initial) k

end ULA.Hilbert
