import WassersteinMixing.Parameters
import WassersteinMixing.LocalError
import UnadjustedLangevin.CanonicalULA

/-! # The actual stationary Brownian reference and Gaussian Euler chain

The two initial coordinates use the diagonal Gibbs coupling.  The independent
canonical Brownian source and the existing Langevin construction provide the
reference, its moment bounds, and the ordinary Gaussian ULA output law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace WassersteinMixing

/-- The concrete common probability space, including both equal initial coordinates. -/
abbrev ActualSpace (P : Parameters) :=
  (E P.dimension × E P.dimension) × ULA.CanonicalBrownian.VectorSample (Fin P.dimension)

/-- The initialization is the diagonal coupling of the actual Gibbs measure. -/
def diagonalGibbsCoupling (P : Parameters) (V : E P.dimension → ℝ) :
    ULA.Coupling (ULA.gibbsMeasure V) (ULA.gibbsMeasure V) where
  joint := (ULA.gibbsMeasure V).map (fun x ↦ (x, x))
  fst := by rw [Measure.map_map measurable_fst (by fun_prop)]; exact Measure.map_id
  snd := by rw [Measure.map_map measurable_snd (by fun_prop)]; exact Measure.map_id

theorem diagonalGibbsCoupling_cost (P : Parameters) (V : E P.dimension → ℝ) :
    ULA.couplingCost (diagonalGibbsCoupling P V).joint = 0 := by
  rw [ULA.couplingCost, diagonalGibbsCoupling,
    eLpNorm_map_measure (by fun_prop) (by fun_prop)]
  simp [Function.comp_def]

/-- The independent canonical Brownian extension of the diagonal Gibbs law. -/
def actualProbability (P : Parameters) (V : E P.dimension → ℝ) : Measure (ActualSpace P) :=
  ULA.initialExtension (diagonalGibbsCoupling P V)
    (ULA.CanonicalBrownian.vectorProbability (Fin P.dimension))

/-- The actual Gibbs law is normalized by strong convexity. -/
theorem actualTarget_isProbability (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) : IsProbabilityMeasure (ULA.gibbsMeasure V) :=
  ULA.isProbabilityMeasure_gibbsMeasure V P.alpha P.alpha_pos
    (hV.regularity.differentiable (by norm_num)) hV.strongConvexity

/-- The common Brownian comparison measure is a probability measure. -/
theorem actualProbability_isProbability (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) : IsProbabilityMeasure (actualProbability P V) := by
  let := actualTarget_isProbability P V hV
  exact ULA.initialExtension_isProbabilityMeasure _ _

/-- The finite second moment of the actual target, derived from the potential. -/
theorem actualTarget_memLp (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) : MemLp (id : E P.dimension → E P.dimension) 2
      (ULA.gibbsMeasure V) :=
  ULA.memLp_id_gibbsMeasure V P.alpha P.alpha_pos
    (hV.regularity.differentiable (by norm_num)) hV.strongConvexity

/-- The normalized Brownian increments used by the actual Gaussian Euler recursion. -/
def actualNoise (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) : ℕ → Lp (E P.dimension) 2 (actualProbability P V) := by
  letI := actualTarget_isProbability P V hV
  exact ULA.Hilbert.productNoise
    (ULA.CanonicalBrownian.vectorProbability (Fin P.dimension)) (diagonalGibbsCoupling P V)
    (ULA.Hilbert.canonicalEulerNoise P.step)
    (ULA.Hilbert.sourceEulerNoise_memLp _ ULA.CanonicalBrownian.coordinate
      ULA.CanonicalBrownian.coordinate_isPreBrownian P.step)

/-- The stationary Langevin reference is constructed by the existing canonical
Brownian theorem, rather than supplied as comparison data. -/
def actualReferenceData (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) :
    letI := actualProbability_isProbability P V hV
    ULA.Hilbert.L2Reference (actualProbability P V) (Fintype.card (Fin P.dimension)) V P.step
      ⟨P.beta, P.beta_pos.le⟩ hV.gradientLipschitz (actualNoise P V hV)
      (ULA.gibbsMeasure V) := by
  letI := actualTarget_isProbability P V hV
  letI := actualProbability_isProbability P V hV
  have hc : ULA.couplingCost (diagonalGibbsCoupling P V).joint ≠ ⊤ := by
    rw [diagonalGibbsCoupling_cost]; exact ENNReal.zero_ne_top
  exact (ULA.Hilbert.canonicalProductReference V P.alpha P.step
    ⟨P.beta, P.beta_pos.le⟩ P.alpha_pos (hV.regularity.differentiable (by norm_num))
    hV.strongConvexity hV.gradientLipschitz P.step_pos
    (μ := ULA.gibbsMeasure V)).reference (diagonalGibbsCoupling P V) hc

/-- The actual reference at an interior local time. -/
def actualSegment (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (n : ℕ) (s : ℝ) :
    Lp (E P.dimension) 2 (actualProbability P V) := by
  letI := actualProbability_isProbability P V hV
  exact (actualReferenceData P V hV).segment n s

/-- The actual stationary diffusion at the grid times. -/
def actualReference (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (n : ℕ) : Lp (E P.dimension) 2 (actualProbability P V) :=
  actualSegment P V hV n 0

/-- Its exact Gibbs law at every grid time. -/
theorem actualReference_stationary (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (n : ℕ) :
    (actualProbability P V).map (actualReference P V hV n) = ULA.gibbsMeasure V := by
  letI := actualProbability_isProbability P V hV
  exact (actualReferenceData P V hV).stationary n

/-- The selected continuous Brownian segment has the Gibbs law at every
interior time, not only at the stored grid knots. -/
theorem actualSegment_stationary (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 P.step) :
    (actualProbability P V).map (actualSegment P V hV n t) = ULA.gibbsMeasure V := by
  letI := actualTarget_isProbability P V hV
  letI := actualProbability_isProbability P V hV
  let c := diagonalGibbsCoupling P V
  let Q := ULA.CanonicalBrownian.vectorProbability (Fin P.dimension)
  let X := ULA.initialExtension_lpReference c Q (actualTarget_memLp P V hV)
  let W := fun i s (p : ActualSpace P) ↦ ULA.CanonicalBrownian.coordinate i s p.2
  have hW : ∀ i, IsPreBrownianReal (W i) (actualProbability P V) :=
    ULA.Hilbert.productPreBrownian Q c ULA.CanonicalBrownian.coordinate
      ULA.CanonicalBrownian.coordinate_isPreBrownian
  let T := ((n : ℝ) + 1) * P.step
  have hT : 0 ≤ T := mul_nonneg (by positivity) P.step_pos.le
  obtain ⟨Y, hY, _hY0, hYe, _⟩ := ULA.exists_lp_langevin_integral_of_brownian
    (actualProbability P V) V ⟨P.beta, P.beta_pos.le⟩ hV.gradientLipschitz X W hW 0 T le_rfl hT
  have heq := ULA.Hilbert.brownianSegments_eq_global (actualProbability P V) V
    ⟨P.beta, P.beta_pos.le⟩ hV.gradientLipschitz X W hW Y hY T hT hYe
    P.step P.step_pos.le n le_rfl
  change (actualProbability P V).map
    (ULA.Hilbert.brownianSegments (actualProbability P V) V ⟨P.beta, P.beta_pos.le⟩
      hV.gradientLipschitz W hW P.step P.step_pos.le X n t) = _
  rw [heq ht]
  have hscalar : ∀ r : ℝ, 0 < r → iIndepFun
      (fun p : ℕ × Fin P.dimension ↦ fun ω ↦
        ULA.Hilbert.brownianEulerNoise (actualProbability P V) W hW r p.1 ω p.2)
      (actualProbability P V) := by
    intro r hr
    have hs := ULA.Hilbert.productEulerNoise_independent Q c ULA.CanonicalBrownian.coordinate
      ULA.CanonicalBrownian.coordinate_isPreBrownian r hr
      (ULA.CanonicalBrownian.coordinate_grid_paths_independent (Fin P.dimension) r.toNNReal)
    simpa only [ULA.Hilbert.productNoise_eq_brownianEulerNoise, actualProbability, W, Q, c, X] using hs
  have hind : ∀ r : ℝ, 0 < r → IndepFun X
      (fun ω k ↦ ULA.Hilbert.brownianEulerNoise (actualProbability P V) W hW r k ω)
      (actualProbability P V) := by
    intro r _hr
    have hs := ULA.Hilbert.productEulerNoise_independentReference Q c
      (actualTarget_memLp P V hV) ULA.CanonicalBrownian.coordinate
      ULA.CanonicalBrownian.coordinate_isPreBrownian r
    simpa only [ULA.Hilbert.productNoise_eq_brownianEulerNoise, actualProbability, W, Q, c, X] using hs
  have hinitial : (actualProbability P V).map X = ULA.gibbsMeasure V :=
    ULA.initialExtension_lpReference_law c Q (actualTarget_memLp P V hV)
  have hs : 0 ≤ (n : ℝ) * P.step + t :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) P.step_pos.le) ht.1
  have hsT : (n : ℝ) * P.step + t ≤ T := by dsimp [T]; nlinarith [ht.2]
  exact ULA.lp_langevin_gibbs_stationary (actualProbability P V) V P.alpha
    ⟨P.beta, P.beta_pos.le⟩ P.alpha_pos (hV.regularity.differentiable (by norm_num))
    hV.strongConvexity hV.gradientLipschitz X hinitial W hW hscalar hind Y hY
    ((n : ℝ) * P.step + t) hs (fun s hs ↦ hYe s ⟨hs.1, hs.2.trans hsT⟩)

/-- The actual Euler initialization, using the same diagonal Gibbs coupling. -/
def actualInitial (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) : Lp (E P.dimension) 2 (actualProbability P V) := by
  letI := actualTarget_isProbability P V hV
  have hc : ULA.couplingCost (diagonalGibbsCoupling P V).joint ≠ ⊤ := by
    rw [diagonalGibbsCoupling_cost]; exact ENNReal.zero_ne_top
  exact ULA.initialExtension_lpInitial (diagonalGibbsCoupling P V)
    (ULA.CanonicalBrownian.vectorProbability (Fin P.dimension)) hc (actualTarget_memLp P V hV)

/-- The actual Gaussian Euler chain on the common Brownian extension. -/
def actualChain (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (n : ℕ) : Lp (E P.dimension) 2 (actualProbability P V) := by
  letI := actualProbability_isProbability P V hV
  exact ULA.Hilbert.lpChain (actualProbability P V) V P.step hV.gradientLipschitz
    (actualInitial P V hV) (actualNoise P V hV) n

/-- The diagonal initialization gives literal equality of the two `L²` states. -/
theorem actual_initial_equal (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) : actualReference P V hV 0 = actualChain P V hV 0 := by
  let := actualTarget_isProbability P V hV
  let := actualProbability_isProbability P V hV
  let Q := ULA.CanonicalBrownian.vectorProbability (Fin P.dimension)
  let c := diagonalGibbsCoupling P V
  have hc : ULA.couplingCost c.joint ≠ ⊤ := by
    rw [diagonalGibbsCoupling_cost]; exact ENNReal.zero_ne_top
  have hstart := (ULA.Hilbert.canonicalProductReference V P.alpha P.step
    ⟨P.beta, P.beta_pos.le⟩ P.alpha_pos (hV.regularity.differentiable (by norm_num))
    hV.strongConvexity hV.gradientLipschitz P.step_pos
    (μ := ULA.gibbsMeasure V)).start c hc
  have hcost := ULA.initialExtension_lp_cost c Q hc (actualTarget_memLp P V hV)
  rw [diagonalGibbsCoupling_cost] at hcost
  simp only [ENNReal.toReal_zero, norm_eq_zero, sub_eq_zero] at hcost
  exact hstart.trans hcost.symm

/-- The constructed chain has exactly the existing independent-Gaussian ULA
law at every iteration, initialized at the Gibbs measure. -/
theorem actualChain_law (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (n : ℕ) :
    (actualProbability P V).map (actualChain P V hV n) =
      (ULA.ulaLawStep V P.step)^[n] (ULA.gibbsMeasure V) := by
  let := actualTarget_isProbability P V hV
  let := actualProbability_isProbability P V hV
  let Q := ULA.CanonicalBrownian.vectorProbability (Fin P.dimension)
  let c := diagonalGibbsCoupling P V
  have hc : ULA.couplingCost c.joint ≠ ⊤ := by
    rw [diagonalGibbsCoupling_cost]; exact ENNReal.zero_ne_top
  have hchain := ULA.Hilbert.product_chain_outputLaw Q c hc (actualTarget_memLp P V hV)
    V P.step ⟨P.beta, P.beta_pos.le⟩ hV.gradientLipschitz (ULA.Hilbert.canonicalEulerNoise P.step)
    (ULA.Hilbert.sourceEulerNoise_memLp Q ULA.CanonicalBrownian.coordinate
      ULA.CanonicalBrownian.coordinate_isPreBrownian P.step) n
  have hout := ULA.Hilbert.productBrownianOutput_eq_ulaLawStep Q c hc
    (actualTarget_memLp P V hV) V P.step ⟨P.beta, P.beta_pos.le⟩ hV.gradientLipschitz
    ULA.CanonicalBrownian.coordinate ULA.CanonicalBrownian.coordinate_isPreBrownian
    P.step_pos (ULA.CanonicalBrownian.coordinate_grid_paths_independent
      (Fin P.dimension) P.step.toNNReal) n
  exact hchain.trans hout

end WassersteinMixing
