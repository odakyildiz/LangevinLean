import WassersteinMixing.ActualCurvature
import WassersteinMixing.SemigroupGlobal
import UnadjustedLangevin.WeakForwardAdapted
import Mathlib.Probability.Process.Filtration

/-! # Actual adaptation to the canonical Brownian past

The filtration contains the actual initial state and all actual Brownian
increments up to the grid time.  Adaptation of the constructed Langevin
solution follows from uniqueness in invariant measurable `L²` subspaces.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace WassersteinMixing

variable (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V)

/-- The actual additive Brownian input measured from time zero. -/
def actualBrownianNoise (t : ℝ) : Lp (E P.dimension) 2 (actualProbability P V) :=
  ULA.brownianLangevinNoise (actualProbability P V) (CanonicalSemigroup.brownian P)
    (CanonicalSemigroup.brownian_preBrownian P V hV) 0 t

/-- The actual initialization agrees with the reference-side Gibbs variable. -/
theorem actualInitial_eq_semigroupInitial :
    actualInitial P V hV = CanonicalSemigroup.initial P V hV := by
  let := actualTarget_isProbability P V hV
  let c := diagonalGibbsCoupling P V
  let Q := ULA.CanonicalBrownian.vectorProbability (Fin P.dimension)
  have hc : ULA.couplingCost c.joint ≠ ⊤ := by
    rw [diagonalGibbsCoupling_cost]; exact ENNReal.zero_ne_top
  have he := ULA.initialExtension_lp_cost c Q hc (actualTarget_memLp P V hV)
  rw [diagonalGibbsCoupling_cost] at he
  simp only [ENNReal.toReal_zero, norm_eq_zero, sub_eq_zero] at he
  change actualInitial P V hV = CanonicalSemigroup.initial P V hV at he
  exact he

/-- The actual grid knot equals the endpoint of any sufficiently long
canonical solution, with no path-identification assumption. -/
theorem actualReference_eq_solutionOn (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (hn : (n : ℝ) * P.step ≤ T) :
    actualReference P V hV n = CanonicalSemigroup.solutionOn P V hV T hT ((n : ℝ) * P.step) := by
  let := actualTarget_isProbability P V hV
  let := actualProbability_isProbability P V hV
  have hs := CanonicalSemigroup.solutionOn_spec P V hV T hT
  change ULA.Hilbert.brownianSegments (actualProbability P V) V ⟨P.beta, P.beta_pos.le⟩
    hV.gradientLipschitz (CanonicalSemigroup.brownian P)
    (CanonicalSemigroup.brownian_preBrownian P V hV) P.step P.step_pos.le
    (CanonicalSemigroup.initial P V hV) n 0 = _
  rw [ULA.Hilbert.brownianSegments_start]
  exact ULA.Hilbert.brownianKnots_eq_global (actualProbability P V) V ⟨P.beta, P.beta_pos.le⟩
    hV.gradientLipschitz (CanonicalSemigroup.initial P V hV) (CanonicalSemigroup.brownian P)
    (CanonicalSemigroup.brownian_preBrownian P V hV) _ hs.1 T hT hs.2.2
    P.step P.step_pos.le n hn

/-- The canonical Brownian past at the grid time `n h`. -/
@[instance_reducible] def actualPast (n : ℕ) : MeasurableSpace (ActualSpace P) :=
  ULA.lpLangevinPast (actualProbability P V) (CanonicalSemigroup.initial P V hV)
    (actualBrownianNoise P V hV) ((n : ℝ) * P.step)

theorem actualPast_le (n : ℕ) : actualPast P V hV n ≤ (inferInstance : MeasurableSpace (ActualSpace P)) :=
  ULA.lpLangevinPast_le _ _ _ _

theorem actualPast_mono : Monotone (actualPast P V hV) := by
  intro n m hnm
  have ht : (n : ℝ) * P.step ≤ (m : ℝ) * P.step :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hnm) P.step_pos.le
  apply sup_le le_sup_left
  apply iSup_le
  intro s
  have hs : (s : ℝ) ∈ Icc 0 ((m : ℝ) * P.step) := ⟨s.property.1, s.property.2.trans ht⟩
  exact (le_iSup (fun t : Icc 0 ((m : ℝ) * P.step) ↦
    (inferInstance : MeasurableSpace (E P.dimension)).comap (actualBrownianNoise P V hV t)) ⟨s, hs⟩).trans le_sup_right

/-- The actual increasing filtration, built from the genuine Brownian past. -/
def actualFiltration : Filtration ℕ (inferInstance : MeasurableSpace (ActualSpace P)) where
  seq := actualPast P V hV
  mono' := actualPast_mono P V hV
  le' := actualPast_le P V hV

/-- The actual stationary reference is adapted to the canonical Brownian past. -/
theorem actualReference_adapted (n : ℕ) :
    AEStronglyMeasurable[actualPast P V hV n] (actualReference P V hV n) (actualProbability P V) := by
  let := actualProbability_isProbability P V hV
  let T := (n : ℝ) * P.step
  have hT : 0 ≤ T := mul_nonneg (Nat.cast_nonneg n) P.step_pos.le
  have hs := CanonicalSemigroup.solutionOn_spec P V hV T hT
  have ha := ULA.lp_langevin_integral_naturalPast (actualProbability P V) V
    ⟨P.beta, P.beta_pos.le⟩ hV.gradientLipschitz (CanonicalSemigroup.initial P V hV)
    (actualBrownianNoise P V hV) (CanonicalSemigroup.solutionOn P V hV T hT)
    (ULA.brownianLangevinNoise_continuous _ _ _ _) (ULA.brownianLangevinNoise_zero _ _ _ _)
    hs.1 T hT hs.2.2 T ⟨hT, le_rfl⟩
  rw [actualReference_eq_solutionOn P V hV n T hT le_rfl]
  exact ha

/-- The normalized Euler innovation is the exact difference of the global
Brownian input at the two adjacent grid times. -/
theorem actualNoise_eq_global_increment (n : ℕ) :
    actualNoise P V hV n = (Real.sqrt (2 * P.step))⁻¹ •
      (actualBrownianNoise P V hV (((n + 1 : ℕ) : ℝ) * P.step) -
        actualBrownianNoise P V hV ((n : ℝ) * P.step)) := by
  let := actualTarget_isProbability P V hV
  unfold actualNoise
  rw [ULA.Hilbert.productNoise_eq_brownianEulerNoise]
  change (Real.sqrt (2 * P.step))⁻¹ •
    ULA.brownianLangevinNoise (actualProbability P V) (CanonicalSemigroup.brownian P)
      (CanonicalSemigroup.brownian_preBrownian P V hV) ((n : ℝ) * P.step) P.step = _
  have hi := ULA.brownianLangevinNoise_increment (actualProbability P V)
    (CanonicalSemigroup.brownian P) (CanonicalSemigroup.brownian_preBrownian P V hV)
    ((n : ℝ) * P.step) P.step
  have ht : (n : ℝ) * P.step + P.step = ((n + 1 : ℕ) : ℝ) * P.step := by push_cast; ring
  rw [ht] at hi
  exact congrArg (fun u ↦ (Real.sqrt (2 * P.step))⁻¹ • u) hi.symm

/-- The true innovation over a step is measurable by the end of that step. -/
theorem actualNoise_adapted (n : ℕ) :
    AEStronglyMeasurable[actualPast P V hV (n + 1)] (actualNoise P V hV n) (actualProbability P V) := by
  let := actualProbability_isProbability P V hV
  let T := ((n + 1 : ℕ) : ℝ) * P.step
  have hT : 0 ≤ T := mul_nonneg (Nat.cast_nonneg _) P.step_pos.le
  have ht : (n : ℝ) * P.step ∈ Icc 0 T := by
    refine ⟨mul_nonneg (Nat.cast_nonneg _) P.step_pos.le, ?_⟩
    dsimp [T]; push_cast; nlinarith [P.step_pos]
  have hB₁ := ULA.lpLangevinPast_noise (actualProbability P V) (CanonicalSemigroup.initial P V hV)
    (actualBrownianNoise P V hV) T T ⟨hT, le_rfl⟩
  have hB₀ := ULA.lpLangevinPast_noise (actualProbability P V) (CanonicalSemigroup.initial P V hV)
    (actualBrownianNoise P V hV) T ((n : ℝ) * P.step) ht
  letI : Fact (actualPast P V hV (n + 1) ≤ (inferInstance : MeasurableSpace (ActualSpace P))) :=
    ⟨actualPast_le P V hV _⟩
  let M := lpMeas (E P.dimension) ℝ (actualPast P V hV (n + 1)) 2 (actualProbability P V)
  have hm₁ : actualBrownianNoise P V hV T ∈ M := mem_lpMeas_iff_aestronglyMeasurable.mpr hB₁
  have hm₀ : actualBrownianNoise P V hV ((n : ℝ) * P.step) ∈ M :=
    mem_lpMeas_iff_aestronglyMeasurable.mpr hB₀
  rw [actualNoise_eq_global_increment]
  exact mem_lpMeas_iff_aestronglyMeasurable.mp
    (M.smul_mem _ (M.sub_mem hm₁ hm₀))

/-- The actual Euler chain is adapted, by its genuine recursion and the
measurability of the actual Brownian innovations. -/
theorem actualChain_adapted (n : ℕ) :
    AEStronglyMeasurable[actualPast P V hV n] (actualChain P V hV n) (actualProbability P V) := by
  let := actualProbability_isProbability P V hV
  induction n with
  | zero =>
    change AEStronglyMeasurable[actualPast P V hV 0] (actualInitial P V hV) _
    rw [actualInitial_eq_semigroupInitial]
    exact ULA.lpLangevinPast_initial _ _ _ _
  | succ n ih =>
    letI : Fact (actualPast P V hV (n + 1) ≤ (inferInstance : MeasurableSpace (ActualSpace P))) :=
      ⟨actualPast_le P V hV _⟩
    let M := lpMeas (E P.dimension) ℝ (actualPast P V hV (n + 1)) 2 (actualProbability P V)
    have hx : AEStronglyMeasurable[actualPast P V hV (n + 1)] (actualChain P V hV n)
        (actualProbability P V) := AEStronglyMeasurable.mono (actualPast_mono P V hV (Nat.le_succ n)) ih
    have hg := ULA.lpDrift_aestronglyMeasurable (actualPast P V hV (n + 1))
      (actualProbability P V) (gradient V) ⟨P.beta, P.beta_pos.le⟩ hV.gradientLipschitz
      (actualChain P V hV n) hx
    have hxM : actualChain P V hV n ∈ M := mem_lpMeas_iff_aestronglyMeasurable.mpr hx
    have hgM : ULA.lpDrift (actualProbability P V) (gradient V) hV.gradientLipschitz
        (actualChain P V hV n) ∈ M := mem_lpMeas_iff_aestronglyMeasurable.mpr hg
    have hnM : actualNoise P V hV n ∈ M :=
      mem_lpMeas_iff_aestronglyMeasurable.mpr (actualNoise_adapted P V hV n)
    exact mem_lpMeas_iff_aestronglyMeasurable.mp
      (M.add_mem (M.sub_mem hxM (M.smul_mem P.step hgM))
        (M.smul_mem (Real.sqrt (2 * P.step)) hnM))

/-- The actual synchronous error is adapted to the same Brownian past. -/
theorem actualError_adapted (n : ℕ) :
    AEStronglyMeasurable[actualPast P V hV n]
      (actualReference P V hV n - actualChain P V hV n) (actualProbability P V) := by
  letI : Fact (actualPast P V hV n ≤ (inferInstance : MeasurableSpace (ActualSpace P))) :=
    ⟨actualPast_le P V hV _⟩
  let M := lpMeas (E P.dimension) ℝ (actualPast P V hV n) 2 (actualProbability P V)
  exact mem_lpMeas_iff_aestronglyMeasurable.mp (M.sub_mem
    (mem_lpMeas_iff_aestronglyMeasurable.mpr (actualReference_adapted P V hV n))
    (mem_lpMeas_iff_aestronglyMeasurable.mpr (actualChain_adapted P V hV n)))

/-- The actual averaged Hessian preserves the actual canonical past. -/
theorem actualCurvature_preserves_past (n : ℕ)
    (u : Lp (E P.dimension) 2 (actualProbability P V))
    (hu : AEStronglyMeasurable[actualPast P V hV n] u (actualProbability P V)) :
    AEStronglyMeasurable[actualPast P V hV n] (actualCurvature P V hV n u) (actualProbability P V) :=
  actualCurvature_adapted P V hV _ n u (actualReference_adapted P V hV n)
    (actualChain_adapted P V hV n) hu

end WassersteinMixing
