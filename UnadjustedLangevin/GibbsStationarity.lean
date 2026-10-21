import UnadjustedLangevin.EulerLimit
import UnadjustedLangevin.ProductBrownian
import UnadjustedLangevin.MarkovLaw
import UnadjustedLangevin.MALAInvariance
import UnadjustedLangevin.CouplingLimit
import UnadjustedLangevin.GaussianInnovationVectors

set_option linter.style.header false

/-! # Gibbs stationarity of the actual additive-noise Langevin solution

The matching-noise Euler approximations converge in `L²`. Their actual iid
Gaussian recursion laws are coupled to the exactly stationary Metropolis
chain; the rejection error tends to zero on a refining uniform mesh. This
proves the law of the integral solution itself, without an assumed invariant
law, Itô formula, or forward-equation uniqueness.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ULA

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- Quotient representatives of the Hilbert-space Euler chain implement the
ordinary pointwise recursion almost everywhere. -/
theorem hilbert_lpChain_coe (U : H → ℝ) (h : ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U)) (initial : Lp H 2 P)
    (W : ℕ → Lp H 2 P) (n : ℕ) :
    Hilbert.lpChain P U h hLip initial W n =ᵐ[P] fun ω ↦
      noiseDrivenChain (Hilbert.pointwiseUpdate U h) (initial ω) (fun k ↦ W k ω) n := by
  induction n with
  | zero => exact ae_of_all _ fun _ ↦ rfl
  | succ n ih =>
    filter_upwards [lpUlaUpdate_coe P U h hLip
      (Hilbert.lpChain P U h hLip initial W n) (W n), ih] with ω hup hprev
    simpa only [Hilbert.lpChain_succ, noiseDrivenChain_succ,
      Hilbert.pointwiseUpdate, hprev] using hup

/-- The proved iid realization theorem identifies the actual `L²` chain law
with iterations of the ordinary ULA transition. -/
theorem hilbert_lpChain_law_eq_ulaLawStep [FiniteDimensional ℝ H]
    (U : H → ℝ) (h : ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (initial : Lp H 2 P) (W : ℕ → Lp H 2 P)
    (hind : IndepFun initial (fun ω n ↦ W n ω) P)
    (hiid : iIndepFun (fun n ω ↦ W n ω) P)
    (hlaw : ∀ n, P.map (W n) = stdGaussian H) (n : ℕ) :
    P.map (Hilbert.lpChain P U h hLip initial W n) =
      (ulaLawStep U h)^[n] (P.map initial) := by
  rw [Measure.map_congr (hilbert_lpChain_coe P U h L hLip initial W n),
    noiseDrivenChain_law_eq_markovLaws P (Hilbert.pointwiseUpdate U h)
      (Hilbert.pointwiseUpdate_measurable U h L hLip)
      initial (fun n ω ↦ W n ω) (Lp.aestronglyMeasurable initial).aemeasurable
      (fun n ↦ (Lp.aestronglyMeasurable (W n)).aemeasurable)
      hind hiid (stdGaussian H) hlaw n]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [markovLaws, ih, Function.iterate_succ_apply']
    rfl

/-- Exact-noise Banach Euler and the actual Hilbert `L²` Euler chain agree. -/
theorem additiveEulerChain_eq_hilbert_lpChain
    (U : H → ℝ) (h : ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (initial : Lp H 2 P) (B : ℝ → Lp H 2 P) (W : ℕ → Lp H 2 P)
    (hincrement : ∀ k : ℕ, B (((k + 1 : ℕ) : ℝ) * h) - B ((k : ℝ) * h) =
      Real.sqrt (2 * h) • W k) (n : ℕ) :
    additiveEulerChain (lpDrift P (gradient U) hLip) h initial B n =
      Hilbert.lpChain P U h hLip initial W n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [additiveEulerChain_succ, Hilbert.lpChain_succ, ih, hincrement n]
    rfl

section Brownian

variable {ι : Type*} [Fintype ι]

/-- The unshifted cumulative Brownian input has exactly the segment increments
used in the Euler normalization. -/
theorem brownianLangevinNoise_grid_increment
    (B : ι → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P)
    (h : ℝ) (k : ℕ) :
    brownianLangevinNoise P B hB 0 (((k + 1 : ℕ) : ℝ) * h) -
      brownianLangevinNoise P B hB 0 ((k : ℝ) * h) =
      brownianLangevinNoise P B hB ((k : ℝ) * h) h := by
  unfold brownianLangevinNoise
  simp only [zero_add]
  rw [show (((k + 1 : ℕ) : ℝ) * h) = (k : ℝ) * h + h by push_cast; ring]
  module

/-- Matching-noise Euler for the cumulative Brownian input is the exact
already-defined normalized Brownian Euler chain. -/
theorem brownian_additiveEulerChain_eq_lpChain
    (U : EuclideanSpace ℝ ι → ℝ) (h : ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U))
    (initial : Lp (EuclideanSpace ℝ ι) 2 P)
    (B : ι → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hh : 0 < h) (n : ℕ) :
    additiveEulerChain (lpDrift P (gradient U) hLip) h initial
      (brownianLangevinNoise P B hB 0) n =
      Hilbert.lpChain P U h hLip initial (Hilbert.brownianEulerNoise P B hB h) n := by
  apply additiveEulerChain_eq_hilbert_lpChain
  intro k
  rw [brownianLangevinNoise_grid_increment,
    Hilbert.brownianEulerNoise_endpoint P B hB h hh k]

/-- Scalar Gaussian coordinate laws and independence supply the vector-valued
iid law needed by the actual Markov recursion. -/
theorem brownianEulerNoise_vectorGaussian
    (B : ι → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P)
    (h : ℝ) (hh : 0 < h)
    (hind : iIndepFun (fun p : ℕ × ι ↦ fun ω ↦
      Hilbert.brownianEulerNoise P B hB h p.1 ω p.2) P) :
    iIndepFun (fun n ω ↦ Hilbert.brownianEulerNoise P B hB h n ω) P ∧
      ∀ n, P.map (Hilbert.brownianEulerNoise P B hB h n) =
        stdGaussian (EuclideanSpace ℝ ι) := by
  have hW (n : ℕ) : AEMeasurable
      (Hilbert.brownianEulerNoise P B hB h n) P :=
    (Lp.aestronglyMeasurable _).aemeasurable
  have hc (n : ℕ) (i : ι) : HasLaw
      (fun ω ↦ Hilbert.brownianEulerNoise P B hB h n ω i) (gaussianReal 0 1) P :=
    Hilbert.sourceEulerNoise_coordinateLaw P B hB h hh n i
  exact ⟨gaussianInnovations_vectorIndependent P _ hW hc hind,
    gaussianInnovations_vectorLaw P _ hW hc hind⟩

/-- Every continuous `L²` integral solution driven by ordinary independent
Brownian Euler innovations preserves its initial Gibbs law. The two noise
independence premises describe only the supplied Brownian realization; they
are proved automatically on the canonical initial/Brownian product space.
There is no invariance, forward-equation, or moment hypothesis. -/
theorem lp_langevin_gibbs_stationary
    (U : EuclideanSpace ℝ ι → ℝ) (m : ℝ) (L : ℝ≥0) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (hLip : LipschitzWith L (gradient U))
    (initial : Lp (EuclideanSpace ℝ ι) 2 P)
    (hinitial : P.map initial = gibbsMeasure U)
    (B : ι → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hscalar : ∀ h : ℝ, 0 < h → iIndepFun (fun p : ℕ × ι ↦ fun ω ↦
      Hilbert.brownianEulerNoise P B hB h p.1 ω p.2) P)
    (hind : ∀ h : ℝ, 0 < h → IndepFun initial
      (fun ω n ↦ Hilbert.brownianEulerNoise P B hB h n ω) P)
    (Y : ℝ → Lp (EuclideanSpace ℝ ι) 2 P) (hY : Continuous Y)
    (T : ℝ) (hT : 0 ≤ T)
    (hYe : ∀ t ∈ Icc 0 T, Y t - initial =
      -(∫ s in 0..t, lpDrift P (gradient U) hLip (Y s)) +
        brownianLangevinNoise P B hB 0 t) :
    P.map (Y T) = gibbsMeasure U := by
  by_cases hTzero : T = 0
  · subst T
    have hY0 : Y 0 = initial := by
      simpa only [intervalIntegral.integral_same, neg_zero,
        brownianLangevinNoise_zero, add_zero, sub_eq_zero] using hYe 0 ⟨le_rfl, le_rfl⟩
    rw [hY0, hinitial]
  have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hTzero)
  have hπ := isProbabilityMeasure_gibbsMeasure U m hm hdiff hsc
  have hmesh : Tendsto (fun n : ℕ ↦ T / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_const_div_atTop_nhds_zero_nat T)
  have hmL : 0 < m + (L : ℝ) := add_pos_of_pos_of_nonneg hm L.coe_nonneg
  have hsmallpos : 0 < min (1 : ℝ) (2 / (m + (L : ℝ))) := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hmesh.eventually (gt_mem_nhds hsmallpos))
  let step : ℕ → ℝ := fun n ↦ T / ((n + N + 1 : ℕ) : ℝ)
  have hstep (n : ℕ) : 0 < step n := by dsimp [step]; positivity
  have hsmall (n : ℕ) : step n ≤ min (1 : ℝ) (2 / (m + (L : ℝ))) :=
    (hN (n + N) (by omega)).le
  have h1 (n : ℕ) : step n ≤ 1 := (hsmall n).trans (min_le_left _ _)
  have hstable (n : ℕ) : step n ≤ 2 / (m + (L : ℝ)) :=
    (hsmall n).trans (min_le_right _ _)
  have hstationary (n : ℕ) : malaOneStep U (step n) (gibbsMeasure U) = gibbsMeasure U :=
    malaOneStep_gibbs_invariant U (step n) L (hstep n) hdiff hLip
  let Xn : ℕ → Lp (EuclideanSpace ℝ ι) 2 P := fun n ↦
    Hilbert.lpChain P U (step n) hLip initial
      (Hilbert.brownianEulerNoise P B hB (step n)) (n + N + 1)
  let ρ : ℕ → Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) := fun n ↦
    malaCoupledChain U (step n) (gibbsMeasure U) (n + N + 1)
  have hρ (n : ℕ) : IsProbabilityMeasure (ρ n) :=
    malaCoupledChain_isProbability U (step n) L hdiff hLip (gibbsMeasure U) (n + N + 1)
  letI : ∀ n, IsProbabilityMeasure (ρ n) := hρ
  have hX : Tendsto Xn atTop (𝓝 (Y T)) := by
    have he := lp_langevin_integral_euler_tendsto P U L hLip initial
      (brownianLangevinNoise P B hB 0) Y (brownianLangevinNoise_zero P B hB 0)
      hY T hT hYe
    apply (he.comp (tendsto_add_atTop_nat N)).congr'
    exact Eventually.of_forall fun n ↦
      brownian_additiveEulerChain_eq_lpChain P U (step n) L hLip initial B hB
        (hstep n) (n + N + 1)
  have hfst (n : ℕ) : (ρ n).map Prod.fst = P.map (Xn n) := by
    obtain ⟨hiid, hlaw⟩ := brownianEulerNoise_vectorGaussian P B hB (step n) (hstep n)
      (hscalar (step n) (hstep n))
    dsimp only [ρ, Xn]
    rw [malaCoupledChain_fst U (step n) L hdiff hLip,
      hilbert_lpChain_law_eq_ulaLawStep P U (step n) L hLip initial
        (Hilbert.brownianEulerNoise P B hB (step n))
        (hind (step n) (hstep n)) hiid hlaw, hinitial]
  have hsnd (n : ℕ) : (ρ n).map Prod.snd = gibbsMeasure U :=
    malaCoupledChain_snd U (step n) L hdiff hLip (gibbsMeasure U)
      (hstationary n) (n + N + 1)
  have hint (n : ℕ) : Integrable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦
      ‖p.1 - p.2‖) (ρ n) :=
    malaCoupledChain_distance_integrable U m (step n) L hm (hstep n) (h1 n)
      (hstable n) hdiff hsc hLip (hstationary n) (n + N + 1)
  have hbound (n : ℕ) :
      (∫ p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, ‖p.1 - p.2‖ ∂ρ n) ≤
        (T * malaRejectionConstant U L) * Real.sqrt (step n) := by
    calc
      _ ≤ ((n + N + 1 : ℕ) : ℝ) * malaRejectionConstant U L * step n *
          Real.sqrt (step n) :=
        malaCoupledChain_distance_integral_le U m (step n) L hm (hstep n) (h1 n)
          (hstable n) hdiff hsc hLip (hstationary n) (n + N + 1)
      _ = _ := by dsimp [step]; field_simp
  have hstepzero : Tendsto step atTop (𝓝 0) := hmesh.comp (tendsto_add_atTop_nat N)
  have hcost : Tendsto (fun n ↦ ∫ p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι,
      ‖p.1 - p.2‖ ∂ρ n) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) hbound
    simpa only [Function.comp_apply, Real.sqrt_zero, mul_zero] using
      ((Real.continuous_sqrt.tendsto 0).comp hstepzero).const_mul (T * malaRejectionConstant U L)
  exact measure_map_Lp_eq_of_coupling_cost_tendsto P Xn (Y T) (gibbsMeasure U) ρ
    hX hfst hsnd hint hcost

end Brownian
end ULA
