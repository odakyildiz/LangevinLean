import WassersteinMixing.SemigroupRandomMALACanonical

/-! # Actual synchronous MALA distance and stationary laws

The common random realization inherits the proved rejection estimate through
its exact law. Its Euler coordinate is identified with the actual Brownian
Euler recursion, so both approximations live on the same probability space.
-/
noncomputable section
set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory
open scoped unitInterval NNReal ENNReal

namespace WassersteinMixing.RandomMALA.Canonical

variable (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V)

theorem input_aemeasurable (r : ℝ) :
    AEMeasurable (input P V hV r) (probability P V) :=
  ((Lp.aestronglyMeasurable _).aemeasurable.comp_fst).prodMk
    (aemeasurable_pi_iff.mpr fun n ↦
      ((Lp.aestronglyMeasurable _).aemeasurable.comp_fst).prodMk (by fun_prop))

theorem state_aemeasurable (r : ℝ) (n : ℕ) :
    AEMeasurable (state P V hV r n) (probability P V) := by
  exact ((ULA.noiseDrivenChain_measurable _
    (update_measurable V r ⟨P.beta, P.beta_pos.le⟩
      (hV.regularity.differentiable (by norm_num)) hV.gradientLipschitz) n).comp
        ((measurable_fst.prodMk measurable_fst).prodMk measurable_snd)).aemeasurable
          |>.comp_aemeasurable (input_aemeasurable P V hV r)

/-- The first coordinate is the actual Brownian-normalized Euler state. -/
def euler (r : ℝ) (n : ℕ) : Lp (E P.dimension) 2 (actualProbability P V) := by
  let := actualProbability_isProbability P V hV
  exact ULA.Hilbert.lpChain (actualProbability P V) V r hV.gradientLipschitz
    (actualInitial P V hV) (gaussian P V hV r) n

theorem state_fst_eq_euler (r : ℝ) (n : ℕ) :
    (fun ω ↦ (state P V hV r n ω).1) =ᵐ[probability P V]
      (fun ω ↦ euler P V hV r n ω.1) := by
  let := actualProbability_isProbability P V hV
  have he := ULA.hilbert_lpChain_coe (actualProbability P V) V r
    ⟨P.beta, P.beta_pos.le⟩ hV.gradientLipschitz (actualInitial P V hV)
    (gaussian P V hV r) n
  have hlift := (measurePreserving_fst (μ := actualProbability P V)
    (ν := uniformPath)).quasiMeasurePreserving.ae_eq_comp he
  filter_upwards [hlift] with ω hω
  change euler P V hV r n ω.1 =
    ULA.noiseDrivenChain (ULA.Hilbert.pointwiseUpdate V r)
      (actualInitial P V hV ω.1) (fun k ↦ gaussian P V hV r k ω.1) n at hω
  rw [hω]
  exact chain_fst V r _ _ n

/-- The actual randomized MALA state has the exact Gibbs law at every step. -/
theorem state_snd_law (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (probability P V).map (fun ω ↦ (state P V hV r n ω).2) = ULA.gibbsMeasure V := by
  let := actualTarget_isProbability P V hV
  change (probability P V).map (Prod.snd ∘ state P V hV r n) = _
  rw [← AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable
      (state_aemeasurable P V hV r n), state_law P V hV r hr n]
  exact ULA.malaCoupledChain_snd V r ⟨P.beta, P.beta_pos.le⟩
    (hV.regularity.differentiable (by norm_num)) hV.gradientLipschitz _
    (ULA.malaOneStep_gibbs_invariant V r ⟨P.beta, P.beta_pos.le⟩ hr
      (hV.regularity.differentiable (by norm_num)) hV.gradientLipschitz) n

theorem state_snd_memLp (r : ℝ) (hr : 0 < r) (n : ℕ) :
    MemLp (fun ω ↦ (state P V hV r n ω).2) 2 (probability P V) := by
  have hm := actualTarget_memLp P V hV
  rw [← state_snd_law P V hV r hr n] at hm
  exact (memLp_map_measure_iff (by fun_prop)
    (measurable_snd.aemeasurable.comp_aemeasurable
      (state_aemeasurable P V hV r n))).mp hm

/-- The actual randomized MALA state as a square-integrable random vector. -/
def mala (r : ℝ) (hr : 0 < r) (n : ℕ) : Lp (E P.dimension) 2 (probability P V) :=
  (state_snd_memLp P V hV r hr n).toLp (fun ω ↦ (state P V hV r n ω).2)

theorem mala_coe (r : ℝ) (hr : 0 < r) (n : ℕ) :
    mala P V hV r hr n =ᵐ[probability P V] fun ω ↦ (state P V hV r n ω).2 :=
  (state_snd_memLp P V hV r hr n).coeFn_toLp

theorem mala_law (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (probability P V).map (mala P V hV r hr n) = ULA.gibbsMeasure V := by
  rw [Measure.map_congr (mala_coe P V hV r hr n), state_snd_law P V hV r hr n]

theorem distance_integrable (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hsmall : r ≤ 2 / (P.alpha + P.beta)) (n : ℕ) :
    Integrable (fun ω ↦ ‖(state P V hV r n ω).1 - (state P V hV r n ω).2‖)
      (probability P V) := by
  have h := ULA.malaCoupledChain_distance_integrable V P.alpha r
    ⟨P.beta, P.beta_pos.le⟩ P.alpha_pos hr hr1 hsmall
    (hV.regularity.differentiable (by norm_num)) hV.strongConvexity hV.gradientLipschitz
    (ULA.malaOneStep_gibbs_invariant V r ⟨P.beta, P.beta_pos.le⟩ hr
      (hV.regularity.differentiable (by norm_num)) hV.gradientLipschitz) n
  rw [← state_law P V hV r hr n] at h
  exact h.comp_aemeasurable (state_aemeasurable P V hV r n)

/-- The actual shared-noise trajectories satisfy the proved first-moment
rejection bound, with no assumed comparison estimate. -/
theorem distance_integral_le (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hsmall : r ≤ 2 / (P.alpha + P.beta)) (n : ℕ) :
    (∫ ω, ‖(state P V hV r n ω).1 - (state P V hV r n ω).2‖ ∂probability P V) ≤
      (n : ℝ) * ULA.malaRejectionConstant V ⟨P.beta, P.beta_pos.le⟩ * r * Real.sqrt r := by
  have h := ULA.malaCoupledChain_distance_integral_le V P.alpha r
    ⟨P.beta, P.beta_pos.le⟩ P.alpha_pos hr hr1 hsmall
    (hV.regularity.differentiable (by norm_num)) hV.strongConvexity hV.gradientLipschitz
    (ULA.malaOneStep_gibbs_invariant V r ⟨P.beta, P.beta_pos.le⟩ hr
      (hV.regularity.differentiable (by norm_num)) hV.gradientLipschitz) n
  rw [← state_law P V hV r hr n,
    integral_map (state_aemeasurable P V hV r n) (by fun_prop)] at h
  exact h

end WassersteinMixing.RandomMALA.Canonical
