import KineticLangevin.HamiltonianIteration
import KineticLangevin.HamiltonianRejection
import KineticLangevin.HamiltonianConvergence
import KineticLangevin.HamiltonianMoments

/-! # Exact Gibbs invariance of the actual Hamiltonian integral flow

The proof passes from explicit invariant corrected Verlet proposals to the
actual selected ODE solution. The rejection probability and numerical limit
are proved, rather than supplied as stationarity contracts.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal ENNReal
namespace KineticLangevin
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure E) [SFinite μ] [Measure.IsAddLeftInvariant μ] [Measure.IsNegInvariant μ]

/-- The selected Hamiltonian endpoint depends continuously on its initial state. -/
theorem hamiltonianFlow_endpoint_continuous (f : E → ℝ) (M : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (T : ℝ) (hT : 0 ≤ T) :
    Continuous (fun z : E×E ↦ hamiltonianFlow f M hLip T hT z T) := by
  have hc := (kineticFlow_endpoint_continuous (gradient f) M 0 1 hLip T hT T
    ⟨hT,le_rfl⟩).comp (continuous_id.prodMk
      (continuous_const : Continuous (fun _ : E×E ↦ (0 : VelocityForcing (E := E) T))))
  simpa only [hamiltonianFlow,Function.comp_def,id_eq] using hc

/-- Actual Hamiltonian Gibbs invariance under precisely the finite quadratic
moment needed by the proved rejection estimate. No invariant-flow premise is used. -/
theorem hamiltonianFlow_preserves_gibbs_of_moment
    (f : E → ℝ) (M : ℝ≥0) (hf : Differentiable ℝ f)
    (hLip : LipschitzWith M (gradient f)) (T : ℝ) (hT : 0 ≤ T)
    [IsFiniteMeasure (hamiltonianGibbs μ f)]
    (henv : Integrable (fun z : E×E ↦ ‖z.1‖^2+‖gradient f z.2‖^2)
      (hamiltonianGibbs μ f)) :
    (hamiltonianGibbs μ f).map (fun z ↦ hamiltonianFlow f M hLip T hT z T) =
      hamiltonianGibbs μ f := by
  let π := hamiltonianGibbs μ f
  let K : ℝ := (M : ℝ)*(2*(M : ℝ)+11)/8
  let B : ℝ := ∫ z, ‖z.1‖^2+‖gradient f z.2‖^2 ∂π
  let δ : ℕ → ℝ := fun n ↦ (2*T^2*K*B)/((n+1 : ℕ) : ℝ)
  have hδ : Tendsto δ atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_const_div_atTop_nhds_zero_nat _)
  have hmesh : Tendsto (fun n : ℕ ↦ T/((n+1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_const_div_atTop_nhds_zero_nat T)
  apply measure_map_eq_of_bounded_test_error_tendsto π _
    (hamiltonianFlow_endpoint_continuous f M hLip T hT).measurable
    (fun n ↦ (verletStep (gradient f) (T/((n+1 : ℕ) : ℝ)))^[n+1])
    (fun n ↦ ((verletStep_measurePreserving μ (gradient f) hLip.continuous.measurable _).measurable).iterate _)
    (fun z ↦ verlet_iterate_tendsto_hamiltonianFlow f M hLip T hT z) δ hδ
  intro F hF hFb
  filter_upwards [hmesh.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1))] with n hn
  let h : ℝ := T/((n+1 : ℕ) : ℝ)
  have hh : 0 ≤ h := div_nonneg hT (by positivity)
  have hh1 : h ≤ 1 := hn.le
  have hs := correctedMeasure_iterate_weak_error π
    (verletStep (gradient f) h) reverseVelocity
    (verletStep_measurePreserving μ (gradient f) hLip.continuous.measurable h).measurable
    (reverseVelocity_measurePreserving μ).measurable
    (verletAcceptance f h) (verletAcceptance_measurable f hf.continuous.measurable hLip.continuous.measurable h)
    (verletAcceptance_nonneg f h) (verletAcceptance_le_one f h)
    (correctedVerlet_preserves_gibbs μ f hf.continuous.measurable hLip.continuous.measurable h)
    F hF 1 (by norm_num) hFb (n+1)
  have hr := verlet_rejection_integral_le π f M hf hLip henv h hh hh1
  have hs' := hs.trans (mul_le_mul_of_nonneg_left hr (by positivity :
    0 ≤ ((n+1 : ℕ) : ℝ)*(2*1)))
  convert hs' using 1
  dsimp [δ,h,K,B]
  field_simp

/-- In finite dimensions the paper's first-order assumptions alone imply
exact invariance of the actual Hamiltonian integral flow. -/
theorem hamiltonianFlow_preserves_gibbs [FiniteDimensional ℝ E]
    (f : E → ℝ) (m : ℝ) (hm : 0<m) (M : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (T : ℝ) (hT : 0 ≤ T) :
    (hamiltonianGibbs (volume : Measure E) f).map
      (fun z ↦ hamiltonianFlow f M hLip T hT z T) =
        hamiltonianGibbs (volume : Measure E) f := by
  haveI := hamiltonianGibbs_finite f m hm hf hsc
  exact hamiltonianFlow_preserves_gibbs_of_moment volume f M hf hLip T hT
    (hamiltonianGibbs_phase_moment f m hm M hf hsc hLip)

end KineticLangevin
