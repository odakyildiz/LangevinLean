import KineticLangevin.HamiltonianWeak
import UnadjustedLangevin.Gibbs
import Mathlib.MeasureTheory.Integral.Prod

/-! # Hamiltonian Gibbs finiteness and moments from strong convexity -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal ENNReal
namespace KineticLangevin
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The actual Hamiltonian Gibbs density factors into velocity and position
weights before any normalization. -/
theorem hamiltonianGibbs_factor (μ : Measure E) [SFinite μ]
    (f : E → ℝ) (hf : Measurable f) :
    hamiltonianGibbs μ f =
      (μ.withDensity (fun v ↦ ENNReal.ofReal (Real.exp (-‖v‖^2/2)))).prod
        (μ.withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-f x)))) := by
  rw [prod_withDensity (by fun_prop) (by fun_prop)]
  unfold hamiltonianGibbs
  congr 1
  funext z
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),← Real.exp_add]
  congr 2
  unfold hamiltonianEnergy
  ring

variable [FiniteDimensional ℝ E]

/-- The unnormalized thermal velocity weight has finite total mass. -/
theorem hamiltonianVelocity_finite :
    IsFiniteMeasure ((volume : Measure E).withDensity
      (fun v ↦ ENNReal.ofReal (Real.exp (-‖v‖^2/2)))) := by
  apply isFiniteMeasure_withDensity
  have hi : Integrable (fun v : E ↦ Real.exp (-‖v‖^2/2)) volume := by
    convert ULA.integrable_exp_neg_mul_norm_sq (H := E) (1/2) (by norm_num) using 1
    funext v
    congr 1
    ring
  exact ne_of_lt ((hasFiniteIntegral_iff_ofReal
    (ae_of_all _ fun _ ↦ Real.exp_nonneg _)).mp hi.hasFiniteIntegral)

/-- The unnormalized potential Gibbs weight is finite from first-order
strong-convexity assumptions. -/
theorem hamiltonianPosition_finite (f : E → ℝ) (m : ℝ) (hm : 0<m)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) :
    IsFiniteMeasure ((volume : Measure E).withDensity
      (fun x ↦ ENNReal.ofReal (Real.exp (-f x)))) :=
  isFiniteMeasure_withDensity (ULA.gibbsPartition_ne_top f m hm hf hsc)

/-- Consequently the full actual Hamiltonian Gibbs measure is finite. -/
theorem hamiltonianGibbs_finite (f : E → ℝ) (m : ℝ) (hm : 0<m)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) :
    IsFiniteMeasure (hamiltonianGibbs (volume : Measure E) f) := by
  rw [hamiltonianGibbs_factor volume f hf.continuous.measurable]
  haveI := hamiltonianVelocity_finite (E := E)
  haveI := hamiltonianPosition_finite f m hm hf hsc
  infer_instance

/-- Thermal Gaussian decay absorbs the velocity second moment. -/
theorem hamiltonianVelocity_norm_sq_integrable :
    Integrable (fun v : E ↦ ‖v‖^2) ((volume : Measure E).withDensity
      (fun v ↦ ENNReal.ofReal (Real.exp (-‖v‖^2/2)))) := by
  apply (integrable_withDensity_iff_integrable_smul'
    (show Measurable (fun v : E ↦ ENNReal.ofReal (Real.exp (-‖v‖^2/2))) by fun_prop)
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).mpr
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _),smul_eq_mul]
  convert ULA.integrable_norm_sq_mul_exp_neg_mul_norm_sq (H := E) (1/2) (by norm_num) using 1
  funext v
  rw [show -‖v‖^2/2 = -(1/2:ℝ)*‖v‖^2 by ring]
  ring

/-- Strong convexity also gives a finite position second moment before
normalization. -/
theorem hamiltonianPosition_norm_sq_integrable (f : E → ℝ) (m : ℝ) (hm : 0<m)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) :
    Integrable (fun x : E ↦ ‖x‖^2) ((volume : Measure E).withDensity
      (fun x ↦ ENNReal.ofReal (Real.exp (-f x)))) := by
  apply (integrable_withDensity_iff_integrable_smul'
    (show Measurable (fun x : E ↦ ENNReal.ofReal (Real.exp (-f x))) by
      exact hf.continuous.measurable.neg.exp.ennreal_ofReal)
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).mpr
  simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _),smul_eq_mul,mul_comm] using
    ULA.integrable_norm_sq_mul_exp_neg_of_strongConvex f m hm hf hsc

/-- Lipschitz growth of the force transfers the position second moment to
the force second moment, under the actual unnormalized Gibbs weight. -/
theorem hamiltonianPosition_force_sq_integrable (f : E → ℝ) (m : ℝ) (hm : 0<m)
    (M : ℝ≥0) (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) :
    Integrable (fun x : E ↦ ‖gradient f x‖^2) ((volume : Measure E).withDensity
      (fun x ↦ ENNReal.ofReal (Real.exp (-f x)))) := by
  haveI := hamiltonianPosition_finite f m hm hf hsc
  have henv := ((hamiltonianPosition_norm_sq_integrable f m hm hf hsc).const_mul
    (2*(M : ℝ)^2)).add (integrable_const (2*‖gradient f 0‖^2))
  apply henv.mono' (hLip.continuous.norm.pow 2).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hg : ‖gradient f x‖ ≤ (M : ℝ)*‖x‖+‖gradient f 0‖ := by
    have ht := norm_sub_le (gradient f x-gradient f 0) (-gradient f 0)
    have hl := hLip.norm_sub_le x 0
    simp only [sub_neg_eq_add,sub_add_cancel,norm_neg,sub_zero] at ht hl
    linarith
  have hs : ‖gradient f x‖^2 ≤ ((M : ℝ)*‖x‖+‖gradient f 0‖)^2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hg
  change ‖gradient f x‖^2 ≤ 2*(M : ℝ)^2*‖x‖^2+2*‖gradient f 0‖^2
  nlinarith [sq_nonneg ((M : ℝ)*‖x‖-‖gradient f 0‖)]

/-- The precise velocity-plus-force moment used in the stationarity limit
is derived from the paper's first-order potential assumptions. -/
theorem hamiltonianGibbs_phase_moment (f : E → ℝ) (m : ℝ) (hm : 0<m)
    (M : ℝ≥0) (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) :
    Integrable (fun z : E×E ↦ ‖z.1‖^2+‖gradient f z.2‖^2)
      (hamiltonianGibbs (volume : Measure E) f) := by
  rw [hamiltonianGibbs_factor volume f hf.continuous.measurable]
  haveI := hamiltonianVelocity_finite (E := E)
  haveI := hamiltonianPosition_finite f m hm hf hsc
  exact (hamiltonianVelocity_norm_sq_integrable (E := E) |>.comp_fst _).add
    ((hamiltonianPosition_force_sq_integrable f m hm M hf hsc hLip).comp_snd _)

end KineticLangevin
