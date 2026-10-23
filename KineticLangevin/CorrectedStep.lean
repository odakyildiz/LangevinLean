import KineticLangevin.FreeOUCorrection
import KineticLangevin.SecondOrderLocal
import KineticLangevin.Integrator

noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace KineticLangevin

section Damped
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Factoring the scalar damping gives the actual Banach-valued convolution. -/
theorem dampedIntegral_factor (γ : ℝ) (F : ℝ→E) (t : ℝ) :
    dampedIntegral γ F t=Real.exp (-γ*t) • ∫ s in 0..t,Real.exp (γ*s) • F s := by
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp [dampedIntegral]
  rw [smul_smul,← Real.exp_add]
  congr 2
  ring

/-- The genuine damped convolution solves its deterministic linear response equation. -/
theorem hasDerivAt_dampedIntegral (γ : ℝ) (F : ℝ→E) (hF : Continuous F) (t : ℝ) :
    HasDerivAt (dampedIntegral γ F) (F t-γ • dampedIntegral γ F t) t := by
  have hc : Continuous (fun s : ℝ ↦ Real.exp (γ*s) • F s) := by fun_prop
  have hd := (((hasDerivAt_id t).const_mul (-γ)).exp).smul
    (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt)
  have he : Real.exp (-γ*t)*Real.exp (γ*t)=1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  convert hd.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s ↦ dampedIntegral_factor γ F s)) using 1
  · simp only [id_eq,mul_one]
    rw [dampedIntegral_factor,smul_smul,smul_smul,he,one_smul]
    module
end Damped

open BrownianConvolution
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] (P : Measure Ω)

/-- Every actual vector convolution vanishes on an interval of zero duration. -/
theorem vectorSegmentLp_zero (k : ℝ→ℝ) (hk : Continuous k) (a : ℝ≥0) :
    vectorSegmentLp ι k hk a 0=0 := by
  have hzero : timeKernelLp k hk 0=0 := by
    apply Lp.ext
    filter_upwards [timeKernelLp_coe k hk 0,Lp.coeFn_zero ℝ 2 (volume : Measure ℝ)] with r hr hz
    rw [hr,hz]
    simp [timeKernel]
  unfold vectorSegmentLp segmentConvolutionLp segmentKernelLp
  rw [hzero,map_zero,map_zero,map_zero]

variable (L : Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) →L[ℝ]
    Lp (EuclideanSpace ℝ ι) 2 P) (V : Lp (EuclideanSpace ℝ ι) 2 P) (γ : ℝ) (a : ℝ≥0)

theorem continuous_freeOUCorrection (k : ℕ) : Continuous (freeOUCorrection P L V γ a k) :=
  ((continuous_phi γ (k+1)).smul continuous_const).add
    (L.continuous.comp ((continuous_vectorSegmentLp ι (phi γ (k+1)) (continuous_phi γ (k+1)) a).comp continuous_real_toNNReal))

@[simp] theorem freeOUCorrection_zero (k : ℕ) : freeOUCorrection P L V γ a k 0=0 := by
  simp only [freeOUCorrection,phi_at_zero,zero_smul,Real.toNNReal_zero,vectorSegmentLp_zero,map_zero,add_zero]

/-- The actual full φ₃ correction is the ordinary primitive of the actual full φ₂ correction. -/
theorem freeOUCorrection_primitive (hγ : 0≤γ) (t : ℝ) (ht : 0≤t) :
    freeOUCorrection P L V γ a 2 t=∫ s in 0..t,freeOUCorrection P L V γ a 1 s := by
  let R := freeOUResponse P L V γ a 2
  have hR : Continuous R := continuous_freeOUResponse P L V γ a 2
  have hd : ∀ s∈Ioo 0 t,HasDerivAt (freeOUCorrection P L V γ a 2) (freeOUCorrection P L V γ a 1 s) s := by
    intro s hs
    have heq : dampedIntegral γ R =ᶠ[𝓝 s] freeOUCorrection P L V γ a 2 := by
      filter_upwards [Ioi_mem_nhds hs.1] with u hu
      exact (freeOUCorrection_eq_convolution P L V γ a 2 hγ u hu.le).symm
    have hD := (hasDerivAt_dampedIntegral γ R hR s).congr_of_eventuallyEq heq.symm
    have he : R s-γ • dampedIntegral γ R s=freeOUCorrection P L V γ a 1 s := by
      rw [show dampedIntegral γ R s=freeOUCorrection P L V γ a 2 s from heq.eq_of_nhds]
      have hb := freeOUCorrection_balance P L V γ a s
      dsimp only [R]
      rw [← hb]
      abel
    rwa [he] at hD
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht
    (continuous_freeOUCorrection P L V γ a 2).continuousOn hd
    ((continuous_freeOUCorrection P L V γ a 1).intervalIntegrable 0 t)
  simpa only [freeOUCorrection_zero,sub_zero] using hi.symm

/-- The velocity correction is exactly the actual damped primitive used in the local Taylor proof. -/
theorem freeOUCorrection_phi_two_eq_dampedPrimitive (hγ : 0≤γ) (t : ℝ) (ht : 0≤t) :
    freeOUCorrection P L V γ a 1 t=
      dampedIntegral γ (fun s ↦ ∫ r in 0..s,freeOUResponse P L V γ a 0 r) t := by
  rw [freeOUCorrection_eq_convolution P L V γ a 1 hγ t ht]
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp only [dampedIntegral]
  rw [uIcc_of_le ht] at hs
  rw [freeOUResponse_primitive P L V γ a 0 s hs.1]

/-- The analytic corrected velocity is exactly the full kernel response, with its fresh Hessian noise. -/
theorem correctedVelocity_freeOUResponse
    (F0 : Lp (EuclideanSpace ℝ ι) 2 P)
    (A : Lp (EuclideanSpace ℝ ι) 2 P →L[ℝ] Lp (EuclideanSpace ℝ ι) 2 P)
    (hγ : 0≤γ) (t : ℝ) (ht : 0≤t) :
    correctedVelocity γ (freeOUResponse P L V γ a 0) F0 A t=
      freeOUResponse P L V γ a 0 t-psi γ 1 t • F0-A (freeOUCorrection P L V γ a 1 t) := by
  rw [correctedVelocity,← freeOUCorrection_phi_two_eq_dampedPrimitive P L V γ a hγ t ht]

/-- Integrating the actual corrected velocity gives precisely the full position correction. -/
theorem correctedPosition_freeOUResponse
    (x0 F0 : Lp (EuclideanSpace ℝ ι) 2 P)
    (A : Lp (EuclideanSpace ℝ ι) 2 P →L[ℝ] Lp (EuclideanSpace ℝ ι) 2 P)
    (hγ : 0≤γ) (t : ℝ) (ht : 0≤t) :
    correctedPosition γ (freeOUResponse P L V γ a 0) x0 F0 A t=
      x0+freeOUResponse P L V γ a 1 t-psi γ 2 t • F0-A (freeOUCorrection P L V γ a 2 t) := by
  have hU := continuous_freeOUResponse P L V γ a 0
  have hF : Continuous (fun s : ℝ ↦ psi γ 1 s • F0) := (continuous_psi γ 1).smul continuous_const
  have hA : Continuous (fun s : ℝ ↦ A (freeOUCorrection P L V γ a 1 s)) :=
    A.continuous.comp (continuous_freeOUCorrection P L V γ a 1)
  have he : (∫ s in 0..t,correctedVelocity γ (freeOUResponse P L V γ a 0) F0 A s)=
      ∫ s in 0..t,freeOUResponse P L V γ a 0 s-psi γ 1 s • F0-A (freeOUCorrection P L V γ a 1 s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht] at hs
    exact correctedVelocity_freeOUResponse P L V γ a F0 A hγ s hs.1
  unfold correctedPosition
  have hiUF : IntervalIntegrable (fun s ↦ freeOUResponse P L V γ a 0 s-psi γ 1 s • F0) volume 0 t :=
    (hU.sub hF).intervalIntegrable 0 t
  rw [he,intervalIntegral.integral_sub hiUF (hA.intervalIntegrable 0 t),
    intervalIntegral.integral_sub (hU.intervalIntegrable 0 t) (hF.intervalIntegrable 0 t),
    intervalIntegral.integral_smul_const,
    A.intervalIntegral_comp_comm ((continuous_freeOUCorrection P L V γ a 1).intervalIntegrable 0 t),
    ← freeOUResponse_primitive P L V γ a 0 t ht,
    ← freeOUCorrection_primitive P L V γ a hγ t ht]
  change x0+(freeOUResponse P L V γ a 1 t-psi γ 2 t • F0-A (freeOUCorrection P L V γ a 2 t))=_
  abel

/-- The true four correlated Brownian responses, pulled back to a common source without thermal scaling. -/
def liftedKLMC2Noise
    (R : Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) →L[ℝ]
      Lp (EuclideanSpace ℝ ι) 2 P)
    (γ : ℝ) (a : ℝ≥0) (t : ℝ) (j : Fin 4) : Lp (EuclideanSpace ℝ ι) 2 P :=
  R (vectorSegmentLp ι (klmc2Kernels γ j) (continuous_klmc2Kernels γ j) a t.toNNReal)

/-- The implemented second-order step is the actual analytic corrected path at the same four-kernel innovation. -/
theorem klmc2Step_eq_corrected_freeOU
    (R : Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) →L[ℝ]
      Lp (EuclideanSpace ℝ ι) 2 P)
    (g : Lp (EuclideanSpace ℝ ι) 2 P → Lp (EuclideanSpace ℝ ι) 2 P)
    (H : Lp (EuclideanSpace ℝ ι) 2 P → Lp (EuclideanSpace ℝ ι) 2 P →L[ℝ] Lp (EuclideanSpace ℝ ι) 2 P)
    (γ : ℝ) (hγ : 0≤γ) (a : ℝ≥0) (t : ℝ) (ht : 0≤t)
    (z : PhaseSpace (Lp (EuclideanSpace ℝ ι) 2 P)) :
    klmc2Step g H γ t z (liftedKLMC2Noise P R γ a t)=
      (correctedVelocity γ (freeOUResponse P (Real.sqrt (2*γ) • R) z.1 γ a 0) (g z.2) (H z.2) t,
       correctedPosition γ (freeOUResponse P (Real.sqrt (2*γ) • R) z.1 γ a 0) z.2 (g z.2) (H z.2) t) := by
  rw [correctedVelocity_freeOUResponse P _ _ _ _ _ _ hγ t ht,
    correctedPosition_freeOUResponse P _ _ _ _ _ _ _ hγ t ht]
  apply Prod.ext <;> dsimp only [klmc2Step,liftedKLMC2Noise,freeOUResponse,freeOUCorrection,klmc2Kernels]
  all_goals simp only [smul_apply,map_add,map_smul,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Nat.reduceAdd]
  all_goals simp only [Matrix.head_cons,Matrix.tail_cons]
  all_goals module

end KineticLangevin
