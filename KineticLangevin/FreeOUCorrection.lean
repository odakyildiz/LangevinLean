import KineticLangevin.FreeOU
import KineticLangevin.KernelConvolution

/-! # The actual KLMC2 Hessian correction is an integral of a free OU velocity

The correction keeps the fresh φ₂/φ₃ stochastic terms. They combine with the
initial velocity into a true free OU path, to which marginal Gaussian cutoff
bounds apply without imposing independence from the initial position.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace KineticLangevin
open BrownianConvolution
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (P : Measure Ω)

/-- The exact free-OU response and its successive position primitives on one actual source. -/
def freeOUResponse
    (L : Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) →L[ℝ]
      Lp (EuclideanSpace ℝ ι) 2 P)
    (V : Lp (EuclideanSpace ℝ ι) 2 P) (γ : ℝ) (a : ℝ≥0) (k : ℕ) (t : ℝ) :
    Lp (EuclideanSpace ℝ ι) 2 P :=
  psi γ k t • V+L (vectorSegmentLp ι (psi γ k) (continuous_psi γ k) a t.toNNReal)

/-- The complete deterministic and stochastic Hessian response, on the very same source. -/
def freeOUCorrection
    (L : Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) →L[ℝ]
      Lp (EuclideanSpace ℝ ι) 2 P)
    (V : Lp (EuclideanSpace ℝ ι) 2 P) (γ : ℝ) (a : ℝ≥0) (k : ℕ) (t : ℝ) :
    Lp (EuclideanSpace ℝ ι) 2 P :=
  phi γ (k+1) t • V+L (vectorSegmentLp ι (phi γ (k+1)) (continuous_phi γ (k+1)) a t.toNNReal)

theorem continuous_freeOUResponse (L : Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) →L[ℝ]
      Lp (EuclideanSpace ℝ ι) 2 P)
    (V : Lp (EuclideanSpace ℝ ι) 2 P) (γ : ℝ) (a : ℝ≥0) (k : ℕ) : Continuous (freeOUResponse P L V γ a k) :=
  ((continuous_psi γ k).smul continuous_const).add
    (L.continuous.comp ((continuous_vectorSegmentLp ι (psi γ k) (continuous_psi γ k) a).comp continuous_real_toNNReal))

/-- Every free-OU primitive is the actual integral of its preceding response. -/
theorem freeOUResponse_primitive (L : Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) →L[ℝ]
      Lp (EuclideanSpace ℝ ι) 2 P)
    (V : Lp (EuclideanSpace ℝ ι) 2 P) (γ : ℝ) (a : ℝ≥0) (k : ℕ) (t : ℝ) (ht : 0≤t) :
    freeOUResponse P L V γ a (k+1) t=∫ s in 0..t,freeOUResponse P L V γ a k s := by
  have hc : Continuous (fun s : ℝ ↦ vectorSegmentLp ι (psi γ k) (continuous_psi γ k) a s.toNNReal) :=
    (continuous_vectorSegmentLp ι (psi γ k) (continuous_psi γ k) a).comp continuous_real_toNNReal
  have hψ : IntervalIntegrable (fun s ↦ psi γ k s • V) volume 0 t :=
    ((continuous_psi γ k).smul continuous_const).intervalIntegrable 0 t
  have hLI : IntervalIntegrable (fun s ↦ L (vectorSegmentLp ι (psi γ k) (continuous_psi γ k) a s.toNNReal)) volume 0 t :=
    (L.continuous.comp hc).intervalIntegrable 0 t
  unfold freeOUResponse
  rw [intervalIntegral.integral_add hψ hLI,
    intervalIntegral.integral_smul_const,L.intervalIntegral_comp_comm (hc.intervalIntegrable 0 t)]
  have hi := vectorSegmentLp_primitive_all ι γ k a t.toNNReal
  rw [Real.coe_toNNReal t ht] at hi
  rw [← hi]
  rfl

/-- The whole Hessian correction, including fresh stochastic terms, is an actual damped convolution. -/
theorem freeOUCorrection_eq_convolution (L : Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) →L[ℝ]
      Lp (EuclideanSpace ℝ ι) 2 P)
    (V : Lp (EuclideanSpace ℝ ι) 2 P) (γ : ℝ) (a : ℝ≥0) (k : ℕ) (hγ : 0≤γ) (t : ℝ) (ht : 0≤t) :
    freeOUCorrection P L V γ a k t=
      ∫ s in 0..t,Real.exp (-γ*(t-s)) • freeOUResponse P L V γ a k s := by
  have hc : Continuous (fun s : ℝ ↦ Real.exp (-γ*(t-s)) •
      vectorSegmentLp ι (psi γ k) (continuous_psi γ k) a s.toNNReal) :=
    (by fun_prop : Continuous (fun s : ℝ ↦ Real.exp (-γ*(t-s)))).smul
      ((continuous_vectorSegmentLp ι (psi γ k) (continuous_psi γ k) a).comp continuous_real_toNNReal)
  have hψ : IntervalIntegrable (fun s ↦ (Real.exp (-γ*(t-s))*psi γ k s) • V) volume 0 t :=
    ((by fun_prop : Continuous (fun s : ℝ ↦ Real.exp (-γ*(t-s)))).mul (continuous_psi γ k)).smul
      continuous_const |>.intervalIntegrable 0 t
  unfold freeOUResponse freeOUCorrection
  simp_rw [smul_add,smul_smul,← map_smul L]
  have hLI : IntervalIntegrable (fun s ↦ L (Real.exp (-γ*(t-s)) •
      vectorSegmentLp ι (psi γ k) (continuous_psi γ k) a s.toNNReal)) volume 0 t :=
    (L.continuous.comp hc).intervalIntegrable 0 t
  rw [intervalIntegral.integral_add hψ hLI,
    intervalIntegral.integral_smul_const,L.intervalIntegral_comp_comm (hc.intervalIntegrable 0 t)]
  have hi := vectorSegmentLp_phi ι γ hγ k a t.toNNReal
  rw [Real.coe_toNNReal t ht] at hi
  rw [← hi]
  rfl

/-- Bounded random Hessian multiplication is a continuous linear map on L²,
so it commutes with every genuine free-OU time primitive. -/
theorem apply_freeOUResponse_primitive (A : Lp (EuclideanSpace ℝ ι) 2 P →L[ℝ] Lp (EuclideanSpace ℝ ι) 2 P)
    (L : Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) →L[ℝ]
      Lp (EuclideanSpace ℝ ι) 2 P)
    (V : Lp (EuclideanSpace ℝ ι) 2 P) (γ : ℝ) (a : ℝ≥0) (k : ℕ) (t : ℝ) (ht : 0≤t) :
    A (freeOUResponse P L V γ a (k+1) t)=∫ s in 0..t,A (freeOUResponse P L V γ a k s) := by
  rw [freeOUResponse_primitive P L V γ a k t ht]
  exact (A.intervalIntegral_comp_comm ((continuous_freeOUResponse P L V γ a k).intervalIntegrable 0 t)).symm

/-- The same random Hessian map commutes with the actual damped stochastic correction. -/
theorem apply_freeOUCorrection_eq_convolution
    (A : Lp (EuclideanSpace ℝ ι) 2 P →L[ℝ] Lp (EuclideanSpace ℝ ι) 2 P)
    (L : Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) →L[ℝ]
      Lp (EuclideanSpace ℝ ι) 2 P)
    (V : Lp (EuclideanSpace ℝ ι) 2 P) (γ : ℝ) (a : ℝ≥0) (k : ℕ) (hγ : 0≤γ) (t : ℝ) (ht : 0≤t) :
    A (freeOUCorrection P L V γ a k t)=
      ∫ s in 0..t,Real.exp (-γ*(t-s)) • A (freeOUResponse P L V γ a k s) := by
  have hc : Continuous (fun s : ℝ ↦ Real.exp (-γ*(t-s)) • freeOUResponse P L V γ a k s) :=
    (by fun_prop : Continuous (fun s : ℝ ↦ Real.exp (-γ*(t-s)))).smul (continuous_freeOUResponse P L V γ a k)
  rw [freeOUCorrection_eq_convolution P L V γ a k hγ t ht,
    ← A.intervalIntegral_comp_comm (hc.intervalIntegrable 0 t)]
  apply intervalIntegral.integral_congr
  intro s _
  exact map_smul A _ _

/-- The complete φ₂ Hessian-difference bundle is the damped primitive of the actual free OU velocity. -/
theorem apply_freeOUCorrection_phi_two
    (A : Lp (EuclideanSpace ℝ ι) 2 P →L[ℝ] Lp (EuclideanSpace ℝ ι) 2 P)
    (L V γ a) (hγ : 0≤γ) (t : ℝ) (ht : 0≤t) :
    A (freeOUCorrection P L V γ a 1 t)=
      ∫ s in 0..t,Real.exp (-γ*(t-s)) •
        ∫ r in 0..s,A (freeOUResponse P L V γ a 0 r) := by
  rw [apply_freeOUCorrection_eq_convolution P A L V γ a 1 hγ t ht]
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp only
  rw [uIcc_of_le ht] at hs
  rw [apply_freeOUResponse_primitive P A L V γ a 0 s hs.1]

/-- The complete φ₃ bundle is the damped second primitive of that same actual free OU velocity. -/
theorem apply_freeOUCorrection_phi_three
    (A : Lp (EuclideanSpace ℝ ι) 2 P →L[ℝ] Lp (EuclideanSpace ℝ ι) 2 P)
    (L V γ a) (hγ : 0≤γ) (t : ℝ) (ht : 0≤t) :
    A (freeOUCorrection P L V γ a 2 t)=
      ∫ s in 0..t,Real.exp (-γ*(t-s)) •
        ∫ r in 0..s,∫ u in 0..r,A (freeOUResponse P L V γ a 0 u) := by
  rw [apply_freeOUCorrection_eq_convolution P A L V γ a 2 hγ t ht]
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp only
  rw [uIcc_of_le ht] at hs
  rw [apply_freeOUResponse_primitive P A L V γ a 1 s hs.1]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  dsimp only
  rw [uIcc_of_le hs.1] at hr
  rw [apply_freeOUResponse_primitive P A L V γ a 0 r hr.1]

/-- The complete φ₂ plus friction-times-φ₃ stochastic response is precisely ψ₂ on the same Brownian source. -/
theorem vectorSegmentLp_phi_balance (γ : ℝ) (a t : ℝ≥0) :
    vectorSegmentLp ι (phi γ 2) (continuous_phi γ 2) a t+
      γ • vectorSegmentLp ι (phi γ 3) (continuous_phi γ 3) a t=
        vectorSegmentLp ι (psi γ 2) (continuous_psi γ 2) a t := by
  have hker : timeKernelLp (phi γ 2) (continuous_phi γ 2) t+
      γ • timeKernelLp (phi γ 3) (continuous_phi γ 3) t=
        timeKernelLp (psi γ 2) (continuous_psi γ 2) t := by
    apply Lp.ext
    filter_upwards [timeKernelLp_coe (phi γ 2) (continuous_phi γ 2) t,
      timeKernelLp_coe (phi γ 3) (continuous_phi γ 3) t,
      timeKernelLp_coe (psi γ 2) (continuous_psi γ 2) t,
      Lp.coeFn_add (timeKernelLp (phi γ 2) (continuous_phi γ 2) t)
        (γ • timeKernelLp (phi γ 3) (continuous_phi γ 3) t),
      Lp.coeFn_smul γ (timeKernelLp (phi γ 3) (continuous_phi γ 3) t)] with r h2 h3 hp hadd hsmul
    rw [hadd,Pi.add_apply,hsmul,Pi.smul_apply,h2,h3,hp]
    by_cases hr : r∈Ioc 0 (t:ℝ)
    · simpa only [timeKernel,indicator_of_mem hr,smul_eq_mul] using phi_two_add_friction_phi_three γ ((t:ℝ)-r)
    · simp only [timeKernel,indicator_of_notMem hr,smul_zero,add_zero]
  let R := (spatialLift ι).comp
    ((ULA.GaussianHilbert.isonormal ULA.CanonicalBrownian.basis).toContinuousLinearMap.comp
      (timeShift a).toContinuousLinearMap)
  change R (timeKernelLp (phi γ 2) (continuous_phi γ 2) t)+
    γ • R (timeKernelLp (phi γ 3) (continuous_phi γ 3) t)=R (timeKernelLp (psi γ 2) (continuous_psi γ 2) t)
  rw [← map_smul,← map_add,hker]

/-- The entire random Hessian bundle keeps the exact φ₂+γφ₃=ψ₂ cancellation, including both noises. -/
theorem freeOUCorrection_balance
    (L : Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) →L[ℝ]
      Lp (EuclideanSpace ℝ ι) 2 P)
    (V : Lp (EuclideanSpace ℝ ι) 2 P) (γ : ℝ) (a : ℝ≥0) (t : ℝ) :
    freeOUCorrection P L V γ a 1 t+γ • freeOUCorrection P L V γ a 2 t=
      freeOUResponse P L V γ a 2 t := by
  unfold freeOUCorrection freeOUResponse
  rw [← phi_two_add_friction_phi_three γ t,← vectorSegmentLp_phi_balance γ a t.toNNReal]
  simp only [map_add,map_smul,add_smul,mul_smul]
  module

end KineticLangevin
