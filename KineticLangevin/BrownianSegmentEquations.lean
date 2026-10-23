import KineticLangevin.BrownianSegments

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace KineticLangevin.BrownianConvolution

/-- The increment of the existing canonical Brownian motion on `(a,a+t]`. -/
def segmentBrownianLp (a t : ℝ≥0) : Lp ℝ 2 probability :=
  ULA.CanonicalBrownian.valueLp (a+t) - ULA.CanonicalBrownian.valueLp a

/-- Translating the unit kernel gives the difference of the two Brownian time indicators. -/
theorem segmentKernelLp_one (a t : ℝ≥0) :
    segmentKernelLp (fun _ => 1) continuous_const a t =
      ULA.CanonicalBrownian.timeIndicator (a+t) - ULA.CanonicalBrownian.timeIndicator a := by
  apply Lp.ext
  have hb : ULA.CanonicalBrownian.timeIndicator (a+t) =ᵐ[volume]
      (Ioc 0 ((a+t : ℝ≥0) : ℝ)).indicator (fun _ : ℝ => (1 : ℝ)) := indicatorConstLp_coeFn
  have ha : ULA.CanonicalBrownian.timeIndicator a =ᵐ[volume]
      (Ioc 0 (a : ℝ)).indicator (fun _ : ℝ => (1 : ℝ)) := indicatorConstLp_coeFn
  filter_upwards [segmentKernelLp_coe (fun _ => 1) continuous_const a t,
    Lp.coeFn_sub (ULA.CanonicalBrownian.timeIndicator (a+t)) (ULA.CanonicalBrownian.timeIndicator a), hb, ha]
    with r hr hsub hb ha
  rw [hr, hsub, Pi.sub_apply, hb, ha]
  simp only [NNReal.coe_add]
  simp only [Set.indicator, mem_Ioc]
  split_ifs <;> simp_all <;> linarith [a.coe_nonneg, t.coe_nonneg]

/-- The constant response is the actual Brownian increment on this segment. -/
theorem segmentConvolutionLp_one (a t : ℝ≥0) :
    segmentConvolutionLp (fun _ => 1) continuous_const a t = segmentBrownianLp a t := by
  unfold segmentConvolutionLp segmentBrownianLp ULA.CanonicalBrownian.valueLp
  rw [segmentKernelLp_one, map_sub]

theorem continuous_segmentConvolutionLp (k : ℝ → ℝ) (hk : Continuous k) (a : ℝ≥0) :
    Continuous (segmentConvolutionLp k hk a) :=
  (ULA.GaussianHilbert.isonormal ULA.CanonicalBrownian.basis).continuous.comp
    ((timeShift a).continuous.comp (continuous_timeKernelLp k hk))

/-- Time integration of the translated velocity response is the translated position response. -/
theorem segmentConvolutionLp_primitive (γ : ℝ) (hγ : 0 ≤ γ) (a t : ℝ≥0) :
    segmentConvolutionLp (psi γ 1) (continuous_psi γ 1) a t =
      ∫ s in 0..(t : ℝ), segmentConvolutionLp (psi γ 0) (continuous_psi γ 0) a s.toNNReal := by
  let L := (ULA.GaussianHilbert.isonormal ULA.CanonicalBrownian.basis).toContinuousLinearMap.comp
    (timeShift a).toContinuousLinearMap
  change L (timeKernelLp (psi γ 1) (continuous_psi γ 1) t) = _
  rw [timeKernelLp_primitive γ hγ t]
  exact (L.intervalIntegral_comp_comm
    (((continuous_timeKernelLp (psi γ 0) (continuous_psi γ 0)).comp
      continuous_real_toNNReal).intervalIntegrable _ _)).symm

/-- The translated responses solve the damped equation driven by the actual Brownian increment. -/
theorem segmentConvolutionLp_balance (γ : ℝ) (a t : ℝ≥0) :
    segmentConvolutionLp (psi γ 0) (continuous_psi γ 0) a t +
      γ • segmentConvolutionLp (psi γ 1) (continuous_psi γ 1) a t = segmentBrownianLp a t := by
  have hbase := velocityLp_add_friction_positionLp γ t
  unfold velocityLp positionLp convolutionLp ULA.CanonicalBrownian.valueLp at hbase
  rw [← map_smul, ← map_add] at hbase
  have hker := (ULA.GaussianHilbert.isonormal ULA.CanonicalBrownian.basis).injective hbase
  unfold segmentConvolutionLp segmentKernelLp
  rw [← map_smul, ← map_add, ← map_smul, ← map_add, hker]
  rw [← timeKernelLp_one]
  exact segmentConvolutionLp_one a t

/-- The same source gives the exact additive-noise integral equation on each segment. -/
theorem segmentConvolutionLp_integral_equation (γ : ℝ) (hγ : 0 ≤ γ) (a t : ℝ≥0) :
    segmentConvolutionLp (psi γ 0) (continuous_psi γ 0) a t = segmentBrownianLp a t -
      γ • ∫ s in 0..(t : ℝ), segmentConvolutionLp (psi γ 0) (continuous_psi γ 0) a s.toNNReal := by
  rw [← segmentConvolutionLp_primitive γ hγ]
  exact eq_sub_iff_add_eq.mpr (segmentConvolutionLp_balance γ a t)

/-- The translated position response is the ordinary convolution of the actual Brownian increments. -/
theorem segmentConvolutionLp_position_eq_brownian_convolution (γ : ℝ) (hγ : 0 ≤ γ)
    (a t : ℝ≥0) :
    segmentConvolutionLp (psi γ 1) (continuous_psi γ 1) a t =
      ∫ s in 0..(t : ℝ), Real.exp (-γ*((t : ℝ)-s)) • segmentBrownianLp a s.toNNReal := by
  let I := ULA.GaussianHilbert.isonormal ULA.CanonicalBrownian.basis
  let L := I.toContinuousLinearMap.comp (timeShift a).toContinuousLinearMap
  have hi := positionLp_eq_brownian_convolution γ hγ t
  unfold positionLp convolutionLp ULA.CanonicalBrownian.valueLp at hi
  have hcont : Continuous (fun s : ℝ => Real.exp (-γ*((t : ℝ)-s)) •
      ULA.CanonicalBrownian.timeIndicator s.toNNReal) := by
    have hb : Continuous (fun s : ℝ => ULA.CanonicalBrownian.timeIndicator s.toNNReal) := by
      rw [show (fun s : ℝ => ULA.CanonicalBrownian.timeIndicator s.toNNReal) =
        (fun s : ℝ => timeKernelLp (fun _ => 1) continuous_const s.toNNReal) from
          funext fun s => (timeKernelLp_one _).symm]
      exact (continuous_timeKernelLp (fun _ => 1) continuous_const).comp continuous_real_toNNReal
    exact (by fun_prop : Continuous (fun s : ℝ => Real.exp (-γ*((t : ℝ)-s)))).smul hb
  have hi' : I (timeKernelLp (psi γ 1) (continuous_psi γ 1) t) =
      I (∫ s in 0..(t : ℝ), Real.exp (-γ*((t : ℝ)-s)) •
        ULA.CanonicalBrownian.timeIndicator s.toNNReal) := by
    change I.toContinuousLinearMap _ = I.toContinuousLinearMap _
    rw [← I.toContinuousLinearMap.intervalIntegral_comp_comm (hcont.intervalIntegrable _ _)]
    simpa only [map_smul, I, LinearIsometry.coe_toContinuousLinearMap] using hi
  have hker := I.injective hi'
  change L (timeKernelLp (psi γ 1) (continuous_psi γ 1) t) = _
  rw [hker, ← L.intervalIntegral_comp_comm (hcont.intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [map_smul]
  congr 1
  exact segmentConvolutionLp_one a s.toNNReal

/-- Integration by parts for the velocity innovation on any Brownian interval. -/
theorem segmentConvolutionLp_velocity_eq_brownian_sub_convolution (γ : ℝ) (hγ : 0 ≤ γ)
    (a t : ℝ≥0) :
    segmentConvolutionLp (psi γ 0) (continuous_psi γ 0) a t = segmentBrownianLp a t -
      γ • ∫ s in 0..(t : ℝ), Real.exp (-γ*((t : ℝ)-s)) • segmentBrownianLp a s.toNNReal := by
  rw [← segmentConvolutionLp_position_eq_brownian_convolution γ hγ]
  exact eq_sub_iff_add_eq.mpr (segmentConvolutionLp_balance γ a t)

end KineticLangevin.BrownianConvolution
