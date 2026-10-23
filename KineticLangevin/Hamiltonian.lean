import KineticLangevin.Flow
import KineticLangevin.OBABO
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Group.Prod

/-! # Hamiltonian energy and volume-preserving elementary flows

These are ingredients for kinetic Gibbs stationarity, not a replacement for
that theorem. We prove exact energy conservation for the actual zero-noise,
zero-friction kinetic integral flow. Kicks and drifts preserve product Haar
measure, hence so does their Verlet composition. The remaining flow-limit
and Gibbs-invariance arguments are separate analytic steps.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal
namespace KineticLangevin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Total energy in velocity-first phase coordinates. -/
def hamiltonianEnergy (f : E → ℝ) (z : E × E) : ℝ := f z.2 + ‖z.1‖^2 / 2

/-- Force work and kinetic-energy change cancel along the Hamiltonian equations. -/
theorem hasDerivWithinAt_hamiltonianEnergy (f : E → ℝ) (hdiff : Differentiable ℝ f)
    (v x : ℝ → E) (t : ℝ)
    (hv : HasDerivWithinAt v (-gradient f (x t)) (Ici t) t)
    (hx : HasDerivWithinAt x (v t) (Ici t) t) :
    HasDerivWithinAt (fun r ↦ hamiltonianEnergy f (v r,x r)) 0 (Ici t) t := by
  have hf := (hdiff (x t)).hasFDerivAt.comp_hasDerivWithinAt t hx
  have hk := hv.norm_sq.div_const 2
  have he : fderiv ℝ f (x t) (v t) + (2 * ⟪v t,-gradient f (x t)⟫) / 2 = 0 := by
    rw [← inner_gradient_left]
    simp only [inner_neg_right, real_inner_comm (v t) (gradient f (x t))]
    ring
  have hh := hf.add hk
  rw [he] at hh
  simpa only [hamiltonianEnergy, Function.comp_def, Pi.add_def] using hh

/-- A scalar continuous function with vanishing right derivative on the
half-open horizon is constant, including its terminal endpoint. -/
theorem eq_initial_of_right_derivative_zero (F : ℝ → ℝ) (T : ℝ)
    (hF : ContinuousOn F (Icc 0 T))
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt F 0 (Ici t) t)
    (t : ℝ) (ht : t ∈ Icc 0 T) : F t = F 0 := by
  have hu := le_gronwallBound_of_liminf_deriv_right_le hF
    (fun s hs r hr ↦ (hd s hs).liminf_right_slope_le hr)
    (le_refl (F 0)) (fun s _ ↦ by simp : ∀ s ∈ Ico 0 T, (0 : ℝ) ≤ 0 * F s + 0) t ht
  have hl := le_gronwallBound_of_liminf_deriv_right_le hF.neg
    (fun s hs r hr ↦ ((hd s hs).neg).liminf_right_slope_le hr)
    (le_refl (-F 0))
    (fun s _ ↦ by simp : ∀ s ∈ Ico 0 T, (-(0 : ℝ)) ≤ 0 * (-F s) + 0) t ht
  simp only [gronwallBound_ε0, zero_mul, sub_zero, Real.exp_zero, mul_one] at hu hl
  change -(F t) ≤ -(F 0) at hl
  linarith

/-- The actual deterministic Hamiltonian integral flow selected by Picard. -/
def hamiltonianFlow (f : E → ℝ) (M : ℝ≥0) (hLip : LipschitzWith M (gradient f))
    (T : ℝ) (hT : 0 ≤ T) (initial : E × E) : ℝ → E × E :=
  kineticFlow (gradient f) M 0 1 hLip T hT initial 0

/-- Energy conservation for an actual zero-friction, zero-forcing integral solution. -/
theorem hamiltonianFlow_energy (f : E → ℝ) (hdiff : Differentiable ℝ f)
    (M : ℝ≥0) (hLip : LipschitzWith M (gradient f)) (T : ℝ) (hT : 0 ≤ T)
    (initial : E × E) (t : ℝ) (ht : t ∈ Icc 0 T) :
    hamiltonianEnergy f (hamiltonianFlow f M hLip T hT initial t) = hamiltonianEnergy f initial := by
  let Y := hamiltonianFlow f M hLip T hT initial
  have hs := kineticFlow_spec (gradient f) M 0 1 hLip T hT initial 0
  have heY : ∀ r ∈ Icc 0 T,
      Y r = initial - ∫ s in 0..r, kineticNegativeDrift (gradient f) 0 1 (Y s) := by
    intro r hr
    have he := hs.2.2 r hr
    simp only [normalizedForcing, ContinuousMap.zero_apply, sub_self, Prod.mk_zero_zero,
      add_zero] at he
    dsimp [Y, hamiltonianFlow]
    rw [sub_eq_iff_eq_add] at he
    simpa only [NNReal.coe_zero, NNReal.coe_one, neg_add_eq_sub] using he
  have hcont : Continuous Y := hs.1
  have hcDrift : Continuous (fun r ↦ kineticNegativeDrift (gradient f) 0 1 (Y r)) :=
    (kineticNegativeDrift_lipschitz (gradient f) M 0 1 hLip).continuous.comp hcont
  have hdY (r : ℝ) (hr : r ∈ Ico 0 T) :
      HasDerivWithinAt Y (-kineticNegativeDrift (gradient f) 0 1 (Y r)) (Ici r) r := by
    have hd := intervalIntegral.integral_hasDerivAt_right
      (hcDrift.intervalIntegrable 0 r) (hcDrift.stronglyMeasurableAtFilter volume (𝓝 r))
      hcDrift.continuousAt
    have hevent : Y =ᶠ[𝓝[Ici r] r]
        (fun s ↦ initial - ∫ u in 0..s, kineticNegativeDrift (gradient f) 0 1 (Y u)) := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds hr.2)] with s hs hsT
      exact heY s ⟨hr.1.trans hs,hsT.le⟩
    exact (hd.const_sub initial).hasDerivWithinAt.congr_of_eventuallyEq hevent
      (heY r ⟨hr.1,hr.2.le⟩)
  have hdEnergy : ∀ r ∈ Ico 0 T,
      HasDerivWithinAt (fun s ↦ hamiltonianEnergy f (Y s)) 0 (Ici r) r := by
    intro r hr
    have hv := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivWithinAt r (hdY r hr)
    have hx := (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivWithinAt r (hdY r hr)
    apply hasDerivWithinAt_hamiltonianEnergy f hdiff (fun s ↦ (Y s).1) (fun s ↦ (Y s).2) r
    · simpa [kineticNegativeDrift, Function.comp_def] using hv
    · simpa [kineticNegativeDrift, Function.comp_def] using hx
  have hcontEnergy : ContinuousOn (fun r ↦ hamiltonianEnergy f (Y r)) (Icc 0 T) := by
    exact ((hdiff.continuous.comp hcont.snd).add ((hcont.fst.norm.pow 2).div_const 2)).continuousOn
  have he := eq_initial_of_right_derivative_zero _ T hcontEnergy hdEnergy t ht
  simpa only [Y, hamiltonianFlow, hs.2.1] using he


/-- Velocity reversal conjugates the symmetric Hamiltonian composition to
its negative-time inverse. -/
theorem reverseVelocity_verlet (g : E → E) (h : ℝ) (z : E × E) :
    reverseVelocity (verletStep g h (reverseVelocity z)) = verletStep g (-h) z := by
  have hk (w : E × E) : reverseVelocity (kickStep g (h/2) w) =
      kickStep g (-(h/2)) (reverseVelocity w) := by
    simpa only [reverseVelocity_twice] using reverseVelocity_kick g (h/2) (reverseVelocity w)
  have ha (w : E × E) : reverseVelocity (driftStep h w) =
      driftStep (-h) (reverseVelocity w) := by
    simpa only [reverseVelocity_twice] using reverseVelocity_drift h (reverseVelocity w)
  unfold verletStep
  rw [hk,ha,hk,reverseVelocity_twice,neg_div]

/-- A velocity-reversed Verlet proposal is an exact involution. -/
def verletProposal (g : E → E) (h : ℝ) (z : E × E) : E × E :=
  reverseVelocity (verletStep g h z)

theorem verletProposal_involutive (g : E → E) (h : ℝ) :
    Function.Involutive (verletProposal g h) := by
  intro z
  exact (reverseVelocity_verlet g h (verletStep g h z)).trans (verletStep_neg g h z)

/-- Reversing velocity leaves the actual Hamiltonian energy unchanged. -/
@[simp] theorem hamiltonianEnergy_reverseVelocity (f : E → ℝ) (z : E × E) :
    hamiltonianEnergy f (reverseVelocity z) = hamiltonianEnergy f z := by
  simp [hamiltonianEnergy, reverseVelocity]

/-- Exact kinetic-energy change across two half kicks, with the two force
values retained rather than replaced by a regularity bound. -/
theorem kineticEnergy_halfkicks (h : ℝ) (v gx gy : E) :
    (‖v - (h/2) • gy‖^2 - ‖v + (h/2) • gx‖^2) / 2 =
      -(h/2) * ⟪v,gx+gy⟫ + h^2/8 * (‖gy‖^2-‖gx‖^2) := by
  simp only [norm_sub_sq_real, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_smul_right, inner_add_right]
  ring

/-- Verlet's exact energy defect is a trapezoidal force-work remainder plus
an explicit difference of squared force norms. -/
theorem verlet_energy_defect_identity (f : E → ℝ) (g : E → E) (h : ℝ) (z : E × E) :
    let vhalf := z.1 - (h/2) • g z.2
    let xnext := z.2 + h • vhalf
    hamiltonianEnergy f (verletStep g h z) - hamiltonianEnergy f z =
      f xnext - f z.2 - (h/2) * ⟪vhalf,g z.2+g xnext⟫ +
        h^2/8 * (‖g xnext‖^2-‖g z.2‖^2) := by
  let vhalf := z.1 - (h/2) • g z.2
  let xnext := z.2 + h • vhalf
  have hv : vhalf + (h/2) • g z.2 = z.1 := by dsimp [vhalf]; module
  have hk := kineticEnergy_halfkicks h vhalf (g z.2) (g xnext)
  rw [hv] at hk
  change (f xnext + ‖vhalf - (h/2) • g xnext‖^2 / 2) -
    (f z.2 + ‖z.1‖^2/2) = _
  nlinarith [hk]

section Volume
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure E) [SFinite μ] [Measure.IsAddLeftInvariant μ]

/-- A free-transport substep is a shear and preserves product Haar measure. -/
theorem driftStep_measurePreserving (h : ℝ) :
    MeasurePreserving (driftStep (E := E) h) (μ.prod μ) (μ.prod μ) := by
  have hm : Measurable (Function.uncurry (fun v x : E ↦ h • v + x)) := by fun_prop
  have hp := (MeasurePreserving.id μ).skew_product hm
    (Filter.Eventually.of_forall fun v ↦ (measurePreserving_add_left μ (h • v)).map_eq)
  convert hp using 1
  funext z
  simp [driftStep, add_comm]

/-- A force kick is a position-dependent velocity translation. It preserves
product Haar measure for every measurable force. -/
theorem kickStep_measurePreserving (g : E → E) (hg : Measurable g) (h : ℝ) :
    MeasurePreserving (kickStep g h) (μ.prod μ) (μ.prod μ) := by
  have hm : Measurable (Function.uncurry (fun x v : E ↦ (-h) • g x + v)) :=
    ((hg.comp measurable_fst).const_smul (-h)).add measurable_snd
  have hp := (MeasurePreserving.id μ).skew_product hm
    (Filter.Eventually.of_forall fun x ↦ (measurePreserving_add_left μ ((-h) • g x)).map_eq)
  have hswap : MeasurePreserving (Prod.swap : E × E → E × E) (μ.prod μ) (μ.prod μ) :=
    Measure.measurePreserving_swap
  have hc := hswap.comp (hp.comp hswap)
  convert hc using 1
  funext z
  simp [Function.comp_def, Prod.swap, kickStep, sub_eq_add_neg, neg_smul, add_comm]

/-- The complete kick-drift-kick composition preserves product Haar volume. -/
theorem verletStep_measurePreserving (g : E → E) (hg : Measurable g) (h : ℝ) :
    MeasurePreserving (verletStep g h) (μ.prod μ) (μ.prod μ) := by
  have hc := (kickStep_measurePreserving μ g hg (h/2)).comp
    ((driftStep_measurePreserving μ h).comp (kickStep_measurePreserving μ g hg (h/2)))
  convert hc using 1
  funext z
  rfl

/-- The velocity reversal is measure preserving for a symmetric Haar factor. -/
theorem reverseVelocity_measurePreserving [Measure.IsNegInvariant μ] :
    MeasurePreserving (reverseVelocity (E := E)) (μ.prod μ) (μ.prod μ) := by
  convert (Measure.measurePreserving_neg μ).prod (MeasurePreserving.id μ) using 1
  funext z
  rfl

/-- The reversible Verlet proposal is an actual volume-preserving involution. -/
theorem verletProposal_measurePreserving [Measure.IsNegInvariant μ]
    (g : E → E) (hg : Measurable g) (h : ℝ) :
    MeasurePreserving (verletProposal g h) (μ.prod μ) (μ.prod μ) := by
  convert (reverseVelocity_measurePreserving μ).comp (verletStep_measurePreserving μ g hg h) using 1
  funext z
  rfl

end Volume
end KineticLangevin
