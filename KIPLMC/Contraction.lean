import KIPLMC.Dynamics
import KIPLMC.Laws
import KineticLangevin.OBABOContraction

/-! # The actual particle OBABO contraction

KIPLMC2 uses the shared OBABO map at temperature `1/N`. The synchronous
contraction proof is temperature independent because both noises cancel.
The averaged lifted potential has exactly the original curvature constants.
-/

noncomputable section
open Set
open scoped NNReal
namespace KIPLMC

/-- A common-noise KIPLMC2 step contracts Monmarché's actual phase metric. -/
theorem kiplmc2Step_synchronous_contraction {N dθ dx : ℕ} (hN : 0 < N)
    (U : IPLA.Joint dθ dx → ℝ) (m γ h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U)
    (hLip : LipschitzWith L (gradient U)) (hm : 0 ≤ m) (hmL : m ≤ (L : ℝ))
    (hγ : 0 < γ) (hL : 0 < (L : ℝ)) (hh : 0 ≤ h)
    (hfriction : 4*(L : ℝ) ≤ γ^2) (hstep : 33*γ^3*h ≤ m)
    (z w : State N dθ dx × State N dθ dx) (ξ ξ' : State N dθ dx) :
    KineticLangevin.weightedPhaseEnergy (1/(L : ℝ)) (1/γ)
      (kiplmc2Step U γ h z ξ ξ'-kiplmc2Step U γ h w ξ ξ') ≤
      (1-m*h/(3*γ))*KineticLangevin.weightedPhaseEnergy (1/(L : ℝ)) (1/γ) (z-w) := by
  have heq : gradient (@averagePotential N dθ dx U) = force U :=
    funext (gradient_averagePotential hdiff)
  have hc := KineticLangevin.obaboStep_synchronous_contraction
    (@averagePotential N dθ dx U) m γ h (thermalAmplitude N γ h) L
    (averagePotential_differentiable hdiff) (averagePotential_strongConvex hN hsc)
    (averagePotential_gradient_lipschitz hN hdiff hLip) hm hmL hγ hL hh hfriction hstep z w ξ ξ'
  simpa only [heq,kiplmc2Step] using hc

/-- The exact implemented KIPLMC2 chains contract under the same sequence
of paired thermostat innovations. No Gaussian-law premise is needed. -/
theorem kiplmc2Chain_synchronous_contraction {N dθ dx : ℕ} (hN : 0 < N)
    (U : IPLA.Joint dθ dx → ℝ) (m γ h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U)
    (hLip : LipschitzWith L (gradient U)) (hm : 0 ≤ m) (hmL : m ≤ (L : ℝ))
    (hγ : 0 < γ) (hL : 0 < (L : ℝ)) (hh : 0 ≤ h)
    (hfriction : 4*(L : ℝ) ≤ γ^2) (hstep : 33*γ^3*h ≤ m)
    (z w : State N dθ dx × State N dθ dx)
    (noise : ℕ → State N dθ dx × State N dθ dx) (n : ℕ) :
    KineticLangevin.weightedPhaseEnergy (1/(L : ℝ)) (1/γ)
      (kiplmc2Chain U γ h z noise n-kiplmc2Chain U γ h w noise n) ≤
      (1-m*h/(3*γ))^n*KineticLangevin.weightedPhaseEnergy (1/(L : ℝ)) (1/γ) (z-w) := by
  have heq : gradient (@averagePotential N dθ dx U) = force U :=
    funext (gradient_averagePotential hdiff)
  apply KineticLangevin.obabo_synchronous_iteration
    (@averagePotential N dθ dx U) m γ h (thermalAmplitude N γ h) L
    (averagePotential_differentiable hdiff) (averagePotential_strongConvex hN hsc)
    (averagePotential_gradient_lipschitz hN hdiff hLip) hm hmL hγ hL hh hfriction hstep
    (fun k ↦ kiplmc2Chain U γ h z noise k) (fun k ↦ kiplmc2Chain U γ h w noise k)
    (fun k ↦ (noise k).1) (fun k ↦ (noise k).2)
  · intro k
    simpa only [heq,kiplmc2Chain,kiplmc2Step] using
      (ULA.noiseDrivenChain_succ (fun s ξ ↦ kiplmc2Step U γ h s ξ.1 ξ.2) z noise k)
  · intro k
    simpa only [heq,kiplmc2Chain,kiplmc2Step] using
      (ULA.noiseDrivenChain_succ (fun s ξ ↦ kiplmc2Step U γ h s ξ.1 ξ.2) w noise k)

/-- Equal initial velocities give a dimension-free position contraction for
the actual particle chains, with the original physical-time rate. -/
theorem kiplmc2Chain_position_decay {N dθ dx : ℕ} (hN : 0 < N)
    (U : IPLA.Joint dθ dx → ℝ) (m γ h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U)
    (hLip : LipschitzWith L (gradient U)) (hm : 0 ≤ m) (hmL : m ≤ (L : ℝ))
    (hγ : 0 < γ) (hL : 0 < (L : ℝ)) (hh : 0 ≤ h)
    (hfriction : 4*(L : ℝ) ≤ γ^2) (hstep : 33*γ^3*h ≤ m)
    (z w : State N dθ dx × State N dθ dx) (hvelocity : z.1 = w.1)
    (noise : ℕ → State N dθ dx × State N dθ dx) (n : ℕ) :
    ‖(kiplmc2Chain U γ h z noise n).2-(kiplmc2Chain U γ h w noise n).2‖ ≤
      Real.sqrt (2*(1-m*h/(3*γ))^n)*‖z.2-w.2‖ := by
  have heq : gradient (@averagePotential N dθ dx U) = force U :=
    funext (gradient_averagePotential hdiff)
  apply KineticLangevin.obabo_synchronous_position_decay
    (@averagePotential N dθ dx U) m γ h (thermalAmplitude N γ h) L
    (averagePotential_differentiable hdiff) (averagePotential_strongConvex hN hsc)
    (averagePotential_gradient_lipschitz hN hdiff hLip) hm hmL hγ hL hh hfriction hstep
    (fun k ↦ kiplmc2Chain U γ h z noise k) (fun k ↦ kiplmc2Chain U γ h w noise k)
    (fun k ↦ (noise k).1) (fun k ↦ (noise k).2)
  · intro k
    simpa only [heq,kiplmc2Chain,kiplmc2Step] using
      (ULA.noiseDrivenChain_succ (fun s ξ ↦ kiplmc2Step U γ h s ξ.1 ξ.2) z noise k)
  · intro k
    simpa only [heq,kiplmc2Chain,kiplmc2Step] using
      (ULA.noiseDrivenChain_succ (fun s ξ ↦ kiplmc2Step U γ h s ξ.1 ξ.2) w noise k)
  · exact hvelocity

end KIPLMC
