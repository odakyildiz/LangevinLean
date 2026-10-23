import KIPLMC.Geometry
import KineticLangevin.Dynamics
import KineticLangevin.PotentialContraction

/-! # Kinetic particle dynamics in physical time

The potential is the average lifted potential, rather than its sum. The
physical-time force and temperature are both normalized by `N`. Applying the
shared kinetic construction therefore does not require a second SDE proof.
-/

noncomputable section
set_option linter.style.header false
open Set
open scoped NNReal
namespace KIPLMC

theorem averagePotential_differentiable {N dθ dx : ℕ}
    {U : IPLA.Joint dθ dx → ℝ} (hdiff : Differentiable ℝ U) :
    Differentiable ℝ (@averagePotential N dθ dx U) :=
  (IPLA.potential_differentiable hdiff).const_mul _

theorem averagePotential_gradient_lipschitz {N dθ dx : ℕ} (hN : 0 < N)
    {U : IPLA.Joint dθ dx → ℝ} {L : ℝ≥0}
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U)) :
    LipschitzWith L (gradient (@averagePotential N dθ dx U)) := by
  have heq : gradient (@averagePotential N dθ dx U) = force U :=
    funext (gradient_averagePotential hdiff)
  rw [heq]
  exact force_lipschitz hN hdiff hLip

/-- Existence of the physical-time particle equation for every continuous
velocity forcing and every finite horizon. Brownian forcing can be substituted
pathwise, or as a continuous L² input, in the shared kinetic construction. -/
theorem exists_kipld_integral {N dθ dx : ℕ} (hN : 0 < N)
    {U : IPLA.Joint dθ dx → ℝ} (L γ : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (initial : State N dθ dx × State N dθ dx) (B : ℝ → State N dθ dx)
    (hB : Continuous B) (hB0 : B 0 = 0) (T : ℝ) (hT : 0 ≤ T) :
    ∃ Y : ℝ → State N dθ dx × State N dθ dx, Continuous Y ∧ Y 0 = initial ∧
      ∀ t ∈ Icc 0 T,
        Y t - initial = -(∫ s in 0..t,
          KineticLangevin.kineticNegativeDrift (force U) γ 1 (Y s)) + (B t, 0) := by
  exact KineticLangevin.exists_kinetic_integral (force U) L γ 1
    (force_lipschitz hN hdiff hLip) initial B hB hB0 T hT

/-- The shared kinetic contraction applied to the actual particle force.
The scaled particle dimension does not enter the rate. This is a pathwise
position estimate; it does not assume or assert a stationary-law endpoint. -/
theorem kipld_synchronous_position_decay {N dθ dx : ℕ} (hN : 0 < N)
    (U : IPLA.Joint dθ dx → ℝ) (m γ : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U)
    (hLip : LipschitzWith L (gradient U)) (hmL : m ≤ (L : ℝ))
    (hγ : 0 < γ) (hfriction : m + (L : ℝ) ≤ γ ^ 2)
    (T : ℝ) (v x y : ℝ → State N dθ dx) (hv0 : v 0 = 0)
    (hvcont : ContinuousOn v (Icc 0 T))
    (hxcont : ContinuousOn x (Icc 0 T)) (hycont : ContinuousOn y (Icc 0 T))
    (hv : ∀ t ∈ Ico 0 T, HasDerivAt v (-γ • v t - (force U (x t) - force U (y t))) t)
    (hx : ∀ t ∈ Ico 0 T, HasDerivAt (fun r ↦ x r - y r) (v t) t)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖x t - y t‖ ≤ Real.sqrt 2 * Real.exp ((-m / γ) * t) * ‖x 0 - y 0‖ := by
  apply KineticLangevin.potential_synchronous_position_decay
    (@averagePotential N dθ dx U) m γ L (averagePotential_differentiable hdiff)
    (averagePotential_strongConvex hN hsc) (averagePotential_gradient_lipschitz hN hdiff hLip)
    hmL hγ hfriction T v x y hv0 hvcont hxcont hycont
    (fun s hs ↦ by simpa only [gradient_averagePotential hdiff] using hv s hs) hx t ht

end KIPLMC
