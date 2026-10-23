import KIPLMC.Dynamics
import KineticLangevin.FlowLaw

/-! # Actual kinetic particle position laws

The force is the gradient of the averaged particle potential. We therefore
reuse the selected continuous-forcing kinetic flow and its independent-product
law, rather than assuming a fresh law-level contraction principle.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace KIPLMC

local instance forcingMeasurable (N dθ dx : ℕ) (T : ℝ) :
    MeasurableSpace (KineticLangevin.VelocityForcing (E := State N dθ dx) T) := borel _
local instance forcingBorel (N dθ dx : ℕ) (T : ℝ) :
    BorelSpace (KineticLangevin.VelocityForcing (E := State N dθ dx) T) := ⟨rfl⟩

/-- The actual independent-product position law of physical-time KIPLD.
The source `Q` specifies the initial velocity and continuous velocity forcing;
its Brownian specialization uses amplitude `sqrt (2*γ/N)`. -/
def kipldPositionLaw {N dθ dx : ℕ} (hN : 0 < N)
    (U : IPLA.Joint dθ dx → ℝ) (L γ : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (T : ℝ) (hT : 0 ≤ T) (t : ℝ) (μ : Measure (State N dθ dx))
    (Q : Measure (State N dθ dx ×
      KineticLangevin.VelocityForcing (E := State N dθ dx) T)) :
    Measure (State N dθ dx) :=
  KineticLangevin.kineticPositionLaw (gradient (@averagePotential N dθ dx U)) L γ
    (averagePotential_gradient_lipschitz hN hdiff hLip) T hT t μ Q

/-- The physical-time KIPLD endpoint law is a probability measure. -/
theorem kipldPositionLaw_probability {N dθ dx : ℕ} (hN : 0 < N)
    (U : IPLA.Joint dθ dx → ℝ) (L γ : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (T : ℝ) (hT : 0 ≤ T) (t : ℝ) (ht : t ∈ Icc 0 T)
    (μ : Measure (State N dθ dx)) [IsProbabilityMeasure μ]
    (Q : Measure (State N dθ dx ×
      KineticLangevin.VelocityForcing (E := State N dθ dx) T)) [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (kipldPositionLaw hN U L γ hdiff hLip T hT t μ Q) :=
  KineticLangevin.kineticPositionLaw_probability _ L γ _ T hT t ht μ Q

/-- Actual position-law contraction in physical time, with a constant and
rate independent of particle count. The two position laws use the same source
law independently of initialization; target stationarity is not a premise. -/
theorem kipldPositionLaw_wasserstein2Real {N dθ dx : ℕ} (hN : 0 < N)
    (U : IPLA.Joint dθ dx → ℝ) (m : ℝ) (L γ : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U)
    (hLip : LipschitzWith L (gradient U)) (hmL : m ≤ (L : ℝ))
    (hγ : 0 < (γ : ℝ)) (hfriction : m + (L : ℝ) ≤ (γ : ℝ)^2)
    (T : ℝ) (hT : 0 ≤ T) (t : ℝ) (ht : t ∈ Icc 0 T)
    (μ ν : Measure (State N dθ dx)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : Measure (State N dθ dx ×
      KineticLangevin.VelocityForcing (E := State N dθ dx) T)) [IsProbabilityMeasure Q]
    (hfinite : ULA.wasserstein2 μ ν ≠ ⊤) :
    ULA.wasserstein2Real (kipldPositionLaw hN U L γ hdiff hLip T hT t μ Q)
      (kipldPositionLaw hN U L γ hdiff hLip T hT t ν Q) ≤
      Real.sqrt 2 * Real.exp ((-m / γ)*t) * ULA.wasserstein2Real μ ν :=
  KineticLangevin.kineticPositionLaw_wasserstein2Real
    (@averagePotential N dθ dx U) m L γ (averagePotential_differentiable hdiff)
    (averagePotential_strongConvex hN hsc) (averagePotential_gradient_lipschitz hN hdiff hLip)
    hmL hγ hfriction T hT t ht μ ν Q hfinite

end KIPLMC
