import KineticLangevin.Hamiltonian

/-! # Volume preservation without a joint Hamiltonian

The paper's interwoven B-A-B update is a velocity kick, position drift,
and another kick on the complete position space. A measurable force suffices
for preservation of product Haar measure. Thus differentiability and a
conservative joint force are unnecessary for the discrete assertion.
The continuous-flow Jacobian assertion is a separate statement.
-/

noncomputable section
open MeasureTheory
namespace PBGSO

variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
  [CompleteSpace Q] [MeasurableSpace Q] [BorelSpace Q] [SecondCountableTopology Q]

/-- Complete interwoven force kick, using velocity-first phase coordinates. -/
def forceKick (F : Q → Q) (h : ℝ) : Q × Q → Q × Q :=
  KineticLangevin.kickStep F h

/-- Complete position drift, advancing parameters and every particle together. -/
def positionDrift (h : ℝ) : Q × Q → Q × Q :=
  KineticLangevin.driftStep h

/-- The B-A-B part of the paper's M-MFPO method. The force can be
`(average_i F(theta,x_i), (grad_x E(theta,x_i))_i)`. -/
def interwovenBAB (F : Q → Q) (h : ℝ) : Q × Q → Q × Q :=
  KineticLangevin.verletStep F h

/-- Generalised force kicks preserve product Haar volume. -/
theorem forceKick_preserves (μ : Measure Q) [SFinite μ] [Measure.IsAddLeftInvariant μ]
    (F : Q → Q) (hF : Measurable F) (h : ℝ) :
    MeasurePreserving (forceKick F h) (μ.prod μ) (μ.prod μ) :=
  KineticLangevin.kickStep_measurePreserving μ F hF h

/-- Position drifts preserve product Haar volume. -/
theorem positionDrift_preserves (μ : Measure Q) [SFinite μ]
    [Measure.IsAddLeftInvariant μ] (h : ℝ) :
    MeasurePreserving (positionDrift h) (μ.prod μ) (μ.prod μ) :=
  KineticLangevin.driftStep_measurePreserving μ h

/-- The discrete volume assertion of the paper, for arbitrary measurable
coupled forces. Thermostat stages are excluded, as in the source lemma. -/
theorem interwovenBAB_preserves (μ : Measure Q) [SFinite μ]
    [Measure.IsAddLeftInvariant μ] (F : Q → Q) (hF : Measurable F) (h : ℝ) :
    MeasurePreserving (interwovenBAB F h) (μ.prod μ) (μ.prod μ) :=
  KineticLangevin.verletStep_measurePreserving μ F hF h

end PBGSO
