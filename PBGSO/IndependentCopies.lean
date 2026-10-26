import PBGSO.LpPullback
import PBGSO.Sampling
import Mathlib.Probability.Independence.Basic

/-! # Actual independent reference trajectories on a product seed space

Independent seeds carry the entire one-copy trajectory, including its initial
state and driving-noise seed. The fixed-time cloud law and independence of the
whole trajectories follow from the actual product construction. Interacting
particles are not asserted to be independent.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace PBGSO
namespace IndependentCopies

variable {Ω Z J : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] [Fintype J]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- One independent complete seed per reference copy. -/
def seeds : Measure (J → Ω) := Measure.pi (fun _ : J => Q)

instance seeds_probability : IsProbabilityMeasure (seeds (J := J) Q) := by
  unfold seeds
  infer_instance

/-- Apply the same actual one-copy random variable to each independent seed. -/
def cloud (V : Ω → Z) (ω : J → Ω) : J → Z := fun i => V (ω i)

@[fun_prop] theorem cloud_measurable (V : Ω → Z) (hV : Measurable V) :
    Measurable (cloud (J := J) V) := by
  exact Measurable.of_eval fun i => hV.comp (measurable_pi_apply i)

/-- The true fixed-time cloud marginal is the iid product of the one-copy
law, derived from independent seeds rather than supplied as an assumption. -/
theorem cloud_law (V : Ω → Z) (hV : Measurable V) :
    (seeds (J := J) Q).map (cloud V) = Measure.pi (fun _ : J => Q.map V) := by
  haveI : IsProbabilityMeasure (Q.map V) :=
    (Measure.isProbabilityMeasure_map_iff hV.aemeasurable).mpr inferInstance
  exact Measure.pi_map_pi (fun _ : J => hV.aemeasurable)

/-- The independent seed construction makes the entire coordinate
trajectories independent, not merely their individual fixed-time marginals. -/
theorem trajectories_independent (V : ℝ → Ω → Z) (hV : ∀ t, Measurable (V t)) :
    iIndepFun (fun i (ω : J → Ω) (t : ℝ) => V t (ω i)) (seeds Q) := by
  exact iIndepFun_pi (fun _ : J =>
    (Measurable.of_eval fun t => hV t).aemeasurable)

section Lp
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The actual L² copy is pullback along its seed coordinate. -/
def copyLp (U : Lp Z 2 Q) (i : J) : Lp Z 2 (seeds (J := J) Q) :=
  lpPullbackCLM (measurePreserving_eval (fun _ : J => Q) i) U

theorem copyLp_coe (U : Lp Z 2 Q) (i : J) :
    copyLp Q U i =ᵐ[seeds Q] fun ω => U (ω i) :=
  lpPullback_coe _ U

@[simp] theorem copyLp_norm (U : Lp Z 2 Q) (i : J) : ‖copyLp Q U i‖ = ‖U‖ :=
  lpPullback_norm _ U

end Lp
end IndependentCopies
end PBGSO
