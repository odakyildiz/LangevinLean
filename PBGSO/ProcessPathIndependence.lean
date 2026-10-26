import PBGSO.DriverPathIndependence
import PBGSO.BrownianPathSpace

/-! # Actual independence of whole paths from finite-grid independence
Finite-dimensional restrictions determine the original raw path measure.
The coordinate product law is derived by measure projective uniqueness;
no whole-path independence or final joint-noise law is supplied.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Classical
namespace PBGSO.ProcessPathIndependence

/-- Literal transposition of raw coordinate and time indices. -/
def transpose (I T E : Type*) [MeasurableSpace E] : (I → T → E) ≃ᵐ (T → I → E) where
  toFun p t i := p i t
  invFun p i t := p t i
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    change Measurable (fun (p : I → T → E) (t : T) (i : I) => p i t)
    fun_prop
  measurable_invFun := by
    change Measurable (fun (p : T → I → E) (i : I) (t : T) => p t i)
    fun_prop

variable {Ω I T E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [Fintype I]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (B : I → T → Ω → E)
  (hm : ∀ i t, Measurable (B i t))
include hm

/-- Genuine independence of every finite time restriction implies genuine
independence of the whole raw coordinate paths. -/
theorem paths_independent_of_finite
    (hi : ∀ J : Finset T, iIndepFun (fun i ω => J.restrict (fun t => B i t ω)) Q) :
    iIndepFun (fun i ω => fun t => B i t ω) Q := by
  let m (i : I) := Q.map (fun ω => fun t => B i t ω)
  have hmB (i : I) : Measurable (fun ω => fun t => B i t ω) :=
    measurable_pi_iff.mpr (hm i)
  haveI (i : I) : IsProbabilityMeasure (m i) :=
    (Measure.isProbabilityMeasure_map_iff (hmB i).aemeasurable).mpr inferInstance
  let ν := Measure.pi m
  let F (J : Finset T) := Q.map (fun ω => J.restrict (fun t i => B i t ω))
  have hmF (J : Finset T) : Measurable (fun ω => J.restrict (fun t i => B i t ω)) :=
    measurable_pi_iff.mpr (fun t => measurable_pi_iff.mpr (fun i => hm i t))
  haveI (J : Finset T) : IsProbabilityMeasure (F J) :=
    (Measure.isProbabilityMeasure_map_iff (hmF J).aemeasurable).mpr inferInstance
  have hQ : IsProjectiveLimit (Q.map (fun ω => fun t i => B i t ω)) F :=
    isProjectiveLimit_map (measurable_pi_iff.mpr
      (fun t => measurable_pi_iff.mpr (fun i => hm i t))).aemeasurable
  have hν : IsProjectiveLimit (ν.map (transpose I T E)) F := by
    intro J
    apply (MeasurableEquiv.map_measurableEquiv_injective (transpose J I E))
    rw [Measure.map_map (transpose J I E).measurable (Finset.measurable_restrict J),
      Measure.map_map ((transpose J I E).measurable.comp (Finset.measurable_restrict J))
        (transpose I T E).measurable,
      Measure.map_map (transpose J I E).measurable (hmF J)]
    change (Measure.pi m).map (fun x i => J.restrict (x i)) =
      Q.map (fun ω i => J.restrict (fun t => B i t ω))
    haveI (i : I) : IsProbabilityMeasure ((m i).map J.restrict) :=
      (Measure.isProbabilityMeasure_map_iff (Finset.measurable_restrict J).aemeasurable).mpr
        inferInstance
    rw [Measure.pi_map_pi (fun _ => (Finset.measurable_restrict J).aemeasurable)]
    have hmi (i : I) : (m i).map J.restrict =
        Q.map (fun ω => J.restrict (fun t => B i t ω)) := by
      rw [Measure.map_map (Finset.measurable_restrict J) (hmB i)]
      rfl
    simp_rw [hmi]
    exact ((hi J).map_fun_eq_pi_map (fun i =>
      (measurable_pi_iff.mpr (fun t : J => hm i t)).aemeasurable)).symm
  have he := hQ.unique hν
  have ht : (Q.map (fun ω i t => B i t ω)).map (transpose I T E) =
      ν.map (transpose I T E) := by
    rw [Measure.map_map (transpose I T E).measurable
      (measurable_pi_iff.mpr (fun i => hmB i))]
    exact he
  have hraw := (MeasurableEquiv.map_measurableEquiv_injective (transpose I T E)) ht
  exact (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hmB i).aemeasurable)).mpr hraw

end PBGSO.ProcessPathIndependence

namespace PBGSO.FilteredBrownian
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

/-- Every primitive Driver already has independent whole coordinate paths;
no added whole-noise independence axiom is required. -/
theorem Driver.paths_independent :
    iIndepFun (fun i ω => fun t : ℝ≥0 => D.process i t ω) Q :=
  ProcessPathIndependence.paths_independent_of_finite Q D.process
    (fun i t => ((D.adapted i t).mono (D.filtration.le t)).measurable)
    (D.finite_paths_independent Q)
end PBGSO.FilteredBrownian
