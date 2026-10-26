import PBGSO.BrownianPathSpace

/-! # Original initial independence from finite observed noise
Finite joint time observations determine the full initial/path product law.
No whole-path independence or product-law conclusion is assumed.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical
namespace PBGSO.ProcessPathIndependence
variable {Ω T V A : Type*} [MeasurableSpace Ω] [MeasurableSpace V] [MeasurableSpace A]
  [Nonempty T] (Q : Measure Ω) [IsProbabilityMeasure Q]
  (Y : T → Ω → V) (X : Ω → A) (hm : ∀ t, Measurable (Y t)) (hX : Measurable X)
include hm hX

/-- Independence of initialization from every finite noise observation
implies independence from the original complete raw path. -/
theorem initial_independent_of_finite
    (hi : ∀ J : Finset T, IndepFun X (fun ω => J.restrict (fun t => Y t ω)) Q) :
    IndepFun X (fun ω => fun t => Y t ω) Q := by
  have hmY : Measurable (fun ω => fun t => Y t ω) := measurable_pi_iff.mpr hm
  let μX := Q.map X
  let μY := Q.map (fun ω => fun t => Y t ω)
  haveI : IsProbabilityMeasure μX :=
    (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).mpr inferInstance
  haveI : IsProbabilityMeasure μY :=
    (Measure.isProbabilityMeasure_map_iff hmY.aemeasurable).mpr inferInstance
  let ν := μX.prod μY
  let f : A × (T → V) → T → A × V := fun p t => (p.1,p.2 t)
  have hf : Measurable f := by fun_prop
  let F (J : Finset T) := Q.map (fun ω => J.restrict (fun t => (X ω,Y t ω)))
  have hmF (J : Finset T) : Measurable (fun ω => J.restrict (fun t => (X ω,Y t ω))) :=
    measurable_pi_iff.mpr (fun t => hX.prodMk (hm t))
  haveI (J : Finset T) : IsProbabilityMeasure (F J) :=
    (Measure.isProbabilityMeasure_map_iff (hmF J).aemeasurable).mpr inferInstance
  have hQ : IsProjectiveLimit (Q.map (fun ω => fun t => (X ω,Y t ω))) F :=
    isProjectiveLimit_map (measurable_pi_iff.mpr (fun t => hX.prodMk (hm t))).aemeasurable
  have hν : IsProjectiveLimit (ν.map f) F := by
    intro J
    let g : A × (J → V) → J → A × V := fun p t => (p.1,p.2 t)
    have hg : Measurable g := by fun_prop
    have hmJ : Measurable (fun ω => J.restrict (fun t => Y t ω)) :=
      measurable_pi_iff.mpr (fun t => hm t)
    have hμJ : μY.map J.restrict = Q.map (fun ω => J.restrict (fun t => Y t ω)) := by
      rw [Measure.map_map (Finset.measurable_restrict J) hmY]
      rfl
    have hp : μX.prod (Q.map (fun ω => J.restrict (fun t => Y t ω))) =
        ν.map (Prod.map id J.restrict) := by
      rw [← hμJ]
      simpa only [Measure.map_id] using
        Measure.map_prod_map μX μY measurable_id (Finset.measurable_restrict J)
    have hjoint := (hi J).map_prod_eq_prod_map_map hX.aemeasurable hmJ.aemeasurable
    calc
      (ν.map f).map J.restrict = ν.map (fun p => J.restrict (f p)) :=
        Measure.map_map (Finset.measurable_restrict J) hf
      _ = (μX.prod (Q.map (fun ω => J.restrict (fun t => Y t ω)))).map g := by
        rw [hp,Measure.map_map hg (measurable_id.prodMap (Finset.measurable_restrict J))]
        rfl
      _ = (Q.map (fun ω => (X ω,J.restrict (fun t => Y t ω)))).map g := by rw [hjoint]
      _ = F J := by
        rw [Measure.map_map hg (hX.prodMk hmJ)]
        rfl
  have he := hQ.unique hν
  let t0 : T := Classical.choice inferInstance
  let g : (T → A × V) → A × (T → V) := fun p => ((p t0).1,fun t => (p t).2)
  have hg : Measurable g := by fun_prop
  have hh := congrArg (Measure.map g) he
  rw [Measure.map_map hg (measurable_pi_iff.mpr (fun t => hX.prodMk (hm t))),
    Measure.map_map hg hf] at hh
  have hleft : g ∘ (fun ω => fun t => (X ω,Y t ω)) = fun ω => (X ω,fun t => Y t ω) := rfl
  have hright : g ∘ f = id := rfl
  rw [hleft,hright,Measure.map_id] at hh
  exact (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hmY.aemeasurable).mpr hh
end PBGSO.ProcessPathIndependence
