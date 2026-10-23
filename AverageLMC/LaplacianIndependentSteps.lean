import UnadjustedLangevin.MarkovLaw

set_option linter.style.header false

/-!
# Fresh-noise laws for weighted Euler recursions

Keeping a passive coordinate in the state retains an arbitrary function of
the initialization. The same ordinary iid realization theorem then identifies
the joint law of that weight, the Euler state, and its next Gaussian noise.
No conditional expectation or Dynkin identity is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace AverageLMC

variable {Ω H Z : Type*} [MeasurableSpace Ω] [MeasurableSpace H] [MeasurableSpace Z]

/-- In every independent iid realization, the actual current recursion state
and the next innovation have the product joint law. -/
theorem noiseDrivenChain_joint_fresh_of_iid
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : H → Z → H) (hF : Measurable (Function.uncurry F))
    (X : Ω → H) (W : ℕ → Ω → Z) (hX : AEMeasurable X P)
    (hW : ∀ n, AEMeasurable (W n) P)
    (hind : IndepFun X (fun a n ↦ W n a) P) (hiid : iIndepFun W P)
    (η : Measure Z) [IsProbabilityMeasure η] (hlaw : ∀ n, P.map (W n) = η) (n : ℕ) :
    P.map (fun a ↦ (ULA.noiseDrivenChain F (X a) (fun k ↦ W k a) n, W n a)) =
      (P.map (fun a ↦ ULA.noiseDrivenChain F (X a) (fun k ↦ W k a) n)).prod η := by
  let Q := Measure.infinitePi (fun _ : ℕ ↦ η)
  have hpath : P.map (fun a k ↦ W k a) = Q := by
    have hp := hiid.map_fun_eq_infinitePi_map₀' hW
    simpa only [hlaw] using hp
  have hpair : P.map (fun a ↦ (X a, fun k ↦ W k a)) = (P.map X).prod Q := by
    rw [hind.map_prod_eq_prod_map_map hX (aemeasurable_pi_iff.mpr hW), hpath]
  have hmap : Measurable (fun p : H × (ℕ → Z) ↦
      (ULA.noiseDrivenChain F p.1 p.2 n, p.2 n)) :=
    (ULA.noiseDrivenChain_measurable F hF n).prodMk (by fun_prop)
  have hprod : IsProbabilityMeasure (P.map X) := by
    constructor
    rw [Measure.map_apply_of_aemeasurable hX MeasurableSet.univ,
      Set.preimage_univ, measure_univ]
  letI := hprod
  have hjoint := congrArg (fun μ : Measure (H × (ℕ → Z)) ↦ μ.map
    (fun p ↦ (ULA.noiseDrivenChain F p.1 p.2 n, p.2 n))) hpair
  rw [AEMeasurable.map_map_of_aemeasurable hmap.aemeasurable
    (hX.prodMk (aemeasurable_pi_iff.mpr hW)),
    ULA.chainLaw_joint_fresh F hF (P.map X) η n] at hjoint
  have hstate := ULA.noiseDrivenChain_law_of_iid P F hF X W hX hW hind hiid η hlaw n
  rw [← hstate] at hjoint
  exact hjoint

/-- A passive initial coordinate is retained exactly at every iteration. -/
theorem noiseDrivenChain_passive {A : Type*} (F : H → Z → H)
    (a : A) (x : H) (w : ℕ → Z) (n : ℕ) :
    ULA.noiseDrivenChain (fun p : A × H ↦ fun z ↦ (p.1, F p.2 z)) (a, x) w n =
      (a, ULA.noiseDrivenChain F x w n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ULA.noiseDrivenChain_succ, ih]

end AverageLMC
