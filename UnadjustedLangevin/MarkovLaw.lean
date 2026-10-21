import UnadjustedLangevin.ChainLaw

set_option linter.style.header false

/-! # Markov update laws of the actual iid recursion

The finite prefix of the canonical noise path is independent of the next noise.
Measurable finite-prefix recursion therefore proves, rather than assumes, that
the actual chain laws iterate the one-step product-noise transition.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ULA

variable {H Z : Type*}

/-- The same recursion evaluated using precisely its finite noise prefix. -/
def finiteNoiseChain (F : H → Z → H) (x : H) : {n : ℕ} → (Fin n → Z) → H
  | 0, _ => x
  | n + 1, w => F (finiteNoiseChain F x (fun i : Fin n ↦ w i.castSucc)) (w (Fin.last n))

/-- Finite-prefix and infinite-path implementations agree pointwise. -/
theorem finiteNoiseChain_eq (F : H → Z → H) (x : H) (w : ℕ → Z) (n : ℕ) :
    finiteNoiseChain F x (fun i : Fin n ↦ w i) = noiseDrivenChain F x w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [finiteNoiseChain, noiseDrivenChain_succ, Fin.val_castSucc, Fin.val_last] using
      congrArg (fun y ↦ F y (w n)) ih

variable [MeasurableSpace H] [MeasurableSpace Z]

/-- The finite-prefix recursion is a measurable function of its inputs. -/
theorem finiteNoiseChain_measurable (F : H → Z → H)
    (hF : Measurable (Function.uncurry F)) (n : ℕ) :
    Measurable (fun p : H × (Fin n → Z) ↦ finiteNoiseChain F p.1 p.2) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
    exact hF.comp ((ih.comp (measurable_fst.prodMk (by fun_prop))).prodMk (by fun_prop))

/-- The canonical iid path prefix and next coordinate are independent. -/
theorem iid_prefix_independent_fresh (η : Measure Z) [IsProbabilityMeasure η] (n : ℕ) :
    IndepFun (fun w : ℕ → Z ↦ fun i : Fin n ↦ w i) (fun w ↦ w n)
      (Measure.infinitePi (fun _ : ℕ ↦ η)) := by
  have hind : iIndepFun (fun k (w : ℕ → Z) ↦ w k)
      (Measure.infinitePi (fun _ : ℕ ↦ η)) :=
    iIndepFun_infinitePi (X := fun _ x ↦ x) (by fun_prop)
  have hdis : Disjoint (Finset.range n) ({n} : Finset ℕ) := by simp
  have hp := hind.indepFun_finset (Finset.range n) {n} hdis (by fun_prop)
  exact hp.comp
    (φ := fun w : (k : (Finset.range n : Finset ℕ)) → Z ↦
      fun i : Fin n ↦ w ⟨i.val, Finset.mem_range.mpr i.isLt⟩)
    (ψ := fun w : (k : ({n} : Finset ℕ)) → Z ↦ w ⟨n, by simp⟩)
    (by fun_prop) (by fun_prop)

/-- One Markov step driven by an independent noise variable. -/
def markovStep (F : H → Z → H) (η : Measure Z) (μ : Measure H) : Measure H :=
  (μ.prod η).map (Function.uncurry F)

/-- Iterated Markov-step laws, starting from `μ`. -/
def markovLaws (F : H → Z → H) (η : Measure Z) (μ : Measure H) : ℕ → Measure H
  | 0 => μ
  | n + 1 => markovStep F η (markovLaws F η μ n)

/-- The joint law of the actual current state and its next iid innovation is
the product of the actual state law and the specified innovation law. -/
theorem chainLaw_joint_fresh
    (F : H → Z → H) (hF : Measurable (Function.uncurry F))
    (μ : Measure H) [IsProbabilityMeasure μ] (η : Measure Z) [IsProbabilityMeasure η]
    (n : ℕ) :
    (μ.prod (Measure.infinitePi (fun _ : ℕ ↦ η))).map
      (fun p ↦ (noiseDrivenChain F p.1 p.2 n, p.2 n)) =
    (chainLaw F μ (Measure.infinitePi (fun _ : ℕ ↦ η)) n).prod η := by
  let Q := Measure.infinitePi (fun _ : ℕ ↦ η)
  let pref : (ℕ → Z) → (Fin n → Z) := fun w i ↦ w i
  let ρ := Q.map pref
  let ν := μ.prod ρ
  let C : H × (Fin n → Z) → H := fun p ↦ finiteNoiseChain F p.1 p.2
  have hprefix : Measurable pref := by fun_prop
  have hC : Measurable C := finiteNoiseChain_measurable F hF n
  have hρ : IsProbabilityMeasure ρ := by
    constructor
    dsimp only [ρ]
    rw [Measure.map_apply hprefix MeasurableSet.univ, Set.preimage_univ, measure_univ]
  have hp : Q.map (fun w ↦ (pref w, w n)) = ρ.prod η := by
    rw [(iid_prefix_independent_fresh η n).map_prod_eq_prod_map_map
      hprefix.aemeasurable (measurable_pi_apply n).aemeasurable,
      Measure.infinitePi_map_eval]
  have hgroup : (μ.prod Q).map (fun p ↦ (p.1, (pref p.2, p.2 n))) =
      μ.prod (ρ.prod η) := by
    have h := Measure.map_prod_map μ Q measurable_id
      (hprefix.prodMk (measurable_pi_apply n))
    rw [Measure.map_id, hp] at h
    convert h.symm using 1
    apply Measure.map_congr
    exact ae_of_all _ fun _ ↦ rfl
  have hassoc : (μ.prod Q).map (fun p ↦ ((p.1, pref p.2), p.2 n)) = ν.prod η := by
    have h := congrArg (fun κ : Measure (H × ((Fin n → Z) × Z)) ↦
      κ.map (MeasurableEquiv.prodAssoc.symm : H × ((Fin n → Z) × Z) →
        (H × (Fin n → Z)) × Z)) hgroup
    rw [Measure.map_map (MeasurableEquiv.prodAssoc.symm.measurable) (by fun_prop),
      (measurePreserving_prodAssoc μ ρ η).symm.map_eq] at h
    exact h
  have hjoint : (μ.prod Q).map
      (fun p ↦ (C (p.1, pref p.2), p.2 n)) = (ν.map C).prod η := by
    have h := congrArg (fun κ : Measure ((H × (Fin n → Z)) × Z) ↦
      κ.map (Prod.map C id)) hassoc
    rw [Measure.map_map (hC.prodMap measurable_id) (by fun_prop),
      ← Measure.map_prod_map ν η hC measurable_id, Measure.map_id] at h
    exact h
  have hstate : ν.map C = chainLaw F μ Q n := by
    have h := congrArg (fun κ : Measure (H × Z) ↦ κ.map Prod.fst) hjoint
    rw [Measure.map_map measurable_fst (by fun_prop)] at h
    simp only [Measure.map_fst_prod, measure_univ, one_smul] at h
    rw [← h]
    apply Measure.map_congr
    exact ae_of_all _ fun p ↦ finiteNoiseChain_eq F p.1 p.2 n
  rw [hstate] at hjoint
  convert hjoint using 1
  apply Measure.map_congr
  exact ae_of_all _ fun p ↦ (congrArg (fun x ↦ (x, p.2 n)) (finiteNoiseChain_eq F p.1 p.2 n)).symm

/-- The actual canonical iid recursion satisfies the Markov law update. -/
theorem chainLaw_succ_iid
    (F : H → Z → H) (hF : Measurable (Function.uncurry F))
    (μ : Measure H) [IsProbabilityMeasure μ] (η : Measure Z) [IsProbabilityMeasure η]
    (n : ℕ) :
    chainLaw F μ (Measure.infinitePi (fun _ : ℕ ↦ η)) (n + 1) =
      markovStep F η (chainLaw F μ (Measure.infinitePi (fun _ : ℕ ↦ η)) n) := by
  have hm : Measurable (fun p : H × (ℕ → Z) ↦
      (noiseDrivenChain F p.1 p.2 n, p.2 n)) :=
    (noiseDrivenChain_measurable F hF n).prodMk ((measurable_pi_apply n).comp measurable_snd)
  rw [markovStep, ← chainLaw_joint_fresh F hF μ η n,
    Measure.map_map hF hm]
  rfl

/-- The canonical recursion laws are precisely the iterated independent-noise
Markov-step laws. No state/noise independence premise is assumed at later times. -/
theorem chainLaw_eq_markovLaws
    (F : H → Z → H) (hF : Measurable (Function.uncurry F))
    (μ : Measure H) [IsProbabilityMeasure μ] (η : Measure Z) [IsProbabilityMeasure η]
    (n : ℕ) :
    chainLaw F μ (Measure.infinitePi (fun _ : ℕ ↦ η)) n = markovLaws F η μ n := by
  induction n with
  | zero => exact chainLaw_zero F μ _
  | succ n ih => rw [chainLaw_succ_iid F hF μ η n, markovLaws, ih]

/-- Measurable independent-noise transitions preserve probability mass. -/
theorem markovStep_isProbability
    (F : H → Z → H) (hF : Measurable (Function.uncurry F))
    (μ : Measure H) [IsProbabilityMeasure μ] (η : Measure Z) [IsProbabilityMeasure η] :
    IsProbabilityMeasure (markovStep F η μ) := by
  constructor
  rw [markovStep, Measure.map_apply hF MeasurableSet.univ, Set.preimage_univ, measure_univ]

/-- Every iterated Markov law is a probability measure. -/
theorem markovLaws_isProbability
    (F : H → Z → H) (hF : Measurable (Function.uncurry F))
    (μ : Measure H) [IsProbabilityMeasure μ] (η : Measure Z) [IsProbabilityMeasure η]
    (n : ℕ) : IsProbabilityMeasure (markovLaws F η μ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure μ)
  | succ n ih =>
    have := ih
    exact markovStep_isProbability F hF _ η

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Any independent iid realization of the recursion has the proved Markov
iterate law, regardless of its probability-space realization. -/
theorem noiseDrivenChain_law_eq_markovLaws (P : Measure Ω) [IsProbabilityMeasure P]
    (F : H → Z → H) (hF : Measurable (Function.uncurry F))
    (X : Ω → H) (W : ℕ → Ω → Z) (hX : AEMeasurable X P)
    (hW : ∀ n, AEMeasurable (W n) P)
    (hind : IndepFun X (fun ω n ↦ W n ω) P) (hiid : iIndepFun W P)
    (η : Measure Z) [IsProbabilityMeasure η] (hlaw : ∀ n, P.map (W n) = η) (n : ℕ) :
    P.map (fun ω ↦ noiseDrivenChain F (X ω) (fun k ↦ W k ω) n) =
      markovLaws F η (P.map X) n := by
  have : IsProbabilityMeasure (P.map X) := by
    constructor
    rw [Measure.map_apply_of_aemeasurable hX MeasurableSet.univ, Set.preimage_univ, measure_univ]
  rw [noiseDrivenChain_law_of_iid P F hF X W hX hW hind hiid η hlaw,
    chainLaw_eq_markovLaws F hF (P.map X) η n]

end ULA
