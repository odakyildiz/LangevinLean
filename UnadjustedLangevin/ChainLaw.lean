import UnadjustedLangevin.Dynamics
import UnadjustedLangevin.LpDrift
import Mathlib.Probability.Independence.InfinitePi

/-!
# The law of a recursion driven by independent noise

The law of the algorithm is defined on the canonical product of its initial
law and its noise-path law. Any independent realization has exactly this law.
In particular, changing a coupling of the initial state to a reference state
cannot change the algorithm's output law. All distribution equalities here are
proved pushforward equalities, rather than fields of a supplied structure.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ULA

variable {H Z : Type*}

/-- A measurable update, driven by a sequence of noise vectors. -/
def noiseDrivenChain (F : H → Z → H) (initial : H) (noise : ℕ → Z) : ℕ → H
  | 0 => initial
  | n + 1 => F (noiseDrivenChain F initial noise n) (noise n)

@[simp] theorem noiseDrivenChain_zero (F : H → Z → H) (initial : H) (noise : ℕ → Z) :
    noiseDrivenChain F initial noise 0 = initial := rfl

@[simp] theorem noiseDrivenChain_succ (F : H → Z → H) (initial : H)
    (noise : ℕ → Z) (n : ℕ) :
    noiseDrivenChain F initial noise (n + 1) =
      F (noiseDrivenChain F initial noise n) (noise n) := rfl

variable [MeasurableSpace H] [MeasurableSpace Z]

/-- Every iterate is a measurable function of the initial state and noise path. -/
theorem noiseDrivenChain_measurable (F : H → Z → H)
    (hF : Measurable (Function.uncurry F)) (n : ℕ) :
    Measurable (fun p : H × (ℕ → Z) ↦ noiseDrivenChain F p.1 p.2 n) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
      exact hF.comp (ih.prodMk ((measurable_pi_apply n).comp measurable_snd))

/-- The output law is specified only by the initial law and the noise-path law. -/
def chainLaw (F : H → Z → H) (μ : Measure H) (Q : Measure (ℕ → Z)) (n : ℕ) :
    Measure H :=
  (μ.prod Q).map (fun p ↦ noiseDrivenChain F p.1 p.2 n)

/-- The first law is exactly the initial law. -/
@[simp] theorem chainLaw_zero (F : H → Z → H) (μ : Measure H)
    (Q : Measure (ℕ → Z)) [IsProbabilityMeasure Q] : chainLaw F μ Q 0 = μ := by
  simp [chainLaw]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- An independent implementation has the canonical output law. Independence
is requested for the initial state and the entire noise path, which is the
usual assumption that the initialization is independent of all algorithmic
randomness. -/
theorem noiseDrivenChain_law_of_indep (P : Measure Ω) [IsProbabilityMeasure P]
    (F : H → Z → H) (hF : Measurable (Function.uncurry F))
    (X : Ω → H) (W : Ω → ℕ → Z) (hX : AEMeasurable X P)
    (hW : AEMeasurable W P) (hind : IndepFun X W P) (n : ℕ) :
    P.map (fun ω ↦ noiseDrivenChain F (X ω) (W ω) n) =
      chainLaw F (P.map X) (P.map W) n := by
  rw [chainLaw, ← hind.map_prod_eq_prod_map_map hX hW,
    AEMeasurable.map_map_of_aemeasurable
      (noiseDrivenChain_measurable F hF n).aemeasurable (hX.prodMk hW)]
  rfl

/-- The iid hypothesis gives the canonical product path law. -/
theorem noiseDrivenChain_law_of_iid (P : Measure Ω) [IsProbabilityMeasure P]
    (F : H → Z → H) (hF : Measurable (Function.uncurry F))
    (X : Ω → H) (W : ℕ → Ω → Z) (hX : AEMeasurable X P)
    (hW : ∀ n, AEMeasurable (W n) P)
    (hind : IndepFun X (fun ω n ↦ W n ω) P) (hiid : iIndepFun W P)
    (η : Measure Z) (hlaw : ∀ n, P.map (W n) = η) (n : ℕ) :
    P.map (fun ω ↦ noiseDrivenChain F (X ω) (fun k ↦ W k ω) n) =
      chainLaw F (P.map X) (Measure.infinitePi (fun _ : ℕ ↦ η)) n := by
  have hp := hiid.map_fun_eq_infinitePi_map₀' hW
  simp_rw [hlaw] at hp
  rw [noiseDrivenChain_law_of_indep P F hF X (fun ω n ↦ W n ω) hX
    (aemeasurable_pi_iff.mpr hW) hind n, hp]

/-- Two independent implementations with the same initial and iid noise laws
have identical output laws, even on different probability spaces. -/
theorem noiseDrivenChain_law_unique
    {Ω' : Type*} [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (F : H → Z → H) (hF : Measurable (Function.uncurry F))
    (X : Ω → H) (X' : Ω' → H) (W : ℕ → Ω → Z) (W' : ℕ → Ω' → Z)
    (hX : AEMeasurable X P) (hX' : AEMeasurable X' P')
    (hW : ∀ n, AEMeasurable (W n) P) (hW' : ∀ n, AEMeasurable (W' n) P')
    (hind : IndepFun X (fun ω n ↦ W n ω) P)
    (hind' : IndepFun X' (fun ω n ↦ W' n ω) P')
    (hiid : iIndepFun W P) (hiid' : iIndepFun W' P')
    (hinitial : P.map X = P'.map X')
    (η : Measure Z) (hlaw : ∀ n, P.map (W n) = η)
    (hlaw' : ∀ n, P'.map (W' n) = η) (n : ℕ) :
    P.map (fun ω ↦ noiseDrivenChain F (X ω) (fun k ↦ W k ω) n) =
      P'.map (fun ω ↦ noiseDrivenChain F (X' ω) (fun k ↦ W' k ω) n) := by
  rw [noiseDrivenChain_law_of_iid P F hF X W hX hW hind hiid η hlaw n,
    noiseDrivenChain_law_of_iid P' F hF X' W' hX' hW' hind' hiid' η hlaw' n,
    hinitial]

/-- The generic noise-driven recursion is exactly the defined ULA algorithm. -/
theorem noiseDrivenChain_eq_ulaChain {d : ℕ} (U : E d → ℝ) (h : ℝ)
    (x : E d) (w : ℕ → E d) (n : ℕ) :
    noiseDrivenChain (ulaUpdate U h) x w n = ulaChain U h x w n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [noiseDrivenChain_succ, ulaChain_succ, ih]

/-- The ULA update is measurable under the sole Lipschitz-gradient regularity
already assumed by the convergence theorem. -/
theorem ulaUpdate_measurable {d : ℕ} (U : E d → ℝ) (h : ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U)) :
    Measurable (Function.uncurry (ulaUpdate U h)) := by
  have hg : Measurable (gradient U) := hLip.continuous.measurable
  exact (measurable_fst.sub ((hg.comp measurable_fst).const_smul h)).add
    (measurable_snd.const_smul (Real.sqrt (2 * h)))

/-- The law of the actual ULA chain, from iid noise and independent initialization. -/
theorem ulaChain_law_of_iid {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (U : E d → ℝ) (h : ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (X : Ω → E d) (W : ℕ → Ω → E d) (hX : AEMeasurable X P)
    (hW : ∀ n, AEMeasurable (W n) P)
    (hind : IndepFun X (fun ω n ↦ W n ω) P) (hiid : iIndepFun W P)
    (η : Measure (E d)) (hlaw : ∀ n, P.map (W n) = η) (n : ℕ) :
    P.map (fun ω ↦ ulaChain U h (X ω) (fun k ↦ W k ω) n) =
      chainLaw (ulaUpdate U h) (P.map X) (Measure.infinitePi (fun _ : ℕ ↦ η)) n := by
  simpa only [noiseDrivenChain_eq_ulaChain] using
    noiseDrivenChain_law_of_iid P (ulaUpdate U h) (ulaUpdate_measurable U h L hLip)
      X W hX hW hind hiid η hlaw n

/-- The `L²` implementation has precisely the same canonical algorithm law.
The representative choice in the quotient space cannot alter this law. -/
theorem lpUlaChain_law_of_iid {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (U : E d → ℝ) (h : ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (X : Lp (E d) 2 P) (W : ℕ → Lp (E d) 2 P)
    (hind : IndepFun X (fun ω n ↦ W n ω) P)
    (hiid : iIndepFun (fun n ω ↦ W n ω) P)
    (η : Measure (E d)) (hlaw : ∀ n, P.map (W n) = η) (n : ℕ) :
    P.map (lpUlaChain P U h hLip X W n) =
      chainLaw (ulaUpdate U h) (P.map X) (Measure.infinitePi (fun _ : ℕ ↦ η)) n := by
  rw [Measure.map_congr (lpUlaChain_coe P U h hLip X W n)]
  exact ulaChain_law_of_iid P U h L hLip X (fun n ω ↦ W n ω)
    (Lp.aestronglyMeasurable X).aemeasurable
    (fun n ↦ (Lp.aestronglyMeasurable (W n)).aemeasurable) hind hiid η hlaw n

end ULA
