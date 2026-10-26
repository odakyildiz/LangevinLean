import PBGSO.FilteredBrownian
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Fin

/-! # Whole coordinate-path independence from primitive filtered drivers
Future vector increments are independent of the full past. Together with
spatial independence for each interval this gives joint independence across
space and time, rather than assuming independent whole coordinate paths.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.FilteredBrownian
variable {Ω I : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

/-- Any nondecreasing deterministic grid has independent full-vector
increments, derived from actual future/full-past independence. -/
theorem vector_grid_increments_independent (τ : ℕ → ℝ≥0) (hτ : Monotone τ) :
    iIndepFun (fun n ω i => D.process i (τ (n+1)) ω-D.process i (τ n) ω) Q := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro s
  induction s using Finset.induction_on_max with
  | empty =>
    intro sets hs
    simp
  | insert n s hlt ih =>
    intro sets hs
    have hn : n ∉ s := fun hn => (hlt n hn).false
    have hsn : MeasurableSet (sets n) := hs n (Finset.mem_insert_self n s)
    have hpast : MeasurableSet[D.filtration (τ n)]
        (⋂ k ∈ s, (fun ω i => D.process i (τ (k+1)) ω-D.process i (τ k) ω) ⁻¹' sets k) := by
      apply Finset.measurableSet_biInter
      intro k hk
      have hkn : k+1 ≤ n := Nat.succ_le_of_lt (hlt k hk)
      have hm : @Measurable Ω (I → ℝ) (D.filtration (τ n)) inferInstance
          (fun ω i => D.process i (τ (k+1)) ω-D.process i (τ k) ω) := by
        apply (@measurable_pi_iff Ω I (fun _ => ℝ) (D.filtration (τ n))
          (fun _ => inferInstance) _).mpr
        intro i
        exact ((D.adapted i (τ (k+1))).mono (D.filtration.mono (hτ hkn))).measurable.sub
          (((D.adapted i (τ k)).mono (D.filtration.mono (hτ ((Nat.le_succ k).trans hkn)))).measurable)
      exact hm (hs k (Finset.mem_insert_of_mem hk))
    have hcurr : MeasurableSet[MeasurableSpace.comap
        (fun ω i => D.process i (τ (n+1)) ω-D.process i (τ n) ω) inferInstance]
        ((fun ω i => D.process i (τ (n+1)) ω-D.process i (τ n) ω) ⁻¹' sets n) :=
      ⟨sets n,hsn,rfl⟩
    have hf := (Indep_iff _ _ _).mp (D.future_independent (τ n) (τ (n+1)) (hτ (Nat.le_succ n)))
      _ _ hcurr hpast
    rw [Finset.prod_insert hn]
    have he : (⋂ k ∈ insert n s, (fun ω i => D.process i (τ (k+1)) ω-D.process i (τ k) ω) ⁻¹' sets k) =
        ((fun ω i => D.process i (τ (n+1)) ω-D.process i (τ n) ω) ⁻¹' sets n) ∩
        (⋂ k ∈ s, (fun ω i => D.process i (τ (k+1)) ω-D.process i (τ k) ω) ⁻¹' sets k) := by
      ext ω
      simp
    rw [he,hf,ih (fun k hk => hs k (Finset.mem_insert_of_mem hk))]

/-- The actual vector process has independent increments. -/
theorem vector_hasIndepIncrements :
    HasIndepIncrements (fun t ω i => D.process i t ω) Q := by
  apply HasIndepIncrements.of_nat
  intro τ hτ _
  exact vector_grid_increments_independent Q D τ hτ


/-- Grouping disjoint rows of an actually independent scalar array preserves
independence of the complete rows. -/
theorem independent_array_rows {A B : Type*} (X : A → B → Ω → ℝ)
    (hm : ∀ a b, Measurable (X a b))
    (h : iIndepFun (fun p : A × B => X p.1 p.2) Q) :
    iIndepFun (fun a ω b => X a b ω) Q := by
  let μ := fun a b => Q.map (X a b)
  letI (a : A) (b : B) : IsProbabilityMeasure (μ a b) :=
    (Measure.isProbabilityMeasure_map_iff (hm a b).aemeasurable).mpr inferInstance
  have hflat := (iIndepFun_iff_map_fun_eq_infinitePi_map (fun p : A × B => hm p.1 p.2)).mp h
  have hrow (a : A) : Q.map (fun ω b => X a b ω) = Measure.infinitePi (μ a) := by
    apply (iIndepFun_iff_map_fun_eq_infinitePi_map (hm a)).mp
    exact h.precomp (g := fun b => (a,b)) (fun _ _ h => (Prod.mk.inj h).2)
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map (fun a => measurable_pi_iff.mpr (hm a))).mpr
  calc
    Q.map (fun ω a b => X a b ω) =
        (Q.map (fun ω (p : A × B) => X p.1 p.2 ω)).map (MeasurableEquiv.curry A B ℝ) := by
      rw [Measure.map_map (MeasurableEquiv.curry A B ℝ).measurable
        (measurable_pi_iff.mpr (fun p => hm p.1 p.2))]
      rfl
    _ = Measure.infinitePi (fun a => Measure.infinitePi (μ a)) := by
      rw [hflat,Measure.infinitePi_map_curry μ]
    _ = _ := by
      congr 1
      funext a
      exact (hrow a).symm

/-- Primitive spatial and temporal increment independence combine into
independence of each coordinate's complete finite increment vector. -/
theorem coordinate_finite_increments_independent (n : ℕ) (τ : Fin (n+1) → ℝ≥0)
    (hτ : Monotone τ) :
    iIndepFun (fun i ω (k : Fin n) => D.process i (τ k.succ) ω-D.process i (τ k.castSucc) ω) Q := by
  have hv := vector_hasIndepIncrements Q D n τ hτ
  have hm (k : Fin n) (i : I) :
      Measurable (fun ω => D.process i (τ k.succ) ω-D.process i (τ k.castSucc) ω) :=
    increment_measurable Q D _ _ i
  have hs (k : Fin n) : iIndepFun
      (fun i ω => D.process i (τ k.succ) ω-D.process i (τ k.castSucc) ω) Q :=
    D.increment_coordinates _ _ (hτ (Fin.castSucc_le_succ k))
  have hf := iIndepFun_uncurry' hm hv hs
  apply independent_array_rows Q
    (fun i (k : Fin n) ω => D.process i (τ k.succ) ω-D.process i (τ k.castSucc) ω)
    (fun i k => hm k i)
  exact hf.precomp (g := fun p : I × Fin n => (p.2,p.1)) (Equiv.prodComm I (Fin n)).injective

/-- Finite-grid scalar values are independent across coordinates. The
starting value is derived to vanish from each primitive Brownian law. -/
theorem coordinate_finite_values_independent (n : ℕ) (τ : Fin (n+1) → ℝ≥0)
    (hτ : Monotone τ) (h0 : τ 0 = 0) :
    iIndepFun (fun i ω (k : Fin (n+1)) => D.process i (τ k) ω) Q := by
  have hm (k : Fin (n+1)) : Measurable (fun r : Fin n → ℝ => Fin.partialSum r k) := by
    induction k using Fin.inductionOn with
    | zero => simp only [Fin.partialSum_zero]; exact measurable_const
    | succ k hk =>
      simp only [Fin.partialSum_succ]
      change Measurable ((fun r : Fin n → ℝ => Fin.partialSum r k.castSucc)+(fun r => r k))
      exact hk.add (measurable_pi_apply k)
  have hi := (coordinate_finite_increments_independent Q D n τ hτ).comp
    (fun _ r => Fin.partialSum r) (fun _ => measurable_pi_iff.mpr hm)
  apply hi.congr
  intro i
  filter_upwards [(D.brownian i).eval_zero_ae_eq_zero] with ω hω
  funext k
  change Fin.partialSum (fun j : Fin n => D.process i (τ j.succ) ω-D.process i (τ j.castSucc) ω) k =
    D.process i (τ k) ω
  induction k using Fin.inductionOn with
  | zero => simp [h0,hω]
  | succ k hk =>
    rw [Fin.partialSum_succ,hk]
    abel


/-- Every common finite set of raw coordinate evaluations is independent
across spatial coordinates. No independence of whole paths is assumed. -/
theorem Driver.finite_paths_independent (J : Finset ℝ≥0) :
    iIndepFun (fun i ω => J.restrict (fun t => D.process i t ω)) Q := by
  classical
  let e := J.orderIsoOfFin rfl
  let τ : Fin (J.card+1) → ℝ≥0 := Fin.cons 0 (fun k => (e k : ℝ≥0))
  have hτ : Monotone τ := by
    intro a
    refine Fin.cases (fun b _ => ?_) (fun a b hab => ?_) a
    · simpa only [τ,Fin.cons_zero] using (zero_le : (0 : ℝ≥0) ≤ τ b)
    · refine Fin.cases (fun hab => ?_) (fun b hab => ?_) b hab
      · exact False.elim (by simpa using hab)
      · change (e a : ℝ≥0) ≤ (e b : ℝ≥0)
        exact e.monotone (by simpa using hab)
  have hi := coordinate_finite_values_independent Q D J.card τ hτ (by simp [τ])
  have h := hi.comp (fun _ a => fun t : J => a (e.symm t).succ)
    (fun _ => measurable_pi_iff.mpr (fun t => measurable_pi_apply _))
  convert h using 1
  funext i ω t
  simp [τ]

end PBGSO.FilteredBrownian
