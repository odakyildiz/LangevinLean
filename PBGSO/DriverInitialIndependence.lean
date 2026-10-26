import PBGSO.DriverPathIndependence

/-! # Initial information and finite Brownian paths
Primitive future independence is promoted to joint independence of an actual
initial variable and every finite set of full-vector Brownian evaluations.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.FilteredBrownian
variable {Ω I : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- Successive independence from the entire previous past gives actual
mutual independence, including an arbitrary adapted initial variable. -/
theorem independent_sequence_of_history {E : Type*} [MeasurableSpace E]
    (F : Filtration ℕ mΩ) (Y : ℕ → Ω → E)
    (hY : ∀ n, @Measurable Ω E (F n) inferInstance (Y n))
    (hind : ∀ n, Indep (MeasurableSpace.comap (Y (n+1)) inferInstance) (F n) Q) :
    iIndepFun Y Q := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro s
  induction s using Finset.induction_on_max with
  | empty => intro sets hs; simp
  | insert n s hlt ih =>
    intro sets hs
    have hn : n ∉ s := fun hn => (hlt n hn).false
    rw [Finset.prod_insert hn]
    cases n with
    | zero =>
      have hse : s = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro k hk
        exact Nat.not_lt_zero k (hlt k hk)
      simp [hse]
    | succ n =>
      have hpast : MeasurableSet[F n] (⋂ k ∈ s, Y k ⁻¹' sets k) := by
        apply Finset.measurableSet_biInter
        intro k hk
        exact ((hY k).mono (F.mono (Nat.le_of_lt_succ (hlt k hk))) le_rfl)
          (hs k (Finset.mem_insert_of_mem hk))
      have hcurr : MeasurableSet[MeasurableSpace.comap (Y (n+1)) inferInstance]
          (Y (n+1) ⁻¹' sets (n+1)) :=
        ⟨sets (n+1),hs (n+1) (Finset.mem_insert_self _ _),rfl⟩
      have hf := (Indep_iff _ _ _).mp (hind n) _ _ hcurr hpast
      have he : (⋂ k ∈ insert (n+1) s, Y k ⁻¹' sets k) =
          (Y (n+1) ⁻¹' sets (n+1)) ∩ (⋂ k ∈ s, Y k ⁻¹' sets k) := by ext ω; simp
      rw [he,hf,ih (fun k hk => hs k (Finset.mem_insert_of_mem hk))]

variable (D : Driver (I := I) Q)
  {H : Type*} [NormedAddCommGroup H] [MeasurableSpace H] [BorelSpace H]
  (X : Ω → H) (hX : StronglyMeasurable[D.filtration 0] X)

include hX

/-- The initial variable and the complete finite array of vector increments
are independent; temporal and spatial dependence are not assumed away. -/
theorem initial_finite_increments_independent (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (n : ℕ) :
    IndepFun X (fun ω (k : Fin n) i => D.process i (τ (k+1)) ω-D.process i (τ k) ω) Q := by
  classical
  let F : Filtration ℕ mΩ :=
    ⟨fun n => D.filtration (τ n),fun _ _ h => D.filtration.mono (hτ h),fun n => D.filtration.le (τ n)⟩
  let Y : ℕ → Ω → H × (I → ℝ)
    | 0 => fun ω => (X ω,0)
    | k+1 => fun ω => (0,fun i => D.process i (τ (k+1)) ω-D.process i (τ k) ω)
  have hY (k : ℕ) : @Measurable Ω (H × (I → ℝ)) (F k) inferInstance (Y k) := by
    cases k with
    | zero => exact (hX.mono (D.filtration.mono zero_le)).measurable.prodMk measurable_const
    | succ k =>
      apply measurable_const.prodMk
      apply (@measurable_pi_iff Ω I (fun _ => ℝ) (D.filtration (τ (k+1)))
        (fun _ => inferInstance) _).mpr
      intro i
      exact (D.adapted i (τ (k+1))).measurable.sub
        (((D.adapted i (τ k)).mono (D.filtration.mono (hτ (Nat.le_succ k)))).measurable)
  have hi : iIndepFun Y Q := independent_sequence_of_history Q F Y hY (fun k => by
    apply indep_of_indep_of_le_left (D.future_independent (τ k) (τ (k+1)) (hτ (Nat.le_succ k)))
    have hm : Measurable (fun a : I → ℝ => ((0 : H),a)) := measurable_const.prodMk measurable_id
    simpa only [MeasurableSpace.comap_comp,Function.comp_def,Y] using
      MeasurableSpace.comap_mono (g := fun ω i => D.process i (τ (k+1)) ω-D.process i (τ k) ω) hm.comap_le)
  have hfin := hi.precomp (g := fun k : Fin (n+1) => (k : ℕ)) Fin.val_injective
  have hmeas (k : Fin (n+1)) : Measurable (Y k) := (hY k).mono (F.le k) le_rfl
  have hsplit := hfin.indepFun_finset ({0} : Finset (Fin (n+1)))
    (Finset.univ.erase 0) (by simp) hmeas
  have hleft : Measurable (fun a : ({0} : Finset (Fin (n+1))) → H × (I → ℝ) =>
      (a ⟨0,by simp⟩).1) := measurable_fst.comp (measurable_pi_apply _)
  have hright : Measurable (fun a : (Finset.univ.erase (0 : Fin (n+1))) → H × (I → ℝ) =>
      fun k : Fin n => (a ⟨k.succ,by simp⟩).2) := by
    apply measurable_pi_iff.mpr
    intro k
    exact measurable_snd.comp (measurable_pi_apply _)
  exact hsplit.comp hleft hright


omit hX in
private theorem partialSum_measurable {n : ℕ} (k : Fin (n+1)) :
    Measurable (fun r : Fin n → ℝ => Fin.partialSum r k) := by
  induction k using Fin.inductionOn with
  | zero => simp only [Fin.partialSum_zero]; exact measurable_const
  | succ k hk =>
    simp only [Fin.partialSum_succ]
    change Measurable ((fun r : Fin n → ℝ => Fin.partialSum r k.castSucc)+(fun r => r k))
    exact hk.add (measurable_pi_apply k)

/-- The initial variable and every full finite vector of Brownian values
are independent, reconstructed from the primitive increment information. -/
theorem initial_finite_values_independent (n : ℕ) (τ : Fin (n+1) → ℝ≥0)
    (hτ : Monotone τ) (h0 : τ 0 = 0) :
    IndepFun X (fun ω (k : Fin (n+1)) i => D.process i (τ k) ω) Q := by
  let τ' : ℕ → ℝ≥0 := fun k => τ ⟨min k n,by omega⟩
  have hτ' : Monotone τ' := fun a b hab => hτ (min_le_min hab le_rfl)
  have he (k : Fin (n+1)) : τ' k = τ k := by
    dsimp [τ']
    congr 1
    apply Fin.ext
    exact Nat.min_eq_left (Nat.le_of_lt_succ k.isLt)
  have he0 (k : Fin n) : τ' k = τ k.castSucc := he k.castSucc
  have he1 (k : Fin n) : τ' (k+1) = τ k.succ := he k.succ
  have hi : IndepFun X
      (fun ω (k : Fin n) i => D.process i (τ k.succ) ω-D.process i (τ k.castSucc) ω) Q := by
    simpa only [he0,he1] using initial_finite_increments_independent Q D X hX τ' hτ' n
  have hm : Measurable (fun a : Fin n → I → ℝ => fun k : Fin (n+1) =>
      fun i => Fin.partialSum (fun j => a j i) k) := by
    apply measurable_pi_iff.mpr
    intro k
    apply measurable_pi_iff.mpr
    intro i
    exact (partialSum_measurable k).comp
      (measurable_pi_iff.mpr (fun j => (measurable_pi_apply i).comp (measurable_pi_apply j)))
  have hf := hi.comp measurable_id hm
  apply hf.congr .rfl
  filter_upwards [ae_all_iff.mpr (fun i => (D.brownian i).eval_zero_ae_eq_zero)] with ω hω
  funext k i
  change Fin.partialSum (fun j : Fin n => D.process i (τ j.succ) ω-D.process i (τ j.castSucc) ω) k =
    D.process i (τ k) ω
  induction k using Fin.inductionOn with
  | zero => simp [h0,hω i]
  | succ k hk => rw [Fin.partialSum_succ,hk]; abel

/-- Initial information is independent of arbitrary finite joint path
evaluations, derived from the Driver's future/full-past primitive. -/
theorem Driver.initial_finite_paths_independent (J : Finset ℝ≥0) :
    IndepFun X (fun ω => J.restrict (fun t i => D.process i t ω)) Q := by
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
  have hi := initial_finite_values_independent Q D X hX J.card τ hτ (by simp [τ])
  have h := hi.comp measurable_id (show Measurable
      (fun a : Fin (J.card+1) → I → ℝ => fun t : J => a (e.symm t).succ) from
    measurable_pi_iff.mpr (fun t => measurable_pi_apply _))
  convert h using 1
  · rfl
  · funext ω t i
    simp [τ]


omit hX in
/-- The natural AE-adapted initial-variable interface. Measurable
representatives are used only internally; the independence conclusion is
about the original raw initial variable and original raw Brownian values. -/
theorem Driver.initial_finite_paths_independent_ae
    (hXA : AEStronglyMeasurable[D.filtration 0] X Q) (J : Finset ℝ≥0) :
    IndepFun X (fun ω => J.restrict (fun t i => D.process i t ω)) Q := by
  have hi := Driver.initial_finite_paths_independent Q D (hXA.mk X)
    hXA.stronglyMeasurable_mk J
  exact hi.congr hXA.ae_eq_mk.symm .rfl

end PBGSO.FilteredBrownian
