import Mathlib.Probability.Independence.InfinitePi

/-! # Independent paired innovation paths

Two independent iid paths combine to an iid path of independent pairs. The
identity is proved on finite restrictions of the actual product measure.
-/
noncomputable section
set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set

namespace WassersteinMixing
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem paired_infinitePi (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ((Measure.infinitePi fun _ : ℕ ↦ μ).prod
      (Measure.infinitePi fun _ : ℕ ↦ ν)).map
        (fun p n ↦ (p.1 n, p.2 n)) =
      Measure.infinitePi (fun _ : ℕ ↦ μ.prod ν) := by
  let M := (Measure.infinitePi fun _ : ℕ ↦ μ).prod
    (Measure.infinitePi fun _ : ℕ ↦ ν)
  have hprefix (s : Finset ℕ) :
      M.map (fun p (i : s) ↦ (p.1 i, p.2 i)) =
        Measure.pi (fun _ : s ↦ μ.prod ν) := by
    have hp := (Measure.map_prod_map
      (Measure.infinitePi fun _ : ℕ ↦ μ) (Measure.infinitePi fun _ : ℕ ↦ ν)
      (measurable_restrict s) (measurable_restrict s)).symm
    have hμ : (Measure.infinitePi fun _ : ℕ ↦ μ).map (s : Set ℕ).domRestrict =
        Measure.pi (fun _ : s ↦ μ) := by
      exact Measure.infinitePi_map_restrict (fun _ : ℕ ↦ μ)
    have hν : (Measure.infinitePi fun _ : ℕ ↦ ν).map (s : Set ℕ).domRestrict =
        Measure.pi (fun _ : s ↦ ν) := by
      exact Measure.infinitePi_map_restrict (fun _ : ℕ ↦ ν)
    rw [hμ, hν] at hp
    have h := congrArg (fun ρ : Measure ((s → A) × (s → B)) ↦
      ρ.map (MeasurableEquiv.arrowProdEquivProdArrow A B s).symm) hp
    rw [Measure.map_map (by fun_prop) (by fun_prop),
      (measurePreserving_arrowProdEquivProdArrow A B s (fun _ ↦ μ)
        (fun _ ↦ ν)).symm.map_eq] at h
    exact h
  apply Measure.eq_infinitePi
  intro s t ht
  have h := congrArg (fun ρ : Measure (s → A × B) ↦
    ρ (univ.pi (fun i : s ↦ t i))) (hprefix s)
  rw [Measure.map_apply (by fun_prop) (.univ_pi fun i : s ↦ ht i), Measure.pi_pi] at h
  rw [Measure.map_apply (by fun_prop) (.pi (s.finite_toSet.countable) (fun i _ ↦ ht i))]
  convert h using 1
  · congr 1
    ext p
    simp
  · exact (s.prod_coe_sort (fun i ↦ (μ.prod ν) (t i))).symm

end WassersteinMixing

namespace WassersteinMixing

variable {Ω X A B : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace A] [MeasurableSpace B]

/-- Appending an independent iid path preserves independent initialization and
turns the two innovation paths into a path of independent pairs. -/
theorem augment_initial_noise_law (Q : Measure Ω) [IsProbabilityMeasure Q]
    (μ : Measure X) (η : Measure A) (ν : Measure B)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η] [IsProbabilityMeasure ν]
    (initial : Ω → X) (noise : Ω → ℕ → A)
    (hi : AEMeasurable initial Q) (hn : AEMeasurable noise Q)
    (hjoint : Q.map (fun ω ↦ (initial ω, noise ω)) =
      μ.prod (Measure.infinitePi fun _ : ℕ ↦ η)) :
    (Q.prod (Measure.infinitePi fun _ : ℕ ↦ ν)).map
      (fun p ↦ (initial p.1, fun n ↦ (noise p.1 n, p.2 n))) =
        μ.prod (Measure.infinitePi fun _ : ℕ ↦ η.prod ν) := by
  let N := Measure.infinitePi (fun _ : ℕ ↦ η)
  let U := Measure.infinitePi (fun _ : ℕ ↦ ν)
  let Z : (ℕ → A) × (ℕ → B) → ℕ → A × B := fun p n ↦ (p.1 n, p.2 n)
  have hz : Measurable Z := by fun_prop
  have hbase : (Q.prod U).map
      (fun p ↦ ((initial p.1, noise p.1), p.2)) = (μ.prod N).prod U := by
    have hm := (Measure.map_prod_map Q U (hi.prodMk hn).measurable_mk
      measurable_id).symm
    rw [← Measure.map_congr (hi.prodMk hn).ae_eq_mk, hjoint, Measure.map_id] at hm
    have he := (measurePreserving_fst (μ := Q) (ν := U)).quasiMeasurePreserving.ae_eq_comp
      (hi.prodMk hn).ae_eq_mk
    apply (Measure.map_congr ?_).trans hm
    filter_upwards [he] with p hp
    exact congrArg (fun x ↦ (x, p.2)) hp
  have hassoc := congrArg (fun ρ : Measure ((X × (ℕ → A)) × (ℕ → B)) ↦
    ρ.map MeasurableEquiv.prodAssoc) hbase
  rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop)
      ((hi.prodMk hn).comp_fst.prodMk measurable_snd.aemeasurable),
    Measure.prodAssoc_prod] at hassoc
  change (Q.prod U).map (fun p ↦ (initial p.1, (noise p.1, p.2))) =
    μ.prod (N.prod U) at hassoc
  have hzip := congrArg (fun ρ : Measure (X × ((ℕ → A) × (ℕ → B))) ↦
    ρ.map (Prod.map id Z)) hassoc
  rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop)
      (hi.comp_fst.prodMk (hn.comp_fst.prodMk measurable_snd.aemeasurable)),
    ← Measure.map_prod_map μ (N.prod U) measurable_id hz,
    Measure.map_id, paired_infinitePi η ν] at hzip
  exact hzip

end WassersteinMixing
