import UnadjustedLangevin.InitialCoupling

set_option linter.style.header false

/-! # Second moments inherited from finite quadratic transport

A finite Wasserstein-2 distance to a measure with finite second moment already
forces the other measure to have finite second moment. Consequently, passing a
measurable initialization into the L² formulation adds no independent moment
assumption. The proof selects one finite-cost coupling, not an optimal one.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ULA

variable {H : Type*} [NormedAddCommGroup H] [MeasurableSpace H]
  [BorelSpace H] [SecondCountableTopology H]

/-- Finite quadratic transport to a finite-second-moment measure implies a
finite second moment for the initial law. No normalization, optimal coupling,
or independent moment assumption on `μ` is needed. -/
theorem memLp_id_of_wasserstein2_ne_top (μ π : Measure H)
    (hfinite : wasserstein2 μ π ≠ ⊤) (hπ : MemLp (fun x : H ↦ x) 2 π) :
    MemLp (fun x : H ↦ x) 2 μ := by
  obtain ⟨c, hc⟩ := exists_finiteCost_coupling μ π hfinite
  have hdiff : MemLp (fun p : H × H ↦ p.1 - p.2) 2 c.joint :=
    hc
  have hsndLaw : MemLp (fun x : H ↦ x) 2 (c.joint.map Prod.snd) := by
    rw [c.snd]
    exact hπ
  have hsnd : MemLp (fun p : H × H ↦ p.2) 2 c.joint := by
    simpa only [Function.comp_def] using hsndLaw.comp_of_map measurable_snd.aemeasurable
  have hfst : MemLp (fun p : H × H ↦ p.1) 2 c.joint := by
    simpa only [Pi.add_def, sub_add_cancel] using hdiff.add hsnd
  have hfstLaw : MemLp (fun x : H ↦ x) 2 (c.joint.map Prod.fst) :=
    (memLp_map_measure_iff (by fun_prop) measurable_fst.aemeasurable).mpr hfst
  rwa [c.fst] at hfstLaw

/-- Two probability laws with finite second moments have finite quadratic
transport distance: their independent product is an explicit finite coupling. -/
theorem wasserstein2_ne_top_of_memLp (μ π : Measure H)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : MemLp (fun x : H ↦ x) 2 μ) (hπ : MemLp (fun x : H ↦ x) 2 π) :
    wasserstein2 μ π ≠ ⊤ := by
  let c : Coupling μ π := {
    joint := μ.prod π
    fst := by simp
    snd := by simp }
  have hfst : MemLp (fun p : H × H ↦ p.1) 2 (μ.prod π) :=
    hμ.comp_measurePreserving measurePreserving_fst
  have hsnd : MemLp (fun p : H × H ↦ p.2) 2 (μ.prod π) :=
    hπ.comp_measurePreserving measurePreserving_snd
  exact ne_top_of_le_ne_top (hfst.sub hsnd).eLpNorm_ne_top (wasserstein2_le_couplingCost c)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A measurable random variable whose law is at finite Wasserstein-2 distance
from a finite-second-moment measure belongs to L². -/
theorem memLp_of_law_of_wasserstein2_ne_top (P : Measure Ω) (X : Ω → H)
    (hX : AEMeasurable X P) (μ π : Measure H) (hlaw : P.map X = μ)
    (hfinite : wasserstein2 μ π ≠ ⊤) (hπ : MemLp (fun x : H ↦ x) 2 π) :
    MemLp X 2 P := by
  have hμ := memLp_id_of_wasserstein2_ne_top μ π hfinite hπ
  have hmap : MemLp (fun x : H ↦ x) 2 (P.map X) := by
    rw [hlaw]
    exact hμ
  simpa only [Function.comp_def] using hmap.comp_of_map hX

/-- The direct pushforward-law version, convenient when the initialization is
specified as a random variable rather than as an abstract law. -/
theorem memLp_of_wasserstein2_map_ne_top (P : Measure Ω) (X : Ω → H)
    (hX : AEMeasurable X P) (π : Measure H)
    (hfinite : wasserstein2 (P.map X) π ≠ ⊤) (hπ : MemLp (fun x : H ↦ x) 2 π) :
    MemLp X 2 P :=
  memLp_of_law_of_wasserstein2_ne_top P X hX (P.map X) π rfl hfinite hπ

end ULA
