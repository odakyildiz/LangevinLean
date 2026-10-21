import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic

/-!
# Couplings and the Wasserstein-2 upper bound

The pinned mathlib has no Wasserstein API. We define the usual infimum of
quadratic coupling costs here. The value lies in `ℝ≥0∞`, so a measure without
finite second moment cannot silently acquire distance zero by `toReal`.

This file proves the passage from an actual pair of random variables to a
transport bound, and the L² perturbation estimate used in synchronous coupling.
It does not assert existence or invariance of a Langevin diffusion.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace ULA

variable {H : Type*} [NormedAddCommGroup H] [MeasurableSpace H]
  [BorelSpace H] [SecondCountableTopology H]

/-- A joint measure whose two marginals are the specified measures. -/
structure Coupling (μ ν : Measure H) where
  joint : Measure (H × H)
  fst : joint.map Prod.fst = μ
  snd : joint.map Prod.snd = ν

/-- The square root of the quadratic transport cost of a joint measure. -/
def couplingCost (γ : Measure (H × H)) : ℝ≥0∞ :=
  eLpNorm (fun p : H × H ↦ p.1 - p.2) 2 γ

/-- Wasserstein-2 as the infimum over every coupling, with infinite costs retained. -/
def wasserstein2 (μ ν : Measure H) : ℝ≥0∞ :=
  ⨅ c : Coupling μ ν, couplingCost c.joint

/-- The real-valued distance, used only after a finite-cost coupling has been
provided. Results below carry that finiteness obligation explicitly. -/
def wasserstein2Real (μ ν : Measure H) : ℝ := (wasserstein2 μ ν).toReal

omit [BorelSpace H] [SecondCountableTopology H] in
/-- Any particular coupling gives an upper bound on Wasserstein-2. -/
theorem wasserstein2_le_couplingCost {μ ν : Measure H} (c : Coupling μ ν) :
    wasserstein2 μ ν ≤ couplingCost c.joint :=
  iInf_le _ c

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

/-- A pair of random variables supplies a coupling of their laws. -/
def randomVariableCoupling (X Y : Ω → H) (hX : Measurable X) (hY : Measurable Y) :
    Coupling (P.map X) (P.map Y) where
  joint := P.map (fun ω ↦ (X ω, Y ω))
  fst := by
    rw [Measure.map_map measurable_fst (hX.prodMk hY)]
    rfl
  snd := by
    rw [Measure.map_map measurable_snd (hX.prodMk hY)]
    rfl

/-- The same construction for almost-everywhere measurable representatives. -/
def aeRandomVariableCoupling (X Y : Ω → H)
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P) :
    Coupling (P.map X) (P.map Y) where
  joint := P.map (fun ω ↦ (X ω, Y ω))
  fst := by
    rw [AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable (hX.prodMk hY)]
    rfl
  snd := by
    rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable (hX.prodMk hY)]
    rfl

/-- The transport cost of a random-variable coupling is its L² distance. -/
theorem randomVariableCoupling_cost (X Y : Ω → H)
    (hX : Measurable X) (hY : Measurable Y) :
    couplingCost (randomVariableCoupling P X Y hX hY).joint =
      eLpNorm (fun ω ↦ X ω - Y ω) 2 P := by
  unfold couplingCost randomVariableCoupling
  exact eLpNorm_map_measure
    (by fun_prop) (hX.prodMk hY).aemeasurable

/-- An actual coupling bounds the Wasserstein distance between the two laws. -/
theorem wasserstein2_le_random_cost (X Y : Ω → H)
    (hX : Measurable X) (hY : Measurable Y) :
    wasserstein2 (P.map X) (P.map Y) ≤ eLpNorm (fun ω ↦ X ω - Y ω) 2 P := by
  simpa only [randomVariableCoupling_cost] using
    wasserstein2_le_couplingCost (randomVariableCoupling P X Y hX hY)

/-- Almost-everywhere measurability suffices for the random-variable bound. -/
theorem wasserstein2_le_ae_random_cost (X Y : Ω → H)
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P) :
    wasserstein2 (P.map X) (P.map Y) ≤ eLpNorm (fun ω ↦ X ω - Y ω) 2 P := by
  refine (wasserstein2_le_couplingCost (aeRandomVariableCoupling P X Y hX hY)).trans_eq ?_
  exact eLpNorm_map_measure (by fun_prop) (hX.prodMk hY)

/-- A finite L² coupling permits conversion to the usual real-valued bound. -/
theorem wasserstein2_le_random_cost_real (X Y : Ω → H)
    (hX : Measurable X) (hY : Measurable Y)
    (hXY : MemLp (fun ω ↦ X ω - Y ω) 2 P) :
    wasserstein2Real (P.map X) (P.map Y) ≤
      (eLpNorm (fun ω ↦ X ω - Y ω) 2 P).toReal :=
  ENNReal.toReal_mono hXY.eLpNorm_ne_top (wasserstein2_le_random_cost P X Y hX hY)

/-- L² random variables provide a finite transport bound equal to their Banach
space distance. This bridges the Bochner-integral local-error theorem to laws. -/
theorem wasserstein2_le_Lp_cost (X Y : Lp H 2 P) :
    wasserstein2 (P.map X) (P.map Y) ≤ ENNReal.ofReal ‖X - Y‖ := by
  have hcost : eLpNorm (fun ω ↦ X ω - Y ω) 2 P = eLpNorm (X - Y) 2 P :=
    (eLpNorm_congr_ae (Lp.coeFn_sub X Y)).symm
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (X - Y))]
  exact (wasserstein2_le_ae_random_cost P X Y
    (Lp.aestronglyMeasurable X).aemeasurable
    (Lp.aestronglyMeasurable Y).aemeasurable).trans_eq hcost

/-- The real-valued L²-to-Wasserstein bridge, with finiteness proved internally. -/
theorem wasserstein2_le_Lp_cost_real (X Y : Lp H 2 P) :
    wasserstein2Real (P.map X) (P.map Y) ≤ ‖X - Y‖ := by
  have hb := wasserstein2_le_Lp_cost P X Y
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simpa only [wasserstein2Real, ENNReal.toReal_ofReal (norm_nonneg _)] using hr

omit [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
/-- Pointwise contraction passes to L²; no probability independence is needed. -/
theorem eLpNorm_contraction (A D : Ω → H) (q : ℝ≥0)
    (hA : AEStronglyMeasurable A P)
    (hcontract : ∀ᵐ ω ∂P, ‖A ω‖ ≤ (q : ℝ) * ‖D ω‖) :
    eLpNorm A 2 P ≤ (q : ℝ≥0∞) * eLpNorm D 2 P := by
  simpa only [ENNReal.smul_def, smul_eq_mul] using
    eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul hA
      (hcontract.mono fun _ h ↦ by exact_mod_cast h) 2

omit [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
/-- The actual synchronous-coupling error decomposes into a contracted term and
a discretization defect. Minkowski's inequality gives the one-step L² bound. -/
theorem synchronous_l2_bound (X Y X' Y' A V : Ω → H) (q : ℝ≥0)
    (hA : AEStronglyMeasurable A P)
    (hidentity : ∀ᵐ ω ∂P, X' ω - Y' ω = A ω - V ω)
    (hcontract : ∀ᵐ ω ∂P, ‖A ω‖ ≤ (q : ℝ) * ‖X ω - Y ω‖) :
    eLpNorm (fun ω ↦ X' ω - Y' ω) 2 P ≤
      (q : ℝ≥0∞) * eLpNorm (fun ω ↦ X ω - Y ω) 2 P + eLpNorm V 2 P := by
  rw [eLpNorm_congr_ae hidentity]
  exact (eLpNorm_sub_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
    (add_le_add (eLpNorm_contraction P A (fun ω ↦ X ω - Y ω) q hA hcontract) le_rfl)

/-- The previous estimate is a genuine measure-level bound for the output laws. -/
theorem synchronous_wasserstein_bound (X Y X' Y' A V : Ω → H) (q : ℝ≥0)
    (hX' : Measurable X') (hY' : Measurable Y')
    (hA : AEStronglyMeasurable A P)
    (hidentity : ∀ᵐ ω ∂P, X' ω - Y' ω = A ω - V ω)
    (hcontract : ∀ᵐ ω ∂P, ‖A ω‖ ≤ (q : ℝ) * ‖X ω - Y ω‖) :
    wasserstein2 (P.map X') (P.map Y') ≤
      (q : ℝ≥0∞) * eLpNorm (fun ω ↦ X ω - Y ω) 2 P + eLpNorm V 2 P :=
  (wasserstein2_le_random_cost P X' Y' hX' hY').trans
    (synchronous_l2_bound P X Y X' Y' A V q hA hidentity hcontract)

/-- The finite-cost real-valued version of the synchronous L² estimate. -/
theorem synchronous_l2_bound_real (X Y X' Y' A V : Ω → H) (q : ℝ≥0)
    (hA : AEStronglyMeasurable A P)
    (hidentity : ∀ᵐ ω ∂P, X' ω - Y' ω = A ω - V ω)
    (hcontract : ∀ᵐ ω ∂P, ‖A ω‖ ≤ (q : ℝ) * ‖X ω - Y ω‖)
    (hXY : MemLp (fun ω ↦ X ω - Y ω) 2 P) (hV : MemLp V 2 P) :
    (eLpNorm (fun ω ↦ X' ω - Y' ω) 2 P).toReal ≤
      (q : ℝ) * (eLpNorm (fun ω ↦ X ω - Y ω) 2 P).toReal + (eLpNorm V 2 P).toReal := by
  have hprod : (q : ℝ≥0∞) * eLpNorm (fun ω ↦ X ω - Y ω) 2 P ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hXY.eLpNorm_ne_top
  have hr := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hprod, hV.eLpNorm_ne_top⟩)
    (synchronous_l2_bound P X Y X' Y' A V q hA hidentity hcontract)
  simpa only [ENNReal.toReal_add hprod hV.eLpNorm_ne_top,
    ENNReal.toReal_mul, ENNReal.coe_toReal] using hr

end ULA
