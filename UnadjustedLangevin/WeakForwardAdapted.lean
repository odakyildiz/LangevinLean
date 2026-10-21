import UnadjustedLangevin.LangevinUniqueness
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.Order.ProjIcc

set_option linter.style.header false

/-! # Adaptedness of the constructed additive Langevin solution

The solution is constructed inside a complete invariant subspace and identified
with any ambient solution by uniqueness. Applied to the closed `L²` subspace of
random variables measurable with respect to a sub-sigma-algebra, this proves
that the solution depends only on its initial data and past additive noise.
Thus adaptedness is a conclusion of the integral construction.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal

namespace ULA

section InvariantSubspace

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- A Lipschitz additive integral equation preserves every complete invariant
linear subspace containing its initial state and all noise values up to `T`. -/
theorem langevin_integral_mem_invariant_submodule
    (g : H → H) (L : ℝ≥0) (hLip : LipschitzWith L g)
    (S : Submodule ℝ H) [CompleteSpace S]
    (hgS : ∀ z ∈ S, g z ∈ S) (x : H) (hx : x ∈ S)
    (B Y : ℝ → H) (hB : Continuous B) (hB0 : B 0 = 0) (hY : Continuous Y)
    (T : ℝ) (hT : 0 ≤ T) (hBS : ∀ t ∈ Icc 0 T, B t ∈ S)
    (hYe : ∀ t ∈ Icc 0 T, Y t - x = -(∫ s in 0..t, g (Y s)) + B t) :
    ∀ t ∈ Icc 0 T, Y t ∈ S := by
  let gS : S → S := fun z ↦ ⟨g z, hgS z z.property⟩
  have hgSLip : LipschitzWith L gS := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    exact hLip.dist_le_mul (z : H) (w : H)
  let BS : ℝ → S := fun t ↦
    ⟨B (projIcc 0 T hT t), hBS _ (projIcc 0 T hT t).property⟩
  have hBScont : Continuous BS :=
    (hB.comp (continuous_subtype_val.comp continuous_projIcc)).subtype_mk _
  have hBSval (t : ℝ) (ht : t ∈ Icc 0 T) : (BS t : H) = B t := by
    simp only [BS, projIcc_of_mem hT ht]
  have hBS0 : BS 0 = 0 := by
    apply Subtype.ext
    exact (hBSval 0 ⟨le_rfl, hT⟩).trans hB0
  obtain ⟨Z, hZ, hZ0, hZe⟩ := exists_langevin_integral gS L hgSLip ⟨x, hx⟩
    BS hBScont hBS0 T hT
  have hlift : ∀ t ∈ Icc 0 T,
      (Z t : H) - x = -(∫ s in 0..t, g (Z s : H)) + B t := by
    intro t ht
    have he := congrArg (fun z : S ↦ (z : H)) (hZe t ht)
    have hi := S.subtypeL.intervalIntegral_comp_comm (μ := volume)
      ((hgSLip.continuous.comp hZ).intervalIntegrable 0 t)
    simp only [Function.comp_apply] at hi
    change (Z t : H) - x = -(S.subtypeL (∫ s in 0..t, gS (Z s))) + (BS t : H) at he
    rw [← hi, hBSval t ht] at he
    exact he
  have hsame := langevin_integral_unique g L hLip x B Y (fun t ↦ (Z t : H))
    hY (continuous_subtype_val.comp hZ) T hT hYe hlift
  intro t ht
  rw [hsame ht]
  exact (Z t).property

end InvariantSubspace

section SubSigmaAlgebra

variable {Ω H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- The actual lifted Lipschitz drift preserves measurability with respect to
any sub-sigma-algebra. Representative choices in `Lp` have no effect. -/
theorem lpDrift_aestronglyMeasurable
    (m : MeasurableSpace Ω) [m0 : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (g : H → H) (L : ℝ≥0) (hLip : LipschitzWith L g)
    (X : Lp H 2 P) (hX : AEStronglyMeasurable[m] X P) :
    AEStronglyMeasurable[m] (lpDrift P g hLip X) P := by
  exact (hLip.continuous.comp_aestronglyMeasurable hX).congr (lpDrift_coe P g hLip X).symm

/-- The integral solution is measurable with respect to every sub-sigma-algebra
that contains the initialization and all additive noise up to the horizon.
Applied separately at each horizon, this is adaptedness to the natural past. -/
theorem lp_langevin_integral_aestronglyMeasurable
    (m : MeasurableSpace Ω) [m0 : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ m0)
    (U : H → ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (initial : Lp H 2 P) (hinitial : AEStronglyMeasurable[m] initial P)
    (B Y : ℝ → Lp H 2 P) (hB : Continuous B) (hB0 : B 0 = 0) (hY : Continuous Y)
    (T : ℝ) (hT : 0 ≤ T)
    (hBmeas : ∀ t ∈ Icc 0 T, AEStronglyMeasurable[m] (B t) P)
    (hYe : ∀ t ∈ Icc 0 T, Y t - initial =
      -(∫ s in 0..t, lpDrift P (gradient U) hLip (Y s)) + B t) :
    ∀ t ∈ Icc 0 T, AEStronglyMeasurable[m] (Y t) P := by
  have : Fact (m ≤ m0) := ⟨hm⟩
  have hg : ∀ z ∈ lpMeas H ℝ m 2 P, lpDrift P (gradient U) hLip z ∈ lpMeas H ℝ m 2 P := by
    intro z hz
    exact mem_lpMeas_iff_aestronglyMeasurable.mpr
      (lpDrift_aestronglyMeasurable m P (gradient U) L hLip z
        (mem_lpMeas_iff_aestronglyMeasurable.mp hz))
  have hS := langevin_integral_mem_invariant_submodule
    (lpDrift P (gradient U) hLip) L (lpDrift_lipschitz P (gradient U) hLip)
    (lpMeas H ℝ m 2 P) hg initial (mem_lpMeas_iff_aestronglyMeasurable.mpr hinitial)
    B Y hB hB0 hY T hT
    (fun t ht ↦ mem_lpMeas_iff_aestronglyMeasurable.mpr (hBmeas t ht)) hYe
  intro t ht
  exact mem_lpMeas_iff_aestronglyMeasurable.mp (hS t ht)

end SubSigmaAlgebra

section NaturalPast

variable {Ω H : Type*} [m0 : MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [mH : MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- Information in the initialization and in the additive noise up to `T`.
This is defined using the actual measurable `Lp` representatives. -/
@[instance_reducible] def lpLangevinPast (initial : Lp H 2 P) (B : ℝ → Lp H 2 P) (T : ℝ) :
    MeasurableSpace Ω :=
  mH.comap initial ⊔ ⨆ t : Icc 0 T, mH.comap (B t)

omit [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
  [IsProbabilityMeasure P] in
/-- The past information is a sub-sigma-algebra of the ambient sample space. -/
theorem lpLangevinPast_le (initial : Lp H 2 P) (B : ℝ → Lp H 2 P) (T : ℝ) :
    lpLangevinPast P initial B T ≤ m0 := by
  apply sup_le
  · exact (Lp.stronglyMeasurable initial).measurable.comap_le
  · exact iSup_le fun t ↦ (Lp.stronglyMeasurable (B t)).measurable.comap_le

omit [InnerProductSpace ℝ H] [CompleteSpace H] [IsProbabilityMeasure P] in
/-- The initialization is measurable with respect to the specified past. -/
theorem lpLangevinPast_initial (initial : Lp H 2 P) (B : ℝ → Lp H 2 P) (T : ℝ) :
    AEStronglyMeasurable[lpLangevinPast P initial B T] initial P := by
  have hm : @Measurable Ω H (lpLangevinPast P initial B T) mH initial :=
    measurable_iff_comap_le.mpr le_sup_left
  exact hm.stronglyMeasurable.aestronglyMeasurable

omit [InnerProductSpace ℝ H] [CompleteSpace H] [IsProbabilityMeasure P] in
/-- Every additive-noise value up to the horizon belongs to the past. -/
theorem lpLangevinPast_noise (initial : Lp H 2 P) (B : ℝ → Lp H 2 P) (T t : ℝ)
    (ht : t ∈ Icc 0 T) :
    AEStronglyMeasurable[lpLangevinPast P initial B T] (B t) P := by
  have hm : @Measurable Ω H (lpLangevinPast P initial B T) mH (B t) := by
    apply measurable_iff_comap_le.mpr
    exact (le_iSup (fun s : Icc 0 T ↦ mH.comap (B s)) ⟨t, ht⟩).trans le_sup_right
  exact hm.stronglyMeasurable.aestronglyMeasurable

/-- Actual adaptedness of every constructed `L²` Langevin integral solution:
all values up to `T` are measurable from the initialization and past noise.
There is no adaptedness or additional measurability hypothesis. -/
theorem lp_langevin_integral_naturalPast
    (U : H → ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (initial : Lp H 2 P) (B Y : ℝ → Lp H 2 P)
    (hB : Continuous B) (hB0 : B 0 = 0) (hY : Continuous Y)
    (T : ℝ) (hT : 0 ≤ T)
    (hYe : ∀ t ∈ Icc 0 T, Y t - initial =
      -(∫ s in 0..t, lpDrift P (gradient U) hLip (Y s)) + B t) :
    ∀ t ∈ Icc 0 T,
      AEStronglyMeasurable[lpLangevinPast P initial B T] (Y t) P := by
  exact lp_langevin_integral_aestronglyMeasurable (lpLangevinPast P initial B T) P
    (lpLangevinPast_le P initial B T) U L hLip initial (lpLangevinPast_initial P initial B T)
    B Y hB hB0 hY T hT (fun t ht ↦ lpLangevinPast_noise P initial B T t ht) hYe

end NaturalPast

end ULA
