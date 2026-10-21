import UnadjustedLangevin.Coupling
import UnadjustedLangevin.InitialCoupling
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Projection, concentration, and quadratic transport

A projected root mean square error is bounded by the full-state Wasserstein
distance to equilibrium plus the projected equilibrium error. This applies to
any continuous linear projection with operator norm at most one. The proof uses
Minkowski on each coupling and takes the infimum; it assumes neither an optimal
coupling nor a Wasserstein triangle inequality.
-/

set_option linter.style.header false

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace ULA.Hilbert

variable {H K : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  [SecondCountableTopology K]

/-- The projected quadratic error, with infinite moments retained. -/
def projectedRMS (μ : Measure H) (T : H →L[ℝ] K) (b : K) : ℝ≥0∞ :=
  eLpNorm (fun x ↦ T x - b) 2 μ

/-- Its real-valued form, only used below with a proved finite upper bound. -/
def projectedRMSReal (μ : Measure H) (T : H →L[ℝ] K) (b : K) : ℝ :=
  (projectedRMS μ T b).toReal

omit [SecondCountableTopology K] in
/-- A contraction cannot increase an `L²` error. -/
theorem projectedDifference_le (γ : Measure (H × H))
    (T : H →L[ℝ] K) (hT : ‖T‖ ≤ 1) :
    eLpNorm (fun p : H × H ↦ T (p.1 - p.2)) 2 γ ≤ ULA.couplingCost γ := by
  apply eLpNorm_mono (by fun_prop)
  intro p
  exact (T.le_opNorm (p.1 - p.2)).trans (by nlinarith [norm_nonneg (p.1 - p.2)])

/-- Minkowski on a joint measure followed by its marginal identities. -/
theorem projectedRMS_le_coupling {μ π : Measure H}
    (T : H →L[ℝ] K) (hT : ‖T‖ ≤ 1) (b : K) (c : ULA.Coupling μ π) :
    projectedRMS μ T b ≤ ULA.couplingCost c.joint + projectedRMS π T b := by
  have hfst : projectedRMS μ T b =
      eLpNorm (fun p : H × H ↦ T p.1 - b) 2 c.joint := by
    conv_lhs => rw [projectedRMS, ← c.fst]
    exact eLpNorm_map_measure (by fun_prop) measurable_fst.aemeasurable
  have hsnd : projectedRMS π T b =
      eLpNorm (fun p : H × H ↦ T p.2 - b) 2 c.joint := by
    conv_lhs => rw [projectedRMS, ← c.snd]
    exact eLpNorm_map_measure (by fun_prop) measurable_snd.aemeasurable
  rw [hfst, hsnd]
  have hid : (fun p : H × H ↦ T p.1 - b) =
      (fun p : H × H ↦ T (p.1 - p.2)) + (fun p : H × H ↦ T p.2 - b) := by
    funext p
    simp only [Pi.add_apply, map_sub]
    abel
  rw [hid]
  exact (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
    (add_le_add (projectedDifference_le c.joint T hT) le_rfl)

/-- Infimizing the coupling estimate needs no optimal transport plan. -/
theorem projectedRMS_le_wasserstein2 {μ π : Measure H}
    (T : H →L[ℝ] K) (hT : ‖T‖ ≤ 1) (b : K)
    (hnonempty : Nonempty (ULA.Coupling μ π)) :
    projectedRMS μ T b ≤ ULA.wasserstein2 μ π + projectedRMS π T b := by
  let : Nonempty (ULA.Coupling μ π) := hnonempty
  unfold ULA.wasserstein2
  rw [ENNReal.iInf_add]
  exact le_iInf (fun c ↦ projectedRMS_le_coupling T hT b c)

/-- Finite transport error and a finite projected equilibrium radius imply a
finite projected error for the current law. -/
theorem projectedRMS_ne_top {μ π : Measure H}
    (T : H →L[ℝ] K) (hT : ‖T‖ ≤ 1) (b : K) (c : ℝ)
    (hfinite : ULA.wasserstein2 μ π ≠ ⊤)
    (hconcentration : projectedRMS π T b ≤ ENNReal.ofReal c) :
    projectedRMS μ T b ≠ ⊤ := by
  obtain ⟨coupling, _⟩ := ULA.exists_finiteCost_coupling μ π hfinite
  have hb := (projectedRMS_le_wasserstein2 T hT b ⟨coupling⟩).trans
    (add_le_add le_rfl hconcentration)
  exact ne_top_of_le_ne_top
    (ENNReal.add_ne_top.mpr ⟨hfinite, ENNReal.ofReal_ne_top⟩) hb

omit [BorelSpace H] [SecondCountableTopology H] [SecondCountableTopology K] in
/-- The real projected norm is exactly the square root of its second moment.
The explicit finiteness premise prevents interpreting a divergent moment through
Lean's totalized integral and `ENNReal.toReal`. -/
theorem projectedRMSReal_eq_sqrt_integral (μ : Measure H)
    (T : H →L[ℝ] K) (b : K) (hfinite : projectedRMS μ T b ≠ ⊤) :
    projectedRMSReal μ T b = Real.sqrt (∫ x, ‖T x - b‖ ^ 2 ∂μ) := by
  have hf : MemLp (fun x ↦ T x - b) 2 μ :=
    lt_top_iff_ne_top.mpr hfinite
  have heq := hf.eLpNorm_eq_integral_rpow_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  have heq' : projectedRMS μ T b =
      ENNReal.ofReal (Real.sqrt (∫ x, ‖T x - b‖ ^ 2 ∂μ)) := by
    simpa only [projectedRMS, ENNReal.toReal_ofNat, Real.rpow_two,
      Real.sqrt_eq_rpow, one_div] using heq
  unfold projectedRMSReal
  rw [heq', ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

omit [BorelSpace H] [SecondCountableTopology H] [SecondCountableTopology K] in
/-- A finite second-moment bound supplies the concentration radius used by the
transport-to-parameter estimate. Integrability is explicit because the Bochner
integral is totalized. -/
theorem projectedRMS_le_of_secondMoment (μ : Measure H)
    (T : H →L[ℝ] K) (b : K) (c : ℝ) (hc : 0 ≤ c)
    (hmem : MemLp (fun x ↦ T x - b) 2 μ)
    (hsecond : (∫ x, ‖T x - b‖ ^ 2 ∂μ) ≤ c ^ 2) :
    projectedRMS μ T b ≤ ENNReal.ofReal c := by
  have hfinite : projectedRMS μ T b ≠ ⊤ := hmem.eLpNorm_ne_top
  have hr : projectedRMSReal μ T b ≤ c := by
    rw [projectedRMSReal_eq_sqrt_integral μ T b hmem.eLpNorm_ne_top]
    exact (Real.sqrt_le_sqrt hsecond).trans_eq (Real.sqrt_sq hc)
  have h := ENNReal.ofReal_le_ofReal hr
  simpa only [projectedRMSReal, ENNReal.ofReal_toReal hfinite] using h

/-- The root mean square parameter error is at most full-state transport error
plus a finite equilibrium concentration radius. Finiteness of the left side
is a consequence, so conversion to `ℝ` cannot conceal an infinite moment. -/
theorem projectedRMSReal_le_wasserstein2Real_add {μ π : Measure H}
    (T : H →L[ℝ] K) (hT : ‖T‖ ≤ 1) (b : K) (c : ℝ)
    (hc : 0 ≤ c) (hfinite : ULA.wasserstein2 μ π ≠ ⊤)
    (hconcentration : projectedRMS π T b ≤ ENNReal.ofReal c) :
    projectedRMSReal μ T b ≤ ULA.wasserstein2Real μ π + c := by
  obtain ⟨coupling, _⟩ := ULA.exists_finiteCost_coupling μ π hfinite
  have hb := (projectedRMS_le_wasserstein2 T hT b ⟨coupling⟩).trans
    (add_le_add le_rfl hconcentration)
  have hsum : ULA.wasserstein2 μ π + ENNReal.ofReal c ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hfinite, ENNReal.ofReal_ne_top⟩
  have hr := ENNReal.toReal_mono hsum hb
  simpa only [projectedRMSReal, ULA.wasserstein2Real,
    ENNReal.toReal_add hfinite ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hc] using hr

end ULA.Hilbert
