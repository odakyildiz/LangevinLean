import UnadjustedLangevin.HilbertDalalyan

/-! # The exact initial Wasserstein term

A reference must be available for every finite initial coupling, with the same
output law. This file makes that missing probabilistic construction an explicit
input and proves the passage to the infimum. No optimal coupling is assumed.
-/

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal

namespace ULA.Hilbert
open ULA

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- Only couplings with finite quadratic cost are needed. -/
abbrev FiniteCoupling (ν₀ π : Measure H) :=
  {c : Coupling ν₀ π // couplingCost c.joint ≠ ⊤}

/-- Explicit reference-realization obligations. This is a supplied construction,
not a theorem that the Gibbs Langevin diffusion exists. A single sufficiently
rich probability space may realize the whole family. The output-law field is
precisely the independence-of-initial-coupling obligation.

There is no convergence inequality among these fields. -/
structure ReferenceFamily (d : ℕ) (U : H → ℝ) (h : ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U)) (ν₀ π : Measure H)
    (ν : ℕ → Measure H) where
  initial : FiniteCoupling ν₀ π → Lp H 2 P
  noise : FiniteCoupling ν₀ π → ℕ → Lp H 2 P
  reference : ∀ c, L2Reference P d U h L hLip (noise c) π
  initialLaw : ∀ c, P.map (initial c) = ν₀
  initialCost : ∀ c,
    ‖initial c - (reference c).segment 0 0‖ ≤ (couplingCost c.val.joint).toReal
  outputLaw : ∀ c n, P.map (lpChain P U h hLip (initial c) (noise c) n) = ν n

/-- The common output has a finite transport cost, proved from the reference
family, rather than assumed to justify `toReal`. -/
theorem ReferenceFamily.output_finite
    {d : ℕ} {U : H → ℝ} {h : ℝ} {L : ℝ≥0}
    {hLip : LipschitzWith L (gradient U)} {ν₀ π : Measure H} {ν : ℕ → Measure H}
    (family : ReferenceFamily P d U h L hLip ν₀ π ν)
    (hfinite : wasserstein2 ν₀ π ≠ ⊤) (n : ℕ) :
    wasserstein2 (ν n) π ≠ ⊤ := by
  obtain ⟨c, hc⟩ := exists_finiteCost_coupling ν₀ π hfinite
  let c' : FiniteCoupling ν₀ π := ⟨c, ne_of_lt hc⟩
  have hb := wasserstein2_le_Lp_cost P
    (lpChain P U h hLip (family.initial c') (family.noise c') n)
    ((family.reference c').segment n 0)
  rw [family.outputLaw c' n, (family.reference c').stationary n] at hb
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb

/-- Dalalyan's bound with the genuine infimum over initial couplings, obtained
from the explicit reference family and the earlier analytic ULA proof. -/
theorem dalalyan_small_step_of_reference_family
    (d : ℕ) (U : H → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (hLip : LipschitzWith L (gradient U)) (hm : 0 < m) (hmL : m ≤ (L : ℝ))
    (hh : 0 < h) (hsmall : h ≤ 2 / (m + (L : ℝ)))
    (ν₀ π : Measure H) (ν : ℕ → Measure H)
    (hfinite : wasserstein2 ν₀ π ≠ ⊤)
    (family : ReferenceFamily P d U h L hLip ν₀ π ν) (n : ℕ) :
    wasserstein2Real (ν n) π ≤
      (1 - m * h) ^ n * wasserstein2Real ν₀ π +
        (33 / 20 : ℝ) * ((L : ℝ) / m) * Real.sqrt (h * d) := by
  have hpos : 0 < m + (L : ℝ) := by positivity
  have hproduct := (le_div_iff₀ hpos).mp hsmall
  have hq : 0 ≤ 1 - m * h := by
    nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hmL)]
  let a : ℝ≥0 := ⟨(1 - m * h) ^ n, pow_nonneg hq n⟩
  let b : ℝ≥0 := ⟨(33 / 20 : ℝ) * ((L : ℝ) / m) * Real.sqrt (h * d), by positivity⟩
  apply wasserstein2_affine_bound_real_of_finite_couplings ν₀ π (ν n) π a b
    hfinite (family.output_finite P hfinite n)
  intro c hc
  let c' : FiniteCoupling ν₀ π := ⟨c, hc⟩
  have hb := dalalyan_small_step_of_integral_reference P d U m h L hdiff hsc hLip
    hm hmL hh hsmall (family.initial c') (family.noise c') π (family.reference c') n
  rw [family.outputLaw c' n] at hb
  exact hb.trans (add_le_add
    (mul_le_mul_of_nonneg_left (family.initialCost c') (pow_nonneg hq n)) le_rfl)

end ULA.Hilbert
