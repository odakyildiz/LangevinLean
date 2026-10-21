import IPLA.ReferenceFamily

/-! # The change of particle number and time scale

These are the substitutions used in Appendix B: `m_N = N*m`, `L_N = N*L`,
and `h = γ/N`. The square-root factorization is an equality, not a bound.
-/

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace IPLA
open ULA

/-- The original and rescaled step-size restrictions are equivalent. -/
theorem scaled_step_iff (N : ℕ) (hN : 0 < N) (m L γ : ℝ) :
    γ / (N : ℝ) ≤ 2 / ((N : ℝ) * m + (N : ℝ) * L) ↔ γ ≤ 2 / (m + L) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← mul_add, mul_comm (N : ℝ) (m + L), div_mul_eq_div_div,
    div_le_div_iff_of_pos_right hn]

/-- Exact equality of the Dalalyan discretization term with the term in (34). -/
theorem scaled_bias_eq (N dθ dx : ℕ) (hN : 0 < N) (m L γ : ℝ) (_hγ : 0 ≤ γ) :
    (33 / 20 : ℝ) * (((N : ℝ) * L) / ((N : ℝ) * m)) *
        Real.sqrt (γ / (N : ℝ) * (dθ + N * dx : ℕ)) =
      (33 / 20 : ℝ) * (L / m) *
        Real.sqrt ((dx : ℝ) + (dθ : ℝ) / (N : ℝ)) * Real.sqrt γ := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [mul_div_mul_left _ _ hn.ne']
  have heq : γ / (N : ℝ) * (dθ + N * dx : ℕ) =
      ((dx : ℝ) + (dθ : ℝ) / (N : ℝ)) * γ := by
    push_cast
    field_simp
    <;> ring
  rw [heq, Real.sqrt_mul (by positivity)]
  ring

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- Dalalyan in the rescaled IPLA coordinates. Geometry will discharge the
lifted convexity, differentiability and smoothness hypotheses from the joint
potential. The only probabilistic inputs are the explicit reference family. -/
theorem scaled_dalalyan
    (N dθ dx : ℕ) (hN : 0 < N) (U : H → ℝ) (m γ : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ ((N : ℝ) * m) U)
    (hLip : LipschitzWith ((N : ℝ≥0) * L) (gradient U))
    (hm : 0 < m) (hmL : m ≤ (L : ℝ)) (hγ : 0 < γ)
    (hsmall : γ ≤ 2 / (m + (L : ℝ)))
    (ν₀ π : Measure H) (ν : ℕ → Measure H)
    (hfinite : wasserstein2 ν₀ π ≠ ⊤)
    (family : ReferenceFamily P (dθ + N * dx) U (γ / N)
      ((N : ℝ≥0) * L) hLip ν₀ π ν) (k : ℕ) :
    wasserstein2Real (ν k) π ≤
      (1 - m * γ) ^ k * wasserstein2Real ν₀ π +
        (33 / 20 : ℝ) * ((L : ℝ) / m) *
          Real.sqrt ((dx : ℝ) + (dθ : ℝ) / (N : ℝ)) * Real.sqrt γ := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hNL : (N : ℝ) * m ≤ (((N : ℝ≥0) * L : ℝ≥0) : ℝ) := by
    simpa using mul_le_mul_of_nonneg_left hmL hn.le
  have hs : γ / (N : ℝ) ≤ 2 / ((N : ℝ) * m + (((N : ℝ≥0) * L : ℝ≥0) : ℝ)) := by
    simpa using (scaled_step_iff N hN m (L : ℝ) γ).mpr hsmall
  have hb := dalalyan_small_step_of_reference_family P (dθ + N * dx) U
    ((N : ℝ) * m) (γ / N) ((N : ℝ≥0) * L) hdiff hsc hLip
    (mul_pos hn hm) hNL (div_pos hγ hn) hs ν₀ π ν hfinite family k
  have hfactor : (N : ℝ) * m * (γ / N) = m * γ := by field_simp
  simp only [NNReal.coe_mul, NNReal.coe_natCast, hfactor] at hb
  rwa [scaled_bias_eq N dθ dx hN m (L : ℝ) γ hγ.le] at hb

end IPLA
