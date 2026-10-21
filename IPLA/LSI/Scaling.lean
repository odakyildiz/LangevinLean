import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

set_option linter.style.header false

/-! # Entropy scaling for IPLA under an LSI on the actual lifted target

These are scalar substitutions in the ULA entropy bound: the lifted gradient
constant is `N * L`, the step is `γ / N`, and the dimension is `dθ + N * dx`.
The lifted LSI constant `β` is kept explicit. The specialization `β = N * α`
is an additional assumption about the lifted target, not a tensorization
consequence of an LSI for a single parameter/latent pair.

These identities and recurrence comparisons assert no marginal concentration
or optimization error bound. In particular, the normalized entropy estimate
does not on its own control distance to a marginal-likelihood maximizer.
-/

namespace IPLA.LSI

/-- The ULA restriction for the lifted step is exactly this IPLA restriction. -/
theorem lifted_lsi_step_iff (N : ℕ) (hN : 0 < N) (β L γ : ℝ) (hL : 0 < L) :
    γ / (N : ℝ) ≤ β / (4 * ((N : ℝ) * L) ^ 2) ↔
      γ ≤ β / (4 * (N : ℝ) * L ^ 2) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have heq : β / (4 * ((N : ℝ) * L) ^ 2) =
      (β / (4 * (N : ℝ) * L ^ 2)) / (N : ℝ) := by
    field_simp [hn.ne', hL.ne']
  rw [heq, div_le_div_iff_of_pos_right hn]

/-- The scaled compatibility condition is equivalent to the base comparison. -/
theorem linear_lsi_compatibility_iff (N : ℕ) (hN : 0 < N) (α L : ℝ) :
    (N : ℝ) * α ≤ (N : ℝ) * L ↔ α ≤ L := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  exact mul_le_mul_iff_of_pos_left hn

theorem linear_lsi_compatibility (N : ℕ) (hN : 0 < N) (α L : ℝ)
    (hαL : α ≤ L) : (N : ℝ) * α ≤ (N : ℝ) * L :=
  (linear_lsi_compatibility_iff N hN α L).mpr hαL

/-- When the actual lifted LSI constant is `N * α`, the IPLA step restriction
has no remaining particle-number factor. -/
theorem linear_lsi_step_iff (N : ℕ) (hN : 0 < N) (α L γ : ℝ) (hL : 0 < L) :
    γ ≤ ((N : ℝ) * α) / (4 * (N : ℝ) * L ^ 2) ↔
      γ ≤ α / (4 * L ^ 2) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have heq : ((N : ℝ) * α) / (4 * (N : ℝ) * L ^ 2) = α / (4 * L ^ 2) := by
    field_simp [hn.ne', hL.ne']
  rw [heq]

/-- The general decay rate retains the actual lifted LSI constant. -/
theorem lifted_entropy_rate_eq (N : ℕ) (β γ : ℝ) (k : ℕ) :
    Real.exp (-β * (γ / (N : ℝ)) * k) =
      Real.exp (-β * γ * k / (N : ℝ)) := by
  congr 1
  ring

/-- The rewritten general rate simplifies under the additional linear LSI
scaling assumption. -/
theorem linear_entropy_rate_eq (N : ℕ) (hN : 0 < N) (α γ : ℝ) (k : ℕ) :
    Real.exp (-((N : ℝ) * α) * γ * k / (N : ℝ)) =
      Real.exp (-α * γ * k) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  congr 1
  field_simp [hn]

/-- The same simplification directly from the ULA step notation. -/
theorem linear_ula_entropy_rate_eq (N : ℕ) (hN : 0 < N) (α γ : ℝ) (k : ℕ) :
    Real.exp (-((N : ℝ) * α) * (γ / (N : ℝ)) * k) =
      Real.exp (-α * γ * k) := by
  rw [lifted_entropy_rate_eq, linear_entropy_rate_eq N hN]

/-- The unnormalized entropy bias after substituting the lifted step and
smoothness. The dimension `D` is kept as a scalar parameter. -/
theorem lifted_entropy_bias_eq (N : ℕ) (hN : 0 < N) (β γ L D : ℝ) :
    8 * (γ / (N : ℝ)) * D * ((N : ℝ) * L) ^ 2 / β =
      8 * γ * (N : ℝ) * D * L ^ 2 / β := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have heq : 8 * (γ / (N : ℝ)) * D * ((N : ℝ) * L) ^ 2 =
      8 * γ * (N : ℝ) * D * L ^ 2 := by
    field_simp [hn]
  exact congrArg (fun a : ℝ ↦ a / β) heq

/-- Dividing the entropy by the particle number cancels one bias factor. -/
theorem normalized_entropy_bias_eq (N : ℕ) (hN : 0 < N) (β γ L D : ℝ) :
    (8 * γ * (N : ℝ) * D * L ^ 2 / β) / (N : ℝ) =
      8 * γ * D * L ^ 2 / β := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [div_right_comm]
  congr 1
  field_simp [hn]

/-- The intensive dimension appearing in normalized entropy. -/
theorem normalized_dimension_eq (N dθ dx : ℕ) (hN : 0 < N) :
    ((dθ + N * dx : ℕ) : ℝ) / (N : ℝ) = (dx : ℝ) + (dθ : ℝ) / (N : ℝ) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  field_simp [hn]
  ring

/-- The normalized bias under an LSI constant `N * α` for the actual lift. -/
theorem linear_normalized_entropy_bias_eq (N dθ dx : ℕ) (hN : 0 < N) (α γ L : ℝ) :
    8 * γ * ((dθ + N * dx : ℕ) : ℝ) * L ^ 2 / ((N : ℝ) * α) =
      (8 * γ * L ^ 2 / α) * ((dx : ℝ) + (dθ : ℝ) / (N : ℝ)) := by
  by_cases hα : α = 0
  · simp [hα]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  field_simp [hn, hα]
  ring

/-- A general entropy bound can be divided by the positive particle number,
with its initial contribution and bias both normalized exactly. -/
theorem normalize_entropy_bound (N : ℕ) (hN : 0 < N) (β γ L D H H₀ q : ℝ)
    (hbound : H ≤ q * H₀ + 8 * γ * (N : ℝ) * D * L ^ 2 / β) :
    H / (N : ℝ) ≤ q * (H₀ / (N : ℝ)) + 8 * γ * D * L ^ 2 / β := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hdiv := (div_le_div_iff_of_pos_right hn).mpr hbound
  have heq : (q * H₀ + 8 * γ * (N : ℝ) * D * L ^ 2 / β) / (N : ℝ) =
      q * (H₀ / (N : ℝ)) + 8 * γ * D * L ^ 2 / β := by
    rw [add_div, normalized_entropy_bias_eq N hN]
    ring
  rwa [heq] at hdiv

/-- The unnormalized one-step forcing loses both particle factors from the
squared step. -/
theorem lifted_entropy_forcing_eq (N : ℕ) (hN : 0 < N) (γ L D : ℝ) :
    6 * (γ / (N : ℝ)) ^ 2 * D * ((N : ℝ) * L) ^ 2 = 6 * γ ^ 2 * D * L ^ 2 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp [hn]

/-- The normalized one-step forcing has the intensive dimension. -/
theorem normalized_entropy_forcing_eq (N dθ dx : ℕ) (hN : 0 < N) (γ L : ℝ) :
    (6 * γ ^ 2 * ((dθ + N * dx : ℕ) : ℝ) * L ^ 2) / (N : ℝ) =
      6 * γ ^ 2 * L ^ 2 * ((dx : ℝ) + (dθ : ℝ) / (N : ℝ)) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  field_simp [hn]
  ring

/-- Normalizing the lifted one-step recurrence. Its analytic recurrence is
an explicit premise; this theorem performs only scalar scaling. -/
theorem normalize_lifted_entropy_recurrence (N : ℕ) (hN : 0 < N)
    (β γ L D : ℝ) (H : ℕ → ℝ)
    (hstep : ∀ k, H (k + 1) ≤ Real.exp (-β * (γ / (N : ℝ))) * H k +
      6 * (γ / (N : ℝ)) ^ 2 * D * ((N : ℝ) * L) ^ 2) (k : ℕ) :
    H (k + 1) / (N : ℝ) ≤ Real.exp (-β * γ / (N : ℝ)) * (H k / (N : ℝ)) +
      (6 * γ ^ 2 * D * L ^ 2) / (N : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hdiv := (div_le_div_iff_of_pos_right hn).mpr (hstep k)
  have harg : -β * (γ / (N : ℝ)) = -β * γ / (N : ℝ) := by ring
  have heq : (Real.exp (-β * (γ / (N : ℝ))) * H k +
      6 * (γ / (N : ℝ)) ^ 2 * D * ((N : ℝ) * L) ^ 2) / (N : ℝ) =
      Real.exp (-β * γ / (N : ℝ)) * (H k / (N : ℝ)) +
        (6 * γ ^ 2 * D * L ^ 2) / (N : ℝ) := by
    rw [lifted_entropy_forcing_eq N hN, add_div, harg]
    ring
  rwa [heq] at hdiv

/-- The normalized recurrence under the additional linear lifted-LSI scale. -/
theorem linear_normalized_entropy_recurrence (N dθ dx : ℕ) (hN : 0 < N)
    (α γ L : ℝ) (H : ℕ → ℝ)
    (hstep : ∀ k, H (k + 1) ≤ Real.exp (-((N : ℝ) * α) * (γ / (N : ℝ))) * H k +
      6 * (γ / (N : ℝ)) ^ 2 * ((dθ + N * dx : ℕ) : ℝ) * ((N : ℝ) * L) ^ 2)
    (k : ℕ) :
    H (k + 1) / (N : ℝ) ≤ Real.exp (-α * γ) * (H k / (N : ℝ)) +
      6 * γ ^ 2 * L ^ 2 * ((dx : ℝ) + (dθ : ℝ) / (N : ℝ)) := by
  have hbase := normalize_lifted_entropy_recurrence N hN ((N : ℝ) * α) γ L
    ((dθ + N * dx : ℕ) : ℝ) H hstep k
  have hrate : Real.exp (-((N : ℝ) * α) * γ / (N : ℝ)) = Real.exp (-α * γ) := by
    simpa only [Nat.cast_one, mul_one] using linear_entropy_rate_eq N hN α γ 1
  rwa [hrate, normalized_entropy_forcing_eq N dθ dx hN] at hbase

end IPLA.LSI
