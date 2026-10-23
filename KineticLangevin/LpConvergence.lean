import KineticLangevin.LpOneStep
import KineticLangevin.Recurrence
import UnadjustedLangevin.Coupling

/-! # Iterating the actual L² KLMC coupling

Auxiliary exact paths, reference exact paths, their common additive inputs,
and the implemented numerical endpoints are explicit. The one-step
inequality is proved from those paths by `lp_exponentialStep_coupling_bound`.
The remaining reference-law requirements are stated as Gaussian velocity
marginals and stationary position marginals, rather than an assumed
Wasserstein convergence theorem. Brownian construction and invariance must
discharge these requirements for an unconditional sampler theorem.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace KineticLangevin

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- The source-paper first-order Wasserstein bound, proved from actual
L² coupled segments and explicit reference marginal laws. The initial term
is the cost of the supplied initial coupling; a separate all-couplings
argument turns it into the optimal initial Wasserstein distance. -/
theorem lp_klmc_reference_wasserstein_bound_of_velocity_norm
    (f : EuclideanSpace ℝ ι → ℝ) (m : ℝ) (M γ : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ)) (hm : 0 < m)
    (hγ : 0 < (γ : ℝ)) (hfriction : m + (M : ℝ) ≤ (γ : ℝ) ^ 2)
    (h : ℝ) (hh : 0 < h) (hstep : 4 * (γ : ℝ) * (M : ℝ) * h ≤ m)
    (S R : ℕ → Lp (EuclideanSpace ℝ ι) 2 P × Lp (EuclideanSpace ℝ ι) 2 P)
    (A Z W : ℕ → ℝ → Lp (EuclideanSpace ℝ ι) 2 P × Lp (EuclideanSpace ℝ ι) 2 P)
    (B : ℕ → ℝ → Lp (EuclideanSpace ℝ ι) 2 P)
    (hA : ∀ n, Continuous (A n)) (hZ : ∀ n, Continuous (Z n)) (hB : ∀ n, Continuous (B n))
    (hA0 : ∀ n, A n 0 = S n) (hZ0 : ∀ n, Z n 0 = R n) (hZh : ∀ n, Z n h = R (n + 1))
    (hupdate : ∀ n, S (n + 1) = exponentialStep (ULA.lpDrift P (gradient f) hLip) γ h
      (S n) (B n h, ∫ s in 0..h, B n s))
    (heA : ∀ n t, t ∈ Icc 0 h → A n t - A n 0 = -(∫ s in 0..t,
      kineticNegativeDrift (ULA.lpDrift P (gradient f) hLip) γ 1 (A n s)) + W n t)
    (heZ : ∀ n t, t ∈ Icc 0 h → Z n t - Z n 0 = -(∫ s in 0..t,
      kineticNegativeDrift (ULA.lpDrift P (gradient f) hLip) γ 1 (Z n s)) + W n t)
    (hmild : ∀ n t, t ∈ Icc 0 h → (A n t).1 = psi γ 0 t • (A n 0).1 -
      (∫ s in 0..t, Real.exp (-(γ : ℝ) * (t - s)) •
        ULA.lpDrift P (gradient f) hLip (A n s).2) + B n t)
    (hkin : ∀ n t, t ∈ Icc 0 h → (A n t).2 - (A n 0).2 = ∫ s in 0..t, (A n s).1)
    (C : ℝ) (hC : 0 ≤ C) (hreference : ∀ n t, t ∈ Icc 0 h → ‖(Z n t).1‖ ≤ C)
    (π : Measure (EuclideanSpace ℝ ι)) (hstationary : ∀ n, P.map (R n).2 = π)
    (hvelocity : (S 0).1 = (R 0).1) (n : ℕ) :
    ULA.wasserstein2Real (P.map (S n).2) π ≤
      Real.sqrt 2 * (1 - 3 * m * h / (4 * (γ : ℝ))) ^ n * ‖(S 0).2 - (R 0).2‖ +
        (M : ℝ) * h * (Real.sqrt 2 * C) / m := by
  let e := fun n ↦ transformNorm γ 0 (S n - R n)
  have hnonneg : ∀ n, 0 ≤ e n := fun n ↦ transformNorm_nonneg _ _ _
  have hM : 0 < (M : ℝ) := hm.trans_le hmM
  have hsmall : (γ : ℝ) * h ≤ 1 / 4 := by
    have hmult : (M : ℝ) * (4 * (γ : ℝ) * h) ≤ (M : ℝ) * 1 := by nlinarith
    have hs := (mul_le_mul_iff_right₀ hM).mp hmult
    linarith
  have hlocal : ∀ k, e (k + 1) ≤ Real.exp (-(m / (γ : ℝ)) * h) * e k +
      (3 / 4 : ℝ) * (M : ℝ) * h ^ 2 * (C + e k) := by
    intro k
    have hb := lp_exponentialStep_coupling_bound_of_velocity_norm P f m M γ hdiff hsc hLip hmM hm.le
      hγ hfriction (A k) (Z k) (W k) (B k) (hA k) (hZ k) (hB k) h hh.le hsmall
      (heA k) (heZ k) (hmild k) (hkin k) C hC (hreference k)
    rw [hA0 k, hZ0 k, hZh k, ← hupdate k] at hb
    simpa only [neg_div] using hb
  have hr := kinetic_firstOrder_coupling_bound e m M γ h (C)
    hm hmM hγ hfriction hh hC hstep hnonneg hlocal n
  have hproject : ULA.wasserstein2Real (P.map (S n).2) π ≤ Real.sqrt 2 / γ * e n := by
    rw [← hstationary n]
    exact (ULA.wasserstein2_le_Lp_cost_real P (S n).2 (R n).2).trans
      (position_le_transformNorm γ hγ (S n - R n))
  have hinit : e 0 = (γ : ℝ) * ‖(S 0).2 - (R 0).2‖ := by
    have heq : S 0 - R 0 = (0, (S 0).2 - (R 0).2) := by ext <;> simp [hvelocity]
    dsimp [e]
    rw [heq, transformNorm_zero_velocity γ hγ.le]
  rw [hinit] at hr
  have hscaled := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ Real.sqrt 2 / (γ : ℝ))
  have hid : Real.sqrt 2 / (γ : ℝ) *
      ((1 - 3 * m * h / (4 * (γ : ℝ))) ^ n * ((γ : ℝ) * ‖(S 0).2 - (R 0).2‖) +
        (γ : ℝ) * (M : ℝ) * h * C / m) =
      Real.sqrt 2 * (1 - 3 * m * h / (4 * (γ : ℝ))) ^ n * ‖(S 0).2 - (R 0).2‖ +
        (M : ℝ) * h * (Real.sqrt 2 * C) / m := by
    field_simp
  exact hproject.trans (hscaled.trans_eq hid)

/-- The source-paper first-order Wasserstein bound, proved from actual
L² coupled segments and explicit reference marginal laws. The initial term
is the cost of the supplied initial coupling; a separate all-couplings
argument turns it into the optimal initial Wasserstein distance. -/
theorem lp_klmc_reference_wasserstein_bound
    (f : EuclideanSpace ℝ ι → ℝ) (m : ℝ) (M γ : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ)) (hm : 0 < m)
    (hγ : 0 < (γ : ℝ)) (hfriction : m + (M : ℝ) ≤ (γ : ℝ) ^ 2)
    (h : ℝ) (hh : 0 < h) (hstep : 4 * (γ : ℝ) * (M : ℝ) * h ≤ m)
    (S R : ℕ → Lp (EuclideanSpace ℝ ι) 2 P × Lp (EuclideanSpace ℝ ι) 2 P)
    (A Z W : ℕ → ℝ → Lp (EuclideanSpace ℝ ι) 2 P × Lp (EuclideanSpace ℝ ι) 2 P)
    (B : ℕ → ℝ → Lp (EuclideanSpace ℝ ι) 2 P)
    (hA : ∀ n, Continuous (A n)) (hZ : ∀ n, Continuous (Z n)) (hB : ∀ n, Continuous (B n))
    (hA0 : ∀ n, A n 0 = S n) (hZ0 : ∀ n, Z n 0 = R n) (hZh : ∀ n, Z n h = R (n + 1))
    (hupdate : ∀ n, S (n + 1) = exponentialStep (ULA.lpDrift P (gradient f) hLip) γ h
      (S n) (B n h, ∫ s in 0..h, B n s))
    (heA : ∀ n t, t ∈ Icc 0 h → A n t - A n 0 = -(∫ s in 0..t,
      kineticNegativeDrift (ULA.lpDrift P (gradient f) hLip) γ 1 (A n s)) + W n t)
    (heZ : ∀ n t, t ∈ Icc 0 h → Z n t - Z n 0 = -(∫ s in 0..t,
      kineticNegativeDrift (ULA.lpDrift P (gradient f) hLip) γ 1 (Z n s)) + W n t)
    (hmild : ∀ n t, t ∈ Icc 0 h → (A n t).1 = psi γ 0 t • (A n 0).1 -
      (∫ s in 0..t, Real.exp (-(γ : ℝ) * (t - s)) •
        ULA.lpDrift P (gradient f) hLip (A n s).2) + B n t)
    (hkin : ∀ n t, t ∈ Icc 0 h → (A n t).2 - (A n 0).2 = ∫ s in 0..t, (A n s).1)
    (hGaussian : ∀ n t, t ∈ Icc 0 h →
      HasLaw ((Z n t).1) (stdGaussian (EuclideanSpace ℝ ι)) P)
    (π : Measure (EuclideanSpace ℝ ι)) (hstationary : ∀ n, P.map (R n).2 = π)
    (hvelocity : (S 0).1 = (R 0).1) (n : ℕ) :
    ULA.wasserstein2Real (P.map (S n).2) π ≤
      Real.sqrt 2 * (1 - 3 * m * h / (4 * (γ : ℝ))) ^ n * ‖(S 0).2 - (R 0).2‖ +
        (M : ℝ) * h * Real.sqrt (2 * (Fintype.card ι : ℝ)) / m := by
  have hb := lp_klmc_reference_wasserstein_bound_of_velocity_norm P f m M γ hdiff hsc hLip hmM
    hm hγ hfriction h hh hstep S R A Z W B hA hZ hB hA0 hZ0 hZh hupdate
    heA heZ hmild hkin (Real.sqrt (Fintype.card ι : ℝ)) (Real.sqrt_nonneg _)
    (fun k t ht ↦ (gaussian_velocity_Lp_norm P (Z k t).1 (hGaussian k t ht)).le)
    π hstationary hvelocity n
  simpa only [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] using hb

end KineticLangevin
