import PBGSO.GaussianMethodBounds

/-! # One-step consistency for time-uniform M-MFPO bounds

The estimates below concern the actual OBABO map.  They are local proof helpers:
reference moments and increments are derived from primitive Lipschitz integral
equations by the final construction, and are not final error assumptions.
-/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace PBGSO.Methods
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The one-step consistency constant before any time accumulation. -/
def momentumLocalDefectConstant (L γ P F Ξ R : ℝ) : ℝ :=
  momentumLocalConsistencyConstant L γ P F Ξ + Real.sqrt γ * Ξ +
    (3 / 2 : ℝ) * γ * Real.sqrt γ * Ξ +
    (2 / 3 : ℝ) * (L + γ + 1) * R

/-- Actual one-step OBABO versus the original kinetic integral equations.
The two innovations are coupled to the literal reference Brownian increment;
no numerical stability or local-error inequality is assumed. -/
theorem obabo_integral_local_sqrt_bound
    (G : E → E) (L γ h P F Ξ R : ℝ)
    (hL : 0 ≤ L) (hγ : 0 ≤ γ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hP : 0 ≤ P) (hF : 0 ≤ F) (hΞ : 0 ≤ Ξ) (_hR : 0 ≤ R)
    (hLip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (p q : ℝ → E) (ξ ξ' b : E)
    (hpInt : IntervalIntegrable p volume 0 h)
    (hfInt : IntervalIntegrable (fun t ↦ G (q t) + γ • p t) volume 0 h)
    (hp : p h = p 0 - (∫ t in 0..h, G (q t) + γ • p t) + b)
    (hq : q h = q 0 + (∫ t in 0..h, p t))
    (hmod : ∀ t ∈ Set.Icc 0 h,
      ‖p t - p 0‖ ≤ R * Real.sqrt t ∧ ‖q t - q 0‖ ≤ R * Real.sqrt t)
    (hpbound : ‖p 0‖ ≤ P) (hfbound : ‖G (q 0)‖ ≤ F)
    (hξ : ‖ξ‖ ≤ Ξ) (hξ' : ‖ξ'‖ ≤ Ξ)
    (hbrown : b = Real.sqrt (γ * h) • (ξ + ξ')) :
    phaseError
      (KineticLangevin.obaboStep G h (Real.exp (-γ * h / 2))
        (Real.sqrt (1 - Real.exp (-γ * h))) (p 0, q 0) ξ ξ')
      (p h, q h) ≤ momentumLocalDefectConstant L γ P F Ξ R * h * Real.sqrt h := by
  let η := Real.exp (-γ * h / 2)
  let σ := Real.sqrt (1 - Real.exp (-γ * h))
  let c := σ • (η • ξ + ξ')
  have h1 := obabo_euler_error G L γ h η σ P F Ξ hL hLip (p 0, q 0)
    ξ ξ' hpbound hfbound hξ
  have h2 : phaseError (momentumEuler G γ h (p 0, q 0) c)
      (momentumEuler G γ h (p 0, q 0) b) ≤
        ((3 / 2 : ℝ) * γ * Real.sqrt γ * Ξ) * h * Real.sqrt h := by
    rw [momentumEuler_noise_error, hbrown]
    exact momentum_noise_coupling_bound γ h Ξ hγ hh.le hΞ ξ ξ' hξ hξ'
  have h3 := momentumEuler_integral_error G L γ h R hh.le hL hγ hLip p q b
    hpInt hfInt hp hq hmod
  have ht1 := phaseError_triangle
    (KineticLangevin.obaboStep G h η σ (p 0, q 0) ξ ξ')
    (momentumEuler G γ h (p 0, q 0) c) (p h, q h)
  have ht2 := phaseError_triangle (momentumEuler G γ h (p 0, q 0) c)
    (momentumEuler G γ h (p 0, q 0) b) (p h, q h)
  have hrem := momentumRemainderBudget_small_step L γ h P F Ξ
    hL hγ hh hh1 hP hF hΞ
  have hs : h ≤ Real.sqrt h := by
    nlinarith [Real.sq_sqrt hh.le, Real.sqrt_nonneg h]
  have hD : 0 ≤ momentumLocalConsistencyConstant L γ P F Ξ := by
    unfold momentumLocalConsistencyConstant
    positivity
  have hd := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs hh.le) hD
  dsimp only [η, σ, c] at *
  unfold momentumLocalDefectConstant
  nlinarith only [h1, h2, h3, ht1, ht2, hrem, hd]

/-- Coefficients of the initial-radius dependence in the local consistency
budget.  Their nonnegativity permits Lyapunov absorption in the uniform proof. -/
def momentumDefectAffine (L γ Ξ p₀ p₁ f₀ f₁ r₀ r₁ : ℝ) : ℝ × ℝ :=
  let a := (γ ^ 2 + γ + L) / 2
  let b := (γ + 1) / 2 + L / 4
  let c := (2 / 3 : ℝ) * (L + γ + 1)
  (a * p₀ + b * f₀ + (L / 2 + Real.sqrt γ +
      (3 / 2 : ℝ) * γ * Real.sqrt γ) * Ξ + c * r₀,
    a * p₁ + b * f₁ + c * r₁)

/-- The actual local defect budget is affine in a reference radius which is
affine in the starting norm. This is an identity, not an error premise. -/
theorem momentumLocalDefectConstant_affine
    (L γ Ξ p₀ p₁ f₀ f₁ r₀ r₁ u : ℝ) :
    momentumLocalDefectConstant L γ (p₀ + p₁ * u)
      (f₀ + f₁ * u) Ξ (r₀ + r₁ * u) =
      (momentumDefectAffine L γ Ξ p₀ p₁ f₀ f₁ r₀ r₁).1 +
      (momentumDefectAffine L γ Ξ p₀ p₁ f₀ f₁ r₀ r₁).2 * u := by
  unfold momentumLocalDefectConstant momentumLocalConsistencyConstant momentumDefectAffine
  ring

/-- Every affine coefficient is derived nonnegative from the primitive
nonnegative radii and Lipschitz/friction constants. -/
theorem momentumDefectAffine_nonneg
    (L γ Ξ p₀ p₁ f₀ f₁ r₀ r₁ : ℝ)
    (hL : 0 ≤ L) (hγ : 0 ≤ γ) (hΞ : 0 ≤ Ξ)
    (hp₀ : 0 ≤ p₀) (hp₁ : 0 ≤ p₁) (hf₀ : 0 ≤ f₀) (hf₁ : 0 ≤ f₁)
    (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁) :
    0 ≤ (momentumDefectAffine L γ Ξ p₀ p₁ f₀ f₁ r₀ r₁).1 ∧
      0 ≤ (momentumDefectAffine L γ Ξ p₀ p₁ f₀ f₁ r₀ r₁).2 := by
  unfold momentumDefectAffine
  constructor <;> positivity

/-- The actual kinetic drift in momentum/position coordinates. -/
def uniformMomentumDrift (G : E → E) (γ : ℝ) (z : E × E) : E × E :=
  (-G z.2 - γ • z.1, z.1)

omit [CompleteSpace E] in
/-- Primitive global force Lipschitz regularity gives the original kinetic
vector field a global Lipschitz bound, without any potential assumption. -/
theorem uniformMomentumDrift_lipschitz (G : E → E) (L γ : ℝ≥0)
    (hLip : LipschitzWith L G) :
    LipschitzWith (L + γ + 1) (uniformMomentumDrift G γ) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [dist_eq_norm]
  have hp : ‖z.1 - w.1‖ ≤ ‖z - w‖ := norm_fst_le (z - w)
  have hq : ‖z.2 - w.2‖ ≤ ‖z - w‖ := norm_snd_le (z - w)
  have hf := hLip.norm_sub_le z.2 w.2
  have he : (uniformMomentumDrift G γ z - uniformMomentumDrift G γ w).1 =
      -(G z.2 - G w.2) - (γ : ℝ) • (z.1 - w.1) := by
    dsimp [uniformMomentumDrift]
    module
  change max _ _ ≤ _
  apply max_le
  · change ‖(uniformMomentumDrift G γ z - uniformMomentumDrift G γ w).1‖ ≤ _
    rw [he]
    calc
      _ ≤ ‖G z.2 - G w.2‖ + (γ : ℝ) * ‖z.1 - w.1‖ := by
        simpa only [norm_neg, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg γ.coe_nonneg] using norm_sub_le (-(G z.2 - G w.2))
            ((γ : ℝ) • (z.1 - w.1))
      _ ≤ (L : ℝ) * ‖z - w‖ + (γ : ℝ) * ‖z - w‖ := by
        exact add_le_add (hf.trans (mul_le_mul_of_nonneg_left hq L.coe_nonneg))
          (mul_le_mul_of_nonneg_left hp γ.coe_nonneg)
      _ ≤ ((L + γ + 1 : ℝ≥0) : ℝ) * ‖z - w‖ := by
        simp only [NNReal.coe_add, NNReal.coe_one]
        nlinarith [norm_nonneg (z - w)]
  · change ‖z.1 - w.1‖ ≤ _
    simp only [NNReal.coe_add, NNReal.coe_one]
    nlinarith [mul_nonneg L.coe_nonneg (norm_nonneg (z - w)),
      mul_nonneg γ.coe_nonneg (norm_nonneg (z - w))]

omit [CompleteSpace E] in
@[simp] theorem uniformMomentumDrift_zero_norm (G : E → E) (γ : ℝ) :
    ‖uniformMomentumDrift G γ 0‖ = ‖G 0‖ := by
  simp [uniformMomentumDrift]


section Gaussian
variable {Ω I Θ : Type*} [MeasurableSpace Ω] [Fintype I]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  (W : I → ℝ≥0 → Ω → ℝ)
  (hW : ∀ i, ProbabilityTheory.IsPreBrownianReal (W i) Q)

/-- The actual two Gaussian half innovations supply the local defect bound.
Their norms and the literal matching Brownian increment are definitions or
proved Gaussian identities; no noise-error estimate is an input. -/
theorem momentumGaussian_local_sqrt_bound
    (G : (Θ × Lp (EuclideanSpace ℝ I) 2 Q) → (Θ × Lp (EuclideanSpace ℝ I) 2 Q))
    (L γ h P F R : ℝ) (hL : 0 ≤ L) (hγ : 0 ≤ γ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hP : 0 ≤ P) (hF : 0 ≤ F) (hR : 0 ≤ R)
    (hLip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (p q : ℝ → Θ × Lp (EuclideanSpace ℝ I) 2 Q) (k : ℕ)
    (hpInt : IntervalIntegrable p volume 0 h)
    (hfInt : IntervalIntegrable (fun t ↦ G (q t) + γ • p t) volume 0 h)
    (hp : p h = p 0 - (∫ t in 0..h, G (q t) + γ • p t) +
      momentumGaussianIncrement (Θ := Θ) Q W hW γ h k)
    (hq : q h = q 0 + (∫ t in 0..h, p t))
    (hmod : ∀ t ∈ Set.Icc 0 h,
      ‖p t - p 0‖ ≤ R * Real.sqrt t ∧ ‖q t - q 0‖ ≤ R * Real.sqrt t)
    (hpbound : ‖p 0‖ ≤ P) (hfbound : ‖G (q 0)‖ ≤ F) :
    phaseError
      (KineticLangevin.obaboStep G h (Real.exp (-γ * h / 2))
        (Real.sqrt (1 - Real.exp (-γ * h))) (p 0, q 0)
        (momentumGaussianNoise (Θ := Θ) Q W hW h k).1
        (momentumGaussianNoise (Θ := Θ) Q W hW h k).2)
      (p h, q h) ≤
      momentumLocalDefectConstant L γ P F (Real.sqrt (Fintype.card I : ℝ)) R *
        h * Real.sqrt h := by
  apply obabo_integral_local_sqrt_bound G L γ h P F
    (Real.sqrt (Fintype.card I : ℝ)) R hL hγ hh hh1 hP hF (Real.sqrt_nonneg _) hR
    hLip p q _ _ _ hpInt hfInt hp hq hmod hpbound hfbound
  · simp only [momentumGaussianNoise, Prod.norm_def, norm_zero,
      momentumHalfNoise_norm Q W hW h hh, max_eq_right (Real.sqrt_nonneg _)]
    rfl
  · simp only [momentumGaussianNoise, Prod.norm_def, norm_zero,
      momentumHalfNoise_norm Q W hW h hh, max_eq_right (Real.sqrt_nonneg _)]
    rfl
  · rfl
end Gaussian

end PBGSO.Methods
