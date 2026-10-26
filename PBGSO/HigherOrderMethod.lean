import PBGSO.Methods

/-!
# HOL-MYPGD: the paper's endpoint quadrature and its verified error

The seven coefficients below are transcribed from Appendix `mmle_details.tex`.
The covariance law is deliberately not asserted by a pathwise definition. The
innovation argument contains a correlated triple for each particle; no noise is
added to the optimiser. The sampler force may be smoothed while the optimiser
uses the original force. Thus these results do not silently remove smoothing
bias or the finite-particle error.
-/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace PBGSO.Methods

variable {Θ X : Type*}
variable [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Seven scalar response coefficients of the higher-order implementation. -/
structure HOLCoefficients where
  μ12 : ℝ
  μ13 : ℝ
  μ22 : ℝ
  μ23 : ℝ
  μ31 : ℝ
  μ32 : ℝ
  μ33 : ℝ

/-- The explicit coefficients in the paper. Meaningful physical parameters
have `α>0`, `h>0`; the pathwise map and bounds themselves use no division
cancellation and remain algebraically defined at zero. -/
def holCoefficients (α γ h : ℝ) : HOLCoefficients where
  μ12 := (1 + γ ^ 2 / α ^ 2) * h - γ ^ 2 / (2 * α) * h ^ 2 -
    γ ^ 2 / α ^ 3 * (1 - Real.exp (-α * h))
  μ13 := γ / α * h - γ / α ^ 2 * (1 - Real.exp (-α * h))
  μ22 := 1 + γ ^ 2 / α ^ 2 * (1 - α * h - Real.exp (-α * h))
  μ23 := γ / α * (1 - Real.exp (-α * h))
  μ31 := γ / α - γ / (α ^ 2 * h) * (1 - Real.exp (-α * h))
  μ32 := γ ^ 3 / α ^ 2 * h + γ ^ 3 / α ^ 2 * h * Real.exp (-α * h) -
    (2 * γ ^ 3 / α ^ 3 + γ / α) * (1 - Real.exp (-α * h))
  μ33 := Real.exp (-α * h) * (1 + γ ^ 2 / α * h) -
    γ ^ 2 / α ^ 2 * (1 - Real.exp (-α * h))

/-- State `(θ,x,u,v)`, allowing `X` itself to be a finite particle cloud. -/
abbrev HOLState (Θ X : Type*) := Θ × X × X × X

/-- The physically useful sum of the four coordinate discrepancies. -/
def holError (z w : HOLState Θ X) : ℝ :=
  ‖z.1 - w.1‖ + ‖z.2.1 - w.2.1‖ +
    ‖z.2.2.1 - w.2.2.1‖ + ‖z.2.2.2 - w.2.2.2‖

/-- Triangle inequality in the sum of the four coordinate errors. -/
theorem holError_triangle (z u w : HOLState Θ X) :
    holError z w ≤ holError z u + holError u w := by
  have h1 := norm_sub_le_norm_sub_add_norm_sub z.1 u.1 w.1
  have h2 := norm_sub_le_norm_sub_add_norm_sub z.2.1 u.2.1 w.2.1
  have h3 := norm_sub_le_norm_sub_add_norm_sub z.2.2.1 u.2.2.1 w.2.2.1
  have h4 := norm_sub_le_norm_sub_add_norm_sub z.2.2.2 u.2.2.2 w.2.2.2
  unfold holError
  linarith

/-- Affine sampler response to an integrated force `D` and a correlated triple
of innovations. This is exactly the three sampler rows in the appendix. -/
def holResponse (μ : HOLCoefficients) (h : ℝ) (θ : Θ) (x u v D : X)
    (ξ : X × X × X) : HOLState Θ X :=
  (θ, x - (h / 2) • D + μ.μ12 • u + μ.μ13 • v + ξ.1,
    -D + μ.μ22 • u + μ.μ23 • v + ξ.2.1,
    μ.μ31 • D + μ.μ32 • u + μ.μ33 • v + ξ.2.2)

/-- A general quadrature version; the optimiser Euler step is completed first
and the sampler force is evaluated at the updated parameter. -/
def holQuadratureStep (Fbar : Θ → X → Θ) (Q : Θ → X → X → X)
    (μ : HOLCoefficients) (h : ℝ) (z : HOLState Θ X) (ξ : X × X × X) :
    HOLState Θ X :=
  let θ := z.1 - h • Fbar z.1 z.2.1
  holResponse μ h θ z.2.1 z.2.2.1 z.2.2.2 (Q θ z.2.1 z.2.2.1) ξ

/-- The actual HOL-MYPGD implementation uses endpoint quadrature `hG(θ,x)`.
`G=∇ₓE^λ` and `Fbar=N⁻¹∑F(θ,xᵢ)` can be chosen independently. -/
def higherOrderStep (Fbar : Θ → X → Θ) (G : Θ → X → X) (α γ h : ℝ)
    (z : HOLState Θ X) (ξ : X × X × X) : HOLState Θ X :=
  holQuadratureStep Fbar (fun θ x _ ↦ h • G θ x) (holCoefficients α γ h) h z ξ

/-- Sensitivity to replacing the integrated force. All other data, including
the entire innovation triple, are identical. -/
theorem holResponse_force_error (μ : HOLCoefficients) (h : ℝ)
    (θ : Θ) (x u v D D' : X) (ξ : X × X × X) :
    holError (holResponse μ h θ x u v D ξ) (holResponse μ h θ x u v D' ξ) =
      (|h| / 2 + 1 + |μ.μ31|) * ‖D - D'‖ := by
  have hx : (x - (h / 2) • D + μ.μ12 • u + μ.μ13 • v + ξ.1) -
      (x - (h / 2) • D' + μ.μ12 • u + μ.μ13 • v + ξ.1) =
      -(h / 2) • (D - D') := by module
  have hu : (-D + μ.μ22 • u + μ.μ23 • v + ξ.2.1) -
      (-D' + μ.μ22 • u + μ.μ23 • v + ξ.2.1) = -(D - D') := by module
  have hv : (μ.μ31 • D + μ.μ32 • u + μ.μ33 • v + ξ.2.2) -
      (μ.μ31 • D' + μ.μ32 • u + μ.μ33 • v + ξ.2.2) =
      μ.μ31 • (D - D') := by module
  dsimp [holError, holResponse]
  rw [sub_self, norm_zero, hx, hu, hv]
  simp only [norm_smul, Real.norm_eq_abs, abs_neg, norm_neg, abs_div]
  norm_num
  ring

private theorem norm_five (a b c d e : X) :
    ‖a + b + c + d + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by
  calc
    _ ≤ ‖a + b + c + d‖ + ‖e‖ := norm_add_le _ _
    _ ≤ (‖a + b + c‖ + ‖d‖) + ‖e‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ((‖a + b‖ + ‖c‖) + ‖d‖) + ‖e‖ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by gcongr; exact norm_add_le _ _

/-- Sum of the three innovation discrepancies. -/
def holNoiseError (ξ ζ : X × X × X) : ℝ :=
  ‖ξ.1 - ζ.1‖ + ‖ξ.2.1 - ζ.2.1‖ + ‖ξ.2.2 - ζ.2.2‖

/-- The full affine response estimate, retaining the coefficient dependence. -/
theorem holResponse_error (μ : HOLCoefficients) (h : ℝ)
    (θ θ' : Θ) (x x' u u' v v' D D' : X) (ξ ζ : X × X × X) :
    holError (holResponse μ h θ x u v D ξ) (holResponse μ h θ' x' u' v' D' ζ) ≤
      ‖θ - θ'‖ + ‖x - x'‖ + (|h| / 2 + 1 + |μ.μ31|) * ‖D - D'‖ +
      (|μ.μ12| + |μ.μ22| + |μ.μ32|) * ‖u - u'‖ +
      (|μ.μ13| + |μ.μ23| + |μ.μ33|) * ‖v - v'‖ + holNoiseError ξ ζ := by
  have hxid : (x - (h / 2) • D + μ.μ12 • u + μ.μ13 • v + ξ.1) -
      (x' - (h / 2) • D' + μ.μ12 • u' + μ.μ13 • v' + ζ.1) =
      (x - x') + (-(h / 2)) • (D - D') + μ.μ12 • (u - u') +
        μ.μ13 • (v - v') + (ξ.1 - ζ.1) := by module
  have huid : (-D + μ.μ22 • u + μ.μ23 • v + ξ.2.1) -
      (-D' + μ.μ22 • u' + μ.μ23 • v' + ζ.2.1) =
      -(D - D') + μ.μ22 • (u - u') + μ.μ23 • (v - v') +
        (ξ.2.1 - ζ.2.1) + 0 := by module
  have hvid : (μ.μ31 • D + μ.μ32 • u + μ.μ33 • v + ξ.2.2) -
      (μ.μ31 • D' + μ.μ32 • u' + μ.μ33 • v' + ζ.2.2) =
      μ.μ31 • (D - D') + μ.μ32 • (u - u') + μ.μ33 • (v - v') +
        (ξ.2.2 - ζ.2.2) + 0 := by module
  have hx := norm_five (x - x') ((-(h / 2)) • (D - D'))
    (μ.μ12 • (u - u')) (μ.μ13 • (v - v')) (ξ.1 - ζ.1)
  have hu := norm_five (-(D - D')) (μ.μ22 • (u - u'))
    (μ.μ23 • (v - v')) (ξ.2.1 - ζ.2.1) 0
  have hv := norm_five (μ.μ31 • (D - D')) (μ.μ32 • (u - u'))
    (μ.μ33 • (v - v')) (ξ.2.2 - ζ.2.2) 0
  rw [← hxid] at hx
  rw [← huid] at hu
  rw [← hvid] at hv
  simp only [norm_smul, Real.norm_eq_abs, abs_neg, abs_div, norm_neg,
    norm_zero, add_zero] at hx hu hv
  norm_num at hx
  dsimp [holError, holResponse, holNoiseError]
  nlinarith

/-- Explicit stability factor for the implemented higher-order map. -/
def holAmplification (μ : HOLCoefficients) (LF LG h : ℝ) : ℝ :=
  max ((1 + |h| * LF) * (1 + (|h| / 2 + 1 + |μ.μ31|) * |h| * LG))
    (max (|μ.μ12| + |μ.μ22| + |μ.μ32|) (|μ.μ13| + |μ.μ23| + |μ.μ33|))

/-- New one-step stability bound for the actual endpoint implementation,
derived using the independent Lipschitz properties of `Fbar` and `G`.
The factor uses maximum column sums and tends to one as the step vanishes. -/
theorem higherOrder_error (Fbar : Θ → X → Θ) (G : Θ → X → X)
    (LF LG α γ h : ℝ) (hLF : 0 ≤ LF) (hLG : 0 ≤ LG)
    (hF : ∀ θ θ' x x', ‖Fbar θ x - Fbar θ' x'‖ ≤ LF * (‖θ - θ'‖ + ‖x - x'‖))
    (hG : ∀ θ θ' x x', ‖G θ x - G θ' x'‖ ≤ LG * (‖θ - θ'‖ + ‖x - x'‖))
    (z w : HOLState Θ X) (ξ ζ : X × X × X) :
    holError (higherOrderStep Fbar G α γ h z ξ) (higherOrderStep Fbar G α γ h w ζ) ≤
      holAmplification (holCoefficients α γ h) LF LG h * holError z w + holNoiseError ξ ζ := by
  let μ := holCoefficients α γ h
  let W := |h| / 2 + 1 + |μ.μ31|
  let T := 1 + |h| * LF
  let θ := z.1 - h • Fbar z.1 z.2.1
  let θ' := w.1 - h • Fbar w.1 w.2.1
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hθx : ‖θ - θ'‖ + ‖z.2.1 - w.2.1‖ ≤ T * (‖z.1 - w.1‖ + ‖z.2.1 - w.2.1‖) := by
    have he : θ - θ' = (z.1 - w.1) - h • (Fbar z.1 z.2.1 - Fbar w.1 w.2.1) := by
      dsimp [θ, θ']; module
    have hn := norm_sub_le (z.1 - w.1) (h • (Fbar z.1 z.2.1 - Fbar w.1 w.2.1))
    rw [← he, norm_smul, Real.norm_eq_abs] at hn
    have hf := mul_le_mul_of_nonneg_left (hF z.1 w.1 z.2.1 w.2.1) (abs_nonneg h)
    dsimp [T]
    nlinarith
  have hD : ‖h • G θ z.2.1 - h • G θ' w.2.1‖ ≤
      |h| * LG * (‖θ - θ'‖ + ‖z.2.1 - w.2.1‖) := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hG _ _ _ _) (abs_nonneg h)).trans_eq (by ring)
  have hr := holResponse_error μ h θ θ' z.2.1 w.2.1
    z.2.2.1 w.2.2.1 z.2.2.2 w.2.2.2 (h • G θ z.2.1) (h • G θ' w.2.1) ξ ζ
  have hC : (1 + W * |h| * LG) * T ≤ holAmplification μ LF LG h := by
    have he : (1 + W * |h| * LG) * T =
        (1 + |h| * LF) * (1 + (|h| / 2 + 1 + |μ.μ31|) * |h| * LG) := by
      dsimp [T, W]
      ring
    rw [he]
    exact le_max_left _ _
  have hU : |μ.μ12| + |μ.μ22| + |μ.μ32| ≤ holAmplification μ LF LG h :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hV : |μ.μ13| + |μ.μ23| + |μ.μ33| ≤ holAmplification μ LF LG h :=
    (le_max_right _ _).trans (le_max_right _ _)
  dsimp only [higherOrderStep, holQuadratureStep]
  apply hr.trans
  calc
    _ ≤ (1 + W * |h| * LG) * (‖θ - θ'‖ + ‖z.2.1 - w.2.1‖) +
        (|μ.μ12| + |μ.μ22| + |μ.μ32|) * ‖z.2.2.1 - w.2.2.1‖ +
        (|μ.μ13| + |μ.μ23| + |μ.μ33|) * ‖z.2.2.2 - w.2.2.2‖ + holNoiseError ξ ζ := by
      have hb := mul_le_mul_of_nonneg_left hD hW
      dsimp [W] at hb ⊢
      nlinarith
    _ ≤ ((1 + W * |h| * LG) * T) * (‖z.1 - w.1‖ + ‖z.2.1 - w.2.1‖) +
        (|μ.μ12| + |μ.μ22| + |μ.μ32|) * ‖z.2.2.1 - w.2.2.1‖ +
        (|μ.μ13| + |μ.μ23| + |μ.μ33|) * ‖z.2.2.2 - w.2.2.2‖ + holNoiseError ξ ζ := by
      have hb := mul_le_mul_of_nonneg_left hθx (by positivity : 0 ≤ 1 + W * |h| * LG)
      nlinarith
    _ ≤ holAmplification μ LF LG h * (‖z.1 - w.1‖ + ‖z.2.1 - w.2.1‖) +
        holAmplification μ LF LG h * ‖z.2.2.1 - w.2.2.1‖ +
        holAmplification μ LF LG h * ‖z.2.2.2 - w.2.2.2‖ + holNoiseError ξ ζ := by gcongr
    _ = _ := by dsimp [holError, μ]; ring

section Quadrature
variable [CompleteSpace X]

/-- The line-integrated force that the endpoint approximation replaces. -/
def lineForce (G : Θ → X → X) (h : ℝ) (θ : Θ) (x u : X) : X :=
  ∫ t in 0..h, G θ (x + t • u)

/-- New quadrature guarantee, proved by integrating Lipschitz variation along
the actual line segment. It is not an assumed numerical-error recurrence. -/
theorem endpoint_quadrature_error (G : Θ → X → X) (L : ℝ≥0) (h : ℝ)
    (hh : 0 ≤ h) (hLip : ∀ θ, LipschitzWith L (G θ)) (θ : Θ) (x u : X) :
    ‖lineForce G h θ x u - h • G θ x‖ ≤ (L : ℝ) * ‖u‖ * h ^ 2 / 2 := by
  have hInt : IntervalIntegrable (fun t : ℝ ↦ G θ (x + t • u)) volume 0 h :=
    ((hLip θ).continuous.comp (by fun_prop)).intervalIntegrable _ _
  have he : lineForce G h θ x u - h • G θ x =
      ∫ t in 0..h, G θ (x + t • u) - G θ x := by
    rw [intervalIntegral.integral_sub hInt intervalIntegrable_const]
    simp [lineForce]
  rw [he]
  have hb (t : ℝ) (ht : t ∈ Set.Ioc 0 h) :
      ‖G θ (x + t • u) - G θ x‖ ≤ (L : ℝ) * ‖u‖ * t := by
    calc
      _ ≤ (L : ℝ) * ‖(x + t • u) - x‖ := by
        simpa only [dist_eq_norm] using (hLip θ).dist_le_mul (x + t • u) x
      _ = _ := by simp [norm_smul, abs_of_nonneg ht.1.le]; ring
  calc
    _ ≤ ∫ t in 0..h, (L : ℝ) * ‖u‖ * t :=
      intervalIntegral.norm_integral_le_of_norm_le hh
        (Filter.Eventually.of_forall hb) ((by fun_prop : Continuous (fun t : ℝ ↦ (L : ℝ) * ‖u‖ * t)).intervalIntegrable _ _)
    _ = _ := by rw [intervalIntegral.integral_const_mul, integral_id]; ring

/-- New full-state local consistency bound for the implementation's endpoint
force quadrature versus the same affine Gaussian update with exact line
quadrature. It applies to every supplied innovation and every particle count.
This comparison is not an exact-SDE convergence claim. -/
theorem higherOrder_quadrature_error (Fbar : Θ → X → Θ) (G : Θ → X → X)
    (L : ℝ≥0) (α γ h : ℝ) (hh : 0 ≤ h) (hLip : ∀ θ, LipschitzWith L (G θ))
    (z : HOLState Θ X) (ξ : X × X × X) :
    holError (higherOrderStep Fbar G α γ h z ξ)
      (holQuadratureStep Fbar (lineForce G h) (holCoefficients α γ h) h z ξ) ≤
      (h / 2 + 1 + |(holCoefficients α γ h).μ31|) *
        ((L : ℝ) * ‖z.2.2.1‖ * h ^ 2 / 2) := by
  dsimp only [higherOrderStep, holQuadratureStep]
  rw [holResponse_force_error, norm_sub_rev, abs_of_nonneg hh]
  apply mul_le_mul_of_nonneg_left
    (endpoint_quadrature_error G L h hh hLip _ _ _) (by positivity)

/-- New finite-step bound for the endpoint-quadrature implementation against
the line-integrated-force variant with the same innovation triples. The only
reference-state moment input is the velocity bound `R`; the numerical error
recurrence itself is proved from the two actual maps. -/
theorem higherOrder_finite_quadrature_error
    (Fbar : Θ → X → Θ) (G : Θ → X → X) (LF : ℝ) (LG : ℝ≥0)
    (α γ h R : ℝ) (hh : 0 ≤ h) (hLF : 0 ≤ LF)
    (hF : ∀ θ θ' x x', ‖Fbar θ x - Fbar θ' x'‖ ≤ LF * (‖θ - θ'‖ + ‖x - x'‖))
    (hG : ∀ θ θ' x x', ‖G θ x - G θ' x'‖ ≤ (LG : ℝ) * (‖θ - θ'‖ + ‖x - x'‖))
    (hLip : ∀ θ, LipschitzWith LG (G θ))
    (ξ : ℕ → X × X × X) (z w : HOLState Θ X)
    (hvelocity : ∀ k,
      ‖(trajectory (holQuadratureStep Fbar (lineForce G h) (holCoefficients α γ h) h) ξ w k).2.2.1‖ ≤ R)
    (n : ℕ) :
    holError (trajectory (higherOrderStep Fbar G α γ h) ξ z n)
      (trajectory (holQuadratureStep Fbar (lineForce G h) (holCoefficients α γ h) h) ξ w n) ≤
      holAmplification (holCoefficients α γ h) LF (LG : ℝ) h ^ n * holError z w +
        ((h / 2 + 1 + |(holCoefficients α γ h).μ31|) *
          ((LG : ℝ) * R * h ^ 2 / 2)) *
          amplificationSum (holAmplification (holCoefficients α γ h) LF (LG : ℝ) h) n := by
  have hA : 0 ≤ holAmplification (holCoefficients α γ h) LF (LG : ℝ) h := by
    unfold holAmplification
    positivity
  apply finite_accumulation _ _ _ hA _ n
  intro k
  dsimp only [trajectory]
  let a := trajectory (higherOrderStep Fbar G α γ h) ξ z k
  let b := trajectory (holQuadratureStep Fbar (lineForce G h) (holCoefficients α γ h) h) ξ w k
  have hs := higherOrder_error Fbar G LF (LG : ℝ) α γ h hLF LG.coe_nonneg hF hG a b (ξ k) (ξ k)
  simp only [holNoiseError, sub_self, norm_zero, add_zero] at hs
  have hl := higherOrder_quadrature_error Fbar G LG α γ h hh hLip b (ξ k)
  have hb : (LG : ℝ) * ‖b.2.2.1‖ * h ^ 2 / 2 ≤ (LG : ℝ) * R * h ^ 2 / 2 := by
    gcongr
    exact hvelocity k
  have hlocal := hl.trans (mul_le_mul_of_nonneg_left hb (by positivity))
  have ht := holError_triangle (higherOrderStep Fbar G α γ h a (ξ k))
    (higherOrderStep Fbar G α γ h b (ξ k))
    (holQuadratureStep Fbar (lineForce G h) (holCoefficients α γ h) h b (ξ k))
  exact ht.trans (add_le_add hs hlocal)

end Quadrature
end PBGSO.Methods
