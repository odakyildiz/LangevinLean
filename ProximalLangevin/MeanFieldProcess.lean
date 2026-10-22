import ProximalLangevin.MeanFieldDrift
import UnadjustedLangevin.BrownianLangevin

set_option linter.style.header false

/-! # Constructing the mean-field integral equation in L²

The parameter force is its actual expectation and the latent force acts
pointwise. Both are constructed from the actual joint gradient. A proved
Lipschitz estimate allows the Banach-space Picard theorem to construct the
continuous L² integral solution on every finite horizon. Parameter-free
additive noise and a deterministic initial parameter preserve a deterministic
parameter. These are L² integral statements, not a claim of pathwise strong-SDE
existence, uniqueness, propagation of chaos, or a Fokker--Planck equation.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace ProximalLangevin

section Expectation
variable {Ω E : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- On a probability space, the actual expectation is bounded by the L² norm. -/
theorem norm_lp_expectation_le (X : Lp E 2 Q) : ‖∫ ω, X ω ∂Q‖ ≤ ‖X‖ := by
  have h₁ : ‖∫ ω, X ω ∂Q‖ₑ ≤ eLpNorm (fun ω => X ω) 1 Q := by
    rw [eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable X)]
    exact enorm_integral_le_lintegral_enorm (fun ω => X ω)
  have h := h₁.trans (eLpNorm_le_eLpNorm_of_exponent_le
    (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  have hr := ENNReal.toReal_mono (Lp.memLp X).eLpNorm_ne_top h
  simpa only [toReal_enorm, Lp.norm_def] using hr

/-- Actual Bochner expectation as a bounded linear map out of L². -/
def lpExpectationCLM : Lp E 2 Q →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun X => ∫ ω, X ω ∂Q
      map_add' := by
        intro X Y
        rw [integral_congr_ae (Lp.coeFn_add X Y)]
        exact integral_add ((Lp.memLp X).integrable (by norm_num))
          ((Lp.memLp Y).integrable (by norm_num))
      map_smul' := by
        intro a X
        rw [integral_congr_ae (Lp.coeFn_smul a X)]
        exact integral_smul a X }
    1 (fun X => by
      change ‖∫ ω, X ω ∂Q‖ ≤ 1 * ‖X‖
      simpa only [one_mul] using norm_lp_expectation_le Q X)

@[simp] theorem lpExpectationCLM_apply (X : Lp E 2 Q) :
    lpExpectationCLM Q X = ∫ ω, X ω ∂Q := rfl

theorem lpExpectationCLM_norm_le (X : Lp E 2 Q) : ‖lpExpectationCLM Q X‖ ≤ ‖X‖ :=
  norm_lp_expectation_le Q X

end Expectation

/-- The latent component of one parameter/latent joint vector. -/
def jointLatentCLM {dθ dx : ℕ} :
    IPLA.Joint dθ dx →L[ℝ] EuclideanSpace ℝ (Fin dx) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (fun j => z (Sum.inr j))
      map_add' := by intro x y; ext j; rfl
      map_smul' := by intro a x; ext j; rfl }

@[simp] theorem jointLatentCLM_apply {dθ dx : ℕ} (z : IPLA.Joint dθ dx)
    (j : Fin dx) : jointLatentCLM z j = z (Sum.inr j) := rfl

/-- Embed only a parameter block into the joint space. -/
def jointParameterInclusionCLM {dθ dx : ℕ} :
    EuclideanSpace ℝ (Fin dθ) →L[ℝ] IPLA.Joint dθ dx :=
  LinearMap.toContinuousLinearMap
    { toFun := fun θ => IPLA.pair θ 0
      map_add' := by intro x y; ext j; cases j <;> simp [IPLA.pair]
      map_smul' := by intro a x; ext j; cases j <;> simp [IPLA.pair] }

@[simp] theorem jointParameterInclusionCLM_parameter {dθ dx : ℕ}
    (θ : EuclideanSpace ℝ (Fin dθ)) (j : Fin dθ) :
    (jointParameterInclusionCLM θ : IPLA.Joint dθ dx) (Sum.inl j) = θ j := rfl

@[simp] theorem jointParameterInclusionCLM_latent {dθ dx : ℕ}
    (θ : EuclideanSpace ℝ (Fin dθ)) (j : Fin dx) :
    (jointParameterInclusionCLM θ : IPLA.Joint dθ dx) (Sum.inr j) = 0 := rfl

/-- The actual latent-coordinate projection on the joint space. -/
def jointLatentMaskCLM {dθ dx : ℕ} : IPLA.Joint dθ dx →L[ℝ] IPLA.Joint dθ dx :=
  ContinuousLinearMap.id ℝ _ - jointParameterInclusionCLM.comp jointParameterCLM

@[simp] theorem jointLatentMaskCLM_parameter {dθ dx : ℕ}
    (z : IPLA.Joint dθ dx) (j : Fin dθ) : jointLatentMaskCLM z (Sum.inl j) = 0 := by
  simp [jointLatentMaskCLM]

@[simp] theorem jointLatentMaskCLM_latent {dθ dx : ℕ}
    (z : IPLA.Joint dθ dx) (j : Fin dx) : jointLatentMaskCLM z (Sum.inr j) = z (Sum.inr j) := by
  simp [jointLatentMaskCLM]

theorem jointParameterInclusionCLM_norm {dθ dx : ℕ}
    (θ : EuclideanSpace ℝ (Fin dθ)) :
    ‖(jointParameterInclusionCLM θ : IPLA.Joint dθ dx)‖ = ‖θ‖ := by
  have h := IPLA.norm_pair_sq θ (0 : EuclideanSpace ℝ (Fin dx))
  change ‖IPLA.pair θ 0‖ = ‖θ‖
  simp only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at h
  nlinarith [norm_nonneg (IPLA.pair θ (0 : EuclideanSpace ℝ (Fin dx))), norm_nonneg θ]

theorem norm_jointLatentMaskCLM_le {dθ dx : ℕ} (z : IPLA.Joint dθ dx) :
    ‖jointLatentMaskCLM z‖ ≤ ‖z‖ := by
  have hs : ‖jointLatentMaskCLM z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type,
      jointLatentMaskCLM_parameter, jointLatentMaskCLM_latent, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      Finset.sum_const_zero, zero_add]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  nlinarith [norm_nonneg (jointLatentMaskCLM z), norm_nonneg z]

section Process
variable {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
  {dθ dx : ℕ}

/-- Average the parameter coordinates and retain the latent coordinates as
actual random variables. This is a bounded linear map, not an assumed drift. -/
def meanFieldAverageCLM : Lp (IPLA.Joint dθ dx) 2 Q →L[ℝ] Lp (IPLA.Joint dθ dx) 2 Q :=
  (Lp.constL 2 Q ℝ).comp
    (jointParameterInclusionCLM.comp (jointParameterCLM.comp (lpExpectationCLM Q))) +
    jointLatentMaskCLM.compLpL 2 Q

theorem meanFieldAverageCLM_norm_le (X : Lp (IPLA.Joint dθ dx) 2 Q) :
    ‖meanFieldAverageCLM Q X‖ ≤ 2 * ‖X‖ := by
  have hc : ‖Lp.const 2 Q (jointParameterInclusionCLM
      (jointParameterCLM (lpExpectationCLM Q X)) : IPLA.Joint dθ dx)‖ ≤ ‖X‖ := by
    calc
      _ ≤ ‖(jointParameterInclusionCLM (jointParameterCLM (lpExpectationCLM Q X)) :
          IPLA.Joint dθ dx)‖ := by simpa using Lp.norm_const_le 2 Q _
      _ = ‖jointParameterCLM (lpExpectationCLM Q X)‖ := jointParameterInclusionCLM_norm _
      _ ≤ ‖lpExpectationCLM Q X‖ := norm_jointParameterCLM_apply_le _
      _ ≤ ‖X‖ := lpExpectationCLM_norm_le Q X
  have hl : ‖jointLatentMaskCLM.compLp X‖ ≤ ‖X‖ := by
    have h : ‖jointLatentMaskCLM.compLp X‖ ≤ 1 * ‖X‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [jointLatentMaskCLM.coeFn_compLp X] with ω he
      rw [he]
      simpa only [one_mul] using norm_jointLatentMaskCLM_le (X ω)
    simpa only [one_mul] using h
  change ‖Lp.const 2 Q (jointParameterInclusionCLM
      (jointParameterCLM (lpExpectationCLM Q X))) + jointLatentMaskCLM.compLp X‖ ≤ _
  exact (norm_add_le _ _).trans (by linarith)

theorem meanFieldAverageCLM_lipschitz : LipschitzWith 2
    (meanFieldAverageCLM Q : Lp (IPLA.Joint dθ dx) 2 Q → Lp (IPLA.Joint dθ dx) 2 Q) := by
  apply LipschitzWith.of_dist_le_mul
  intro X Y
  simpa only [dist_eq_norm_sub, ← map_sub, NNReal.coe_ofNat] using
    meanFieldAverageCLM_norm_le Q (X - Y)

/-- The actual mean-field drift: expected parameter force and pointwise latent force. -/
def lpMeanFieldDrift (V : IPLA.Joint dθ dx → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L (gradient V)) (X : Lp (IPLA.Joint dθ dx) 2 Q) :
    Lp (IPLA.Joint dθ dx) 2 Q :=
  meanFieldAverageCLM Q (ULA.lpDrift Q (gradient V) hLip X)

/-- A conservative global Lipschitz constant for the constructed drift. -/
theorem lpMeanFieldDrift_lipschitz (V : IPLA.Joint dθ dx → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L (gradient V)) :
    LipschitzWith (2 * L) (lpMeanFieldDrift Q V hLip) :=
  (meanFieldAverageCLM_lipschitz Q).comp (ULA.lpDrift_lipschitz Q (gradient V) hLip)

/-- Picard constructs the continuous mean-field L² integral solution from
its actual gradient and a continuous L² additive input on every finite horizon. -/
theorem exists_lp_meanField_integral
    (V : IPLA.Joint dθ dx → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L (gradient V))
    (initial : Lp (IPLA.Joint dθ dx) 2 Q) (B : ℝ → Lp (IPLA.Joint dθ dx) 2 Q)
    (hB : Continuous B) (hB0 : B 0 = 0) (T : ℝ) (hT : 0 ≤ T) :
    ∃ Y : ℝ → Lp (IPLA.Joint dθ dx) 2 Q, Continuous Y ∧ Y 0 = initial ∧
      ∀ t ∈ Icc 0 T, Y t - initial =
        -(∫ s in 0..t, lpMeanFieldDrift Q V hLip (Y s)) + B t :=
  ULA.exists_langevin_integral (lpMeanFieldDrift Q V hLip) (2 * L)
    (lpMeanFieldDrift_lipschitz Q V hLip) initial B hB hB0 T hT


/-- The averaging map has exactly its intended pointwise block action. -/
theorem meanFieldAverageCLM_coe (X : Lp (IPLA.Joint dθ dx) 2 Q) :
    meanFieldAverageCLM Q X =ᵐ[Q] fun ω =>
      IPLA.pair (jointParameterCLM (lpExpectationCLM Q X)) (jointLatentCLM (X ω)) := by
  let c : IPLA.Joint dθ dx := jointParameterInclusionCLM
    (jointParameterCLM (lpExpectationCLM Q X))
  change Lp.const 2 Q c + jointLatentMaskCLM.compLp X =ᵐ[Q] _
  filter_upwards [Lp.coeFn_add (Lp.const 2 Q c) (jointLatentMaskCLM.compLp X),
    Lp.coeFn_const (μ := Q) (p := 2) (c := c), jointLatentMaskCLM.coeFn_compLp X]
    with ω ha hc hl
  rw [ha, Pi.add_apply, hc, hl]
  ext j
  cases j <;> simp [c, IPLA.pair]

/-- Averaging makes the parameter block a constant random variable. -/
theorem meanFieldAverageCLM_parameter (X : Lp (IPLA.Joint dθ dx) 2 Q) :
    jointParameterCLM.compLp (meanFieldAverageCLM Q X) =
      Lp.const 2 Q (jointParameterCLM (lpExpectationCLM Q X)) := by
  apply Lp.ext
  filter_upwards [jointParameterCLM.coeFn_compLp (meanFieldAverageCLM Q X),
    meanFieldAverageCLM_coe Q X,
    Lp.coeFn_const (μ := Q) (p := 2)
      (c := jointParameterCLM (lpExpectationCLM Q X))] with ω hp hm hc
  rw [hp, hm, hc]
  rfl

/-- Averaging leaves the actual latent random variable unchanged. -/
theorem meanFieldAverageCLM_latent (X : Lp (IPLA.Joint dθ dx) 2 Q) :
    jointLatentCLM.compLp (meanFieldAverageCLM Q X) = jointLatentCLM.compLp X := by
  apply Lp.ext
  filter_upwards [jointLatentCLM.coeFn_compLp (meanFieldAverageCLM Q X),
    meanFieldAverageCLM_coe Q X, jointLatentCLM.coeFn_compLp X] with ω hp hm hx
  rw [hp, hm, hx]
  rfl

/-- The actual expected parameter force of a square-integrable joint vector. -/
def lpMeanFieldParameterForce (V : IPLA.Joint dθ dx → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L (gradient V)) (X : Lp (IPLA.Joint dθ dx) 2 Q) :
    EuclideanSpace ℝ (Fin dθ) :=
  jointParameterCLM (lpExpectationCLM Q (ULA.lpDrift Q (gradient V) hLip X))

theorem lpMeanFieldParameterForce_continuous (V : IPLA.Joint dθ dx → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L (gradient V)) : Continuous (lpMeanFieldParameterForce Q V hLip) :=
  jointParameterCLM.continuous.comp ((lpExpectationCLM Q).continuous.comp
    (ULA.lpDrift_lipschitz Q (gradient V) hLip).continuous)

/-- The parameter projection of the actual drift is its expected force. -/
theorem lpMeanFieldDrift_parameter (V : IPLA.Joint dθ dx → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L (gradient V)) (X : Lp (IPLA.Joint dθ dx) 2 Q) :
    jointParameterCLM.compLp (lpMeanFieldDrift Q V hLip X) =
      Lp.const 2 Q (lpMeanFieldParameterForce Q V hLip X) :=
  meanFieldAverageCLM_parameter Q _

/-- The latent projection of the actual drift is pointwise latent gradient. -/
theorem lpMeanFieldDrift_latent (V : IPLA.Joint dθ dx → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L (gradient V)) (X : Lp (IPLA.Joint dθ dx) 2 Q) :
    jointLatentCLM.compLp (lpMeanFieldDrift Q V hLip X) =
      jointLatentCLM.compLp (ULA.lpDrift Q (gradient V) hLip X) :=
  meanFieldAverageCLM_latent Q _

/-- The expected force equals the actual mean-field drift integral whenever
the input parameter is deterministic. The latent marginal is its actual law. -/
theorem lpMeanFieldParameterForce_eq_meanFieldDrift
    (V : IPLA.Joint dθ dx → ℝ) {L : ℝ≥0} (hLip : LipschitzWith L (gradient V))
    (X : Lp (IPLA.Joint dθ dx) 2 Q) (θ : EuclideanSpace ℝ (Fin dθ))
    (hθ : jointParameterCLM.compLp X = Lp.const 2 Q θ) :
    lpMeanFieldParameterForce Q V hLip X =
      meanFieldDrift V θ (Q.map (jointLatentCLM.compLp X)) := by
  have hp : ∀ᵐ ω ∂Q, jointParameterCLM (X ω) = θ := by
    have hh := jointParameterCLM.coeFn_compLp X
    rw [hθ] at hh
    filter_upwards [hh, Lp.coeFn_const (μ := Q) (p := 2) (c := θ)] with ω hh hc
    exact hh.symm.trans hc
  have hgrad : Integrable (fun ω => gradient V (X ω)) Q :=
    (ULA.lpDrift_memLp Q (gradient V) hLip X).integrable (by norm_num)
  have heq : lpMeanFieldParameterForce Q V hLip X =
      ∫ ω, jointParameterCLM (gradient V (X ω)) ∂Q := by
    unfold lpMeanFieldParameterForce
    rw [lpExpectationCLM_apply,
      integral_congr_ae (ULA.lpDrift_coe Q (gradient V) hLip X)]
    exact (jointParameterCLM.integral_comp_comm hgrad).symm
  rw [heq, meanFieldDrift,
    integral_map (Lp.aestronglyMeasurable (jointLatentCLM.compLp X)).aemeasurable
      (parameterGradient_latent_lipschitz hLip θ).continuous.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hp, jointLatentCLM.coeFn_compLp X] with ω hθω hx
  rw [hx]
  unfold parameterGradient
  congr 2
  ext j
  cases j with
  | inl j => exact congrArg (fun x : EuclideanSpace ℝ (Fin dθ) => x j) hθω
  | inr j => rfl

/-- Projection of the constructed equation preserves a deterministic
parameter and gives its genuine integral equation. -/
theorem lp_meanField_parameter_equation
    (V : IPLA.Joint dθ dx → ℝ) {L : ℝ≥0} (hLip : LipschitzWith L (gradient V))
    (initial : Lp (IPLA.Joint dθ dx) 2 Q) (θ₀ : EuclideanSpace ℝ (Fin dθ))
    (hinitial : jointParameterCLM.compLp initial = Lp.const 2 Q θ₀)
    (B Y : ℝ → Lp (IPLA.Joint dθ dx) 2 Q) (hY : Continuous Y)
    (hBθ : ∀ t, jointParameterCLM.compLp (B t) = 0)
    (T : ℝ) (heq : ∀ t ∈ Icc 0 T, Y t - initial =
      -(∫ s in 0..t, lpMeanFieldDrift Q V hLip (Y s)) + B t)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    jointParameterCLM.compLp (Y t) = Lp.const 2 Q
      (θ₀ - ∫ s in 0..t, lpMeanFieldParameterForce Q V hLip (Y s)) := by
  let P := (@jointParameterCLM dθ dx).compLpL 2 Q
  let C := (Lp.constL 2 Q ℝ : EuclideanSpace ℝ (Fin dθ) →L[ℝ]
    Lp (EuclideanSpace ℝ (Fin dθ)) 2 Q)
  have hd : IntervalIntegrable (fun s => lpMeanFieldDrift Q V hLip (Y s)) volume 0 t :=
    ((lpMeanFieldDrift_lipschitz Q V hLip).continuous.comp hY).intervalIntegrable _ _
  have hf : IntervalIntegrable (fun s => lpMeanFieldParameterForce Q V hLip (Y s))
      volume 0 t := ((lpMeanFieldParameterForce_continuous Q V hLip).comp hY).intervalIntegrable _ _
  have hp := congrArg P (heq t ht)
  change P (Y t - initial) = P (-(∫ s in 0..t, lpMeanFieldDrift Q V hLip (Y s)) + B t) at hp
  rw [map_sub, map_add, map_neg, ← P.intervalIntegral_comp_comm hd] at hp
  have hid : (fun s => P (lpMeanFieldDrift Q V hLip (Y s))) =
      fun s => C (lpMeanFieldParameterForce Q V hLip (Y s)) := by
    funext s
    exact lpMeanFieldDrift_parameter Q V hLip (Y s)
  rw [hid, C.intervalIntegral_comp_comm hf] at hp
  change jointParameterCLM.compLp (Y t) - jointParameterCLM.compLp initial =
    -Lp.const 2 Q (∫ s in 0..t, lpMeanFieldParameterForce Q V hLip (Y s)) +
      jointParameterCLM.compLp (B t) at hp
  rw [hinitial, hBθ t, add_zero] at hp
  rw [show Lp.const 2 Q (θ₀ - ∫ s in 0..t, lpMeanFieldParameterForce Q V hLip (Y s)) =
      Lp.const 2 Q θ₀ - Lp.const 2 Q (∫ s in 0..t, lpMeanFieldParameterForce Q V hLip (Y s))
      from map_sub (Lp.constₗ 2 Q ℝ) _ _]
  rw [sub_eq_iff_eq_add] at hp
  rw [hp]
  abel

/-- The latent component satisfies the actual projected gradient equation. -/
theorem lp_meanField_latent_equation
    (V : IPLA.Joint dθ dx → ℝ) {L : ℝ≥0} (hLip : LipschitzWith L (gradient V))
    (initial : Lp (IPLA.Joint dθ dx) 2 Q)
    (B Y : ℝ → Lp (IPLA.Joint dθ dx) 2 Q) (hY : Continuous Y)
    (T : ℝ) (heq : ∀ t ∈ Icc 0 T, Y t - initial =
      -(∫ s in 0..t, lpMeanFieldDrift Q V hLip (Y s)) + B t)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    jointLatentCLM.compLp (Y t) - jointLatentCLM.compLp initial =
      -(∫ s in 0..t, jointLatentCLM.compLp (ULA.lpDrift Q (gradient V) hLip (Y s))) +
        jointLatentCLM.compLp (B t) := by
  let P := (@jointLatentCLM dθ dx).compLpL 2 Q
  have hd : IntervalIntegrable (fun s => lpMeanFieldDrift Q V hLip (Y s)) volume 0 t :=
    ((lpMeanFieldDrift_lipschitz Q V hLip).continuous.comp hY).intervalIntegrable _ _
  have hp := congrArg P (heq t ht)
  rw [map_sub, map_add, map_neg, ← P.intervalIntegral_comp_comm hd] at hp
  change jointLatentCLM.compLp (Y t) - jointLatentCLM.compLp initial =
    -(∫ s in 0..t, jointLatentCLM.compLp (lpMeanFieldDrift Q V hLip (Y s))) +
      jointLatentCLM.compLp (B t) at hp
  simpa only [lpMeanFieldDrift_latent] using hp


/-- The constructed solution has a continuous deterministic parameter, its
actual latent marginal, and both mean-field integral equations. No solution
trajectory or law evolution is assumed in this existence statement. -/
theorem exists_lp_meanField_equations
    (V : IPLA.Joint dθ dx → ℝ) {L : ℝ≥0} (hLip : LipschitzWith L (gradient V))
    (initial : Lp (IPLA.Joint dθ dx) 2 Q) (θ₀ : EuclideanSpace ℝ (Fin dθ))
    (hinitial : jointParameterCLM.compLp initial = Lp.const 2 Q θ₀)
    (B : ℝ → Lp (IPLA.Joint dθ dx) 2 Q) (hB : Continuous B) (hB0 : B 0 = 0)
    (hBθ : ∀ t, jointParameterCLM.compLp (B t) = 0) (T : ℝ) (hT : 0 ≤ T) :
    ∃ (Y : ℝ → Lp (IPLA.Joint dθ dx) 2 Q) (θ : ℝ → EuclideanSpace ℝ (Fin dθ)),
      Continuous Y ∧ Continuous θ ∧ Y 0 = initial ∧ θ 0 = θ₀ ∧
      (∀ t ∈ Icc 0 T, Y t - initial =
        -(∫ s in 0..t, lpMeanFieldDrift Q V hLip (Y s)) + B t) ∧
      (∀ t ∈ Icc 0 T, jointParameterCLM.compLp (Y t) = Lp.const 2 Q (θ t)) ∧
      (∀ t ∈ Icc 0 T, θ t - θ₀ =
        -(∫ s in 0..t, meanFieldDrift V (θ s) (Q.map (jointLatentCLM.compLp (Y s))))) ∧
      (∀ t ∈ Icc 0 T, jointLatentCLM.compLp (Y t) - jointLatentCLM.compLp initial =
        -(∫ s in 0..t, jointLatentCLM.compLp (ULA.lpDrift Q (gradient V) hLip (Y s))) +
          jointLatentCLM.compLp (B t)) := by
  obtain ⟨Y, hY, hY0, heq⟩ := exists_lp_meanField_integral Q V hLip initial B hB hB0 T hT
  let θ : ℝ → EuclideanSpace ℝ (Fin dθ) := fun t =>
    θ₀ - ∫ s in 0..t, lpMeanFieldParameterForce Q V hLip (Y s)
  have hf : Continuous (fun s => lpMeanFieldParameterForce Q V hLip (Y s)) :=
    (lpMeanFieldParameterForce_continuous Q V hLip).comp hY
  have hθ : Continuous θ := continuous_const.sub
    (intervalIntegral.continuous_primitive (fun a b => hf.intervalIntegrable a b) 0)
  have hp : ∀ t ∈ Icc 0 T, jointParameterCLM.compLp (Y t) = Lp.const 2 Q (θ t) :=
    lp_meanField_parameter_equation Q V hLip initial θ₀ hinitial B Y hY hBθ T heq
  refine ⟨Y, θ, hY, hθ, hY0, ?_, heq, hp, ?_, ?_⟩
  · simp [θ]
  · intro t ht
    have hid : (∫ s in 0..t, lpMeanFieldParameterForce Q V hLip (Y s)) =
        ∫ s in 0..t, meanFieldDrift V (θ s) (Q.map (jointLatentCLM.compLp (Y s))) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      exact lpMeanFieldParameterForce_eq_meanFieldDrift Q V hLip (Y s) (θ s)
        (hp s ⟨hs.1, hs.2.trans ht.2⟩)
    change (θ₀ - ∫ s in 0..t, lpMeanFieldParameterForce Q V hLip (Y s)) - θ₀ =
      -(∫ s in 0..t, meanFieldDrift V (θ s) (Q.map (jointLatentCLM.compLp (Y s))))
    rw [hid]
    abel
  · exact lp_meanField_latent_equation Q V hLip initial B Y hY T heq

/-- Actual Brownian-coordinate inputs, with only their latent coordinates
retained, give a concrete continuous L² input. Noise continuity and its zero
initial value are conclusions of the Brownian laws. -/
def meanFieldBrownianNoise
    (W : (Fin dθ ⊕ Fin dx) → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, ProbabilityTheory.IsPreBrownianReal (W i) Q) (a t : ℝ) :
    Lp (IPLA.Joint dθ dx) 2 Q :=
  jointLatentMaskCLM.compLp (ULA.brownianLangevinNoise Q W hW a t)

omit [IsProbabilityMeasure Q] in
theorem meanFieldBrownianNoise_continuous
    (W : (Fin dθ ⊕ Fin dx) → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, ProbabilityTheory.IsPreBrownianReal (W i) Q) (a : ℝ) :
    Continuous (meanFieldBrownianNoise Q W hW a) :=
  ((@jointLatentMaskCLM dθ dx).compLpL 2 Q).continuous.comp
    (ULA.brownianLangevinNoise_continuous Q W hW a)

omit [IsProbabilityMeasure Q] in
@[simp] theorem meanFieldBrownianNoise_zero
    (W : (Fin dθ ⊕ Fin dx) → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, ProbabilityTheory.IsPreBrownianReal (W i) Q) (a : ℝ) :
    meanFieldBrownianNoise Q W hW a 0 = 0 := by
  simp only [meanFieldBrownianNoise, ULA.brownianLangevinNoise_zero]
  exact map_zero ((@jointLatentMaskCLM dθ dx).compLpL 2 Q)

omit [IsProbabilityMeasure Q] in
@[simp] theorem meanFieldBrownianNoise_parameter
    (W : (Fin dθ ⊕ Fin dx) → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, ProbabilityTheory.IsPreBrownianReal (W i) Q) (a t : ℝ) :
    jointParameterCLM.compLp (meanFieldBrownianNoise Q W hW a t) = 0 := by
  apply Lp.ext
  filter_upwards [jointParameterCLM.coeFn_compLp (meanFieldBrownianNoise Q W hW a t),
    jointLatentMaskCLM.coeFn_compLp (ULA.brownianLangevinNoise Q W hW a t),
    Lp.coeFn_zero (E := EuclideanSpace ℝ (Fin dθ)) (p := 2) (μ := Q)] with ω hp hl hz
  rw [hp, hz]
  change jointParameterCLM (jointLatentMaskCLM.compLp
    (ULA.brownianLangevinNoise Q W hW a t) ω) = 0
  rw [hl]
  ext j
  simp

/-- Genuine finite-horizon mean-field L² existence with a Brownian input.
All stochastic input continuity is derived from the coordinate Brownian laws;
no pathwise strong-SDE, independence or adaptedness assertion is made. -/
theorem exists_lp_meanField_integral_of_brownian
    (V : IPLA.Joint dθ dx → ℝ) {L : ℝ≥0} (hLip : LipschitzWith L (gradient V))
    (initial : Lp (IPLA.Joint dθ dx) 2 Q)
    (W : (Fin dθ ⊕ Fin dx) → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, ProbabilityTheory.IsPreBrownianReal (W i) Q)
    (a T : ℝ) (hT : 0 ≤ T) :
    ∃ Y : ℝ → Lp (IPLA.Joint dθ dx) 2 Q, Continuous Y ∧ Y 0 = initial ∧
      ∀ t ∈ Icc 0 T, Y t - initial =
        -(∫ s in 0..t, lpMeanFieldDrift Q V hLip (Y s)) +
          meanFieldBrownianNoise Q W hW a t :=
  exists_lp_meanField_integral Q V hLip initial (meanFieldBrownianNoise Q W hW a)
    (meanFieldBrownianNoise_continuous Q W hW a) (meanFieldBrownianNoise_zero Q W hW a) T hT

/-- Split Moreau smoothing supplies the actual globally Lipschitz gradient
needed by the mean-field construction. Its coefficient is `L₁+1/eta`. -/
theorem exists_lp_moreau_meanField_integral
    {g₁ g₂ : IPLA.Joint dθ dx → ℝ} {L₁ : ℝ≥0} {eta : ℝ}
    (hg₁ : Differentiable ℝ g₁) (hLip₁ : LipschitzWith L₁ (gradient g₁))
    (hg₂ : ConvexOn ℝ univ g₂) (hb : ∃ b, ∀ z, b ≤ g₂ z) (heta : 0 < eta)
    (initial : Lp (IPLA.Joint dθ dx) 2 Q) (B : ℝ → Lp (IPLA.Joint dθ dx) 2 Q)
    (hB : Continuous B) (hB0 : B 0 = 0) (T : ℝ) (hT : 0 ≤ T) :
    ∃ hLip : LipschitzWith (smoothingLipschitz L₁ eta)
        (gradient (smoothedPotential g₁ g₂ eta)),
      ∃ Y : ℝ → Lp (IPLA.Joint dθ dx) 2 Q, Continuous Y ∧ Y 0 = initial ∧
        ∀ t ∈ Icc 0 T, Y t - initial =
          -(∫ s in 0..t, lpMeanFieldDrift Q (smoothedPotential g₁ g₂ eta) hLip (Y s)) + B t := by
  have he := moreau_differentiable hg₂ hb heta
  have hg : gradient (moreau g₂ eta) = residual g₂ eta := funext (gradient_moreau hg₂ hb heta)
  have hLipe : LipschitzWith eta.toNNReal⁻¹ (gradient (moreau g₂ eta)) := by
    rw [hg]
    simpa only [Real.toNNReal_inv] using residual_lipschitz hg₂ hb heta
  have hLip := smoothed_gradient_lipschitz hg₁ he hLip₁ hLipe
  exact ⟨hLip, exists_lp_meanField_integral Q _ hLip initial B hB hB0 T hT⟩

end Process
end ProximalLangevin
