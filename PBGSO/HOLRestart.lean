import PBGSO.HOLUniformLocal
import PBGSO.GlobalIntegral
import PBGSO.MethodIntegralSegments
import PBGSO.AdditiveContraction

/-! # Actual restarted HOL integral trajectories on the implementation source

Every restart is constructed from the primitive globally Lipschitz forces and
the same shifted physical Brownian input. Initial states may be arbitrary L²
random variables, including actual numerical iterates. No law, moment bound,
local error, or numerical contraction is assumed by this construction.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace PBGSO.Methods

variable {Ω I Θ : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  {f : Ω → ULA.CanonicalBrownian.VectorSample I}
  (hf : MeasurePreserving f Q (ULA.CanonicalBrownian.vectorProbability I))

/-- The same physical Brownian path, shifted to an arbitrary restart time.
Only the final sampler auxiliary is forced. -/
def higherOrderRestartInput (α a t : ℝ) :
    HOLState Θ (Lp (EuclideanSpace ℝ I) 2 Q) :=
  holBrownianIncrement (Real.sqrt α • ULA.brownianLangevinNoise Q
    (canonicalPullbackCoordinate I hf) (canonicalPullbackCoordinate_isPreBrownian I hf) a t)

omit [DecidableEq I] [NormedSpace ℝ Θ] [CompleteSpace Θ] in
theorem higherOrderRestartInput_continuous (α a : ℝ) :
    Continuous (higherOrderRestartInput (Θ := Θ) Q hf α a) := by
  have hb := ULA.brownianLangevinNoise_continuous Q (canonicalPullbackCoordinate I hf)
    (canonicalPullbackCoordinate_isPreBrownian I hf) a
  change Continuous (fun t : ℝ ↦ (0, 0, 0, Real.sqrt α •
    ULA.brownianLangevinNoise Q (canonicalPullbackCoordinate I hf)
      (canonicalPullbackCoordinate_isPreBrownian I hf) a t))
  exact continuous_const.prodMk (continuous_const.prodMk
    (continuous_const.prodMk (hb.const_smul (Real.sqrt α))))

omit [DecidableEq I] [NormedSpace ℝ Θ] [CompleteSpace Θ] in
@[simp] theorem higherOrderRestartInput_zero (α a : ℝ) :
    higherOrderRestartInput (Θ := Θ) Q hf α a 0 = 0 := by
  simp [higherOrderRestartInput, ULA.brownianLangevinNoise_zero, holBrownianIncrement]

/-- The square-root input coefficient is computed from the actual Brownian
coordinate increment, independently of the random restart state. -/
theorem higherOrderRestartInput_bound (α a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    ‖higherOrderRestartInput (Θ := Θ) Q hf α a t‖ ≤
      (Real.sqrt α * Real.sqrt (2 * (Fintype.card I : ℝ))) * Real.sqrt t := by
  have hn : ∀ b : Lp (EuclideanSpace ℝ I) 2 Q,
      ‖holBrownianIncrement (Θ := Θ) b‖ = ‖b‖ := by
    intro b
    simp only [holBrownianIncrement, Prod.norm_def, norm_zero]
    simp only [max_eq_right (norm_nonneg b)]
  dsimp only [higherOrderRestartInput]
  rw [hn, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    ULA.brownianLangevinNoise_norm Q (canonicalPullbackCoordinate I hf)
      (canonicalPullbackCoordinate_isPreBrownian I hf) a t ha ht]
  exact (by ring : Real.sqrt α * (Real.sqrt (2 * (Fintype.card I : ℝ)) * Real.sqrt t) =
    Real.sqrt α * Real.sqrt (2 * (Fintype.card I : ℝ)) * Real.sqrt t).le

omit [NormedSpace ℝ Θ] [CompleteSpace Θ] in
/-- The exact endpoint input is the fourth component of the same Gaussian
kernel block that supplies the printed numerical update. -/
theorem higherOrderRestartInput_endpoint (α γ : ℝ) (hα : 0 ≤ α) (a h : ℝ≥0) :
    higherOrderRestartInput (Θ := Θ) Q hf α a h =
      holBrownianIncrement (holPullbackVectorNoise I hf α γ a h 3) := by
  rw [higherOrderPullbackGaussianIncrement_brownian Q hf α γ hα a h]
  rfl

omit [DecidableEq I] [NormedSpace ℝ Θ] [CompleteSpace Θ] in
/-- Literal telescoping of the physical Brownian coordinates. -/
theorem higherOrderRestartInput_increment (α a t : ℝ) :
    higherOrderRestartInput (Θ := Θ) Q hf α 0 (a + t) -
      higherOrderRestartInput Q hf α 0 a = higherOrderRestartInput Q hf α a t := by
  change (0 - 0, 0 - 0, 0 - 0,
    Real.sqrt α • ULA.brownianLangevinNoise Q (canonicalPullbackCoordinate I hf)
      (canonicalPullbackCoordinate_isPreBrownian I hf) 0 (a + t) -
    Real.sqrt α • ULA.brownianLangevinNoise Q (canonicalPullbackCoordinate I hf)
      (canonicalPullbackCoordinate_isPreBrownian I hf) 0 a) = _
  rw [← smul_sub, PBGSO.MethodSegments.brownianNoise_increment]
  simp [higherOrderRestartInput, holBrownianIncrement]

section Construction
variable
  (Fbar : Θ → Lp (EuclideanSpace ℝ I) 2 Q → Θ)
  (G : Θ → Lp (EuclideanSpace ℝ I) 2 Q → Lp (EuclideanSpace ℝ I) 2 Q)
  (LF LG α γ : ℝ) (hLF : 0 ≤ LF) (hLG : 0 ≤ LG)
  (hF : ∀ θ θ' x x', ‖Fbar θ x - Fbar θ' x'‖ ≤ LF * (‖θ - θ'‖ + ‖x - x'‖))
  (hG : ∀ θ θ' x x', ‖G θ x - G θ' x'‖ ≤ LG * (‖θ - θ'‖ + ‖x - x'‖))

include LF LG hLF hLG hF hG in
/-- Actual global Picard existence permits every random-state restart used by
the uniform comparison. It is not an abstract reference-process premise. -/
theorem exists_higherOrder_restart
    (z : HOLState Θ (Lp (EuclideanSpace ℝ I) 2 Q)) (a : ℝ) :
    ∃ r : ℝ → HOLState Θ (Lp (EuclideanSpace ℝ I) 2 Q),
      Continuous r ∧ r 0 = z ∧ ∀ t, 0 ≤ t →
        r t - z = (∫ s in 0..t, holDrift Fbar G α γ (r s)) +
          higherOrderRestartInput Q hf α a t :=
  PBGSO.exists_global_integral_solution (holDrift Fbar G α γ)
    (holDriftGlobalLip LF LG α γ)
    (holDrift_globally_lipschitz Fbar G LF LG α γ hLF hLG hF hG) z
    (higherOrderRestartInput Q hf α a)
    (higherOrderRestartInput_continuous Q hf α a)
    (higherOrderRestartInput_zero Q hf α a)

/-- A fixed actual choice of the constructed restart, with all properties
proved below. It uses no adaptedness or future-independence assumption. -/
def higherOrderRestart
    (z : HOLState Θ (Lp (EuclideanSpace ℝ I) 2 Q)) (a : ℝ) :
    ℝ → HOLState Θ (Lp (EuclideanSpace ℝ I) 2 Q) :=
  Classical.choose (exists_higherOrder_restart Q hf Fbar G LF LG α γ hLF hLG hF hG z a)

variable (z : HOLState Θ (Lp (EuclideanSpace ℝ I) 2 Q)) (a : ℝ)

theorem higherOrderRestart_continuous :
    Continuous (higherOrderRestart Q hf Fbar G LF LG α γ hLF hLG hF hG z a) :=
  (Classical.choose_spec
    (exists_higherOrder_restart Q hf Fbar G LF LG α γ hLF hLG hF hG z a)).1

@[simp] theorem higherOrderRestart_zero :
    higherOrderRestart Q hf Fbar G LF LG α γ hLF hLG hF hG z a 0 = z :=
  (Classical.choose_spec
    (exists_higherOrder_restart Q hf Fbar G LF LG α γ hLF hLG hF hG z a)).2.1

theorem higherOrderRestart_equation (t : ℝ) (ht : 0 ≤ t) :
    higherOrderRestart Q hf Fbar G LF LG α γ hLF hLG hF hG z a t - z =
      (∫ s in 0..t, holDrift Fbar G α γ
        (higherOrderRestart Q hf Fbar G LF LG α γ hLF hLG hF hG z a s)) +
          higherOrderRestartInput Q hf α a t :=
  (Classical.choose_spec
    (exists_higherOrder_restart Q hf Fbar G LF LG α γ hLF hLG hF hG z a)).2.2 t ht

/-- Common-input uniqueness identifies the actual Picard choice with any
other trajectory satisfying the same original integral equation. -/
theorem higherOrderRestart_unique
    (r : ℝ → HOLState Θ (Lp (EuclideanSpace ℝ I) 2 Q)) (hr : Continuous r)
    (_hr0 : r 0 = z)
    (heq : ∀ t, 0 ≤ t → r t - z =
      (∫ s in 0..t, holDrift Fbar G α γ (r s)) + higherOrderRestartInput Q hf α a t)
    (t : ℝ) (ht : 0 ≤ t) :
    higherOrderRestart Q hf Fbar G LF LG α γ hLF hLG hF hG z a t = r t := by
  have hu := ULA.langevin_integral_unique (fun w ↦ -holDrift Fbar G α γ w)
    (holDriftGlobalLip LF LG α γ)
    (holDrift_globally_lipschitz Fbar G LF LG α γ hLF hLG hF hG).neg z
    (higherOrderRestartInput Q hf α a)
    (higherOrderRestart Q hf Fbar G LF LG α γ hLF hLG hF hG z a) r
    (higherOrderRestart_continuous Q hf Fbar G LF LG α γ hLF hLG hF hG z a) hr t ht
    (fun s hs ↦ by
      simpa only [intervalIntegral.integral_neg, neg_neg] using
        higherOrderRestart_equation Q hf Fbar G LF LG α γ hLF hLG hF hG z a s hs.1)
    (fun s hs ↦ by
      simpa only [intervalIntegral.integral_neg, neg_neg] using heq s hs.1)
  exact hu ⟨ht, le_rfl⟩

omit z a in
/-- Restart compatibility with the original continuous process is proved from
its integral equation and uniqueness, rather than assumed as a law identity. -/
theorem higherOrderRestart_agrees
    (Y : ℝ → HOLState Θ (Lp (EuclideanSpace ℝ I) 2 Q)) (hY : Continuous Y)
    (heq : ∀ t, 0 ≤ t → Y t - Y 0 =
      (∫ s in 0..t, holDrift Fbar G α γ (Y s)) + higherOrderRestartInput Q hf α 0 t)
    (a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    higherOrderRestart Q hf Fbar G LF LG α γ hLF hLG hF hG (Y a) a t = Y (a + t) := by
  apply higherOrderRestart_unique Q hf Fbar G LF LG α γ hLF hLG hF hG (Y a) a
    (fun s ↦ Y (a + s)) (hY.comp (continuous_const.add continuous_id)) (by simp)
  · intro s hs
    have he := PBGSO.MethodSegments.integral_shift Y (fun r ↦ holDrift Fbar G α γ (Y r))
      (higherOrderRestartInput Q hf α 0)
      ((holDrift_globally_lipschitz Fbar G LF LG α γ hLF hLG hF hG).continuous.comp hY)
      heq a s ha hs
    rw [higherOrderRestartInput_increment] at he
    exact he
  · exact ht

omit z in
/-- Contractivity of the actual restarted integral solution follows from a
primitive weighted drift pairing. The numerical update is not assumed to be
contractive. Source empirical A3 supplies this pairing in particle clients. -/
theorem higherOrderRestart_contracts
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : HOLState Θ (Lp (EuclideanSpace ℝ I) 2 Q) →L[ℝ] H) (ρ : ℝ)
    (hmono : ∀ x y,
      inner ℝ (C (x - y)) (C (holDrift Fbar G α γ x - holDrift Fbar G α γ y)) ≤
        -ρ * ‖C (x - y)‖ ^ 2)
    (z w : HOLState Θ (Lp (EuclideanSpace ℝ I) 2 Q)) (t : ℝ) (ht : 0 ≤ t) :
    ‖C (higherOrderRestart Q hf Fbar G LF LG α γ hLF hLG hF hG z a t -
        higherOrderRestart Q hf Fbar G LF LG α γ hLF hLG hF hG w a t)‖ ≤
      Real.exp (-ρ * t) * ‖C (z - w)‖ := by
  have hm : ∀ x y, ρ * ‖C (x - y)‖ ^ 2 ≤
      inner ℝ (C (x - y))
        (C ((-holDrift Fbar G α γ x) - (-holDrift Fbar G α γ y))) := by
    intro x y
    rw [show -holDrift Fbar G α γ x - -holDrift Fbar G α γ y =
      -(holDrift Fbar G α γ x - holDrift Fbar G α γ y) by abel,
      map_neg, inner_neg_right]
    linarith [hmono x y]
  have hc := PBGSO.transformed_additive_integral_contraction
    (fun w ↦ -holDrift Fbar G α γ w) (holDriftGlobalLip LF LG α γ)
    (holDrift_globally_lipschitz Fbar G LF LG α γ hLF hLG hF hG).neg C ρ hm
    (higherOrderRestart Q hf Fbar G LF LG α γ hLF hLG hF hG z a)
    (higherOrderRestart Q hf Fbar G LF LG α γ hLF hLG hF hG w a)
    (higherOrderRestartInput Q hf α a)
    (higherOrderRestart_continuous Q hf Fbar G LF LG α γ hLF hLG hF hG z a)
    (higherOrderRestart_continuous Q hf Fbar G LF LG α γ hLF hLG hF hG w a) t
    (fun s hs ↦ by
      simpa only [higherOrderRestart_zero, intervalIntegral.integral_neg, neg_neg] using
        higherOrderRestart_equation Q hf Fbar G LF LG α γ hLF hLG hF hG z a s hs.1)
    (fun s hs ↦ by
      simpa only [higherOrderRestart_zero, intervalIntegral.integral_neg, neg_neg] using
        higherOrderRestart_equation Q hf Fbar G LF LG α γ hLF hLG hF hG w a s hs.1)
    t ⟨ht, le_rfl⟩
  simpa only [higherOrderRestart_zero] using hc

end Construction
end PBGSO.Methods
