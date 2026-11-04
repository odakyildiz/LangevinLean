import WassersteinMixing.SemigroupRandomMALABounds
import WassersteinMixing.ActualAdapted
import WassersteinMixing.SemigroupEulerActual
import WassersteinMixing.SemigroupLift
import WassersteinMixing.SemigroupLimits

/-! # Actual MALA approximation of the canonical Langevin observables

The uniformly randomized MALA and matching Brownian Euler trajectories are
realized on one probability space. The proved rejection estimate and genuine
Euler convergence therefore imply convergence in probability to the actual
Langevin state, and stationarity upgrades this to strong `L²` convergence of
every observable.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace WassersteinMixing.RandomMALA.Canonical

/-- The isometric pullback to the genuinely augmented Brownian/uniform source. -/
def stateLift (P : Parameters) (V : E P.dimension → ℝ) :
    Lp (E P.dimension) 2 (actualProbability P V) →ₗᵢ[ℝ]
      Lp (E P.dimension) 2 (probability P V) :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst

/-- The actual canonical Langevin state, lifted onto the common MALA source. -/
def diffusion (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V)
    (t : ℝ) : Lp (E P.dimension) 2 (probability P V) :=
  stateLift P V (CanonicalSemigroup.state P V hV t)

private theorem integral_norm_le_lp_norm {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] (Q : Measure Ω) [IsProbabilityMeasure Q] (Z : Lp H 2 Q) :
    (∫ ω, ‖Z ω‖ ∂Q) ≤ ‖Z‖ := by
  have hint := MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.memLp Z)
  have he := ENNReal.toReal_mono (Lp.eLpNorm_ne_top Z)
    (eLpNorm_le_eLpNorm_of_exponent_le (μ := Q) (f := Z)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  rw [eLpNorm_one_eq_lintegral_enorm hint.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hint,
    ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _),
    ← Lp.norm_def] at he
  exact he

theorem diffusion_law (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (t : ℝ) :
    (probability P V).map (diffusion P V hV t) = ULA.gibbsMeasure V := by
  let := actualProbability_isProbability P V hV
  let := probability_isProbability P V hV
  exact (KineticLangevin.sourcePullback_map Prod.fst
    (measurePreserving_fst (μ := actualProbability P V) (ν := uniformPath))
    (CanonicalSemigroup.state P V hV t)).trans (CanonicalSemigroup.state_law P V hV t)

theorem continuous_diffusion (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) : Continuous (diffusion P V hV) :=
  (stateLift P V).continuous.comp (CanonicalSemigroup.continuous_state P V hV)

/-- The Brownian innovation is the exact normalized increment used by Euler. -/
theorem gaussian_eq_brownian (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (r : ℝ) :
    gaussian P V hV r = ULA.Hilbert.brownianEulerNoise (actualProbability P V)
      (CanonicalSemigroup.brownian P) (CanonicalSemigroup.brownian_preBrownian P V hV) r := by
  let := actualTarget_isProbability P V hV
  funext n
  have he := ULA.Hilbert.productNoise_eq_brownianEulerNoise
    (ULA.CanonicalBrownian.vectorProbability (Fin P.dimension)) (diagonalGibbsCoupling P V)
    ULA.CanonicalBrownian.coordinate ULA.CanonicalBrownian.coordinate_isPreBrownian r n
  convert he using 1 <;> rfl

/-- The Euler coordinate of the actual randomized chain is literally the
matching-noise additive Euler method for the global Langevin equation. -/
theorem euler_eq_additive (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (r : ℝ) (hr : 0 < r) (n : ℕ) :
    letI := actualProbability_isProbability P V hV
    euler P V hV r n = ULA.additiveEulerChain
      (ULA.lpDrift (actualProbability P V) (gradient V) hV.gradientLipschitz) r
      (CanonicalSemigroup.initial P V hV)
      (ULA.brownianLangevinNoise (actualProbability P V) (CanonicalSemigroup.brownian P)
        (CanonicalSemigroup.brownian_preBrownian P V hV) 0) n := by
  let := actualProbability_isProbability P V hV
  unfold euler
  rw [actualInitial_eq_semigroupInitial P V hV, gaussian_eq_brownian P V hV r]
  exact (ULA.brownian_additiveEulerChain_eq_lpChain (actualProbability P V) V r
    ⟨P.beta, P.beta_pos.le⟩ hV.gradientLipschitz (CanonicalSemigroup.initial P V hV)
    (CanonicalSemigroup.brownian P) (CanonicalSemigroup.brownian_preBrownian P V hV) hr n).symm

/-- Actual Brownian Euler convergence on the arbitrary common meshes used in
the discrete semigroup composition argument. -/
theorem euler_variable_tendsto {I : Type*} {l : Filter I}
    (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V)
    (step : I → ℝ) (count : I → ℕ) (hstep : ∀ i, 0 < step i)
    (hmesh : Tendsto step l (𝓝 0)) (T : ℝ) (hT : 0 ≤ T)
    (hbound : ∀ i, (count i : ℝ) * step i ≤ T)
    (t : ℝ) (htime : Tendsto (fun i ↦ (count i : ℝ) * step i) l (𝓝 t)) :
    Tendsto (fun i ↦ euler P V hV (step i) (count i)) l
      (𝓝 (CanonicalSemigroup.state P V hV t)) := by
  let := actualProbability_isProbability P V hV
  have he := CanonicalSemigroup.shiftedEuler_variable_tendsto P V hV
    0 T le_rfl hT step count (fun i ↦ (hstep i).le) hmesh hbound t htime
  simp only [zero_add, CanonicalSemigroup.state_zero] at he
  exact he.congr' (Eventually.of_forall fun i ↦ (euler_eq_additive P V hV _ (hstep i) _).symm)

/-- The same convergence after appending the independent uniform path. -/
theorem liftedEuler_variable_tendsto {I : Type*} {l : Filter I}
    (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V)
    (step : I → ℝ) (count : I → ℕ) (hstep : ∀ i, 0 < step i)
    (hmesh : Tendsto step l (𝓝 0)) (T : ℝ) (hT : 0 ≤ T)
    (hbound : ∀ i, (count i : ℝ) * step i ≤ T)
    (t : ℝ) (htime : Tendsto (fun i ↦ (count i : ℝ) * step i) l (𝓝 t)) :
    Tendsto (fun i ↦ stateLift P V (euler P V hV (step i) (count i))) l
      (𝓝 (diffusion P V hV t)) :=
  (stateLift P V).continuous.tendsto _ |>.comp
    (euler_variable_tendsto P V hV step count hstep hmesh T hT hbound t htime)

/-- The proved rejection estimate compares the actual `L²` representatives. -/
theorem mala_euler_integral_le (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hsmall : r ≤ 2 / (P.alpha + P.beta)) (n : ℕ) :
    (∫ ω, ‖mala P V hV r hr n ω - stateLift P V (euler P V hV r n) ω‖
      ∂probability P V) ≤
      (n : ℝ) * ULA.malaRejectionConstant V ⟨P.beta, P.beta_pos.le⟩ * r * Real.sqrt r := by
  have he := Lp.coeFn_compMeasurePreserving (euler P V hV r n)
    (measurePreserving_fst (μ := actualProbability P V) (ν := uniformPath))
  have hident : (fun ω ↦ ‖mala P V hV r hr n ω -
      stateLift P V (euler P V hV r n) ω‖) =ᵐ[probability P V]
      fun ω ↦ ‖(state P V hV r n ω).1 - (state P V hV r n ω).2‖ := by
    filter_upwards [mala_coe P V hV r hr n, he, state_fst_eq_euler P V hV r n]
      with ω hm he hf
    change stateLift P V (euler P V hV r n) ω = _ at he
    dsimp only [Function.comp_apply] at he
    rw [hm, he, ← hf, norm_sub_rev]
  rw [integral_congr_ae hident]
  exact distance_integral_le P V hV r hr hr1 hsmall n

/-- Actual MALA states converge in probability to the actual Langevin state.
Only the mesh and endpoint times are inputs; all comparison estimates have
already been proved for these random trajectories. -/
theorem mala_variable_tendstoInMeasure {I : Type*} {l : Filter I}
    (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V)
    (step : I → ℝ) (count : I → ℕ) (hstep : ∀ i, 0 < step i)
    (hmesh : Tendsto step l (𝓝 0)) (T : ℝ) (hT : 0 ≤ T)
    (hbound : ∀ i, (count i : ℝ) * step i ≤ T)
    (t : ℝ) (htime : Tendsto (fun i ↦ (count i : ℝ) * step i) l (𝓝 t)) :
    TendstoInMeasure (probability P V)
      (fun i ω ↦ mala P V hV (step i) (hstep i) (count i) ω) l
      (diffusion P V hV t) := by
  let := actualProbability_isProbability P V hV
  let := probability_isProbability P V hV
  let C := ULA.malaRejectionConstant V ⟨P.beta, P.beta_pos.le⟩
  let X := fun i ↦ mala P V hV (step i) (hstep i) (count i)
  let Y := fun i ↦ stateLift P V (euler P V hV (step i) (count i))
  let Z := diffusion P V hV t
  have hC : 0 ≤ C := ULA.malaRejectionConstant_nonneg V _
  have hconv : Tendsto Y l (𝓝 Z) :=
    liftedEuler_variable_tendsto P V hV step count hstep hmesh T hT hbound t htime
  have herror : Tendsto (fun i ↦ T * C * Real.sqrt (step i) + ‖Y i - Z‖) l (𝓝 0) := by
    have hs := (Real.continuous_sqrt.tendsto 0).comp hmesh
    simpa only [Real.sqrt_zero, mul_zero, add_zero, Function.comp_def] using
      (hs.const_mul (T * C)).add (tendsto_iff_norm_sub_tendsto_zero.mp hconv)
  have hsmall : ∀ᶠ i in l, step i ≤ 1 ∧ step i ≤ 2 / (P.alpha + P.beta) :=
    (hmesh.eventually_le_const zero_lt_one).and
      (hmesh.eventually_le_const (div_pos (by norm_num) (add_pos P.alpha_pos P.beta_pos)))
  have hmean : Tendsto (fun i ↦ ∫ ω, ‖X i ω - Z ω‖ ∂probability P V) l (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _)
      ?_ herror
    filter_upwards [hsmall] with i hi
    have hint (W : Lp (E P.dimension) 2 (probability P V)) :=
      MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.memLp W)
    have hxy := (hint (X i)).sub (hint (Y i))
    have hyz := (hint (Y i)).sub (hint Z)
    have hxz := (hint (X i)).sub (hint Z)
    calc
      _ ≤ ∫ ω, ‖X i ω - Y i ω‖ + ‖Y i ω - Z ω‖ ∂probability P V :=
        integral_mono_ae hxz.norm (hxy.norm.add hyz.norm)
          (Eventually.of_forall fun ω ↦ norm_sub_le_norm_sub_add_norm_sub _ _ _)
      _ = (∫ ω, ‖X i ω - Y i ω‖ ∂probability P V) +
          (∫ ω, ‖Y i ω - Z ω‖ ∂probability P V) := integral_add hxy.norm hyz.norm
      _ ≤ (count i : ℝ) * C * step i * Real.sqrt (step i) + ‖Y i - Z‖ := by
        apply add_le_add (mala_euler_integral_le P V hV _ (hstep i) hi.1 hi.2 _)
        have he : (∫ ω, ‖Y i ω - Z ω‖ ∂probability P V) =
            ∫ ω, ‖(Y i - Z) ω‖ ∂probability P V :=
          integral_congr_ae (Lp.coeFn_sub (Y i) Z |>.symm.fun_comp norm)
        rw [he]
        exact integral_norm_le_lp_norm _ _
      _ ≤ T * C * Real.sqrt (step i) + ‖Y i - Z‖ := by
        apply add_le_add _ le_rfl
        have hb := mul_le_mul_of_nonneg_right (hbound i)
          (mul_nonneg hC (Real.sqrt_nonneg (step i)))
        nlinarith only [hb]
  exact StationaryObservables.tendstoInMeasure_of_integral_norm_sub (probability P V)
    (fun i ω ↦ X i ω) Z
    (fun i ↦ (MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.memLp (X i))).sub
      (MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.memLp Z))) hmean

variable {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Evaluation at the actual stationary randomized MALA state. -/
def malaEvaluation (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (r : ℝ) (hr : 0 < r) (n : ℕ) :
    Lp F 2 (ULA.gibbsMeasure V) →ₗᵢ[𝕜] Lp F 2 (probability P V) :=
  StationaryObservables.evaluation _ _ (mala P V hV r hr n) (mala_law P V hV r hr n)

/-- Evaluation at the actual global diffusion on the same augmented source. -/
def diffusionEvaluation (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (t : ℝ) :
    Lp F 2 (ULA.gibbsMeasure V) →ₗᵢ[𝕜] Lp F 2 (probability P V) :=
  StationaryObservables.evaluation _ _ (diffusion P V hV t) (diffusion_law P V hV t)

omit [CompleteSpace F] in
/-- The stationary observable limit is strong in `L²`, even for unbounded
observables. It follows from actual state convergence and density. -/
theorem malaEvaluation_variable_tendsto [NormedSpace ℝ F]
    {I : Type*} {l : Filter I} [l.IsCountablyGenerated]
    (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V)
    (step : I → ℝ) (count : I → ℕ) (hstep : ∀ i, 0 < step i)
    (hmesh : Tendsto step l (𝓝 0)) (T : ℝ) (hT : 0 ≤ T)
    (hbound : ∀ i, (count i : ℝ) * step i ≤ T)
    (t : ℝ) (htime : Tendsto (fun i ↦ (count i : ℝ) * step i) l (𝓝 t))
    (f : Lp F 2 (ULA.gibbsMeasure V)) :
    Tendsto (fun i ↦ malaEvaluation (𝕜 := 𝕜) P V hV (step i) (hstep i) (count i) f) l
      (𝓝 (diffusionEvaluation (𝕜 := 𝕜) P V hV t f)) := by
  let := actualTarget_isProbability P V hV
  let := probability_isProbability P V hV
  exact StationaryObservables.evaluation_tendsto_inMeasure (𝕜 := 𝕜) _ _
    (fun i ↦ mala P V hV (step i) (hstep i) (count i)) (diffusion P V hV t)
    (fun i ↦ mala_law P V hV _ (hstep i) _) (diffusion_law P V hV t)
    (mala_variable_tendstoInMeasure P V hV step count hstep hmesh T hT hbound t htime) f

omit [CompleteSpace F] in
/-- Source augmentation commutes with every real or complex observable. -/
theorem diffusionEvaluation_eq_lift (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (t : ℝ) :
    diffusionEvaluation (𝕜 := 𝕜) (F := F) P V hV t =
      (Lp.compMeasurePreservingₗᵢ 𝕜 Prod.fst
        (measurePreserving_fst (μ := actualProbability P V) (ν := uniformPath))).comp
        (CanonicalSemigroup.evaluation P V hV t) := by
  let := actualProbability_isProbability P V hV
  apply LinearIsometry.ext
  intro f
  exact stationaryEvaluation_sourceLift (𝕜 := 𝕜) Prod.fst
    (measurePreserving_fst (μ := actualProbability P V) (ν := uniformPath))
    (ULA.gibbsMeasure V) (CanonicalSemigroup.state P V hV t)
    (CanonicalSemigroup.state_law P V hV t) f

/-- Compression on the augmented source is exactly the original diffusion
transition; auxiliary independent uniforms disappear isometrically. -/
theorem diffusion_compression (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (t : ℝ) :
    ObservableTransition.compression (diffusionEvaluation (𝕜 := 𝕜) (F := F) P V hV 0)
      (diffusionEvaluation P V hV t) = CanonicalSemigroup.op P V hV t := by
  rw [diffusionEvaluation_eq_lift, diffusionEvaluation_eq_lift]
  exact compression_isometricLift _ _ _

/-- The concrete finite-step MALA transition on its canonical random source. -/
def malaOp (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (r : ℝ) (hr : 0 < r) (n : ℕ) :
    Lp F 2 (ULA.gibbsMeasure V) →L[𝕜] Lp F 2 (ULA.gibbsMeasure V) :=
  ObservableTransition.compression (diffusionEvaluation P V hV 0)
    (malaEvaluation P V hV r hr n)

/-- Actual MALA transitions converge strongly to the actual Langevin operator. -/
theorem malaOp_variable_tendsto [NormedSpace ℝ F]
    {I : Type*} {l : Filter I} [l.IsCountablyGenerated]
    (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V)
    (step : I → ℝ) (count : I → ℕ) (hstep : ∀ i, 0 < step i)
    (hmesh : Tendsto step l (𝓝 0)) (T : ℝ) (hT : 0 ≤ T)
    (hbound : ∀ i, (count i : ℝ) * step i ≤ T)
    (t : ℝ) (htime : Tendsto (fun i ↦ (count i : ℝ) * step i) l (𝓝 t))
    (f : Lp F 2 (ULA.gibbsMeasure V)) :
    Tendsto (fun i ↦ malaOp (𝕜 := 𝕜) P V hV (step i) (hstep i) (count i) f) l
      (𝓝 (CanonicalSemigroup.op (𝕜 := 𝕜) P V hV t f)) := by
  rw [← diffusion_compression (𝕜 := 𝕜) (F := F) P V hV t]
  exact (diffusionEvaluation (𝕜 := 𝕜) (F := F) P V hV 0).toContinuousLinearMap.adjoint.continuous.tendsto
    (diffusionEvaluation (𝕜 := 𝕜) P V hV t f) |>.comp
      (malaEvaluation_variable_tendsto (𝕜 := 𝕜) P V hV step count hstep hmesh T hT hbound t htime f)

end WassersteinMixing.RandomMALA.Canonical
