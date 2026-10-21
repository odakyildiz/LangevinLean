import IPLA.Model
import UnadjustedLangevin.Gibbs
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Disintegration

set_option linter.style.header false

/-! # Marginal-density foundations from joint strong convexity

For the original joint potential `U(θ,x)`, this module proves that every latent
partition is finite and positive, the parameter marginal is continuous, its tails
vanish, and therefore a marginal maximizer exists. These conclusions require only
joint differentiability and strong convexity. No marginal regularity, existence
assumption, Hessian, or second derivative is supplied.

Strong log-concavity of the marginal and the dimension-sharp concentration bound
are separate mathematical statements; this file does not assume or claim them.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter
open scoped ENNReal Topology
namespace IPLA

@[simp] theorem pair_parameter {dθ dx : ℕ} (θ : EuclideanSpace ℝ (Fin dθ))
    (x : EuclideanSpace ℝ (Fin dx)) (j : Fin dθ) :
    pair θ x (Sum.inl j) = θ j := by simp [pair]

@[simp] theorem pair_particle {dθ dx : ℕ} (θ : EuclideanSpace ℝ (Fin dθ))
    (x : EuclideanSpace ℝ (Fin dx)) (j : Fin dx) :
    pair θ x (Sum.inr j) = x j := by simp [pair]

/-- The pair coordinates preserve the orthogonal decomposition into parameter
and latent variables. -/
theorem norm_pair_sq {dθ dx : ℕ} (θ : EuclideanSpace ℝ (Fin dθ)) (x : EuclideanSpace ℝ (Fin dx)) :
    ‖pair θ x‖ ^ 2 = ‖θ‖ ^ 2 + ‖x‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type, pair_parameter, pair_particle]

/-- Joint continuity of the parameter/latent pairing. -/
theorem continuous_pair {dθ dx : ℕ} :
    Continuous (fun p : EuclideanSpace ℝ (Fin dθ) × EuclideanSpace ℝ (Fin dx) ↦
      pair p.1 p.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro j
  cases j <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop

/-- A Gaussian domination uniform in both the parameter and latent variable. -/
theorem marginal_weight_gaussian_bound {dθ dx : ℕ} (U : Joint dθ dx → ℝ)
    (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) (θ : EuclideanSpace ℝ (Fin dθ))
    (x : EuclideanSpace ℝ (Fin dx)) :
    Real.exp (-U (pair θ x)) ≤
      Real.exp (‖gradient U 0‖ ^ 2 / m - U 0) *
        Real.exp (-(m / 4) * ‖θ‖ ^ 2) * Real.exp (-(m / 4) * ‖x‖ ^ 2) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hb := ULA.strongConvex_quadratic_lower_bound U m hm hdiff hsc (pair θ x)
  rw [norm_pair_sq] at hb
  linarith

/-- An integrable bound for every parameter slice, with no local parameter
restriction. -/
theorem marginal_weight_uniform_bound {dθ dx : ℕ} (U : Joint dθ dx → ℝ)
    (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) (θ : EuclideanSpace ℝ (Fin dθ))
    (x : EuclideanSpace ℝ (Fin dx)) :
    ‖Real.exp (-U (pair θ x))‖ ≤
      Real.exp (‖gradient U 0‖ ^ 2 / m - U 0) * Real.exp (-(m / 4) * ‖x‖ ^ 2) := by
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply (marginal_weight_gaussian_bound U m hm hdiff hsc θ x).trans
  have he : Real.exp (-(m / 4) * ‖θ‖ ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg ‖θ‖]
  calc
    _ ≤ (Real.exp (‖gradient U 0‖ ^ 2 / m - U 0) * 1) *
        Real.exp (-(m / 4) * ‖x‖ ^ 2) := by gcongr
    _ = _ := by ring

/-- Every latent partition is integrable from joint assumptions alone. -/
theorem integrable_marginal_weight {dθ dx : ℕ} (U : Joint dθ dx → ℝ)
    (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) (θ : EuclideanSpace ℝ (Fin dθ)) :
    Integrable (fun x ↦ Real.exp (-U (pair θ x))) volume := by
  have hi := (ULA.integrable_exp_neg_mul_norm_sq
    (H := EuclideanSpace ℝ (Fin dx)) (m / 4) (by positivity)).const_mul
    (Real.exp (‖gradient U 0‖ ^ 2 / m - U 0))
  apply hi.mono'
  · exact (Real.continuous_exp.comp
      (hdiff.continuous.comp
        (continuous_pair.comp (continuous_const.prodMk continuous_id))).neg).aestronglyMeasurable
  · exact ae_of_all _ (marginal_weight_uniform_bound U m hm hdiff hsc θ)

/-- The finite extended integral agrees with the ordinary real marginal. -/
theorem marginalDensity_eq_ofReal_integral {dθ dx : ℕ} (U : Joint dθ dx → ℝ)
    (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) (θ : EuclideanSpace ℝ (Fin dθ)) :
    marginalDensity U θ = ENNReal.ofReal (∫ x, Real.exp (-U (pair θ x)) ∂volume) := by
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrable_marginal_weight U m hm hdiff hsc θ)
    (ae_of_all _ fun _ ↦ Real.exp_nonneg _)).symm

/-- The parameter marginal is finite, excluding infinite-likelihood maximizers. -/
theorem marginalDensity_ne_top {dθ dx : ℕ} (U : Joint dθ dx → ℝ)
    (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) (θ : EuclideanSpace ℝ (Fin dθ)) :
    marginalDensity U θ ≠ ⊤ := by
  rw [marginalDensity_eq_ofReal_integral U m hm hdiff hsc θ]
  exact ENNReal.ofReal_ne_top

/-- Every parameter has strictly positive marginal density. -/
theorem marginalDensity_pos {dθ dx : ℕ} (U : Joint dθ dx → ℝ)
    (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) (θ : EuclideanSpace ℝ (Fin dθ)) :
    0 < marginalDensity U θ := by
  rw [marginalDensity_eq_ofReal_integral U m hm hdiff hsc θ]
  exact ENNReal.ofReal_pos.mpr (integral_exp_pos
    (integrable_marginal_weight U m hm hdiff hsc θ))

/-- Continuity of the real-valued marginal follows by dominated convergence. -/
theorem continuous_marginal_integral {dθ dx : ℕ} (U : Joint dθ dx → ℝ)
    (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) :
    Continuous (fun θ : EuclideanSpace ℝ (Fin dθ) ↦
      ∫ x, Real.exp (-U (pair θ x)) ∂volume) := by
  apply continuous_of_dominated
    (bound := fun x : EuclideanSpace ℝ (Fin dx) ↦
      Real.exp (‖gradient U 0‖ ^ 2 / m - U 0) * Real.exp (-(m / 4) * ‖x‖ ^ 2))
  · exact fun θ ↦ (integrable_marginal_weight U m hm hdiff hsc θ).aestronglyMeasurable
  · exact fun θ ↦ ae_of_all _ (marginal_weight_uniform_bound U m hm hdiff hsc θ)
  · exact (ULA.integrable_exp_neg_mul_norm_sq
      (H := EuclideanSpace ℝ (Fin dx)) (m / 4) (by positivity)).const_mul _
  · apply ae_of_all
    intro x
    exact Real.continuous_exp.comp
      (hdiff.continuous.comp (continuous_pair.comp (continuous_id.prodMk continuous_const))).neg

/-- The actual extended-valued marginal is continuous as well. -/
theorem continuous_marginalDensity {dθ dx : ℕ} (U : Joint dθ dx → ℝ)
    (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) : Continuous (marginalDensity U) := by
  have heq : marginalDensity U = fun θ ↦
      ENNReal.ofReal (∫ x, Real.exp (-U (pair θ x)) ∂volume) := by
    funext θ
    exact marginalDensity_eq_ofReal_integral U m hm hdiff hsc θ
  rw [heq]
  exact ENNReal.continuous_ofReal.comp (continuous_marginal_integral U m hm hdiff hsc)

/-- Joint strong convexity gives a Gaussian parameter tail after integrating
out the latent variable. The constant is finite and independent of `θ`. -/
theorem marginal_integral_gaussian_bound {dθ dx : ℕ} (U : Joint dθ dx → ℝ)
    (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) (θ : EuclideanSpace ℝ (Fin dθ)) :
    (∫ x, Real.exp (-U (pair θ x)) ∂volume) ≤
      (Real.exp (‖gradient U 0‖ ^ 2 / m - U 0) *
        (∫ x : EuclideanSpace ℝ (Fin dx), Real.exp (-(m / 4) * ‖x‖ ^ 2) ∂volume)) *
          Real.exp (-(m / 4) * ‖θ‖ ^ 2) := by
  have hi := (ULA.integrable_exp_neg_mul_norm_sq
    (H := EuclideanSpace ℝ (Fin dx)) (m / 4) (by positivity)).const_mul
    (Real.exp (‖gradient U 0‖ ^ 2 / m - U 0) * Real.exp (-(m / 4) * ‖θ‖ ^ 2))
  have hb := integral_mono (integrable_marginal_weight U m hm hdiff hsc θ)
    hi (marginal_weight_gaussian_bound U m hm hdiff hsc θ)
  rw [integral_const_mul] at hb
  convert hb using 1
  ring

/-- The parameter marginal vanishes at infinity. -/
theorem tendsto_marginal_integral_cocompact {dθ dx : ℕ} (U : Joint dθ dx → ℝ)
    (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) :
    Tendsto (fun θ : EuclideanSpace ℝ (Fin dθ) ↦
      ∫ x, Real.exp (-U (pair θ x)) ∂volume) (cocompact _) (𝓝 0) := by
  have hn : Tendsto (fun θ : EuclideanSpace ℝ (Fin dθ) ↦ ‖θ‖ ^ 2)
      (cocompact _) atTop := by
    simpa only [pow_two] using
      (tendsto_norm_cocompact_atTop (E := EuclideanSpace ℝ (Fin dθ))).atTop_mul_atTop₀
        tendsto_norm_cocompact_atTop
  have he : Tendsto (fun θ : EuclideanSpace ℝ (Fin dθ) ↦
      Real.exp (-(m / 4) * ‖θ‖ ^ 2)) (cocompact _) (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (by linarith)).mpr hn)
  apply squeeze_zero (fun θ ↦ integral_nonneg (fun _ ↦ Real.exp_nonneg _))
    (marginal_integral_gaussian_bound U m hm hdiff hsc)
  simpa only [mul_zero] using he.const_mul
    (Real.exp (‖gradient U 0‖ ^ 2 / m - U 0) *
      (∫ x : EuclideanSpace ℝ (Fin dx), Real.exp (-(m / 4) * ‖x‖ ^ 2) ∂volume))

/-- Existence of the actual marginal maximizer is derived from the original
joint assumptions. No maximizer or compactness premise is introduced. -/
theorem exists_marginalMaximizer {dθ dx : ℕ} (U : Joint dθ dx → ℝ)
    (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) :
    ∃ θ : EuclideanSpace ℝ (Fin dθ), IsMarginalMaximizer U θ := by
  have hpos : 0 < ∫ x, Real.exp (-U (pair (0 : EuclideanSpace ℝ (Fin dθ)) x)) ∂volume :=
    integral_exp_pos (integrable_marginal_weight U m hm hdiff hsc 0)
  have he := (tendsto_marginal_integral_cocompact U m hm hdiff hsc).eventually_lt_const hpos
  obtain ⟨θ, hθ⟩ := (continuous_marginal_integral U m hm hdiff hsc).exists_forall_ge' 0
    (he.mono fun _ h ↦ h.le)
  refine ⟨θ, ?_⟩
  intro θ'
  rw [marginalDensity_eq_ofReal_integral U m hm hdiff hsc θ',
    marginalDensity_eq_ofReal_integral U m hm hdiff hsc θ]
  exact ENNReal.ofReal_le_ofReal (hθ θ')

/-- Tonelli factorization of identical nonnegative weights over finitely many
independent latent coordinates. This extended-integral statement also records
divergence correctly; no integrability premise is hidden. -/
theorem lintegral_fin_prod_eq_pow {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [SigmaFinite μ] (f : E → ℝ≥0∞) (hf : Measurable f) (n : ℕ) :
    (∫⁻ x : Fin n → E, ∏ i, f (x i) ∂Measure.pi (fun _ ↦ μ)) =
      (∫⁻ x, f x ∂μ) ^ n := by
  induction n with
  | zero => simp [Measure.pi_empty_univ]
  | succ n ih =>
    have hm : Measurable (fun x : Fin (n + 1) → E ↦ ∏ i, f (x i)) := by fun_prop
    have hpres := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ μ) 0).symm
    rw [← hpres.lintegral_comp hm]
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.prod_univ_succ, Fin.insertNth_zero, Fin.zero_succAbove,
      Equiv.coe_fn_mk, Fin.cons_succ, Fin.cons_zero, cast_eq]
    rw [lintegral_prod_mul (f := f)
      (g := fun x : Fin n → E ↦ ∏ i, f (x i)) hf.aemeasurable
      (Measurable.aemeasurable (by fun_prop)), ih, pow_succ]
    exact mul_comm _ _

/-- Change of variables for a nonnegative weight under scalar dilation. -/
theorem lintegral_comp_smul_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → ℝ≥0∞) (hf : Measurable f) (r : ℝ) (hr : r ≠ 0) :
    (∫⁻ x, f (r • x) ∂μ) =
      ENNReal.ofReal |(r ^ Module.finrank ℝ E)⁻¹| * ∫⁻ x, f x ∂μ := by
  rw [← lintegral_map hf (show Measurable (fun x : E ↦ r • x) by fun_prop),
    Measure.map_addHaar_smul μ hr, lintegral_smul_measure]
  rfl

/-- Integrating the actual scaled particle potential at a fixed parameter
gives the `N`th power of the original marginal, times the explicit scalar
Jacobian. This is the factor that cancels in the normalized parameter law. -/
theorem scaled_particle_partition {N dθ dx : ℕ} (hN : 0 < N)
    (U : Joint dθ dx → ℝ) (hdiff : Differentiable ℝ U) (θ : EuclideanSpace ℝ (Fin dθ)) :
    (∫⁻ x : Fin N → EuclideanSpace ℝ (Fin dx),
      ∏ i, ENNReal.ofReal (Real.exp (-U (pair θ (Real.sqrt N • x i)))) ∂volume) =
      (ENNReal.ofReal |((Real.sqrt N) ^ dx)⁻¹| * marginalDensity U θ) ^ N := by
  have hf : Measurable (fun x : EuclideanSpace ℝ (Fin dx) ↦
      ENNReal.ofReal (Real.exp (-U (pair θ x)))) := by
    exact (Real.continuous_exp.comp
      (hdiff.continuous.comp
        (continuous_pair.comp
          (continuous_const.prodMk continuous_id))).neg).measurable.ennreal_ofReal
  have hs : Measurable (fun x : EuclideanSpace ℝ (Fin dx) ↦
      ENNReal.ofReal (Real.exp (-U (pair θ (Real.sqrt N • x))))) := hf.comp (by fun_prop)
  rw [volume_pi, lintegral_fin_prod_eq_pow _ _ hs]
  rw [lintegral_comp_smul_eq volume _ hf _
    (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hN))]
  simp only [finrank_euclideanSpace, Fintype.card_fin, marginalDensity]

/-- Assemble the scaled state from its parameter and particle blocks. -/
def configuration {N dθ dx : ℕ} (θ : EuclideanSpace ℝ (Fin dθ))
    (x : Fin N → EuclideanSpace ℝ (Fin dx)) : State N dθ dx :=
  WithLp.toLp 2 (Sum.elim θ (fun p ↦ x p.1 p.2))

@[simp] theorem configuration_parameter {N dθ dx : ℕ} (θ : EuclideanSpace ℝ (Fin dθ))
    (x : Fin N → EuclideanSpace ℝ (Fin dx)) (j : Fin dθ) :
    configuration θ x (Sum.inl j) = θ j := rfl

@[simp] theorem configuration_particle {N dθ dx : ℕ} (θ : EuclideanSpace ℝ (Fin dθ))
    (x : Fin N → EuclideanSpace ℝ (Fin dx)) (i : Fin N) (j : Fin dx) :
    configuration θ x (Sum.inr (i, j)) = x i j := rfl

/-- Grouping coordinates is a constructed continuous linear equivalence. -/
def configurationCLE {N dθ dx : ℕ} :
    (EuclideanSpace ℝ (Fin dθ) × (Fin N → EuclideanSpace ℝ (Fin dx))) ≃L[ℝ] State N dθ dx :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p ↦ configuration p.1 p.2
      invFun := fun z ↦ (parameterCLM z, fun i ↦ block z i)
      left_inv := by
        intro p
        apply Prod.ext
        · ext j
          rfl
        · funext i
          ext j
          rfl
      right_inv := by
        intro z
        ext j
        cases j <;> rfl
      map_add' := by
        intro p q
        ext j
        cases j <;> rfl
      map_smul' := by
        intro a p
        ext j
        cases j <;> rfl }

@[simp] theorem configurationCLE_apply {N dθ dx : ℕ}
    (p : EuclideanSpace ℝ (Fin dθ) × (Fin N → EuclideanSpace ℝ (Fin dx))) :
    configurationCLE p = configuration p.1 p.2 := rfl

@[simp] theorem parameter_configuration {N dθ dx : ℕ} (θ : EuclideanSpace ℝ (Fin dθ))
    (x : Fin N → EuclideanSpace ℝ (Fin dx)) : parameterCLM (configuration θ x) = θ := by
  ext j
  rfl

@[simp] theorem joint_configuration {N dθ dx : ℕ} (θ : EuclideanSpace ℝ (Fin dθ))
    (x : Fin N → EuclideanSpace ℝ (Fin dx)) (i : Fin N) :
    joint i (configuration θ x) = pair θ (Real.sqrt N • x i) := by
  ext j
  cases j <;> simp [joint, pair, configuration]

/-- In grouped coordinates the actual Gibbs weight factors over particles. -/
theorem weight_configuration {N dθ dx : ℕ} (U : Joint dθ dx → ℝ)
    (θ : EuclideanSpace ℝ (Fin dθ)) (x : Fin N → EuclideanSpace ℝ (Fin dx)) :
    ULA.gibbsWeight (@potential N dθ dx U) (configuration θ x) =
      ∏ i, ENNReal.ofReal (Real.exp (-U (pair θ (Real.sqrt N • x i)))) := by
  unfold ULA.gibbsWeight potential
  simp only [joint_configuration, ← Finset.sum_neg_distrib, Real.exp_sum]
  exact ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ Real.exp_nonneg _)

/-- A density commutes with a measurable coordinate equivalence. -/
theorem map_withDensity_comp_equiv {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (e : A ≃ᵐ B) (w : B → ℝ≥0∞) (hw : Measurable w) :
    (μ.withDensity (w ∘ e)).map e = (μ.map e).withDensity w := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, ← lintegral_indicator (e.measurable hs),
    ← lintegral_indicator hs, lintegral_map (hw.indicator hs) e.measurable]
  apply lintegral_congr
  intro a
  rfl

/-- Tonelli's theorem identifies the first-coordinate density of a weighted
product measure. -/
theorem map_fst_withDensity {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite ν]
    (w : A × B → ℝ≥0∞) (hw : Measurable w) :
    ((μ.prod ν).withDensity w).map Prod.fst =
      μ.withDensity (fun θ ↦ ∫⁻ x, w (θ, x) ∂ν) := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs, withDensity_apply _ (measurable_fst hs),
    withDensity_apply _ hs, ← lintegral_indicator (measurable_fst hs),
    ← lintegral_indicator hs,
    lintegral_prod _ (hw.indicator (measurable_fst hs)).aemeasurable]
  apply lintegral_congr
  intro θ
  by_cases hθ : θ ∈ s <;> simp [hθ]

/-- Normalization is unchanged by multiplication by any finite positive
constant. This is why grouping coordinates and the particle Jacobian cancel. -/
theorem normalize_smul_eq {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hctop : c ≠ ⊤) :
    ((c • μ) Set.univ)⁻¹ • (c • μ) = (μ Set.univ)⁻¹ • μ := by
  rw [Measure.smul_apply, smul_eq_mul,
    ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop), smul_smul]
  congr 1
  rw [mul_right_comm, ENNReal.inv_mul_cancel hc0 hctop, one_mul]

/-- The finite-dimensional coordinate grouping changes volume by a constructed
finite positive constant. Its value is irrelevant after normalization. -/
theorem configuration_map_volume {N dθ dx : ℕ} :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      (volume : Measure (EuclideanSpace ℝ (Fin dθ) ×
        (Fin N → EuclideanSpace ℝ (Fin dx)))).map configurationCLE =
          c • (volume : Measure (State N dθ dx)) := by
  let μ := (volume : Measure (EuclideanSpace ℝ (Fin dθ) ×
    (Fin N → EuclideanSpace ℝ (Fin dx)))).map (@configurationCLE N dθ dx)
  have : (volume : Measure (EuclideanSpace ℝ (Fin dθ) ×
      (Fin N → EuclideanSpace ℝ (Fin dx)))).IsAddHaarMeasure := by
    apply Measure.prod.instIsAddHaarMeasure
  have : μ.IsAddHaarMeasure := configurationCLE.isAddHaarMeasure_map volume
  refine ⟨Measure.addHaarScalarFactor μ volume, ?_, ENNReal.coe_ne_top, ?_⟩
  · simpa only [ne_eq, ENNReal.coe_eq_zero] using
      (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume).ne'
  · exact Measure.isAddLeftInvariant_eq_smul μ volume

/-- The parameter law with density proportional to the `N`th power of the
original latent marginal. This names the statistical target without assuming
anything about its concentration. -/
def marginalTarget {dθ dx : ℕ} (N : ℕ) (U : Joint dθ dx → ℝ) :
    Measure (EuclideanSpace ℝ (Fin dθ)) :=
  (∫⁻ θ, marginalDensity U θ ^ N ∂volume)⁻¹ •
    volume.withDensity (fun θ ↦ marginalDensity U θ ^ N)

/-- The actual lifted Gibbs target has exactly the claimed parameter
marginal, with density proportional to `(∫ exp(-U(θ,x)) dx)^N`.

All coordinate changes, product integrals, and particle-scaling factors are
proved above and cancel upon normalization. The only potential assumptions
are the original joint differentiability and strong convexity. -/
theorem gibbsTarget_parameter_marginal {N dθ dx : ℕ} (hN : 0 < N)
    (U : Joint dθ dx → ℝ) (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) :
    (@gibbsTarget N dθ dx U).map parameterCLM = marginalTarget N U := by
  let A := EuclideanSpace ℝ (Fin dθ)
  let B := Fin N → EuclideanSpace ℝ (Fin dx)
  let w := ULA.gibbsWeight (@potential N dθ dx U)
  let μ := (volume : Measure (State N dθ dx)).withDensity w
  let ρ := (volume : Measure A).withDensity (fun θ ↦ marginalDensity U θ ^ N)
  let D : ℝ≥0∞ := ENNReal.ofReal |((Real.sqrt N) ^ dx)⁻¹|
  have hw : Measurable w :=
    (Real.continuous_exp.comp
      (potential_differentiable hdiff).continuous.neg).measurable.ennreal_ofReal
  have hρ : Measurable (fun θ ↦ marginalDensity U θ ^ N) :=
    (continuous_marginalDensity U m hm hdiff hsc).measurable.pow_const N
  have he : Measurable (@configurationCLE N dθ dx) := configurationCLE.continuous.measurable
  have hp : Measurable (@parameterCLM N dθ dx) := parameterCLM.continuous.measurable
  obtain ⟨c, hc0, hctop, hc⟩ := @configuration_map_volume N dθ dx
  have hew :
      ((volume : Measure (A × B)).withDensity (w ∘ configurationCLE)).map
        (@configurationCLE N dθ dx) = c • μ := by
    have hh := map_withDensity_comp_equiv (volume : Measure (A × B))
      (@configurationCLE N dθ dx).toHomeomorph.toMeasurableEquiv w hw
    change ((volume : Measure (A × B)).withDensity (w ∘ configurationCLE)).map
      (@configurationCLE N dθ dx) =
        ((volume : Measure (A × B)).map (@configurationCLE N dθ dx)).withDensity w at hh
    rw [hc, withDensity_smul_measure] at hh
    exact hh
  have hcomp : (@parameterCLM N dθ dx) ∘ configurationCLE =
      (Prod.fst : A × B → A) := by
    funext p
    exact parameter_configuration p.1 p.2
  have hfiber (θ : A) :
      (∫⁻ x : B, (w ∘ configurationCLE) (θ, x) ∂volume) =
        D ^ N * marginalDensity U θ ^ N := by
    simp only [Function.comp_apply, configurationCLE_apply, w, weight_configuration]
    rw [scaled_particle_partition hN U hdiff θ, mul_pow]
  have hproj : c • μ.map (@parameterCLM N dθ dx) = D ^ N • ρ := by
    calc
      _ = (c • μ).map (@parameterCLM N dθ dx) :=
        (Measure.map_smul c hp.aemeasurable).symm
      _ = (((volume : Measure (A × B)).withDensity
          (w ∘ configurationCLE)).map configurationCLE).map (@parameterCLM N dθ dx) := by rw [hew]
      _ = ((volume : Measure (A × B)).withDensity
          (w ∘ configurationCLE)).map Prod.fst := by rw [Measure.map_map hp he, hcomp]
      _ = (volume : Measure A).withDensity (fun θ ↦
          ∫⁻ x : B, (w ∘ configurationCLE) (θ, x) ∂volume) :=
        map_fst_withDensity _ _ _ (hw.comp he)
      _ = (volume : Measure A).withDensity (fun θ ↦ D ^ N * marginalDensity U θ ^ N) := by
        congr 1
        funext θ
        exact hfiber θ
      _ = D ^ N • ρ := withDensity_smul (D ^ N) hρ
  have hD0 : D ≠ 0 := by
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    exact abs_pos.mpr (inv_ne_zero (pow_ne_zero _
      (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hN))))
  have hDtop : D ≠ ⊤ := ENNReal.ofReal_ne_top
  have hnorm := congrArg (fun ν : Measure A ↦ (ν Set.univ)⁻¹ • ν) hproj
  rw [normalize_smul_eq _ c hc0 hctop,
    normalize_smul_eq _ (D ^ N) (ENNReal.pow_ne_zero hD0 _) (ENNReal.pow_ne_top hDtop)] at hnorm
  have hμmass : μ Set.univ = ULA.gibbsPartition (@potential N dθ dx U) := by
    dsimp only [μ]
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    rfl
  have hρmass : ρ Set.univ = ∫⁻ θ, marginalDensity U θ ^ N ∂volume := by
    dsimp only [ρ]
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  rw [Measure.map_apply hp MeasurableSet.univ, Set.preimage_univ, hμmass, hρmass] at hnorm
  change ((ULA.gibbsPartition (@potential N dθ dx U))⁻¹ • μ).map parameterCLM = _
  rw [Measure.map_smul _ hp.aemeasurable]
  exact hnorm

/-- The marginal power density normalizes to a probability measure as a
consequence of its proved equality with the actual Gibbs projection. -/
theorem marginalTarget_isProbability {N dθ dx : ℕ} (hN : 0 < N)
    (U : Joint dθ dx → ℝ) (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) : IsProbabilityMeasure (marginalTarget N U) := by
  have : IsProbabilityMeasure (@gibbsTarget N dθ dx U) :=
    ULA.isProbabilityMeasure_gibbsMeasure (potential U) ((N : ℝ) * m)
      (mul_pos (by exact_mod_cast hN) hm)
      (potential_differentiable hdiff) (potential_strongConvex hsc)
  constructor
  rw [← gibbsTarget_parameter_marginal hN U m hm hdiff hsc,
    Measure.map_apply parameterCLM.continuous.measurable MeasurableSet.univ, Set.preimage_univ]
  exact measure_univ

/-- The normalizer of the powered marginal density is strictly positive. -/
theorem marginalPartition_pos {N dθ dx : ℕ}
    (U : Joint dθ dx → ℝ) (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) :
    0 < ∫⁻ θ, marginalDensity U θ ^ N ∂volume := by
  apply (lintegral_pos_iff_support (μ := (volume : Measure (EuclideanSpace ℝ (Fin dθ))))
    (f := fun θ ↦ marginalDensity U θ ^ N)
    ((continuous_marginalDensity U m hm hdiff hsc).measurable.pow_const N)).mpr
  have hs : Function.support (fun θ ↦ marginalDensity U θ ^ N) = Set.univ := by
    ext θ
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ENNReal.pow_ne_zero (ne_of_gt (marginalDensity_pos U m hm hdiff hsc θ)) N
  rw [hs]
  exact Measure.measure_univ_pos.mpr (NeZero.ne _)

/-- The powered marginal partition is finite. Its proof uses the previously
established probability identity, so divergence cannot disappear in a real
conversion or an infinite normalizing constant. -/
theorem marginalPartition_ne_top {N dθ dx : ℕ} (hN : 0 < N)
    (U : Joint dθ dx → ℝ) (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) :
    (∫⁻ θ, marginalDensity U θ ^ N ∂volume) ≠ ⊤ := by
  have := marginalTarget_isProbability hN U m hm hdiff hsc
  have hmass : marginalTarget N U Set.univ = 1 := measure_univ
  intro hZ
  have hzero : marginalTarget N U = 0 := by simp [marginalTarget, hZ]
  rw [hzero] at hmass
  simp at hmass

/-- The parameter marginal has finite second moment, without a separate
marginal moment or concentration assumption. -/
theorem marginalTarget_memLp {N dθ dx : ℕ} (hN : 0 < N)
    (U : Joint dθ dx → ℝ) (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) :
    MemLp (fun θ : EuclideanSpace ℝ (Fin dθ) ↦ θ) 2 (marginalTarget N U) := by
  rw [← gibbsTarget_parameter_marginal hN U m hm hdiff hsc]
  apply (memLp_map_measure_iff (by fun_prop)
    parameterCLM.continuous.measurable.aemeasurable).mpr
  exact (ULA.memLp_id_gibbsMeasure (@potential N dθ dx U) ((N : ℝ) * m)
    (mul_pos (by exact_mod_cast hN) hm)
    (potential_differentiable hdiff) (potential_strongConvex hsc)).continuousLinearMap_comp
      parameterCLM

end IPLA
