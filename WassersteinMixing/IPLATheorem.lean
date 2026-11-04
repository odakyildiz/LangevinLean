import WassersteinMixing.IPLA
import IPLA.Degenerate

set_option linter.style.header false

/-! # Linear-step IPLA bounds in the original IPLA statement form

The statements below use exactly the binders of Project 03's `IPLA.theorem1`,
with two changes: the joint potential is twice continuously differentiable and
the step satisfies `γ * L ≤ 1`. Their right-hand sides are written out in full.
The ordering `m ≤ L` is derived for a nonzero joint space; zero dimensions are
included separately, as in Project 03.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace WassersteinMixing

/-- The linear-step discretization term written without auxiliary definitions. -/
theorem iplaLinearBias_eq_explicit (m L γ D : ℝ) (hm : 0 < m) (hL : 0 ≤ L) (hD : 0 ≤ D) :
    iplaLinearBias m L γ D = 6 * (L / Real.sqrt m) * Real.sqrt D * γ := by
  have hs := ipla_linear_bias_scale m L γ D hm hL hD
  have hsm : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr hm).ne'
  calc iplaLinearBias m L γ D = (Real.sqrt m * iplaLinearBias m L γ D) / Real.sqrt m := by
        field_simp
    _ = 6 * (L / Real.sqrt m) * Real.sqrt D * γ := by
        rw [hs]
        field_simp

/-- The new discretization term is Project 03's term times `(40/11) √(mγ)`. -/
theorem ipla_linear_step_term_eq_project03_mul (m L γ D : ℝ) (hm : 0 < m) (hγ : 0 ≤ γ) :
    6 * (L / Real.sqrt m) * Real.sqrt D * γ =
      (40 / 11 : ℝ) * Real.sqrt (m * γ) *
        ((33 / 20 : ℝ) * (L / m) * Real.sqrt D * Real.sqrt γ) := by
  have hsm : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr hm).ne'
  rw [Real.sqrt_mul hm.le]
  field_simp
  rw [Real.sq_sqrt hm.le, Real.sq_sqrt hγ]
  ring

/-- The new discretization term is at most Project 03's when `m * γ ≤ 121 / 1600`. -/
theorem ipla_linear_step_term_le_project03 (m L γ D : ℝ) (hm : 0 < m) (hL : 0 ≤ L)
    (hγ : 0 ≤ γ) (hD : 0 ≤ D) (hsmall : m * γ ≤ 121 / 1600) :
    6 * (L / Real.sqrt m) * Real.sqrt D * γ ≤
      (33 / 20 : ℝ) * (L / m) * Real.sqrt D * Real.sqrt γ := by
  have h := ipla_linear_bias_le_project03 m L γ D hm hL hγ hD hsmall
  rw [iplaLinearBias_eq_explicit m L γ D hm hL hD] at h
  exact h

/-- On a nonzero joint space, strong convexity and a Lipschitz gradient force `m ≤ L`. -/
theorem ipla_curvature_le_smoothness {dθ dx : ℕ} [Nonempty (Fin dθ ⊕ Fin dx)]
    {U : IPLA.Joint dθ dx → ℝ} {m : ℝ} {L : ℝ≥0}
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U)
    (hLip : LipschitzWith L (gradient U)) : m ≤ L := by
  obtain ⟨i⟩ := ‹Nonempty (Fin dθ ⊕ Fin dx)›
  let v : IPLA.Joint dθ dx := EuclideanSpace.single i 1
  have hv : ‖v‖ = 1 := by simp [v]
  have hmono := ULA.strong_gradient_monotone hdiff hsc v 0
  have hcs := real_inner_le_norm (gradient U v - gradient U 0) (v - 0)
  have hlip := hLip.dist_le_mul v 0
  rw [dist_eq_norm, dist_eq_norm] at hlip
  simp only [sub_zero, hv] at hmono hcs hlip
  nlinarith

/-- Two probability measures on a one-point space coincide. -/
theorem probability_eq_of_subsingleton {α : Type*} [MeasurableSpace α] [Subsingleton α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : μ = ν := by
  ext s _
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  · have hs : s = univ := Set.eq_univ_of_forall (fun z ↦ Subsingleton.elim x z ▸ hx)
    simp [hs]

/-- Every square-integrable stationary law of the Gaussian IPLA transition can
replace the constructed invariant law in an initialization distance. -/
theorem IPLASetting.wasserstein2Real_invariantLaw_le (A : IPLASetting)
    (μ stationary : Measure (IPLA.State A.N A.dθ A.dx))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure stationary]
    (hμ : MemLp (id : IPLA.State A.N A.dθ A.dx → IPLA.State A.N A.dθ A.dx) 2 μ)
    (hmoment : MemLp (id : IPLA.State A.N A.dθ A.dx → IPLA.State A.N A.dθ A.dx) 2 stationary)
    (hstationary : ULA.ulaLawStep (IPLA.potential A.U) (A.γ / A.N) stationary = stationary) :
    ULA.wasserstein2Real μ A.invariantLaw ≤ ULA.wasserstein2Real μ stationary := by
  let P := A.parameters
  let V := @IPLA.potential A.N A.dθ A.dx A.U
  have hV : PotentialAssumptions P V := A.potentialAssumptions
  let ν := A.invariantLaw
  let : IsProbabilityMeasure ν :=
    coordinateInvariantLaw_isProbability P (iplaCoordinates A.N A.dθ A.dx) V hV
  have hν : MemLp (id : IPLA.State A.N A.dθ A.dx → IPLA.State A.N A.dθ A.dx) 2 ν :=
    coordinateInvariantLaw_memLp P (iplaCoordinates A.N A.dθ A.dx) V hV
  have hνinv : ULA.ulaLawStep V P.step ν = ν :=
    coordinateInvariantLaw_invariant P (iplaCoordinates A.N A.dθ A.dx) V hV
  have hfinite := ULA.wasserstein2_ne_top_of_memLp stationary ν hmoment hν
  have hcontract := ula_iterate_wasserstein2Real_le P V hV stationary ν hfinite 1
  simp only [Function.iterate_one] at hcontract
  change ULA.wasserstein2Real (ULA.ulaLawStep V (A.γ / A.N) stationary)
    (ULA.ulaLawStep V (A.γ / A.N) ν) ≤ P.contraction ^ 1 * _ at hcontract
  rw [hstationary, pow_one] at hcontract
  rw [show ULA.ulaLawStep V (A.γ / A.N) ν = ν from hνinv] at hcontract
  have hzero : ULA.wasserstein2Real stationary ν = 0 := by
    have hlt := P.contraction_lt_one
    have hnonneg : 0 ≤ ULA.wasserstein2Real stationary ν := ENNReal.toReal_nonneg
    nlinarith
  have ht := wasserstein2Real_triangle μ stationary ν
    (ULA.wasserstein2_ne_top_of_memLp μ stationary hμ hmoment) hfinite
  rw [hzero, add_zero] at ht
  exact ht

/-- The Gaussian IPLA transition has a stationary law with finite second moment. -/
theorem ipla_stationary_law_exists
    (N dθ dx : ℕ) (hN : 0 < N)
    {Data : Type*} (U : Data → IPLA.Joint dθ dx → ℝ) (y : Data)
    (m γ : ℝ) (L : ℝ≥0)
    (hU : ContDiff ℝ 2 (U y)) (hsc : StrongConvexOn univ m (U y))
    (hLip : LipschitzWith L (gradient (U y)))
    (hm : 0 < m) (hγ : 0 < γ) (hγL : γ * L ≤ 1) :
    ∃ stationary : Measure (IPLA.State N dθ dx), IsProbabilityMeasure stationary ∧
      MemLp (id : IPLA.State N dθ dx → IPLA.State N dθ dx) 2 stationary ∧
      ULA.ulaLawStep (IPLA.potential (U y)) (γ / N) stationary = stationary := by
  classical
  by_cases hindex : Nonempty (Fin dθ ⊕ Fin dx)
  · have hmL : m ≤ L :=
      ipla_curvature_le_smoothness (hU.differentiable (by norm_num)) hsc hLip
    let A : IPLASetting :=
      { N := N, dθ := dθ, dx := dx, U := U y, m := m, L := L, γ := γ
        particles_pos := hN, curvature_pos := hm, curvature_le_smoothness := hmL
        step_pos := hγ, step_small := hγL, regularity := hU
        strongConvexity := hsc, gradientLipschitz := hLip }
    exact ⟨A.invariantLaw,
      coordinateInvariantLaw_isProbability A.parameters (iplaCoordinates N dθ dx)
        (IPLA.potential (U y)) A.potentialAssumptions,
      coordinateInvariantLaw_memLp A.parameters (iplaCoordinates N dθ dx)
        (IPLA.potential (U y)) A.potentialAssumptions,
      coordinateInvariantLaw_invariant A.parameters (iplaCoordinates N dθ dx)
        (IPLA.potential (U y)) A.potentialAssumptions⟩
  · have hθ : dθ = 0 := Nat.eq_zero_of_not_pos (fun hp ↦ hindex ⟨Sum.inl ⟨0, hp⟩⟩)
    have hx : dx = 0 := Nat.eq_zero_of_not_pos (fun hp ↦ hindex ⟨Sum.inr ⟨0, hp⟩⟩)
    subst dθ
    subst dx
    let δ : Measure (IPLA.State N 0 0) := Measure.dirac 0
    have : IsProbabilityMeasure (ULA.ulaLawStep (IPLA.potential (U y)) (γ / N) δ) := by
      unfold ULA.ulaLawStep
      infer_instance
    refine ⟨δ, inferInstance, ?_, probability_eq_of_subsingleton _ _⟩
    exact MemLp.of_bound measurable_id.aestronglyMeasurable 0
      (Filter.Eventually.of_forall fun z ↦ by simp [Subsingleton.elim z 0])

/-- Linear-step parameter error for the actual Gaussian IPLA recursion, with the
same initialization distance as Project 03. Every hypothesis is displayed; the
lifted invariant law, comparison and concentration are derived in the proof. -/
theorem ipla_linear_step_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N dθ dx : ℕ) (hN : 0 < N)
    {Data : Type*} (U : Data → IPLA.Joint dθ dx → ℝ) (y : Data)
    (m γ : ℝ) (L : ℝ≥0)
    (hU : ContDiff ℝ 2 (U y)) (hsc : StrongConvexOn univ m (U y))
    (hLip : LipschitzWith L (gradient (U y)))
    (hm : 0 < m)
    (hγ : 0 < γ) (hγL : γ * L ≤ 1)
    (θStar : EuclideanSpace ℝ (Fin dθ)) (hMaximizer : IPLA.IsMarginalMaximizer (U y) θStar)
    (initial : Lp (IPLA.State N dθ dx) 2 P) (noise : ℕ → Lp (IPLA.State N dθ dx) 2 P)
    (hGaussian : IPLA.GaussianInnovations P initial noise)
    (k : ℕ) :
    Real.sqrt (∫ z, ‖IPLA.parameterCLM z - θStar‖ ^ 2
      ∂(IPLA.laws P (U y) γ L (hU.differentiable (by norm_num)) hLip initial noise k)) ≤
      Real.sqrt (2 * (dθ : ℝ) / ((N : ℝ) * m)) +
        (1 - m * γ) ^ k * ULA.wasserstein2Real (P.map initial) (IPLA.gibbsTarget (U y)) +
        6 * ((L : ℝ) / Real.sqrt m) *
          Real.sqrt ((dx : ℝ) + (dθ : ℝ) / (N : ℝ)) * γ := by
  classical
  by_cases hindex : Nonempty (Fin dθ ⊕ Fin dx)
  · have hmL : m ≤ L :=
      ipla_curvature_le_smoothness (hU.differentiable (by norm_num)) hsc hLip
    have h := ipla_gaussian_parameter_error P N dθ dx hN (U y) m γ L hm hmL hγ hγL hU hsc
      hLip θStar hMaximizer initial noise hGaussian k
    rwa [iplaLinearBias_eq_explicit m L γ _ hm L.coe_nonneg
      (iplaEffectiveDimension_nonneg N dθ dx), iplaEffectiveDimension] at h
  · have hθ : dθ = 0 := Nat.eq_zero_of_not_pos (fun hp ↦ hindex ⟨Sum.inl ⟨0, hp⟩⟩)
    have hx : dx = 0 := Nat.eq_zero_of_not_pos (fun hp ↦ hindex ⟨Sum.inr ⟨0, hp⟩⟩)
    subst dθ
    subst dx
    have : IsProbabilityMeasure (@IPLA.gibbsTarget N 0 0 (U y)) :=
      IPLA.gibbsTarget_isProbability hN (U y) m hm (hU.differentiable (by norm_num)) hsc
    simp [IPLA.parameterRMS_zero_dimension, ULA.wasserstein2Real_eq_zero_of_subsingleton]

/-- The same linear-step bound with initialization measured from any
square-integrable stationary law of the Gaussian IPLA transition. -/
theorem ipla_linear_step_bound_stationary
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N dθ dx : ℕ) (hN : 0 < N)
    {Data : Type*} (U : Data → IPLA.Joint dθ dx → ℝ) (y : Data)
    (m γ : ℝ) (L : ℝ≥0)
    (hU : ContDiff ℝ 2 (U y)) (hsc : StrongConvexOn univ m (U y))
    (hLip : LipschitzWith L (gradient (U y)))
    (hm : 0 < m)
    (hγ : 0 < γ) (hγL : γ * L ≤ 1)
    (θStar : EuclideanSpace ℝ (Fin dθ)) (hMaximizer : IPLA.IsMarginalMaximizer (U y) θStar)
    (stationary : Measure (IPLA.State N dθ dx)) [IsProbabilityMeasure stationary]
    (hmoment : MemLp (id : IPLA.State N dθ dx → IPLA.State N dθ dx) 2 stationary)
    (hstationary : ULA.ulaLawStep (IPLA.potential (U y)) (γ / N) stationary = stationary)
    (initial : Lp (IPLA.State N dθ dx) 2 P) (noise : ℕ → Lp (IPLA.State N dθ dx) 2 P)
    (hGaussian : IPLA.GaussianInnovations P initial noise)
    (k : ℕ) :
    Real.sqrt (∫ z, ‖IPLA.parameterCLM z - θStar‖ ^ 2
      ∂(IPLA.laws P (U y) γ L (hU.differentiable (by norm_num)) hLip initial noise k)) ≤
      Real.sqrt (2 * (dθ : ℝ) / ((N : ℝ) * m)) +
        (1 - m * γ) ^ k * ULA.wasserstein2Real (P.map initial) stationary +
        6 * ((L : ℝ) / Real.sqrt m) *
          Real.sqrt ((dx : ℝ) + (dθ : ℝ) / (N : ℝ)) * γ := by
  classical
  by_cases hindex : Nonempty (Fin dθ ⊕ Fin dx)
  · have hmL : m ≤ L :=
      ipla_curvature_le_smoothness (hU.differentiable (by norm_num)) hsc hLip
    let A : IPLASetting :=
      { N := N, dθ := dθ, dx := dx, U := U y, m := m, L := L, γ := γ
        particles_pos := hN, curvature_pos := hm, curvature_le_smoothness := hmL
        step_pos := hγ, step_small := hγL, regularity := hU
        strongConvexity := hsc, gradientLipschitz := hLip }
    have hμ : MemLp (id : IPLA.State N dθ dx → IPLA.State N dθ dx) 2 (P.map initial) :=
      (memLp_map_measure_iff (by fun_prop)
        (Lp.aestronglyMeasurable initial).aemeasurable).mpr (Lp.memLp initial)
    have h := ipla_parameter_error A θStar hMaximizer (P.map initial) hμ k
    rw [A.law_eq_gaussian P initial noise hGaussian k] at h
    have hw := A.wasserstein2Real_invariantLaw_le (P.map initial) stationary hμ hmoment
      hstationary
    have hq : 0 ≤ (1 - m * γ) ^ k := by
      apply pow_nonneg
      have h1 : m * γ ≤ γ * L := by nlinarith
      linarith
    have hb : A.bias = 6 * ((L : ℝ) / Real.sqrt m) *
        Real.sqrt ((dx : ℝ) + (dθ : ℝ) / (N : ℝ)) * γ := by
      change iplaLinearBias m L γ (iplaEffectiveDimension N dθ dx) = _
      rw [iplaLinearBias_eq_explicit m L γ _ hm L.coe_nonneg
        (iplaEffectiveDimension_nonneg N dθ dx), iplaEffectiveDimension]
    change _ ≤ Real.sqrt (2 * (dθ : ℝ) / ((N : ℝ) * m)) +
      (1 - m * γ) ^ k * ULA.wasserstein2Real (P.map initial) A.invariantLaw + A.bias at h
    rw [hb] at h
    nlinarith [mul_le_mul_of_nonneg_left hw hq]
  · have hθ : dθ = 0 := Nat.eq_zero_of_not_pos (fun hp ↦ hindex ⟨Sum.inl ⟨0, hp⟩⟩)
    have hx : dx = 0 := Nat.eq_zero_of_not_pos (fun hp ↦ hindex ⟨Sum.inr ⟨0, hp⟩⟩)
    subst dθ
    subst dx
    simp [IPLA.parameterRMS_zero_dimension, ULA.wasserstein2Real_eq_zero_of_subsingleton]

/-- Explicit particle number, step and iteration count for normalized parameter
accuracy `ε`, with Project 03's initialization distance. In a nonzero joint
space, `hstep` implies step positivity and stability. The zero-dimensional
case is handled directly, including zero smoothness. -/
theorem ipla_linear_step_accuracy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N dθ dx : ℕ) (hN : 0 < N)
    {Data : Type*} (U : Data → IPLA.Joint dθ dx → ℝ) (y : Data)
    (m γ : ℝ) (L : ℝ≥0)
    (hU : ContDiff ℝ 2 (U y)) (hsc : StrongConvexOn univ m (U y))
    (hLip : LipschitzWith L (gradient (U y)))
    (hm : 0 < m)
    (θStar : EuclideanSpace ℝ (Fin dθ)) (hMaximizer : IPLA.IsMarginalMaximizer (U y) θStar)
    (initial : Lp (IPLA.State N dθ dx) 2 P) (noise : ℕ → Lp (IPLA.State N dθ dx) 2 P)
    (hGaussian : IPLA.GaussianInnovations P initial noise)
    (ε : ℝ) (hε : 0 < ε) (hparticles : 18 * (dθ : ℝ) ≤ (N : ℝ) * ε ^ 2)
    (hstep : γ = 1 / ((L : ℝ) *
      max 1 (18 * Real.sqrt ((dx : ℝ) + (dθ : ℝ) / (N : ℝ)) / ε)))
    (k : ℕ)
    (hk : (L : ℝ) / m * max 1 (18 * Real.sqrt ((dx : ℝ) + (dθ : ℝ) / (N : ℝ)) / ε) *
      Real.log (1 + 3 * Real.sqrt m *
        ULA.wasserstein2Real (P.map initial) (IPLA.gibbsTarget (U y)) / ε) ≤ k) :
    Real.sqrt m * Real.sqrt (∫ z, ‖IPLA.parameterCLM z - θStar‖ ^ 2
      ∂(IPLA.laws P (U y) γ L (hU.differentiable (by norm_num)) hLip initial noise k)) ≤ ε := by
  classical
  by_cases hindex : Nonempty (Fin dθ ⊕ Fin dx)
  · have hmL : m ≤ L :=
      ipla_curvature_le_smoothness (hU.differentiable (by norm_num)) hsc hLip
    have hL : (0 : ℝ) < L := hm.trans_le hmL
    have hγ : 0 < γ := hstep ▸ iplaAccuracyStep_pos L _ ε hL
    have hγL : γ * L ≤ 1 := hstep ▸ iplaAccuracyStep_mul_L_le L _ ε hL
    let A : IPLASetting :=
      { N := N, dθ := dθ, dx := dx, U := U y, m := m, L := L, γ := γ
        particles_pos := hN, curvature_pos := hm, curvature_le_smoothness := hmL
        step_pos := hγ, step_small := hγL, regularity := hU
        strongConvexity := hsc, gradientLipschitz := hLip }
    have hμ : MemLp (id : IPLA.State N dθ dx → IPLA.State N dθ dx) 2 (P.map initial) :=
      (memLp_map_measure_iff (by fun_prop)
        (Lp.aestronglyMeasurable initial).aemeasurable).mpr (Lp.memLp initial)
    have h := ipla_parameter_accuracy_target A θStar hMaximizer (P.map initial) hμ ε hε
      hparticles hstep k hk
    rwa [A.law_eq_gaussian P initial noise hGaussian k] at h
  · have hθ : dθ = 0 := Nat.eq_zero_of_not_pos (fun hp ↦ hindex ⟨Sum.inl ⟨0, hp⟩⟩)
    have hx : dx = 0 := Nat.eq_zero_of_not_pos (fun hp ↦ hindex ⟨Sum.inr ⟨0, hp⟩⟩)
    subst dθ
    subst dx
    rw [IPLA.parameterRMS_zero_dimension, mul_zero]
    exact hε.le

/-- The same accuracy guarantee with the initialization distance measured from any
square-integrable stationary law of the Gaussian IPLA transition. -/
theorem ipla_linear_step_accuracy_stationary
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N dθ dx : ℕ) (hN : 0 < N)
    {Data : Type*} (U : Data → IPLA.Joint dθ dx → ℝ) (y : Data)
    (m γ : ℝ) (L : ℝ≥0)
    (hU : ContDiff ℝ 2 (U y)) (hsc : StrongConvexOn univ m (U y))
    (hLip : LipschitzWith L (gradient (U y)))
    (hm : 0 < m)
    (θStar : EuclideanSpace ℝ (Fin dθ)) (hMaximizer : IPLA.IsMarginalMaximizer (U y) θStar)
    (stationary : Measure (IPLA.State N dθ dx)) [IsProbabilityMeasure stationary]
    (hmoment : MemLp (id : IPLA.State N dθ dx → IPLA.State N dθ dx) 2 stationary)
    (hstationary : ULA.ulaLawStep (IPLA.potential (U y)) (γ / N) stationary = stationary)
    (initial : Lp (IPLA.State N dθ dx) 2 P) (noise : ℕ → Lp (IPLA.State N dθ dx) 2 P)
    (hGaussian : IPLA.GaussianInnovations P initial noise)
    (ε : ℝ) (hε : 0 < ε) (hparticles : 18 * (dθ : ℝ) ≤ (N : ℝ) * ε ^ 2)
    (hstep : γ = 1 / ((L : ℝ) *
      max 1 (18 * Real.sqrt ((dx : ℝ) + (dθ : ℝ) / (N : ℝ)) / ε)))
    (k : ℕ)
    (hk : (L : ℝ) / m * max 1 (18 * Real.sqrt ((dx : ℝ) + (dθ : ℝ) / (N : ℝ)) / ε) *
      Real.log (1 + 3 * Real.sqrt m * ULA.wasserstein2Real (P.map initial) stationary / ε) ≤ k) :
    Real.sqrt m * Real.sqrt (∫ z, ‖IPLA.parameterCLM z - θStar‖ ^ 2
      ∂(IPLA.laws P (U y) γ L (hU.differentiable (by norm_num)) hLip initial noise k)) ≤ ε := by
  classical
  by_cases hindex : Nonempty (Fin dθ ⊕ Fin dx)
  · have hmL : m ≤ L :=
      ipla_curvature_le_smoothness (hU.differentiable (by norm_num)) hsc hLip
    have hL : (0 : ℝ) < L := hm.trans_le hmL
    have hγ : 0 < γ := hstep ▸ iplaAccuracyStep_pos L _ ε hL
    have hγL : γ * L ≤ 1 := hstep ▸ iplaAccuracyStep_mul_L_le L _ ε hL
    let A : IPLASetting :=
      { N := N, dθ := dθ, dx := dx, U := U y, m := m, L := L, γ := γ
        particles_pos := hN, curvature_pos := hm, curvature_le_smoothness := hmL
        step_pos := hγ, step_small := hγL, regularity := hU
        strongConvexity := hsc, gradientLipschitz := hLip }
    have hμ : MemLp (id : IPLA.State N dθ dx → IPLA.State N dθ dx) 2 (P.map initial) :=
      (memLp_map_measure_iff (by fun_prop)
        (Lp.aestronglyMeasurable initial).aemeasurable).mpr (Lp.memLp initial)
    have hw := A.wasserstein2Real_invariantLaw_le (P.map initial) stationary hμ hmoment
      hstationary
    have hpref : 0 ≤ (L : ℝ) / m *
        max 1 (18 * Real.sqrt ((dx : ℝ) + (dθ : ℝ) / (N : ℝ)) / ε) :=
      mul_nonneg (div_nonneg L.coe_nonneg hm.le) (zero_le_one.trans (le_max_left _ _))
    have hlog : Real.log (1 + 3 * Real.sqrt m *
          ULA.wasserstein2Real (P.map initial) A.invariantLaw / ε) ≤
        Real.log (1 + 3 * Real.sqrt m *
          ULA.wasserstein2Real (P.map initial) stationary / ε) := by
      have h0 : 0 ≤ ULA.wasserstein2Real (P.map initial) A.invariantLaw := ENNReal.toReal_nonneg
      apply Real.log_le_log (by positivity)
      gcongr
    have hk' : iplaAccuracyPrefactor m L (iplaEffectiveDimension N dθ dx) ε *
        Real.log (1 + 3 * Real.sqrt m *
          ULA.wasserstein2Real (P.map initial) A.invariantLaw / ε) ≤ k :=
      (mul_le_mul_of_nonneg_left hlog hpref).trans hk
    have h := ipla_parameter_accuracy A θStar hMaximizer (P.map initial) hμ ε hε
      hparticles hstep k hk'
    rwa [A.law_eq_gaussian P initial noise hGaussian k] at h
  · have hθ : dθ = 0 := Nat.eq_zero_of_not_pos (fun hp ↦ hindex ⟨Sum.inl ⟨0, hp⟩⟩)
    have hx : dx = 0 := Nat.eq_zero_of_not_pos (fun hp ↦ hindex ⟨Sum.inr ⟨0, hp⟩⟩)
    subst dθ
    subst dx
    rw [IPLA.parameterRMS_zero_dimension, mul_zero]
    exact hε.le

end WassersteinMixing
