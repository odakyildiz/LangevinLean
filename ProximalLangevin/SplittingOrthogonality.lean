import ProximalLangevin.IndependenceHelpers
import UnadjustedLangevin.WeakForwardAdapted
import UnadjustedLangevin.BrownianLangevin
import UnadjustedLangevin.BrownianInnovations
import Mathlib.Probability.Independence.Integration

set_option linter.style.header false

/-!
# Orthogonality of the constructed Langevin past and future Brownian increments

The scalar weak Markov property and independence of Brownian coordinates
provide the source independence. Adaptedness of the actual integral solution
then gives the required `L²` orthogonality; it is not supplied as a field of
a convergence assumption bundle.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal RealInnerProductSpace

namespace ProximalLangevin

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

omit [Fintype ι] in
/-- The complete shifted future and the stopped past of independent scalar
Brownian coordinates are independent vector-valued path families. -/
theorem brownian_future_past_independent [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) Q)
    (hmeas : ∀ i t, Measurable (B i t))
    (hpaths : iIndepFun (fun i ω t ↦ B i t ω) Q) (T : ℝ≥0) :
    IndepFun (fun ω (i : ι) (s : ℝ≥0) ↦ B i (T + s) ω - B i T ω)
      (fun ω (i : ι) (t : ℝ≥0) ↦ B i (min t T) ω) Q := by
  classical
  let := Fintype.ofFinite ι
  let X : ι → Bool → Ω → (ℝ≥0 → ℝ) := fun i b ω t ↦
    if b then B i (min t T) ω else B i (T + t) ω - B i T ω
  have hXm (i : ι) (b : Bool) : Measurable (X i b) := by
    refine measurable_pi_iff.mpr fun t ↦ ?_
    cases b <;> simp only [X, Bool.false_eq_true, ↓reduceIte]
    · exact (hmeas i _).sub (hmeas i _)
    · exact hmeas i _
  have hrow (i : ι) : iIndepFun (X i) Q := by
    have hi := ((hB i).indepFun_shift T).comp measurable_id
      (measurable_pi_iff.mpr fun t ↦ measurable_pi_apply
        (⟨min t T, min_le_right t T⟩ : Iic T))
    convert iIndepFun_bool_of_indepFun hi using 1
    funext b ω t
    cases b <;> rfl
  have hrows : iIndepFun (fun i ω b ↦ X i b ω) Q := by
    exact hpaths.comp (fun _ (w : ℝ≥0 → ℝ) (b : Bool) t ↦
      if b then w (min t T) else w (T + t) - w T)
      (fun i ↦ measurable_pi_iff.mpr fun b ↦ measurable_pi_iff.mpr fun t ↦ by
        cases b <;> fun_prop)
  have hall : iIndepFun (fun p : ι × Bool ↦ X p.1 p.2) Q :=
    iIndepFun_uncurry' hXm hrows hrow
  let S : Finset (ι × Bool) := Finset.univ.filter (fun p ↦ p.2 = false)
  let R : Finset (ι × Bool) := Finset.univ.filter (fun p ↦ p.2 = true)
  have hdis : Disjoint S R := by simp [S, R, Finset.disjoint_left]
  have hs (i : ι) : (i, false) ∈ S := by simp [S]
  have hr (i : ι) : (i, true) ∈ R := by simp [R]
  have hi := hall.indepFun_finset S R hdis (fun p ↦ hXm p.1 p.2)
  exact hi.comp
    (measurable_pi_iff.mpr fun i ↦ measurable_pi_apply (⟨(i, false), hs i⟩ : S))
    (measurable_pi_iff.mpr fun i ↦ measurable_pi_apply (⟨(i, true), hr i⟩ : R))

/-- The pointwise vector presentation of the Langevin noise from time zero. -/
def rawBrownianNoise (B : ι → ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : EuclideanSpace ℝ ι :=
  Real.sqrt 2 • (ULA.brownianCoordinates B t.toNNReal ω - ULA.brownianCoordinates B 0 ω)

omit [IsProbabilityMeasure Q] in
theorem brownianNoise_coe (B : ι → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) Q) (t : ℝ) :
    ULA.brownianLangevinNoise Q B hB 0 t =ᵐ[Q] rawBrownianNoise B t := by
  unfold ULA.brownianLangevinNoise ULA.brownianCoordinatesRealLp
  simp only [zero_add, Real.toNNReal_zero]
  filter_upwards [Lp.coeFn_smul (Real.sqrt 2)
      (ULA.brownianCoordinatesLp Q B hB t.toNNReal - ULA.brownianCoordinatesLp Q B hB 0),
    Lp.coeFn_sub (ULA.brownianCoordinatesLp Q B hB t.toNNReal)
      (ULA.brownianCoordinatesLp Q B hB 0),
    ULA.brownianCoordinatesLp_coe Q B hB t.toNNReal,
    ULA.brownianCoordinatesLp_coe Q B hB 0] with ω hs hd ht h0
  simp only [hs, hd, ht, h0, rawBrownianNoise, Pi.smul_apply, Pi.sub_apply]

omit [Fintype ι] in
theorem rawBrownianNoise_measurable [Finite ι] (B : ι → ℝ≥0 → Ω → ℝ)
    (hmeas : ∀ i t, Measurable (B i t)) (t : ℝ) : Measurable (rawBrownianNoise B t) := by
  let := Fintype.ofFinite ι
  unfold rawBrownianNoise ULA.brownianCoordinates
  exact (((WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.mpr fun i ↦ hmeas i _)).sub
    ((WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.mpr fun i ↦ hmeas i _))).const_smul
      (Real.sqrt 2 : ℝ)

/-- A future Brownian increment is independent of the initialization and all
earlier actual `L²` Brownian-noise representatives. -/
theorem brownian_future_independent_initial_past
    (B : ι → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) Q)
    (hmeas : ∀ i t, Measurable (B i t))
    (hpaths : iIndepFun (fun i ω t ↦ B i t ω) Q)
    (initial : Lp (EuclideanSpace ℝ ι) 2 Q)
    (hinit : IndepFun initial (fun ω (i : ι) (t : ℝ≥0) ↦ B i t ω) Q)
    (t h : ℝ) (ht : 0 ≤ t) (hth : t ≤ h) :
    IndepFun
      (fun ω (r : Option (Icc (0 : ℝ) t)) ↦
        r.elim (initial ω) (fun s ↦ ULA.brownianLangevinNoise Q B hB 0 s ω))
      (ULA.brownianLangevinNoise Q B hB 0 h - ULA.brownianLangevinNoise Q B hB 0 t) Q := by
  have hhh : 0 ≤ h := ht.trans hth
  have hdelta : 0 ≤ h - t := sub_nonneg.mpr hth
  have hadd : t.toNNReal + (h - t).toNNReal = h.toNNReal := by
    apply NNReal.eq
    simp only [NNReal.coe_add, Real.coe_toNNReal _ ht,
      Real.coe_toNNReal _ hdelta, Real.coe_toNNReal _ hhh]
    ring
  let past : Ω → Icc (0 : ℝ) t → EuclideanSpace ℝ ι :=
    fun ω s ↦ rawBrownianNoise B s ω
  let future : Ω → EuclideanSpace ℝ ι :=
    fun ω ↦ rawBrownianNoise B h ω - rawBrownianNoise B t ω
  have hpast : Measurable past := measurable_pi_iff.mpr fun s ↦
    rawBrownianNoise_measurable B hmeas s
  have hfuture : Measurable future :=
    (rawBrownianNoise_measurable B hmeas h).sub (rawBrownianNoise_measurable B hmeas t)
  have hpf : IndepFun past future Q := by
    have hi := (brownian_future_past_independent Q B hB hmeas hpaths t.toNNReal).symm
    have hmPast : Measurable (fun w : ι → ℝ≥0 → ℝ ↦ fun s : Icc (0 : ℝ) t ↦
        Real.sqrt 2 • (WithLp.toLp 2 (fun i ↦ w i s.1.toNNReal) -
          WithLp.toLp 2 (fun i ↦ w i 0))) := by fun_prop
    have hmFuture : Measurable (fun w : ι → ℝ≥0 → ℝ ↦
        Real.sqrt 2 • WithLp.toLp 2 (fun i ↦ w i (h - t).toNNReal)) := by fun_prop
    have hj := hi.comp hmPast hmFuture
    convert hj using 1
    · funext ω s
      have hst : s.1.toNNReal ≤ t.toNNReal := Real.toNNReal_le_toNNReal s.2.2
      simp [past, rawBrownianNoise, ULA.brownianCoordinates, min_eq_left hst]
    · funext ω
      ext i
      simp [future, rawBrownianNoise, ULA.brownianCoordinates, hadd]
      ring
  have hip : IndepFun initial (fun ω ↦ (past ω, future ω)) Q := by
    have hm : Measurable (fun w : ι → ℝ≥0 → ℝ ↦
        ((fun s : Icc (0 : ℝ) t ↦ Real.sqrt 2 •
          (WithLp.toLp 2 (fun i ↦ w i s.1.toNNReal) - WithLp.toLp 2 (fun i ↦ w i 0))),
        (Real.sqrt 2 • (WithLp.toLp 2 (fun i ↦ w i h.toNNReal) -
          WithLp.toLp 2 (fun i ↦ w i 0)) -
          Real.sqrt 2 • (WithLp.toLp 2 (fun i ↦ w i t.toNNReal) -
            WithLp.toLp 2 (fun i ↦ w i 0))))) := by fun_prop
    exact hinit.comp measurable_id hm
  have hj := indepFun_prodMk_left_of_indepFun (Lp.stronglyMeasurable initial).measurable
    hpast hfuture hip hpf
  have hopt : IndepFun
      (fun ω (r : Option (Icc (0 : ℝ) t)) ↦ r.elim (initial ω) (fun s ↦ past ω s))
      future Q := by
    have hm : Measurable (fun p : (EuclideanSpace ℝ ι) ×
        (Icc (0 : ℝ) t → EuclideanSpace ℝ ι) ↦
        fun r : Option (Icc (0 : ℝ) t) ↦ r.elim p.1 (fun s ↦ p.2 s)) := by
      refine measurable_pi_iff.mpr fun r ↦ ?_
      cases r with
      | none => exact measurable_fst
      | some s => exact (measurable_pi_apply s).comp measurable_snd
    exact hj.comp hm measurable_id
  have hopt' := hopt.process_congr_left (X' := fun r ω ↦
    r.elim (initial ω) (fun s ↦ ULA.brownianLangevinNoise Q B hB 0 s ω)) (fun r ↦ by
      cases r with
      | none => exact Filter.EventuallyEq.rfl
      | some s => exact (brownianNoise_coe Q B hB s).symm)
  apply hopt'.congr Filter.EventuallyEq.rfl
  filter_upwards [Lp.coeFn_sub (ULA.brownianLangevinNoise Q B hB 0 h)
      (ULA.brownianLangevinNoise Q B hB 0 t),
    brownianNoise_coe Q B hB h, brownianNoise_coe Q B hB t] with ω hd hh ht'
  exact (hd.trans (congrArg₂ (· - ·) hh ht')).symm

omit [IsProbabilityMeasure Q] in
/-- Every random variable measurable from the natural initialization/noise
past inherits its independence from a supplied future source variable. -/
theorem naturalPast_independent_of_aestronglyMeasurable
    (initial : Lp (EuclideanSpace ℝ ι) 2 Q)
    (noise : ℝ → Lp (EuclideanSpace ℝ ι) 2 Q) (t : ℝ)
    (W : Ω → EuclideanSpace ℝ ι)
    (hind : IndepFun (fun ω (r : Option (Icc (0 : ℝ) t)) ↦
      r.elim (initial ω) (fun s ↦ noise s ω)) W Q)
    (Z : Ω → EuclideanSpace ℝ ι)
    (hZ : AEStronglyMeasurable[ULA.lpLangevinPast Q initial noise t] Z Q) :
    IndepFun Z W Q := by
  let F : Ω → Option (Icc (0 : ℝ) t) → EuclideanSpace ℝ ι :=
    fun ω r ↦ r.elim (initial ω) (fun s ↦ noise s ω)
  have hs : ULA.lpLangevinPast Q initial noise t ≤
      MeasurableSpace.pi.comap F := by
    apply sup_le
    · exact MeasurableSpace.comap_le_comap_pi (g := fun r ω ↦ F ω r) none
    · apply iSup_le
      intro s
      exact MeasurableSpace.comap_le_comap_pi (g := fun r ω ↦ F ω r) (some s)
  have hm : IndepFun (hZ.mk Z) W Q :=
    indep_of_indep_of_le_left hind (hZ.stronglyMeasurable_mk.measurable.comap_le.trans hs)
  exact hm.congr hZ.ae_eq_mk.symm Filter.EventuallyEq.rfl

/-- The finite-dimensional Brownian vector has zero mean. -/
theorem brownianCoordinates_integral_zero
    (B : ι → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) Q) (t : ℝ≥0) :
    (∫ ω, ULA.brownianCoordinates B t ω ∂Q) = 0 := by
  have hint : Integrable (ULA.brownianCoordinates B t) Q :=
    (ULA.gaussian_coordinates_memLp Q _ t
      (ULA.brownianCoordinates_coordinateLaw Q B hB t)).integrable (by norm_num)
  ext i
  have hi := (EuclideanSpace.proj i).integral_comp_comm hint
  change (EuclideanSpace.proj i) (∫ ω, ULA.brownianCoordinates B t ω ∂Q) = 0
  rw [← hi]
  exact (hB i).integral_eval t

/-- The actual `L²` additive Langevin noise is centered at every real time. -/
theorem brownianNoise_integral_zero
    (B : ι → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) Q) (t : ℝ) :
    (∫ ω, ULA.brownianLangevinNoise Q B hB 0 t ω ∂Q) = 0 := by
  have hint (s : ℝ≥0) : Integrable (ULA.brownianCoordinates B s) Q :=
    (ULA.gaussian_coordinates_memLp Q _ s
      (ULA.brownianCoordinates_coordinateLaw Q B hB s)).integrable (by norm_num)
  rw [integral_congr_ae (brownianNoise_coe Q B hB t)]
  unfold rawBrownianNoise
  rw [integral_smul, integral_sub (hint _) (hint _),
    brownianCoordinates_integral_zero Q B hB t.toNNReal,
    brownianCoordinates_integral_zero Q B hB 0]
  simp

/-- Binary independence and zero mean imply genuine `L²` orthogonality. -/
theorem independent_centered_lp_inner_zero
    (X W : Lp (EuclideanSpace ℝ ι) 2 Q) (hind : IndepFun X W Q)
    (hmean : (∫ ω, W ω ∂Q) = 0) : inner ℝ X W = 0 := by
  rw [L2.inner_def]
  have hi := hind.integral_bilin
    ((Lp.memLp X).integrable (by norm_num)) ((Lp.memLp W).integrable (by norm_num))
    (innerSL ℝ)
  change (∫ ω, inner ℝ (X ω) (W ω) ∂Q) =
    inner ℝ (∫ ω, X ω ∂Q) (∫ ω, W ω ∂Q) at hi
  rw [hmean, inner_zero_right] at hi
  exact hi

/-- A Lipschitz function of the actual Langevin solution is orthogonal to
every later Brownian increment. Adaptedness is derived from the integral
equation by the existing invariant-subspace construction. -/
theorem lp_langevin_future_inner_zero
    (U : EuclideanSpace ℝ ι → ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (initial : Lp (EuclideanSpace ℝ ι) 2 Q)
    (B : ι → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) Q)
    (hmeas : ∀ i s, Measurable (B i s))
    (hpaths : iIndepFun (fun i ω s ↦ B i s ω) Q)
    (hinit : IndepFun initial (fun ω (i : ι) (s : ℝ≥0) ↦ B i s ω) Q)
    (Y : ℝ → Lp (EuclideanSpace ℝ ι) 2 Q) (hY : Continuous Y)
    (t h : ℝ) (ht : 0 ≤ t) (hth : t ≤ h)
    (hYe : ∀ s ∈ Icc (0 : ℝ) h, Y s - initial =
      -(∫ r in 0..s, ULA.lpDrift Q (gradient U) hLip (Y r)) +
        ULA.brownianLangevinNoise Q B hB 0 s)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (Lb : ℝ≥0)
    (hLipb : LipschitzWith Lb b) :
    inner ℝ (ULA.lpDrift Q b hLipb (Y t))
      (ULA.brownianLangevinNoise Q B hB 0 h - ULA.brownianLangevinNoise Q B hB 0 t) = 0 := by
  let noise := ULA.brownianLangevinNoise Q B hB 0
  have hadapt := ULA.lp_langevin_integral_naturalPast Q U L hLip initial noise Y
    (ULA.brownianLangevinNoise_continuous Q B hB 0)
    (ULA.brownianLangevinNoise_zero Q B hB 0) hY t ht
    (fun s hs ↦ hYe s ⟨hs.1, hs.2.trans hth⟩)
  have hZ := ULA.lpDrift_aestronglyMeasurable
    (ULA.lpLangevinPast Q initial noise t) Q b Lb hLipb (Y t)
    (hadapt t ⟨ht, le_rfl⟩)
  have hind := naturalPast_independent_of_aestronglyMeasurable Q initial noise t
    (fun ω ↦ (noise h - noise t : Lp (EuclideanSpace ℝ ι) 2 Q) ω)
    (brownian_future_independent_initial_past Q B hB hmeas hpaths initial hinit t h ht hth)
    (ULA.lpDrift Q b hLipb (Y t)) hZ
  apply independent_centered_lp_inner_zero Q _ _ hind
  have hi₁ := (Lp.memLp (noise h)).integrable (by norm_num)
  have hi₂ := (Lp.memLp (noise t)).integrable (by norm_num)
  rw [integral_congr_ae (Lp.coeFn_sub (noise h) (noise t))]
  change (∫ ω, noise h ω - noise t ω ∂Q) = 0
  rw [integral_sub hi₁ hi₂]
  change (∫ ω, ULA.brownianLangevinNoise Q B hB 0 h ω ∂Q) -
    (∫ ω, ULA.brownianLangevinNoise Q B hB 0 t ω ∂Q) = 0
  rw [brownianNoise_integral_zero Q B hB h, brownianNoise_integral_zero Q B hB t, sub_self]

end ProximalLangevin
