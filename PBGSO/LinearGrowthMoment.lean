import PBGSO.IntegralQuadraticEnergy
import PBGSO.ParticleWeakBound
import PBGSO.ConstructedPredictableModel
import PBGSO.FilteredIntegralContinuity

/-! # Endpoint moment control for linear-growth original integral equations
These estimates avoid an unproved strong Doob maximal inequality. The actual
L² drift primitive and actual noise energy give an endpoint Volterra bound;
its constants can be uniform over a stopping localization. Fatou and primitive
linear growth can then transfer coefficient moments to the un-stopped process.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
namespace PBGSO.LinearGrowthMoment

/-- An integral upper inequality suffices for Gronwall. Neither a pointwise
energy derivative nor absolute continuity of the bounded curve is assumed. -/
theorem volterra_bound (e : ℝ → ℝ) {T a A c : ℝ}
    (hT : 0 ≤ T) (hc : 0 ≤ c)
    (he : IntervalIntegrable e volume 0 T)
    (hbound : ∀ t ∈ Icc 0 T, e t ≤ a + c * ∫ r in 0..t, A + e r) :
    e T ≤ Real.exp (c * T) * (a + A) - A := by
  let w : ℝ → ℝ := fun r => c * (A + e r)
  let F : ℝ → ℝ := fun t => a + A + ∫ r in 0..t, w r
  have hw : IntervalIntegrable w volume 0 T :=
    ((intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => A) volume 0 T).add he).const_mul c
  have hF (t : ℝ) (ht : t ∈ Icc 0 T) : e t + A ≤ F t := by
    dsimp only [F, w]
    rw [intervalIntegral.integral_const_mul]
    linarith [hbound t ht]
  have hG := IntegralQuadraticEnergy.integral_gronwall F w hT hw
    (by intro r hr; simp only [F, intervalIntegral.integral_same, add_zero])
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      simpa only [w, add_comm] using mul_le_mul_of_nonneg_left (hF r (Ioc_subset_Icc_self hr)) hc)
  have hlast := hF T ⟨hT, le_rfl⟩
  simp only [F, intervalIntegral.integral_same, add_zero] at hG
  linarith

section IntegralSquare
variable {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedAddCommGroup H]

/-- The square of a genuine Bochner drift primitive is controlled by its
actual time-square integral, with the exact horizon-length factor. -/
theorem integral_norm_sq (b : ℝ → E) {t : ℝ} (ht : 0 ≤ t)
    (hb : MemLp b 2 (volume.restrict (Ioc 0 t))) :
    ‖∫ r in 0..t, b r‖ ^ 2 ≤ t * ∫ r in 0..t, ‖b r‖ ^ 2 := by
  have hi := hb.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (f := b) (μ := volume) ht
  have hcs := PBGSO.integral_mul_le_sqrt_integrals (volume.restrict (Ioc 0 t))
    (fun r => ‖b r‖) (fun _ => (1 : ℝ)) hb.norm (memLp_const 1)
  simp only [mul_one, one_pow, integral_const, Measure.real, Measure.restrict_apply_univ,
    Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal ht, smul_eq_mul] at hcs
  simp only [intervalIntegral.integral_of_le ht] at hnorm ⊢
  have hnonneg : 0 ≤ ∫ r in Ioc 0 t, ‖b r‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h1 := Real.sq_sqrt hnonneg
  have h2 := Real.sq_sqrt ht
  have hleft : ‖∫ r in Ioc 0 t, b r‖ ≤
      Real.sqrt (∫ r in Ioc 0 t, ‖b r‖ ^ 2) * Real.sqrt t := hnorm.trans hcs
  have hprod : (Real.sqrt (∫ r in Ioc 0 t, ‖b r‖ ^ 2) * Real.sqrt t) ^ 2 =
      (∫ r in Ioc 0 t, ‖b r‖ ^ 2) * t := by rw [mul_pow, h1, h2]
  nlinarith [norm_nonneg (∫ r in Ioc 0 t, b r),
    Real.sqrt_nonneg (∫ r in Ioc 0 t, ‖b r‖ ^ 2), Real.sqrt_nonneg t,
    sq_nonneg (Real.sqrt (∫ r in Ioc 0 t, ‖b r‖ ^ 2) * Real.sqrt t -
      ‖∫ r in Ioc 0 t, b r‖)]

/-- A literal state/drift/noise decomposition yields its quadratic endpoint
bound. The stochastic noise term is its actual norm, not an assumed error. -/
theorem decomposition_norm_sq (x x0 m : E) (b : ℝ → E) {t : ℝ}
    (ht : 0 ≤ t) (hb : MemLp b 2 (volume.restrict (Ioc 0 t)))
    (heq : x = x0 + (∫ r in 0..t, b r) + m) :
    ‖x‖ ^ 2 ≤ 3 * ‖x0‖ ^ 2 +
      3 * t * (∫ r in 0..t, ‖b r‖ ^ 2) + 3 * ‖m‖ ^ 2 := by
  have hs := integral_norm_sq b ht hb
  have hn : ‖x‖ ≤ ‖x0‖ + ‖∫ r in 0..t, b r‖ + ‖m‖ := by
    rw [heq]
    have h1 := norm_add_le x0 (∫ r in 0..t, b r)
    have h2 := norm_add_le (x0 + ∫ r in 0..t, b r) m
    linarith
  have hsq : ‖x‖ ^ 2 ≤ (‖x0‖ + ‖∫ r in 0..t, b r‖ + ‖m‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith [sq_nonneg (‖x0‖ - ‖∫ r in 0..t, b r‖),
    sq_nonneg (‖x0‖ - ‖m‖), sq_nonneg (‖∫ r in 0..t, b r‖ - ‖m‖)]

/-- Primitive linear growth yields the quadratic coefficient bound, without
assuming a moment or energy inequality. -/
theorem quadratic_growth (x : H) (b : E) (σ : F) {K P : ℝ} (hK : 0 ≤ K) (hP : 0 ≤ P)
    (hg : ‖b‖ + ‖σ‖ ≤ K * (1 + P + ‖x‖)) :
    ‖b‖ ^ 2 + ‖σ‖ ^ 2 ≤ 3 * K ^ 2 * (1 + P ^ 2 + ‖x‖ ^ 2) := by
  have hsq : (‖b‖ + ‖σ‖) ^ 2 ≤ (K * (1 + P + ‖x‖)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hg 2
  have haux : (1 + P + ‖x‖) ^ 2 ≤ 3 * (1 + P ^ 2 + ‖x‖ ^ 2) := by
    nlinarith [sq_nonneg (1-P), sq_nonneg (1-‖x‖), sq_nonneg (P-‖x‖)]
  have hmul := mul_le_mul_of_nonneg_left haux (sq_nonneg K)
  nlinarith [mul_nonneg (norm_nonneg b) (norm_nonneg σ)]

/-- Genuine integral decomposition and actual noise moments imply a uniform
endpoint bound. This is directly applicable with E an actual L² space; its
noise-moment premise is discharged by the computed Brownian corollary below. -/
theorem endpoint_moment_bound (X b m : ℝ → E) (σ : ℝ → F)
    {T A L : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hb : MemLp b 2 (volume.restrict (Ioc 0 T)))
    (hσ : MemLp σ 2 (volume.restrict (Ioc 0 T)))
    (hX : IntervalIntegrable (fun r => ‖X r‖ ^ 2) volume 0 T)
    (heq : ∀ t ∈ Icc 0 T, X t = X 0 + (∫ r in 0..t, b r) + m t)
    (hnoise : ∀ t ∈ Icc 0 T, ‖m t‖ ^ 2 ≤ ∫ r in 0..t, ‖σ r‖ ^ 2)
    (hgrowth : ∀ r ∈ Ioc 0 T, ‖b r‖ ^ 2 + ‖σ r‖ ^ 2 ≤ L * (A + ‖X r‖ ^ 2)) :
    ‖X T‖ ^ 2 ≤ Real.exp ((3 * (T+1) * L) * T) * (3 * ‖X 0‖ ^ 2 + A) - A := by
  apply volterra_bound (fun r => ‖X r‖ ^ 2) hT (by positivity) hX
  intro t ht
  have hsub : volume.restrict (Ioc 0 t) ≤ volume.restrict (Ioc 0 T) :=
    Measure.restrict_mono (Ioc_subset_Ioc le_rfl ht.2) le_rfl
  have hb' := hb.mono_measure hsub
  have hσ' := hσ.mono_measure hsub
  have hbs := (memLp_two_iff_integrable_sq_norm hb'.aestronglyMeasurable).mp hb'
  have hss := (memLp_two_iff_integrable_sq_norm hσ'.aestronglyMeasurable).mp hσ'
  have hx : IntervalIntegrable (fun r => ‖X r‖ ^ 2) volume 0 t := hX.mono_set' (by simpa only [uIoc_of_le ht.1, uIoc_of_le hT] using Ioc_subset_Ioc le_rfl ht.2)
  have hright : Integrable (fun r => L * (A + ‖X r‖ ^ 2)) (volume.restrict (Ioc 0 t)) := by
    exact ((integrable_const A).add ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mp hx)).const_mul L
  have hi := integral_mono_ae (hbs.add hss) hright
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        exact hgrowth r ⟨hr.1, hr.2.trans ht.2⟩)
  simp only [Pi.add_apply] at hi
  rw [integral_add hbs hss, integral_const_mul] at hi
  have hdec := decomposition_norm_sq (X t) (X 0) (m t) b ht.1 hb' (heq t ht)
  have hno := hnoise t ht
  rw [intervalIntegral.integral_of_le ht.1] at hdec hno ⊢
  have hnB : 0 ≤ ∫ r in Ioc 0 t, ‖b r‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hnS : 0 ≤ ∫ r in Ioc 0 t, ‖σ r‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have htB := mul_nonneg (sub_nonneg.mpr ht.2) hnB
  have hmul := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 3 * (T+1))
  nlinarith
end IntegralSquare

section LocalizationLimit
variable {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H]
  (Q : Measure Ω)

/-- A uniform actual endpoint second-moment bound survives almost-sure
localization limits. Both L² membership and the limiting moment are derived
by Fatou; neither uniform integrability nor L² convergence is assumed. -/
theorem localized_limit_memLp (Y : ℕ → Ω → H) (X : Ω → H) {C : ℝ}
    (hC : 0 ≤ C) (hY : ∀ n, MemLp (Y n) 2 Q)
    (hbound : ∀ n, ‖(hY n).toLp (Y n)‖ ^ 2 ≤ C)
    (hlim : ∀ᵐ ω ∂Q, Tendsto (fun n => Y n ω) atTop (𝓝 (X ω))) :
    ∃ hX : MemLp X 2 Q, ‖hX.toLp X‖ ^ 2 ≤ C := by
  have hm := aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hY n).aestronglyMeasurable) hlim
  have hnorm (n : ℕ) : eLpNorm (Y n) 2 Q ≤ ENNReal.ofReal (Real.sqrt C) := by
    rw [← Lp.enorm_toLp (hY n), ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (Real.le_sqrt_of_sq_le (hbound n))
  have hFatou := Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall hnorm)
    (fun n => (hY n).aestronglyMeasurable) hm hlim
  have hX : MemLp X 2 Q := lt_of_le_of_lt hFatou (by finiteness)
  refine ⟨hX, ?_⟩
  have hn : ‖hX.toLp X‖ ≤ Real.sqrt C := by
    rw [Lp.norm_toLp]
    simpa only [ENNReal.toReal_ofReal (Real.sqrt_nonneg C)] using
      ENNReal.toReal_mono (by finiteness : ENNReal.ofReal (Real.sqrt C) ≠ ⊤) hFatou
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rwa [Real.sq_sqrt hC] at hs
end LocalizationLimit

section RawGrowth
variable {Ω H E F : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- The norm square of an actual L² class is the raw second moment. -/
theorem toLp_norm_sq (f : Ω → E) (hf : MemLp f 2 Q) :
    ‖hf.toLp f‖ ^ 2 = ∫ ω, ‖f ω‖ ^ 2 ∂Q := by
  rw [ProximalLangevin.lp_norm_sq_eq_integral]
  exact integral_congr_ae (hf.coeFn_toLp.fun_comp (fun z => ‖z‖ ^ 2))

/-- Actual primitive pointwise linear growth derives both spatial L²
coefficient membership and their exact quadratic moment bound. -/
theorem coefficients_of_linear_growth (X : Ω → H) (b : Ω → E) (σ : Ω → F)
    (hX : MemLp X 2 Q) (hb : AEStronglyMeasurable b Q) (hσ : AEStronglyMeasurable σ Q)
    {K P : ℝ} (hK : 0 ≤ K) (hP : 0 ≤ P)
    (hg : ∀ᵐ ω ∂Q, ‖b ω‖ + ‖σ ω‖ ≤ K * (1 + P + ‖X ω‖)) :
    ∃ hb2 : MemLp b 2 Q, ∃ hσ2 : MemLp σ 2 Q,
      ‖hb2.toLp b‖ ^ 2 + ‖hσ2.toLp σ‖ ^ 2 ≤
        3 * K ^ 2 * (1 + P ^ 2 + ‖hX.toLp X‖ ^ 2) := by
  have hcontrol : MemLp (fun ω => K * (1 + P + ‖X ω‖)) 2 Q :=
    ((memLp_const (1+P)).add hX.norm).const_mul K
  have hb2 : MemLp b 2 Q := hcontrol.mono' hb (hg.mono fun ω hω => by
    linarith [norm_nonneg (σ ω)])
  have hσ2 : MemLp σ 2 Q := hcontrol.mono' hσ (hg.mono fun ω hω => by
    linarith [norm_nonneg (b ω)])
  refine ⟨hb2, hσ2, ?_⟩
  rw [toLp_norm_sq Q b hb2, toLp_norm_sq Q σ hσ2, toLp_norm_sq Q X hX]
  have hbs := (memLp_two_iff_integrable_sq_norm hb2.aestronglyMeasurable).mp hb2
  have hss := (memLp_two_iff_integrable_sq_norm hσ2.aestronglyMeasurable).mp hσ2
  have hxs := (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).mp hX
  have hi := integral_mono_ae (hbs.add hss)
    (((integrable_const (1+P^2)).add hxs).const_mul (3*K^2))
    (hg.mono fun ω hω => quadratic_growth (X ω) (b ω) (σ ω) hK hP hω)
  simp only [Pi.add_apply] at hi
  rw [integral_add hbs hss, integral_const_mul, integral_add (integrable_const _) hxs,
    integral_const] at hi
  simpa only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul, add_assoc] using hi
/-- Original coefficients restricted to an actual stopping event obey
the same primitive linear-growth estimate against the stopped state. The
coefficient moments are then derived, rather than supplied as a hypothesis. -/
theorem stopped_coefficients_of_linear_growth (X Y : Ω → H) (b : Ω → E) (σ : Ω → F)
    (S : Set Ω) (hY : MemLp Y 2 Q) (hb : AEStronglyMeasurable b Q)
    (hσ : AEStronglyMeasurable σ Q) {K P : ℝ} (hK : 0 ≤ K) (hP : 0 ≤ P)
    (hbefore : ∀ᵐ ω ∂Q, ω ∈ S → Y ω = X ω)
    (hzero : ∀ᵐ ω ∂Q, ω ∉ S → b ω = 0 ∧ σ ω = 0)
    (hgrowth : ∀ᵐ ω ∂Q, ω ∈ S → ‖b ω‖ + ‖σ ω‖ ≤ K * (1 + P + ‖X ω‖)) :
    ∃ hb2 : MemLp b 2 Q, ∃ hσ2 : MemLp σ 2 Q,
      ‖hb2.toLp b‖ ^ 2 + ‖hσ2.toLp σ‖ ^ 2 ≤
        3 * K ^ 2 * (1 + P ^ 2 + ‖hY.toLp Y‖ ^ 2) := by
  apply coefficients_of_linear_growth Q Y b σ hY hb hσ hK hP
  filter_upwards [hbefore, hzero, hgrowth] with ω hbef hz hg
  by_cases hω : ω ∈ S
  · rw [hbef hω]
    exact hg hω
  · simpa only [(hz hω).1, (hz hω).2, norm_zero, add_zero] using
      mul_nonneg hK (show 0 ≤ 1 + P + ‖Y ω‖ by positivity)

/-- Uniform actual second moments and joint strong measurability derive
product-space square integrability on a finite horizon. This supplies the
raw coefficient hypothesis of the actual section/integrator construction. -/
theorem product_memLp_of_uniform_moment (f : ℝ → Ω → E) (T : ℝ≥0) {C : ℝ}
    (hf : StronglyMeasurable (Function.uncurry f))
    (hmem : ∀ t ∈ Ioc 0 (T : ℝ), MemLp (f t) 2 Q)
    (hbound : ∀ t (ht : t ∈ Ioc 0 (T : ℝ)),
      ‖(hmem t ht).toLp (f t)‖ ^ 2 ≤ C) :
    MemLp (Function.uncurry f) 2 ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := by
  have hs : StronglyMeasurable (fun p : ℝ × Ω => ‖f p.1 p.2‖ ^ 2) := hf.norm.pow 2
  have hinner : Integrable (fun t => ∫ ω, ‖f t ω‖ ^ 2 ∂Q)
      (volume.restrict (Ioc 0 (T : ℝ))) := by
    apply (integrable_const C).mono' hs.integral_prod_right'.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
    rw [← toLp_norm_sq Q (f t) (hmem t ht)]
    exact hbound t ht
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  apply (integrable_prod_iff hs.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (memLp_two_iff_integrable_sq_norm (hmem t ht).aestronglyMeasurable).mp (hmem t ht)
  · simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hinner

/-- The actual integrated raw energy is bounded by horizon length times
the uniform derived spatial moment, with Fubini justified internally. -/
theorem product_energy_le (f : ℝ → Ω → E) (T : ℝ≥0) {C : ℝ}
    (hf : StronglyMeasurable (Function.uncurry f))
    (hmem : ∀ t ∈ Ioc 0 (T : ℝ), MemLp (f t) 2 Q)
    (hbound : ∀ t (ht : t ∈ Ioc 0 (T : ℝ)),
      ‖(hmem t ht).toLp (f t)‖ ^ 2 ≤ C) :
    (∫ p : ℝ × Ω, ‖f p.1 p.2‖ ^ 2 ∂((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) ≤ T * C := by
  have hm := product_memLp_of_uniform_moment Q f T hf hmem hbound
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  change Integrable (fun p : ℝ × Ω => ‖f p.1 p.2‖ ^ 2)
    ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) at hi
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ _ in Ioc 0 (T : ℝ), C := by
      apply integral_mono_ae hi.integral_prod_left (integrable_const C)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [← toLp_norm_sq Q (f t) (hmem t ht)]
      exact hbound t ht
    _ = T * C := by simp only [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal T.coe_nonneg, smul_eq_mul]

/-- Jointly measurable primitive linear-growth coefficients have actual
global time×probability L² membership once the uniform state endpoint
moment has been derived. No L²-valued coefficient curve is supplied. -/
theorem coefficient_product_memLp (X : ℝ → Ω → H) (b : ℝ → Ω → E)
    (σ : ℝ → Ω → F) (T : ℝ≥0) {K P C : ℝ} (hK : 0 ≤ K) (hP : 0 ≤ P)
    (hb : StronglyMeasurable (Function.uncurry b))
    (hσ : StronglyMeasurable (Function.uncurry σ))
    (hX : ∀ t ∈ Ioc 0 (T : ℝ), MemLp (X t) 2 Q)
    (hbound : ∀ t (ht : t ∈ Ioc 0 (T : ℝ)), ‖(hX t ht).toLp (X t)‖ ^ 2 ≤ C)
    (hgrowth : ∀ t ∈ Ioc 0 (T : ℝ), ∀ᵐ ω ∂Q,
      ‖b t ω‖ + ‖σ t ω‖ ≤ K * (1 + P + ‖X t ω‖)) :
    MemLp (Function.uncurry b) 2 ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) ∧
      MemLp (Function.uncurry σ) 2 ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := by
  have hpoint (t : ℝ) (ht : t ∈ Ioc 0 (T : ℝ)) :=
    coefficients_of_linear_growth Q (X t) (b t) (σ t) (hX t ht)
      hb.of_uncurry_left.aestronglyMeasurable hσ.of_uncurry_left.aestronglyMeasurable
      hK hP (hgrowth t ht)
  choose hb2 hσ2 hs using hpoint
  have hall (t : ℝ) (ht : t ∈ Ioc 0 (T : ℝ)) :
      ‖(hb2 t ht).toLp (b t)‖ ^ 2 + ‖(hσ2 t ht).toLp (σ t)‖ ^ 2 ≤
        3 * K ^ 2 * (1 + P ^ 2 + C) :=
    (hs t ht).trans (mul_le_mul_of_nonneg_left
      (show 1 + P ^ 2 + ‖(hX t ht).toLp (X t)‖ ^ 2 ≤ 1 + P ^ 2 + C by
        linarith [hbound t ht]) (by positivity))
  constructor
  · apply product_memLp_of_uniform_moment Q b T (C := 3*K^2*(1+P^2+C)) hb hb2
    intro t ht
    nlinarith [hall t ht, sq_nonneg ‖(hσ2 t ht).toLp (σ t)‖]
  · apply product_memLp_of_uniform_moment Q σ T (C := 3*K^2*(1+P^2+C)) hσ hσ2
    intro t ht
    nlinarith [hall t ht, sq_nonneg ‖(hb2 t ht).toLp (b t)‖]

end RawGrowth

section Computed
open ProbabilityTheory FilteredBrownian
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

/-- The actual completed predictable Brownian integral has exactly its
original finite-column time-square energy. -/
theorem computed_noise_norm_sq (T : ℝ≥0)
    (σ : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hσ : MemLp σ 2 (volume.restrict (Ioc 0 (T : ℝ))))
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ t i) Q)
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    ‖ConstructedPredictableModel.integral Q D T σ hσ hA t‖ ^ 2 =
      ∫ r in 0..t, ‖σ r‖ ^ 2 := by
  have he := predictableCurveIntegral_increment_isometry Q D T σ hσ hA
    (ContinuousLinearMap.id ℝ Z) (fun _ _ => rfl) 0 t.toNNReal (by simp) (by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ht.1]
      exact ht.2)
  rw [predictableCurveIntegral_zero, sub_zero, weightedPairing_id] at he
  simp only [columnWeighted_id] at he
  simpa only [ConstructedPredictableModel.integral,
    intervalIntegral.integral_of_le ht.1, NNReal.coe_zero, Real.coe_toNNReal _ ht.1] using he

/-- Genuine computed Brownian noise and primitive quadratic coefficient
growth give an actual endpoint second-moment bound, with no supplied noise
isometry, martingale, dissipation, energy or state-moment conclusion. The
constant is independent of any localization index entering X,b,σ. -/
theorem computed_endpoint_moment_bound (X b : ℝ → Lp Z 2 Q)
    (σ : ℝ → ColumnHilbert (I := I) (Z := Z) Q) (T : ℝ≥0) {A L : ℝ}
    (hL : 0 ≤ L)
    (hb : MemLp b 2 (volume.restrict (Ioc 0 (T : ℝ))))
    (hσ : MemLp σ 2 (volume.restrict (Ioc 0 (T : ℝ))))
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ t i) Q)
    (heq : ∀ t ∈ Icc 0 (T : ℝ), X t = X 0 + (∫ r in 0..t, b r) +
      ConstructedPredictableModel.integral Q D T σ hσ hA t)
    (hgrowth : ∀ r ∈ Ioc 0 (T : ℝ),
      ‖b r‖ ^ 2 + ‖σ r‖ ^ 2 ≤ L * (A + ‖X r‖ ^ 2)) :
    ‖X T‖ ^ 2 ≤ Real.exp ((3 * (T+1) * L) * T) * (3 * ‖X 0‖ ^ 2 + A) - A := by
  have hbi : IntervalIntegrable b volume 0 (T : ℝ) := by
    rw [intervalIntegrable_iff, uIoc_of_le T.coe_nonneg]
    exact hb.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hi := (IntegralQuadraticEnergy.integral_absolutelyContinuous b hbi).continuousOn
  rw [uIcc_of_le T.coe_nonneg] at hi
  have hcont : ContinuousOn X (Icc 0 (T : ℝ)) :=
    ((continuousOn_const.add hi).add
      (ConstructedPredictableModel.integral_continuous Q D T σ hσ hA).continuousOn).congr
        (fun t ht => heq t ht)
  have hsq : IntervalIntegrable (fun r => ‖X r‖ ^ 2) volume 0 (T : ℝ) :=
    ((hcont.norm.pow 2).mono (by
      intro r hr
      simpa only [uIcc_of_le T.coe_nonneg] using hr)).intervalIntegrable
  exact endpoint_moment_bound X b
    (ConstructedPredictableModel.integral Q D T σ hσ hA) σ T.coe_nonneg hL hb hσ hsq heq
    (fun t ht => le_of_eq (computed_noise_norm_sq Q D T σ hσ hA t ht)) hgrowth
end Computed
end PBGSO.LinearGrowthMoment
