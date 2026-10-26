import PBGSO.MeanFieldContraction
import PBGSO.WeakContraction
import PBGSO.EmpiricalMonotonicity
import UnadjustedLangevin.InitialCoupling
import UnadjustedLangevin.InitialExtension
import UnadjustedLangevin.CouplingLimit
import ProximalLangevin.SplittingL2Energy

/-!
# From actual coupling energies to Wasserstein laws

The transport distance is the infimum over all genuine initial couplings.
No optimal-coupling existence or supplied Wasserstein conclusion is assumed.
The generic energy theorem takes actual output couplings and their quadratic
energy comparisons; coupled-generator or integral-equation arguments can
produce those data. Realising the same output laws from every initial coupling
is an explicit process-level requirement of that theorem.

The additive specialisation below applies to actual integral solutions of
the independent general observation/response/sampler maps. It derives the
sampler law bound from their proved common-input contraction. State-dependent
strong-SDE and martingale-problem equivalence are separate requirements.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology
namespace PBGSO

section CouplingCost
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

omit [BorelSpace H] [SecondCountableTopology H] in
/-- The genuine coupling cost squared is its quadratic integral, whenever
the difference has a finite second moment. -/
theorem couplingCost_sq_eq_integral (Λ : Measure (H × H))
    (hΛ : MemLp (fun p : H × H => p.1 - p.2) 2 Λ) :
    (ULA.couplingCost Λ).toReal ^ 2 = ∫ p, ‖p.1 - p.2‖ ^ 2 ∂Λ := by
  let D := hΛ.toLp (fun p : H × H => p.1 - p.2)
  have hn := ProximalLangevin.lp_norm_sq_eq_integral Λ D
  rw [Lp.norm_toLp] at hn
  change (ULA.couplingCost Λ).toReal ^ 2 = _ at hn
  exact hn.trans (integral_congr_ae (hΛ.coeFn_toLp.fun_comp fun v => ‖v‖ ^ 2))

omit [InnerProductSpace ℝ H] [BorelSpace H] [SecondCountableTopology H] in
/-- Finite-second-moment marginals make every coupling cost finite; this
does not require the coupling to be independent or optimal. -/
theorem coupling_difference_memLp (μ ν : Measure H)
    (hμ : MemLp (fun x : H => x) 2 μ) (hν : MemLp (fun x : H => x) 2 ν)
    (c : ULA.Coupling μ ν) :
    MemLp (fun p : H × H => p.1 - p.2) 2 c.joint := by
  have hx : MemLp (fun p : H × H => p.1) 2 c.joint := by
    have h := hμ
    rw [← c.fst] at h
    exact h.comp_of_map measurable_fst.aemeasurable
  have hy : MemLp (fun p : H × H => p.2) 2 c.joint := by
    have h := hν
    rw [← c.snd] at h
    exact h.comp_of_map measurable_snd.aemeasurable
  exact hx.sub hy

omit [InnerProductSpace ℝ H] [BorelSpace H] [SecondCountableTopology H] in
/-- A finite actual joint law bounds the ordinary real-valued transport
distance without converting infinity to zero. -/
theorem wasserstein_le_finite_coupling (μ ν : Measure H) (c : ULA.Coupling μ ν)
    (hc : ULA.couplingCost c.joint ≠ ⊤) :
    ULA.wasserstein2Real μ ν ≤ (ULA.couplingCost c.joint).toReal :=
  ENNReal.toReal_mono hc (ULA.wasserstein2_le_couplingCost c)

omit [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H] in
/-- The first norm moment is at most the root second moment on a probability
space. Applied to the actual coupling difference, this supplies the
characteristic-function estimate used for separation of transport laws. -/
theorem integral_norm_le_second_cost {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Ω → H) (hD : MemLp D 2 Q) :
    (∫ ω, ‖D ω‖ ∂Q) ≤ (eLpNorm D 2 Q).toReal := by
  have hInt := (hD.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  have hOne : ENNReal.ofReal (∫ ω, ‖D ω‖ ∂Q) = eLpNorm D 1 Q := by
    rw [ofReal_integral_norm_eq_lintegral_enorm hInt,
      eLpNorm_one_eq_lintegral_enorm hD.aestronglyMeasurable]
  have hle : eLpNorm D 1 Q ≤ eLpNorm D 2 Q :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hr := ENNReal.toReal_mono hD.eLpNorm_ne_top hle
  rw [← hOne, ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _)] at hr
  exact hr

/-- The characteristic functions of the two marginal laws are controlled by
the cost of any finite coupling. -/
theorem charFun_norm_sub_le_couplingCost (μ ν : Measure H) [IsProbabilityMeasure μ]
    (c : ULA.Coupling μ ν) (hc : ULA.couplingCost c.joint ≠ ⊤) (t : H) :
    ‖charFun μ t - charFun ν t‖ ≤ ‖t‖ * (ULA.couplingCost c.joint).toReal := by
  let := c.isProbabilityMeasure
  have hD : MemLp (fun p : H × H => p.1 - p.2) 2 c.joint :=
    lt_top_iff_ne_top.mpr hc
  have hInt := (hD.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).norm
  have hb := ULA.charFun_marginals_norm_sub_le c.joint hInt t
  rw [c.fst, c.snd] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (integral_norm_le_second_cost c.joint _ hD) (norm_nonneg _))

/-- Pairing particle i with particle i gives the finite empirical
Wasserstein bound. The proof uses the genuine empirical pair measure and
computes its quadratic transport cost exactly; no particle independence is
assumed. The positive particle count makes the two empirical measures laws. -/
theorem empiricalCloud_wasserstein_sq_le (N : ℕ) (hN : 0 < N)
    (z w : Fin N → H) :
    ULA.wasserstein2Real (Model.empiricalLaw N z) (Model.empiricalLaw N w) ^ 2 ≤
      (N : ℝ)⁻¹ * ∑ i, ‖z i - w i‖ ^ 2 := by
  let Λ := Model.empiricalLaw N (fun i => (z i, w i))
  have hpair := empiricalPair_isCoupling N z w
  let c : ULA.Coupling (Model.empiricalLaw N z) (Model.empiricalLaw N w) :=
    ⟨Λ, hpair.1, hpair.2⟩
  have hΛ : MemLp (fun p : H × H => p.1 - p.2) 2 Λ :=
    (memLp_two_iff_integrable_sq_norm
      (measurable_fst.sub measurable_snd).aestronglyMeasurable).2
      (empiricalLaw_integrable N hN (fun i => (z i, w i)) _)
  have hb := wasserstein_le_finite_coupling _ _ c hΛ.eLpNorm_ne_top
  have hs := couplingCost_sq_eq_integral Λ hΛ
  calc
    _ ≤ (ULA.couplingCost Λ).toReal ^ 2 :=
      (sq_le_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).2 hb
    _ = _ := by rw [hs, integral_empiricalLaw]; rfl

variable [CompleteSpace H]

/-- Zero quadratic transport separates probability laws. The proof chooses
arbitrarily small finite couplings from the defining infimum and compares
characteristic functions; no optimal coupling is assumed. -/
theorem measure_eq_of_wasserstein2_zero (μ ν : Measure H)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hzero : ULA.wasserstein2 μ ν = 0) : μ = ν := by
  apply Measure.ext_of_charFun
  funext t
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := ε / (‖t‖ + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hi : ULA.wasserstein2 μ ν < ENNReal.ofReal δ := by
    rw [hzero]
    exact ENNReal.ofReal_pos.mpr hδ
  obtain ⟨c, hc⟩ := iInf_lt_iff.mp hi
  have hcfin : ULA.couplingCost c.joint ≠ ⊤ := ne_of_lt (hc.trans_le le_top)
  have hcr : (ULA.couplingCost c.joint).toReal < δ := by
    have hh := (ENNReal.toReal_lt_toReal hcfin ENNReal.ofReal_ne_top).mpr hc
    simpa only [ENNReal.toReal_ofReal hδ.le] using hh
  have hb := charFun_norm_sub_le_couplingCost μ ν c hcfin t
  have hb' : ‖charFun μ t - charFun ν t‖ ≤
      (‖t‖ + 1) * (ULA.couplingCost c.joint).toReal := by
    nlinarith [ENNReal.toReal_nonneg (a := ULA.couplingCost c.joint)]
  have hl : ‖charFun μ t - charFun ν t‖ < ε := by
    calc
      _ ≤ (‖t‖ + 1) * (ULA.couplingCost c.joint).toReal := hb'
      _ < (‖t‖ + 1) * δ := mul_lt_mul_of_pos_left hcr (by positivity)
      _ = ε := by dsimp [δ]; field_simp
  simpa only [zero_add] using hl.le

/-- The real transport distance can be used for equality only after its
finiteness has been established explicitly. -/
theorem measure_eq_of_finite_wasserstein2Real_zero (μ ν : Measure H)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hfinite : ULA.wasserstein2 μ ν ≠ ⊤) (hzero : ULA.wasserstein2Real μ ν = 0) :
    μ = ν := by
  apply measure_eq_of_wasserstein2_zero μ ν
  change (ULA.wasserstein2 μ ν).toReal = 0 at hzero
  have h := ENNReal.ofReal_toReal hfinite
  rw [hzero, ENNReal.ofReal_zero] at h
  exact h.symm

end CouplingCost

section InfimumBridge
variable {H : Type*} [NormedAddCommGroup H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- Actual quadratic coupling energies give the condition-number prefactor
after taking the infimum over all initial couplings. The family contains
output joint laws, not a supplied Wasserstein bound or an optimal coupling. -/
theorem wasserstein_decay_of_coupled_energies
    (μ ν μt νt : Measure H)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure μt] [IsProbabilityMeasure νt]
    (hμ : MemLp (fun x : H => x) 2 μ) (hν : MemLp (fun x : H => x) 2 ν)
    (hμt : MemLp (fun x : H => x) 2 μt) (hνt : MemLp (fun x : H => x) 2 νt)
    (lower upper ρ t : ℝ) (hlower : 0 < lower) (hupper : 0 ≤ upper)
    (output : ULA.Coupling μ ν → ULA.Coupling μt νt)
    (initialEnergy finalEnergy : ULA.Coupling μ ν → ℝ)
    (hInitial : ∀ c, initialEnergy c ≤ upper * (ULA.couplingCost c.joint).toReal ^ 2)
    (hFinal : ∀ c, lower * (ULA.couplingCost (output c).joint).toReal ^ 2 ≤ finalEnergy c)
    (hDecay : ∀ c, finalEnergy c ≤ Real.exp (-2 * ρ * t) * initialEnergy c) :
    ULA.wasserstein2Real μt νt ≤ Real.sqrt (upper / lower) * Real.exp (-ρ * t) *
      ULA.wasserstein2Real μ ν := by
  let a : ℝ≥0 := ⟨Real.sqrt (upper / lower) * Real.exp (-ρ * t), by positivity⟩
  have hi := ULA.wasserstein2_ne_top_of_memLp μ ν hμ hν
  have ho := ULA.wasserstein2_ne_top_of_memLp μt νt hμt hνt
  have hs := ULA.wasserstein2_affine_bound_real_of_finite_couplings
    μ ν μt νt a 0 hi ho
  apply (by simpa only [NNReal.coe_zero, add_zero] using hs :
    (∀ c : ULA.Coupling μ ν, ULA.couplingCost c.joint ≠ ⊤ →
      ULA.wasserstein2Real μt νt ≤ (a : ℝ) * (ULA.couplingCost c.joint).toReal) → _)
  intro c _
  have hOutFin := (coupling_difference_memLp μt νt hμt hνt (output c)).eLpNorm_ne_top
  apply (wasserstein_le_finite_coupling μt νt (output c) hOutFin).trans
  have hsq : (ULA.couplingCost (output c).joint).toReal ^ 2 ≤
      (upper / lower) * Real.exp (-2 * ρ * t) * (ULA.couplingCost c.joint).toReal ^ 2 := by
    apply (mul_le_mul_iff_of_pos_left hlower).mp
    have hi' := mul_le_mul_of_nonneg_left (hInitial c) (Real.exp_pos (-2 * ρ * t)).le
    calc
      _ ≤ finalEnergy c := hFinal c
      _ ≤ Real.exp (-2 * ρ * t) * (upper * (ULA.couplingCost c.joint).toReal ^ 2) :=
        (hDecay c).trans hi'
      _ = _ := by field_simp
  change (ULA.couplingCost (output c).joint).toReal ≤
    (Real.sqrt (upper / lower) * Real.exp (-ρ * t)) * (ULA.couplingCost c.joint).toReal
  apply (sq_le_sq₀ ENNReal.toReal_nonneg (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hupper hlower.le)]
  have he : Real.exp (-ρ * t) ^ 2 = Real.exp (-2 * ρ * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact hsq

omit [BorelSpace H] [SecondCountableTopology H] in
/-- Finite couplings whose costs converge to the defining transport
infimum. Attainment of that infimum is unnecessary. -/
theorem exists_coupling_cost_tendsto (μ ν : Measure H)
    (hfinite : ULA.wasserstein2 μ ν ≠ ⊤) :
    ∃ c : ℕ → ULA.Coupling μ ν,
      (∀ n, ULA.couplingCost (c n).joint ≠ ⊤) ∧
      Filter.Tendsto (fun n => (ULA.couplingCost (c n).joint).toReal)
        Filter.atTop (𝓝 (ULA.wasserstein2Real μ ν)) := by
  have hnonneg : 0 ≤ ULA.wasserstein2Real μ ν := ENNReal.toReal_nonneg
  have hex (n : ℕ) : ∃ c : ULA.Coupling μ ν,
      ULA.couplingCost c.joint <
        ENNReal.ofReal (ULA.wasserstein2Real μ ν + 1 / ((n : ℝ) + 1)) := by
    apply iInf_lt_iff.mp
    apply (ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (add_nonneg hnonneg (by positivity))]
    change ULA.wasserstein2Real μ ν < _
    have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  choose c hc using hex
  have hcfin (n : ℕ) : ULA.couplingCost (c n).joint ≠ ⊤ :=
    ne_of_lt ((hc n).trans_le le_top)
  refine ⟨c, hcfin, ?_⟩
  have hlo (n : ℕ) : ULA.wasserstein2Real μ ν ≤
      (ULA.couplingCost (c n).joint).toReal :=
    wasserstein_le_finite_coupling μ ν (c n) (hcfin n)
  have hup (n : ℕ) : (ULA.couplingCost (c n).joint).toReal ≤
      ULA.wasserstein2Real μ ν + 1 / ((n : ℝ) + 1) := by
    have h := (ENNReal.toReal_lt_toReal (hcfin n) ENNReal.ofReal_ne_top).mpr (hc n)
    rw [ENNReal.toReal_ofReal (add_nonneg hnonneg (by positivity))] at h
    exact h.le
  have hz : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hz' : Filter.Tendsto (fun n : ℕ => ULA.wasserstein2Real μ ν +
      1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 (ULA.wasserstein2Real μ ν)) := by
    simpa only [add_zero] using hz.const_add (ULA.wasserstein2Real μ ν)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz' hlo hup

omit [BorelSpace H] [SecondCountableTopology H] in
/-- Any continuous bound in the actual initial coupling cost passes to the
optimal transport infimum. This also supports the mixed deterministic-law
quadratic metric, whose square root is not affine. -/
theorem bound_of_all_finite_couplings (μ ν : Measure H)
    (hfinite : ULA.wasserstein2 μ ν ≠ ⊤) (f : ℝ → ℝ)
    (hf : ContinuousAt f (ULA.wasserstein2Real μ ν)) (b : ℝ)
    (hb : ∀ c : ULA.Coupling μ ν, ULA.couplingCost c.joint ≠ ⊤ →
      b ≤ f (ULA.couplingCost c.joint).toReal) :
    b ≤ f (ULA.wasserstein2Real μ ν) := by
  obtain ⟨c, hc, ht⟩ := exists_coupling_cost_tendsto μ ν hfinite
  exact ge_of_tendsto (hf.tendsto.comp ht) (Filter.Eventually.of_forall fun n => hb (c n) (hc n))

end InfimumBridge

section WeakLaws
variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype I]

/-- The paper's Euclidean product distance between a deterministic full
optimiser state and a sampler law. Its transport component is a genuine
infimum over all couplings. Finiteness is proved in its use below. -/
def optimizerLawDistance (s s' : S) (ν ν' : Measure Z) : ℝ :=
  Real.sqrt (‖s - s'‖ ^ 2 + ULA.wasserstein2Real ν ν' ^ 2)

/-- The full multiplicative-noise weak-generator contraction passes to the
optimal law distance. The process hypothesis is an actual synchronous weak
solution with the specified marginal trajectories for every initial coupling;
it is not an energy inequality or a Wasserstein-bound hypothesis. The
quadratic separation test must explicitly belong to the generator domain. -/
theorem weak_law_contraction
    (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    (tests : Set (Z → ℝ)) (pairTests : Set (Z × Z → ℝ))
    (s s' : ℝ → S) (ν ν' : ℝ → Measure Z)
    [IsProbabilityMeasure (ν 0)] [IsProbabilityMeasure (ν' 0)]
    (hν : MemLp (fun z : Z => z) 2 (ν 0))
    (hν' : MemLp (fun z : Z => z) 2 (ν' 0))
    (hquad : couplingQuadratic D ∈ pairTests)
    (ρ T : ℝ) (hmono : TwistedJointMonotonicity M D ρ)
    (realize : ∀ c : ULA.Coupling (ν 0) (ν' 0),
      ∃ Λ : ℝ → Measure (Z × Z),
        IsCoupledWeakSolution M tests pairTests s s' ν ν' Λ ∧ Λ 0 = c.joint)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    optimizerLawDistance (s t) (s' t) (ν t) (ν' t) ≤
      Real.sqrt D.conditionNumber * Real.exp (-ρ * t) *
        optimizerLawDistance (s 0) (s' 0) (ν 0) (ν' 0) := by
  have hfinite := ULA.wasserstein2_ne_top_of_memLp (ν 0) (ν' 0) hν hν'
  apply bound_of_all_finite_couplings (ν 0) (ν' 0) hfinite
    (fun d => Real.sqrt D.conditionNumber * Real.exp (-ρ * t) *
      Real.sqrt (‖s 0 - s' 0‖ ^ 2 + d ^ 2)) (by fun_prop)
  intro c _
  obtain ⟨Λ, hsol, hΛ⟩ := realize c
  let ct : ULA.Coupling (ν t) (ν' t) :=
    ⟨Λ t, (hsol.coupling t ht.1).1, (hsol.coupling t ht.1).2⟩
  have hνt : MemLp (fun z : Z => z) 2 (ν t) :=
    (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).2
      (hsol.left.second_moment t ht.1)
  have hνt' : MemLp (fun z : Z => z) 2 (ν' t) :=
    (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).2
      (hsol.right.second_moment t ht.1)
  have hct := coupling_difference_memLp (ν t) (ν' t) hνt hνt' ct
  have hb := wasserstein_le_finite_coupling (ν t) (ν' t) ct hct.eLpNorm_ne_top
  have hsq := couplingCost_sq_eq_integral ct.joint hct
  have hmetric : optimizerLawDistance (s t) (s' t) (ν t) (ν' t) ≤
      Real.sqrt (euclideanCouplingEnergy s s' Λ t) := by
    apply Real.sqrt_le_sqrt
    dsimp only [euclideanCouplingEnergy]
    rw [← hsq]
    exact add_le_add (le_refl _) ((sq_le_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).2 hb)
  have hd := hsol.rms_decay D hquad ρ T hmono t ht
  have hinit := couplingCost_sq_eq_integral c.joint
    (coupling_difference_memLp (ν 0) (ν' 0) hν hν' c)
  apply hmetric.trans
  simpa only [euclideanCouplingEnergy, hΛ, ← hinit] using hd

/-- Stationary uniqueness is a law equality, obtained by decay and the
separation property of the transport infimum. Existence of the stationary
weak laws and of their synchronous realizations remains explicit. -/
theorem stationary_weak_laws_unique [CompleteSpace Z]
    (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    (tests : Set (Z → ℝ)) (pairTests : Set (Z × Z → ℝ))
    (s s' : S) (ν ν' : Measure Z)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hν : MemLp (fun z : Z => z) 2 ν) (hν' : MemLp (fun z : Z => z) 2 ν')
    (hquad : couplingQuadratic D ∈ pairTests)
    (ρ : ℝ) (hρ : 0 < ρ) (hmono : TwistedJointMonotonicity M D ρ)
    (realize : ∀ c : ULA.Coupling ν ν',
      ∃ Λ : ℝ → Measure (Z × Z),
        IsCoupledWeakSolution M tests pairTests (fun _ => s) (fun _ => s')
          (fun _ => ν) (fun _ => ν') Λ ∧ Λ 0 = c.joint) :
    s = s' ∧ ν = ν' := by
  have hd : optimizerLawDistance s s' ν ν' = 0 :=
    stationary_distance_zero (Real.sqrt_nonneg _) hρ (fun t ht =>
      weak_law_contraction M D tests pairTests (fun _ => s) (fun _ => s')
        (fun _ => ν) (fun _ => ν') hν hν' hquad ρ t hmono realize t ⟨ht, le_rfl⟩)
  have hs := Real.sq_sqrt (add_nonneg (sq_nonneg ‖s - s'‖)
    (sq_nonneg (ULA.wasserstein2Real ν ν')))
  change optimizerLawDistance s s' ν ν' ^ 2 = _ at hs
  rw [hd, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hs
  have hn : ‖s - s'‖ = 0 := by nlinarith [sq_nonneg (ULA.wasserstein2Real ν ν')]
  have hw : ULA.wasserstein2Real ν ν' = 0 := by nlinarith [sq_nonneg ‖s - s'‖]
  exact ⟨sub_eq_zero.mp (norm_eq_zero.mp hn),
    measure_eq_of_finite_wasserstein2Real_zero ν ν'
      (ULA.wasserstein2_ne_top_of_memLp ν ν' hν hν') hw⟩

end WeakLaws

namespace LipschitzDynamics
variable {Ω A Z G H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  (D : PBGSO.LipschitzDynamics A Z G)

/-- Constructed actual general additive integral solutions contract their
deterministic optimiser and sampler laws. The initial sampler cost here is
the selected L² coupling. Optimising that cost across law-preserving
realisations is performed separately by `bound_of_all_finite_couplings`.
The norm on the Banach product is the maximum norm, made explicit by `max`. -/
theorem exists_contracting_pair_laws (initial other : A × Lp Z 2 Q)
    (B : ℝ → Lp Z 2 Q) (hB : Continuous B) (hB0 : B 0 = 0)
    (C : (A × Lp Z 2 Q) →L[ℝ] H) (ρ lower upper : ℝ)
    (hlower : 0 < lower) (hupper : 0 ≤ upper)
    (hLower : ∀ x, lower * ‖x‖ ^ 2 ≤ ‖C x‖ ^ 2)
    (hUpper : ∀ x, ‖C x‖ ^ 2 ≤ upper * ‖x‖ ^ 2)
    (hJoint : ∀ x y,
      inner ℝ (C (x - y)) (C (D.field Q x - D.field Q y)) ≤
        -ρ * ‖C (x - y)‖ ^ 2)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ Y W : ℝ → A × Lp Z 2 Q,
      Continuous Y ∧ Continuous W ∧ Y 0 = initial ∧ W 0 = other ∧
      (∀ t ∈ Icc 0 T, Y t - initial =
        (∫ r in 0..t, D.field Q (Y r)) + (0, B t)) ∧
      (∀ t ∈ Icc 0 T, W t - other =
        (∫ r in 0..t, D.field Q (W r)) + (0, B t)) ∧
      (∀ t ∈ Icc 0 T,
        max ‖(Y t).1 - (W t).1‖
          (ULA.wasserstein2Real (Q.map (Y t).2) (Q.map (W t).2)) ≤
        Real.sqrt (upper / lower) * Real.exp (-ρ * t) *
          max ‖initial.1 - other.1‖ ‖initial.2 - other.2‖) := by
  obtain ⟨Y, W, hY, hW, hYi, hWi, heY, heW, hd⟩ :=
    D.exists_contracting_pair Q initial other B hB hB0 C ρ lower upper hlower hupper
      hLower hUpper hJoint T hT
  refine ⟨Y, W, hY, hW, hYi, hWi, heY, heW, ?_⟩
  intro t ht
  have hLaw := ULA.wasserstein2_le_Lp_cost_real Q (Y t).2 (W t).2
  have hA : ‖(Y t).1 - (W t).1‖ ≤ ‖Y t - W t‖ := norm_fst_le (Y t - W t)
  have hZ : ‖(Y t).2 - (W t).2‖ ≤ ‖Y t - W t‖ := norm_snd_le (Y t - W t)
  have hb := max_le (hA.trans (hd t ht)) ((hLaw.trans hZ).trans (hd t ht))
  simpa only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub] using hb

end LipschitzDynamics
end PBGSO
