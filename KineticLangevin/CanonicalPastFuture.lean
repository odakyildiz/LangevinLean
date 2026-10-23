import KineticLangevin.PastFutureIndependence

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types true
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace KineticLangevin

/-- A finite random recursion depends only on the innovations used before its terminal index. -/
theorem noiseDrivenChain_eq_of_prefix {E Z : Type*} (step : E → Z → E)
    (z : E) (W N : ℕ → Z) (n : ℕ) (heq : ∀ k < n,W k=N k) :
    ULA.noiseDrivenChain step z W n=ULA.noiseDrivenChain step z N n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ULA.noiseDrivenChain_succ,ih (fun k hk => heq k (Nat.lt_trans hk (Nat.lt_succ_self n))),
      heq n (Nat.lt_succ_self n)]

/-- The deterministic splitting recursion depends only on the noise entries used before its endpoint. -/
theorem kineticSplitNoiseChain_eq_of_prefix {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → E) (γ h : ℝ) (z : E×E) (W N : ℕ → E) (n : ℕ) (heq : ∀ k<n,W k=N k) :
    kineticSplitNoiseChain g γ h z W n=kineticSplitNoiseChain g γ h z N n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [kineticSplitNoiseChain,ih (fun k hk => heq k (Nat.lt_trans hk (Nat.lt_succ_self n))),
      heq n (Nat.lt_succ_self n)]

namespace GenericCanonicalCoupling
open BrownianConvolution
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {μ π : Measure (H ι)} [IsProbabilityMeasure μ]
local instance pastFuture_couplingProbability (c : ULA.Coupling μ π) : IsProbabilityMeasure c.joint := c.isProbabilityMeasure

/-- The lifted actual segment convolution has its original pointwise Brownian representative. -/
theorem inputLift_coe (c : ULA.Coupling μ π) (γ : ℝ)
    (Z : Lp (H ι) 2 (ULA.CanonicalBrownian.vectorProbability ι)) :
    inputLift c γ Z =ᵐ[probability c] fun p : Sample ι => Real.sqrt (2*γ) • Z p.2.2 := by
  filter_upwards [Lp.coeFn_smul (Real.sqrt (2*γ)) (brownianLift c Z),brownianLift_coe c Z]
    with p hsm hb
  change (Real.sqrt (2*γ) • brownianLift c Z : Lp (H ι) 2 (probability c)) p = _
  rw [hsm,Pi.smul_apply,hb]

/-- A genuine past splitting approximation is independent of an arbitrary future exponential convolution. -/
theorem splitChain_velocity_future_independent (c : ULA.Coupling μ π)
    (hπ : MemLp (id : H ι → H ι) 2 π) (f : H ι → ℝ) (M γ : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (a r : ℝ≥0) (n : ℕ) :
    IndepFun ((kineticSplitChain (ULA.lpDrift (probability c) (gradient f) hLip) γ
      ((a : ℝ)/((n+1 : ℕ) : ℝ)) (referenceInitial c hπ) (globalInput c γ) (n+1)).1)
      (inputLift c γ (vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) a r)) (probability c) := by
  let h : ℝ≥0 := a/((n+1 : ℕ) : ℝ≥0)
  let starts : ℕ → ℝ≥0 := fun k => ((min k n : ℕ) : ℝ≥0)*h
  let W : ULA.CanonicalBrownian.VectorSample ι → ℕ → H ι := fun ω k =>
    vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) (starts k) h ω
  let F : ULA.CanonicalBrownian.VectorSample ι → H ι := vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) a r
  have hW : Measurable W := measurable_pi_iff.mpr (fun _ => (Lp.stronglyMeasurable _).measurable)
  have hF : Measurable F := (Lp.stronglyMeasurable _).measurable
  have hh : ((n+1 : ℕ) : ℝ≥0)*h=a := by
    dsimp [h]
    exact mul_div_cancel₀ a (by exact_mod_cast Nat.succ_ne_zero n)
  have hends (k : ℕ) : starts k+h≤a := by
    calc
      starts k+h=(((min k n : ℕ) : ℝ≥0)+1)*h := by dsimp [starts];ring
      _ ≤ (((n+1 : ℕ) : ℝ≥0))*h := by
        gcongr
        exact_mod_cast Nat.succ_le_succ (Nat.min_le_right k n)
      _ = a := hh
  have hiB : IndepFun W F (ULA.CanonicalBrownian.vectorProbability ι) :=
    vectorSegments_future_independent ι (fun _ : ℕ => psi γ 0) (fun _ => continuous_psi γ 0)
      starts (fun _ => h) a r hends (psi γ 0) (continuous_psi γ 0)
  let A := ((H ι × H ι) × H ι)
  let ν : Measure A := c.joint.prod (stdGaussian (H ι))
  letI : IsProbabilityMeasure ν := by dsimp [ν];infer_instance
  have hiP := indepFun_prod_initial_of_indep ν (ULA.CanonicalBrownian.vectorProbability ι) W F hW hF hiB
  have hsource : MeasurePreserving (fun p : Sample ι => ((p.1,p.2.1),p.2.2))
      (probability c) (ν.prod (ULA.CanonicalBrownian.vectorProbability ι)) :=
    MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc c.joint (stdGaussian (H ι)) (ULA.CanonicalBrownian.vectorProbability ι))
  have hiSource := indepFun_comp_measurePreserving _ _
    (measurable_fst.prodMk (hW.comp measurable_snd)) (hF.comp measurable_snd) hiP _ hsource
  let chainFun : A × (ℕ → H ι) → H ι := fun p =>
    (ULA.noiseDrivenChain (kineticSplitStep (gradient f) γ h) (p.1.2,p.1.1.2)
      (fun k => Real.sqrt (2*(γ : ℝ)) • p.2 k) (n+1)).1
  have hchainFun : Measurable chainFun := by
    have hstep : Measurable (Function.uncurry (kineticSplitStep (gradient f) (γ : ℝ) (h : ℝ))) :=
      kineticSplitStep_measurable (gradient f) hLip.continuous γ h
    have hc : Measurable (fun p : (H ι×H ι)×(ℕ→H ι) =>
        ULA.noiseDrivenChain (kineticSplitStep (gradient f) (γ : ℝ) (h : ℝ)) p.1 p.2 (n+1)) :=
      ULA.noiseDrivenChain_measurable (kineticSplitStep (gradient f) (γ : ℝ) (h : ℝ)) hstep (n+1)
    have hi : Measurable (fun p : A×(ℕ→H ι) => (p.1.2,p.1.1.2)) := by
      exact measurable_fst.snd.prodMk measurable_fst.fst.snd
    have hn : Measurable (fun p : A×(ℕ→H ι) => fun k => Real.sqrt (2*(γ : ℝ)) • p.2 k) := by
      apply measurable_pi_iff.mpr
      intro k
      have hv : Measurable (fun p : A×(ℕ→H ι) => p.2 k) :=
        (measurable_pi_apply k).comp measurable_snd
      exact hv.const_smul (Real.sqrt (2*(γ : ℝ)))
    have hproj : Measurable (Prod.fst : H ι×H ι → H ι) := measurable_fst
    have hcomp := hproj.comp (hc.comp (hi.prodMk hn))
    convert hcomp using 1
    funext p
    rfl
  have hiRaw := ProbabilityTheory.IndepFun.comp hiSource hchainFun
    (show Measurable (fun x : H ι => Real.sqrt (2*(γ : ℝ)) • x) by fun_prop)
  let N : ℕ → Lp (H ι) 2 (probability c) := fun k => inputLift c γ
    (vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) (starts k) h)
  let S := kineticSplitNoiseChain (ULA.lpDrift (probability c) (gradient f) hLip) γ h
    (referenceInitial c hπ) N (n+1)
  have hN := ae_all_iff.mpr (fun k => inputLift_coe c γ
    (vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) (starts k) h))
  have hS : S.1 =ᵐ[probability c] fun p : Sample ι =>
      chainFun ((p.1,p.2.1),W p.2.2) := by
    filter_upwards [lp_kineticSplitNoiseChain_coe (probability c) (gradient f) M hLip γ h
      (referenceInitial c hπ) N (n+1),referenceInitial_coe c hπ,hN] with p hs hi hn
    have hn' : (fun k => N k p)=(fun k => Real.sqrt (2*(γ : ℝ)) • W p.2.2 k) := funext hn
    have he := congrArg Prod.fst hs
    change S.1 p = _ at he
    rw [hi,hn',kineticSplitNoiseChain_eq_noiseDrivenChain] at he
    exact he
  have hfuture := inputLift_coe c γ (vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) a r)
  have hiS : IndepFun S.1 (inputLift c γ (vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) a r))
      (probability c) := ProbabilityTheory.IndepFun.congr hiRaw hS.symm hfuture.symm
  have heS : kineticSplitChain (ULA.lpDrift (probability c) (gradient f) hLip) γ h
      (referenceInitial c hπ) (globalInput c γ) (n+1)=S := by
    rw [kineticSplitChain_eq_noiseChain]
    change kineticSplitNoiseChain _ _ _ _ _ _ = kineticSplitNoiseChain _ _ _ _ _ _
    apply kineticSplitNoiseChain_eq_of_prefix
    intro k hk
    rw [ouInputIncrement_globalInput c γ γ.coe_nonneg h k]
    have hmin : min k n=k := Nat.min_eq_left (Nat.le_of_lt_succ hk)
    simp only [N,starts,hmin,filtered,Real.toNNReal_coe]
  have hhR : (h : ℝ)=(a : ℝ)/((n+1 : ℕ) : ℝ) := by simp only [h,NNReal.coe_div,NNReal.coe_natCast]
  rw [← hhR,heS]
  exact hiS

/-- The actual continuous reference velocity depends only on initial data and past Brownian noise. -/
theorem globalReferenceFlow_velocity_future_independent (c : ULA.Coupling μ π)
    (hπ : MemLp (id : H ι → H ι) 2 π) (f : H ι → ℝ) (M γ : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (T : ℝ) (hT : 0 ≤ T)
    (a r : ℝ≥0) (ha : (a : ℝ) ≤ T) :
    IndepFun ((globalReferenceFlow c hπ f M γ hLip T hT a).1)
      (inputLift c γ (vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) a r)) (probability c) := by
  let Y := globalReferenceFlow c hπ f M γ hLip T hT
  let G := ULA.lpDrift (probability c) (gradient f) hLip
  have hs := globalReferenceFlow_spec c hπ f M γ hLip T hT
  have hlim := kineticSplitChain_tendsto G M γ (ULA.lpDrift_lipschitz _ _ hLip)
    (referenceInitial c hπ) (globalInput c γ) Y (continuous_globalInput c γ) (globalInput_zero c γ)
    hs.1 a a.coe_nonneg (fun t ht => by
      simpa only [Y,hs.2.1] using hs.2.2 t ⟨ht.1,ht.2.trans ha⟩)
  exact indepFun_of_tendsto_Lp (probability c) _ _ _
    ((continuous_fst.tendsto (Y a)).comp hlim)
    (fun n => splitChain_velocity_future_independent c hπ f M γ hLip a r n)

/-- The actual future convolution on the coupling extension has its exact thermal Gaussian law. -/
theorem futureInput_hasLaw (c : ULA.Coupling μ π) (γ : ℝ) (hγ : 0 ≤ γ) (a r : ℝ≥0) :
    HasLaw (inputLift c γ (vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) a r))
      ((stdGaussian (H ι)).map (fun x => Real.sqrt (1-(psi γ 0 r)^2) • x)) (probability c) := by
  have hsource : MeasurePreserving (fun p : Sample ι => p.2.2) (probability c)
      (ULA.CanonicalBrownian.vectorProbability ι) :=
    (measurePreserving_snd : MeasurePreserving Prod.snd (GenericCanonicalSource.canonicalSourceProbability ι)
      (ULA.CanonicalBrownian.vectorProbability ι)).comp
      (measurePreserving_snd : MeasurePreserving Prod.snd (probability c) (GenericCanonicalSource.canonicalSourceProbability ι))
  have hl := (vectorOU_hasLaw ι γ hγ a r).comp hsource.hasLaw
  have he : inputLift c γ (vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) a r) =
      brownianLift c (Real.sqrt (2*γ) • vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) a r) := by
    simp only [inputLift,smul_apply,map_smul]
  rw [he]
  exact hl.congr (brownianLift_coe c _)

/-- The true reference velocity and the true next-interval OU convolution have the exact independent Gaussian joint law. -/
theorem globalReferenceFlow_velocity_future_jointLaw
    (f : H ι → ℝ) (m : ℝ) (hm : 0 < m) (M γ : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith M (gradient f))
    (c : ULA.Coupling μ (ULA.gibbsMeasure f))
    (hπ : MemLp (id : H ι → H ι) 2 (ULA.gibbsMeasure f))
    (T : ℝ) (hT : 0 ≤ T) (a r : ℝ≥0) (ha : (a : ℝ) ≤ T) :
    HasLaw (fun ω => ((globalReferenceFlow c hπ f M γ hLip T hT a).1 ω,
      inputLift c γ (vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) a r) ω))
      ((stdGaussian (H ι)).prod ((stdGaussian (H ι)).map (fun x => Real.sqrt (1-(psi γ 0 r)^2) • x)))
      (probability c) := by
  letI := ULA.isProbabilityMeasure_gibbsMeasure f m hm hf hsc
  have hs := globalReferenceFlow_stationary f m hm M γ hf hsc hLip c hπ T hT a ⟨a.coe_nonneg,ha⟩
  have hv := (measurePreserving_fst : MeasurePreserving Prod.fst
    (kineticGibbsTarget f) (stdGaussian (H ι))).hasLaw.comp hs
  exact (globalReferenceFlow_velocity_future_independent c hπ f M γ hLip T hT a r ha).hasLaw_prod
    hv (futureInput_hasLaw c γ γ.coe_nonneg a r)

/-- At every KLMC grid point the reference-chain velocity is independent of the actual following OU convolution. -/
theorem referenceChain_velocity_future_jointLaw
    (f : H ι → ℝ) (m : ℝ) (hm : 0 < m) (M γ : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith M (gradient f))
    (c : ULA.Coupling μ (ULA.gibbsMeasure f))
    (hπ : MemLp (id : H ι → H ι) 2 (ULA.gibbsMeasure f)) (h : ℝ≥0) (n : ℕ) (r : ℝ≥0) :
    HasLaw (fun ω => ((referenceChain c hπ f M γ hLip h n).1 ω,
      inputLift c γ (vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) r) ω))
      ((stdGaussian (H ι)).prod ((stdGaussian (H ι)).map (fun x => Real.sqrt (1-(psi γ 0 r)^2) • x)))
      (probability c) := by
  let a : ℝ≥0 := (n : ℝ≥0)*h
  have ha : (a : ℝ)=(n : ℝ)*(h : ℝ) := rfl
  rw [referenceChain_eq_globalReferenceFlow c hπ f M γ hLip h a a.coe_nonneg n (by rw [ha])]
  exact globalReferenceFlow_velocity_future_jointLaw f m hm M γ hf hsc hLip c hπ a a.coe_nonneg a r le_rfl

end GenericCanonicalCoupling
end KineticLangevin
