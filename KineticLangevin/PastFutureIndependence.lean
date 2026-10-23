import KineticLangevin.GenericCanonicalKLMC
import KineticLangevin.LpPhaseLaw
import Mathlib.Probability.Independence.CharacteristicFunction

noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace KineticLangevin.BrownianConvolution

/-- Regrouping an independent rectangular array preserves independence of its rows. -/
theorem iIndepFun_curry {Ω I J : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {E : Type*} [MeasurableSpace E] (X : I → J → Ω → E)
    (hX : ∀ i j,Measurable (X i j))
    (hi : iIndepFun (fun p : I×J => X p.1 p.2) P) :
    iIndepFun (fun i ω j => X i j ω) P := by
  have hs := hi.precomp (Equiv.sigmaEquivProd I J).injective
  have hl := hs.map_fun_eq_infinitePi_map (fun p : (i : I)×J => hX p.1 p.2)
  have hc : HasLaw (MeasurableEquiv.piCurry (fun (_ : I) (_ : J) => E))
      (Measure.infinitePi (fun i => Measure.infinitePi (fun j => P.map (X i j))))
      (Measure.infinitePi (fun p : (i : I)×J => P.map (X p.1 p.2))) :=
    ⟨(MeasurableEquiv.piCurry _).measurable.aemeasurable,
      Measure.infinitePi_map_piCurry (fun i j => P.map (X i j))⟩
  have hj := hc.comp (⟨(measurable_pi_iff.mpr (fun p : (i : I)×J => hX p.1 p.2)).aemeasurable,hl⟩ :
    HasLaw (fun (ω : Ω) (p : (i : I)×J) => X p.1 p.2 ω) _ P)
  exact iIndepFun_comp_hasLaw (fun i (ω : ∀ i : I,J → E) => ω i)
    (fun i => measurable_pi_apply i) (fun ω i j => X i j ω)
    (measurable_pi_iff.mpr (fun i => measurable_pi_iff.mpr (hX i))) hj
    (iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id))

/-- Past Brownian values and a future deterministic convolution form independent scalar blocks. -/
theorem scalarSegments_future_independent {κ : Type*}
    (kernels : κ → ℝ → ℝ) (hks : ∀ j,Continuous (kernels j))
    (starts durations : κ → ℝ≥0) (a r : ℝ≥0) (htimes : ∀ j,starts j+durations j ≤ a)
    (k : ℝ → ℝ) (hk : Continuous k) :
    iIndepFun (fun b : Bool => fun ω : Sample => fun j : κ => if b then segmentConvolutionLp k hk a r ω
      else segmentConvolutionLp (kernels j) (hks j) (starts j) (durations j) ω) probability := by
  let K : ((b : Bool) × κ) → TimeHilbert := fun p => if p.1 then segmentKernelLp k hk a r
    else segmentKernelLp (kernels p.2) (hks p.2) (starts p.2) (durations p.2)
  have hg : IsGaussianProcess (fun p : (b : Bool)×κ => fun ω =>
      ULA.GaussianHilbert.isonormal ULA.CanonicalBrownian.basis (K p) ω) probability :=
    ULA.isGaussianProcess_of_linearMap_Lp probability
      (ULA.GaussianHilbert.isonormal ULA.CanonicalBrownian.basis).toLinearMap
      (ULA.GaussianHilbert.isonormal_hasGaussianLaw ULA.CanonicalBrownian.basis) K
  have he : (fun p : (b : Bool)×κ => fun ω =>
      ULA.GaussianHilbert.isonormal ULA.CanonicalBrownian.basis (K p) ω) =
      (fun p : (b : Bool)×κ => fun ω => if p.1 then segmentConvolutionLp k hk a r ω
        else segmentConvolutionLp (kernels p.2) (hks p.2) (starts p.2) (durations p.2) ω) := by
    funext p ω
    rcases p with ⟨b,j⟩
    cases b <;> rfl
  rw [he] at hg
  apply IsGaussianProcess.iIndepFun_of_covariance_eq_zero
    (X := fun (b : Bool) (j : κ) (ω : Sample) => if b then segmentConvolutionLp k hk a r ω
      else segmentConvolutionLp (kernels j) (hks j) (starts j) (durations j) ω)
    hg (fun b j => by cases b <;> exact (Lp.aestronglyMeasurable _).aemeasurable)
  intro b c hbc i j
  cases b <;> cases c
  · exact (hbc rfl).elim
  · exact segmentConvolutionLp_covariance_zero _ _ _ _ (starts i) (durations i) a r (htimes i)
  · rw [covariance_comm]
    exact segmentConvolutionLp_covariance_zero _ _ _ _ (starts j) (durations j) a r (htimes j)
  · exact (hbc rfl).elim

/-- All spatial copies of the past and future scalar blocks remain independent after regrouping. -/
theorem vectorSegments_future_blocks_independent {κ : Type*} (ι : Type*)
    (kernels : κ → ℝ → ℝ) (hks : ∀ j,Continuous (kernels j))
    (starts durations : κ → ℝ≥0) (a r : ℝ≥0) (htimes : ∀ j,starts j+durations j ≤ a)
    (k : ℝ → ℝ) (hk : Continuous k) :
    iIndepFun (fun b : Bool => fun ω : ULA.CanonicalBrownian.VectorSample ι =>
      fun (i : ι) (j : κ) => if b then segmentConvolutionLp k hk a r (ω i)
      else segmentConvolutionLp (kernels j) (hks j) (starts j) (durations j) (ω i))
      (ULA.CanonicalBrownian.vectorProbability ι) := by
  let X := fun (i : ι) (b : Bool) (ω : ULA.CanonicalBrownian.VectorSample ι) (j : κ) =>
    if b then segmentConvolutionLp k hk a r (ω i)
    else segmentConvolutionLp (kernels j) (hks j) (starts j) (durations j) (ω i)
  have hm : ∀ i b,Measurable (X i b) := by
    intro i b
    apply measurable_pi_iff.mpr
    intro j
    cases b <;> exact (Lp.stronglyMeasurable _).measurable.comp (measurable_pi_apply i)
  have hi : iIndepFun (fun p : ι×Bool => X p.1 p.2) (ULA.CanonicalBrownian.vectorProbability ι) := by
    apply iIndepFun_uncurry' hm
    · exact iIndepFun_infinitePi (X := fun _ ω (b : Bool) j => if b then segmentConvolutionLp k hk a r ω
        else segmentConvolutionLp (kernels j) (hks j) (starts j) (durations j) ω)
        (fun _ => measurable_pi_iff.mpr (fun b : Bool => measurable_pi_iff.mpr (fun j => by
          cases b <;> exact (Lp.stronglyMeasurable _).measurable)))
    · intro i
      exact iIndepFun_comp_hasLaw _ (fun b : Bool => measurable_pi_iff.mpr (fun j => by
        cases b <;> exact (Lp.stronglyMeasurable _).measurable))
        (fun ω : ULA.CanonicalBrownian.VectorSample ι => ω i) (measurable_pi_apply i)
        (measurePreserving_eval_infinitePi (fun _ : ι => probability) i).hasLaw
        (scalarSegments_future_independent kernels hks starts durations a r htimes k hk)
  have hs := hi.precomp (g := fun p : Bool×ι => (p.2,p.1))
    (by intro p q hp;cases p;cases q;simp_all)
  exact iIndepFun_curry (fun b i => X i b) (fun b i => hm i b) hs

/-- Any finite set of actual past Brownian vectors is independent of every actual future convolution. -/
theorem vectorSegments_future_independent {κ : Type*} [Countable κ] [Nonempty κ]
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (kernels : κ → ℝ → ℝ) (hks : ∀ j,Continuous (kernels j))
    (starts durations : κ → ℝ≥0) (a r : ℝ≥0) (htimes : ∀ j,starts j+durations j ≤ a)
    (k : ℝ → ℝ) (hk : Continuous k) :
    IndepFun (fun ω : ULA.CanonicalBrownian.VectorSample ι =>
      fun j => vectorSegmentLp ι (kernels j) (hks j) (starts j) (durations j) ω) (vectorSegmentLp ι k hk a r)
      (ULA.CanonicalBrownian.vectorProbability ι) := by
  classical
  have hi := (vectorSegments_future_blocks_independent ι kernels hks starts durations a r htimes k hk).indepFun
    (by decide : false ≠ true)
  let pastPack : (ι → κ → ℝ) → κ → EuclideanSpace ℝ ι :=
    fun x j => WithLp.toLp 2 (fun i => x i j)
  let futurePack : (ι → κ → ℝ) → EuclideanSpace ℝ ι :=
    fun x => WithLp.toLp 2 (fun i => x i (Classical.choice inferInstance))
  have hp := ProbabilityTheory.IndepFun.comp hi (show Measurable pastPack by fun_prop) (show Measurable futurePack by fun_prop)
  have hpast : (fun ω => pastPack (fun i j => segmentConvolutionLp (kernels j) (hks j) (starts j) (durations j) (ω i)))
      =ᵐ[ULA.CanonicalBrownian.vectorProbability ι] fun ω j => vectorSegmentLp ι (kernels j) (hks j) (starts j) (durations j) ω := by
    have hs := ae_all_iff.mpr (fun j => spatialLift_coe ι
      (segmentConvolutionLp (kernels j) (hks j) (starts j) (durations j)))
    filter_upwards [hs] with ω hω
    funext j
    exact (hω j).symm
  have hfuture : (fun ω => futurePack (fun i (_ : κ) => segmentConvolutionLp k hk a r (ω i)))
      =ᵐ[ULA.CanonicalBrownian.vectorProbability ι] vectorSegmentLp ι k hk a r :=
    (spatialLift_coe ι (segmentConvolutionLp k hk a r)).symm
  exact ProbabilityTheory.IndepFun.congr hp hpast hfuture

end KineticLangevin.BrownianConvolution

namespace KineticLangevin

/-- Independence is preserved by an actual measure-preserving source projection. -/
theorem indepFun_comp_measurePreserving {Ω Ξ A B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace A] [MeasurableSpace B]
    {P : Measure Ω} {Q : Measure Ξ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : Ξ → A) (Y : Ξ → B) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y Q) (φ : Ω → Ξ) (hφ : MeasurePreserving φ P Q) :
    IndepFun (X ∘ φ) (Y ∘ φ) P := by
  apply (indepFun_iff_map_prod_eq_prod_map_map (hX.comp hφ.measurable).aemeasurable
    (hY.comp hφ.measurable).aemeasurable).mpr
  have he := hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable
  rw [← hφ.map_eq] at he
  simp only [Measure.map_map hX hφ.measurable,Measure.map_map hY hφ.measurable,
    Measure.map_map (hX.prodMk hY) hφ.measurable] at he
  exact he

/-- Adjoining an independent initial coordinate preserves independence from the future block. -/
theorem indepFun_prod_initial_of_indep {Ω A E F : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure A) (P : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (X : Ω → E) (Y : Ω → F) (hX : Measurable X) (hY : Measurable Y) (hi : IndepFun X Y P) :
    IndepFun (fun p : A×Ω => (p.1,X p.2)) (fun p : A×Ω => Y p.2) (μ.prod P) := by
  haveI : IsProbabilityMeasure (P.map X) := (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).mpr inferInstance
  haveI : IsProbabilityMeasure (P.map Y) := (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).mpr inferInstance
  have hp : MeasurePreserving (fun ω => (X ω,Y ω)) P ((P.map X).prod (P.map Y)) :=
    ⟨hX.prodMk hY,hi.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable⟩
  have hs := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μ (P.map X) (P.map Y))
  have hz := hs.comp ((MeasurePreserving.id μ).prod hp)
  exact indepFun_comp_measurePreserving Prod.fst Prod.snd measurable_fst measurable_snd
    (indepFun_prod (X := id) (Y := id) measurable_id measurable_id)
    (fun p : A×Ω => ((p.1,X p.2),Y p.2)) hz

section LpLimit
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- The actual dual characteristic function is continuous in an L² random vector. -/
theorem continuous_charFunDual_map_Lp (L : E →L[ℝ] ℝ) :
    Continuous (fun X : Lp E 2 P => charFunDual (P.map X) L) := by
  have hc := (ULA.continuous_charFun_map_Lp P (1 : ℝ)).comp (L.compLpL 2 P).continuous
  convert hc using 1
  funext X
  rw [charFunDual_eq_charFun_map_one,Measure.map_map L.continuous.measurable (Lp.stronglyMeasurable X).measurable]
  congr 1
  exact Measure.map_congr (ContinuousLinearMap.coeFn_compLpL L X).symm

/-- Independence of the same future random vector is closed under genuine L² convergence of the past. -/
theorem indepFun_of_tendsto_Lp (Xn : ℕ → Lp E 2 P) (X Y : Lp E 2 P)
    (hX : Tendsto Xn atTop (𝓝 X)) (hi : ∀ n,IndepFun (Xn n) Y P) :
    IndepFun X Y P := by
  apply (indepFun_iff_charFunDual_prod (Lp.aestronglyMeasurable X).aemeasurable
    (Lp.aestronglyMeasurable Y).aemeasurable).mpr
  intro L
  have hpair : Tendsto (fun n => (Xn n,Y)) atTop (𝓝 (X,Y)) := hX.prodMk_nhds tendsto_const_nhds
  have hactual := ((continuous_charFunDual_map_lpPhase P L).tendsto (X,Y)).comp hpair
  have htarget := (((continuous_charFunDual_map_Lp P (L.comp (ContinuousLinearMap.inl ℝ E E))).tendsto X).comp hX).mul
    (tendsto_const_nhds (x := charFunDual (P.map Y) (L.comp (ContinuousLinearMap.inr ℝ E E))))
  have he (n : ℕ) := (indepFun_iff_charFunDual_prod (Lp.aestronglyMeasurable (Xn n)).aemeasurable
    (Lp.aestronglyMeasurable Y).aemeasurable).mp (hi n) L
  exact tendsto_nhds_unique hactual (htarget.congr' (Eventually.of_forall (fun n => (he n).symm)))

end LpLimit
end KineticLangevin
