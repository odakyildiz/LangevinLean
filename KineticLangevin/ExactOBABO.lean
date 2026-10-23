import KineticLangevin.CanonicalStationarity
import KineticLangevin.GibbsTarget
import KineticLangevin.LpHamiltonianLaw

/-! # The exact Gibbs-preserving O--Hamiltonian--O comparison map -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace KineticLangevin
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- Replace only the Verlet portion of the actual OBABO step by the proved
exact Hamiltonian flow, retaining exactly the same two thermostat inputs. -/
def exactObaboStep (f : E → ℝ) (M : ℝ≥0) (hLip : LipschitzWith M (gradient f))
    (h : ℝ) (hh : 0≤h) (δ σ : ℝ) (z : E×E) (ξ : E×E) : E×E :=
  ornsteinStep δ σ ξ.2
    (hamiltonianFlow f M hLip h hh (ornsteinStep δ σ ξ.1 z) h)

theorem exactObaboStep_continuous (f : E → ℝ) (M : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (h : ℝ) (hh : 0≤h) (δ σ : ℝ) :
    Continuous (Function.uncurry (exactObaboStep f M hLip h hh δ σ)) := by
  have hc := hamiltonianFlow_endpoint_continuous f M hLip h hh
  unfold Function.uncurry exactObaboStep ornsteinStep
  fun_prop

/-- After the first thermostat, the updated phase still has its actual Gibbs
law and remains independent of the second fresh Gaussian vector. -/
theorem firstThermostat_joint_fresh
    (f : E → ℝ) (m : ℝ) (hm : 0<m) (hf : Differentiable ℝ f)
    (hsc : StrongConvexOn univ m f) (δ σ : ℝ) (hvariance : δ^2+σ^2=1) :
    ((kineticGibbsTarget f).prod ((stdGaussian E).prod (stdGaussian E))).map
      (fun p ↦ (ornsteinStep δ σ p.2.1 p.1,p.2.2)) =
        (kineticGibbsTarget f).prod (stdGaussian E) := by
  haveI := kineticGibbsTarget_probability f m hm hf hsc
  let π := kineticGibbsTarget f
  let G := stdGaussian E
  have hOU : Measurable (fun p : (E×E)×E ↦ ornsteinStep δ σ p.2 p.1) := by
    unfold ornsteinStep
    fun_prop
  have hfirst : (π.prod G).map (fun p ↦ ornsteinStep δ σ p.2 p.1)=π :=
    thermostat_preserves_target f m hm hf hsc δ σ hvariance
  have hAssoc := (measurePreserving_prodAssoc π G G).map_eq
  change (π.prod (G.prod G)).map _ = π.prod G
  rw [← hAssoc,Measure.map_map (by unfold ornsteinStep; fun_prop)
    MeasurableEquiv.prodAssoc.measurable]
  have hp := Measure.map_prod_map (π.prod G) G hOU measurable_id
  rw [hfirst,Measure.map_id] at hp
  change (((π.prod G).prod G).map (fun p ↦ (ornsteinStep δ σ p.1.2 p.1.1,p.2))) = _
  simpa only [Prod.map_def,id_eq] using hp.symm

/-- The actual exact O--Hamiltonian--O random map preserves the normalized
Gaussian-times-Gibbs target under the original potential assumptions. -/
theorem exactObaboStep_preserves_target
    (f : E → ℝ) (m : ℝ) (hm : 0<m) (M : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (h : ℝ) (hh : 0≤h)
    (δ σ : ℝ) (hvariance : δ^2+σ^2=1) :
    ((kineticGibbsTarget f).prod ((stdGaussian E).prod (stdGaussian E))).map
      (Function.uncurry (exactObaboStep f M hLip h hh δ σ)) = kineticGibbsTarget f := by
  haveI := kineticGibbsTarget_probability f m hm hf hsc
  let π := kineticGibbsTarget f
  let G := stdGaussian E
  let A : (E×E)×(E×E) → (E×E)×E :=
    fun p ↦ (ornsteinStep δ σ p.2.1 p.1,p.2.2)
  let B : (E×E)×E → (E×E)×E :=
    fun p ↦ (hamiltonianFlow f M hLip h hh p.1 h,p.2)
  let C : (E×E)×E → E×E := fun p ↦ ornsteinStep δ σ p.2 p.1
  have hA : Measurable A := by unfold A ornsteinStep; fun_prop
  have hB : Measurable B :=
    ((hamiltonianFlow_endpoint_continuous f M hLip h hh).measurable.comp measurable_fst).prodMk measurable_snd
  have hC : Measurable C := by unfold C ornsteinStep; fun_prop
  have hfirst : (π.prod G).map C=π := thermostat_preserves_target f m hm hf hsc δ σ hvariance
  have hH : (π.prod G).map B=π.prod G := by
    have he := Measure.map_prod_map π G
      (hamiltonianFlow_endpoint_continuous f M hLip h hh).measurable measurable_id
    rw [hamiltonianFlow_preserves_target f m hm M hf hsc hLip h hh,Measure.map_id] at he
    simpa only [B,Prod.map_def,id_eq] using he.symm
  calc
    _ = (((π.prod (G.prod G)).map A).map B).map C := by
      rw [Measure.map_map hC hB,Measure.map_map (hC.comp hB) hA]
      rfl
    _ = ((π.prod G).map B).map C := by rw [firstThermostat_joint_fresh f m hm hf hsc δ σ hvariance]
    _ = (π.prod G).map C := by rw [hH]
    _ = π := hfirst

/-- The explicit target/Gaussian-pair product supplies genuine L² coordinate
witnesses for the synchronous exact-versus-Verlet local comparison. -/
theorem exactObabo_lp_source
    (f : E → ℝ) (m : ℝ) (hm : 0<m) (hf : Differentiable ℝ f)
    (hsc : StrongConvexOn univ m f) (δ σ : ℝ) (hvariance : δ^2+σ^2=1) :
    let P := (kineticGibbsTarget f).prod ((stdGaussian E).prod (stdGaussian E))
    ∃ (Z : Lp E 2 P × Lp E 2 P) (Ξ Ξ' : Lp E 2 P),
      lpPhaseCoe P Z =ᵐ[P] Prod.fst ∧
      Ξ =ᵐ[P] (fun p : (E×E)×(E×E) ↦ p.2.1) ∧
      Ξ' =ᵐ[P] (fun p : (E×E)×(E×E) ↦ p.2.2) ∧
      P.map (lpPhaseCoe P (ornsteinStep δ σ Ξ Z))=kineticGibbsTarget f := by
  haveI := kineticGibbsTarget_probability f m hm hf hsc
  let P := (kineticGibbsTarget f).prod ((stdGaussian E).prod (stdGaussian E))
  let V : (E×E)×(E×E) → E := fun p ↦ p.1.1
  let X : (E×E)×(E×E) → E := fun p ↦ p.1.2
  let W : (E×E)×(E×E) → E := fun p ↦ p.2.1
  let W' : (E×E)×(E×E) → E := fun p ↦ p.2.2
  have hv : MemLp V 2 P := (kineticGibbsTarget_velocity_memLp f m hm hf hsc).comp_measurePreserving measurePreserving_fst
  have hx : MemLp X 2 P := (kineticGibbsTarget_position_memLp f m hm hf hsc).comp_measurePreserving measurePreserving_fst
  have hW : MemLp W 2 P :=
    ((show MemLp (id : E → E) 2 (stdGaussian E) from IsGaussian.memLp_two_id).comp_measurePreserving
      (measurePreserving_fst : MeasurePreserving Prod.fst ((stdGaussian E).prod (stdGaussian E)) _)).comp_measurePreserving measurePreserving_snd
  have hW' : MemLp W' 2 P :=
    ((show MemLp (id : E → E) 2 (stdGaussian E) from IsGaussian.memLp_two_id).comp_measurePreserving
      (measurePreserving_snd : MeasurePreserving Prod.snd ((stdGaussian E).prod (stdGaussian E)) _)).comp_measurePreserving measurePreserving_snd
  let Z := (hv.toLp V,hx.toLp X)
  let Ξ := hW.toLp W
  let Ξ' := hW'.toLp W'
  have hZ : lpPhaseCoe P Z =ᵐ[P] Prod.fst := by
    filter_upwards [hv.coeFn_toLp,hx.coeFn_toLp] with p hv hx
    exact Prod.ext hv hx
  refine ⟨Z,Ξ,Ξ',hZ,hW.coeFn_toLp,hW'.coeFn_toLp,?_⟩
  have hcoe : lpPhaseCoe P (ornsteinStep δ σ Ξ Z) =ᵐ[P]
      fun p : (E×E)×(E×E) ↦ ornsteinStep δ σ p.2.1 p.1 := by
    filter_upwards [lp_ornsteinStep_coe P δ σ Ξ Z,hZ,hW.coeFn_toLp] with p hO hZ hΞ
    rw [hO,hZ,hΞ]
  rw [Measure.map_congr hcoe]
  have hj := congrArg (fun μ : Measure ((E×E)×E) ↦ μ.map Prod.fst)
    (firstThermostat_joint_fresh f m hm hf hsc δ σ hvariance)
  rw [Measure.map_map measurable_fst (by unfold ornsteinStep; fun_prop),Measure.map_fst_prod] at hj
  simpa only [P,measure_univ,one_smul,Function.comp_def] using hj

end KineticLangevin
