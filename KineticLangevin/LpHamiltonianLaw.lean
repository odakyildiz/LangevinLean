import KineticLangevin.KineticSplittingLp
import KineticLangevin.LpPhaseLaw
import KineticLangevin.GibbsTarget
import KineticLangevin.LpOneStep
import KineticLangevin.VerletLocal
import UnadjustedLangevin.StationaryMoments

/-! # Actual L² Hamiltonian reference and its Gibbs moments

The L² integral flow represents the actual finite-dimensional Hamiltonian
flow almost everywhere. Convergence in measure identifies the two limits
of the same Verlet approximants. Gibbs invariance gives its moment bounds.
-/

noncomputable section
set_option linter.style.header false
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace KineticLangevin
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (P : Measure Ω) [IsProbabilityMeasure P]

theorem measure_map_lpPhase_eq_pointwise_limit
    (S : Lp E 2 P × Lp E 2 P) (Sn : ℕ → Lp E 2 P × Lp E 2 P)
    (hS : Tendsto Sn atTop (𝓝 S)) (Y : Ω → E × E) (hY : Measurable Y)
    (fn : ℕ → Ω → E × E) (hfn : ∀ n, Measurable (fn n))
    (hcoe : ∀ n, lpPhaseCoe P (Sn n) =ᵐ[P] fn n)
    (hpoint : ∀ᵐ ω ∂P, Tendsto (fun n ↦ fn n ω) atTop (𝓝 (Y ω))) :
    P.map (lpPhaseCoe P S) = P.map Y := by
  apply Measure.ext_of_charFunDual
  funext L
  let F : E × E → ℂ := fun z ↦ Complex.exp ((L z : ℂ) * Complex.I)
  have hF : Continuous F := by dsimp [F];fun_prop
  have hb (z : E × E) : ‖F z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hlim : Tendsto (fun n ↦ ∫ ω, F (fn n ω) ∂P) atTop (𝓝 (∫ ω, F (Y ω) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ))
    · intro n
      exact (hF.measurable.comp (hfn n)).aestronglyMeasurable
    · exact integrable_const 1
    · intro n
      exact ae_of_all _ (fun ω ↦ (hb _).le)
    · exact hpoint.mono (fun ω hω ↦ hF.continuousAt.tendsto.comp hω)
  have heq (n : ℕ) : charFunDual (P.map (lpPhaseCoe P (Sn n))) L =
      ∫ ω, F (fn n ω) ∂P := by
    change (∫ z, F z ∂P.map (lpPhaseCoe P (Sn n))) = _
    rw [integral_map (measurable_lpPhaseCoe P (Sn n)).aemeasurable hF.aestronglyMeasurable]
    exact integral_congr_ae ((hcoe n).mono (fun ω hω ↦ congrArg F hω))
  have hactual := ((continuous_charFunDual_map_lpPhase P L).tendsto S).comp hS
  change Tendsto (fun n ↦ charFunDual (P.map (lpPhaseCoe P (Sn n))) L) atTop
    (𝓝 (charFunDual (P.map (lpPhaseCoe P S)) L)) at hactual
  simp only [heq] at hactual
  have htarget : (∫ ω, F (Y ω) ∂P) = charFunDual (P.map Y) L := by
    change _ = ∫ z, F z ∂P.map Y
    rw [integral_map hY.aemeasurable hF.aestronglyMeasurable]
  rw [← htarget]
  exact tendsto_nhds_unique hactual hlim

theorem lpPhaseCoe_eq_pointwise_limit
    (S : Lp E 2 P × Lp E 2 P) (Sn : ℕ → Lp E 2 P × Lp E 2 P)
    (hS : Tendsto Sn atTop (𝓝 S)) (Y : Ω → E × E)
    (fn : ℕ → Ω → E × E) (hfn : ∀ n, Measurable (fn n))
    (hcoe : ∀ n, lpPhaseCoe P (Sn n) =ᵐ[P] fn n)
    (hpoint : ∀ᵐ ω ∂P, Tendsto (fun n ↦ fn n ω) atTop (𝓝 (Y ω))) :
    lpPhaseCoe P S =ᵐ[P] Y := by
  have h1 := tendstoInMeasure_of_tendsto_Lp ((continuous_fst.tendsto S).comp hS)
  have h2 := tendstoInMeasure_of_tendsto_Lp ((continuous_snd.tendsto S).comp hS)
  have hc1 : ∀ n, ((Sn n).1 : Ω → E) =ᵐ[P] fun ω ↦ (fn n ω).1 :=
    fun n ↦ (hcoe n).mono (fun ω hω ↦ congrArg Prod.fst hω)
  have hc2 : ∀ n, ((Sn n).2 : Ω → E) =ᵐ[P] fun ω ↦ (fn n ω).2 :=
    fun n ↦ (hcoe n).mono (fun ω hω ↦ congrArg Prod.snd hω)
  have hp1 := tendstoInMeasure_of_tendsto_ae (fun n ↦ (hfn n).fst.aestronglyMeasurable)
    (hpoint.mono (fun ω hω ↦ (continuous_fst.tendsto (Y ω)).comp hω))
  have hp2 := tendstoInMeasure_of_tendsto_ae (fun n ↦ (hfn n).snd.aestronglyMeasurable)
    (hpoint.mono (fun ω hω ↦ (continuous_snd.tendsto (Y ω)).comp hω))
  have he1 := tendstoInMeasure_ae_unique (h1.congr hc1 Filter.EventuallyEq.rfl) hp1
  have he2 := tendstoInMeasure_ae_unique (h2.congr hc2 Filter.EventuallyEq.rfl) hp2
  filter_upwards [he1,he2] with ω hω1 hω2
  exact Prod.ext hω1 hω2

theorem lp_verlet_iterate_coe (g : E → E) (M : ℝ≥0) (hg : LipschitzWith M g)
    (h : ℝ) (S : Lp E 2 P × Lp E 2 P) (n : ℕ) :
    lpPhaseCoe P ((verletStep (ULA.lpDrift P g hg) h)^[n] S) =ᵐ[P]
      fun ω ↦ (verletStep g h)^[n] (lpPhaseCoe P S ω) := by
  induction n with
  | zero => exact ae_of_all _ (fun _ ↦ rfl)
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    filter_upwards [lp_verletStep_coe P g M hg h ((verletStep (ULA.lpDrift P g hg) h)^[n] S),ih]
      with ω hstep hprev
    rw [hstep,hprev,Function.iterate_succ_apply']

section Hilbert

def lpHamiltonianFlow (g : E → E) (M : ℝ≥0) (hg : LipschitzWith M g)
    (T : ℝ) (hT : 0 ≤ T) (S : Lp E 2 P × Lp E 2 P) : ℝ → Lp E 2 P × Lp E 2 P :=
  kineticFlow (ULA.lpDrift P g hg) M 0 1 (ULA.lpDrift_lipschitz P g hg) T hT S 0

theorem lpHamiltonianFlow_spec (g : E → E) (M : ℝ≥0) (hg : LipschitzWith M g)
    (T : ℝ) (hT : 0 ≤ T) (S : Lp E 2 P × Lp E 2 P) :
    Continuous (lpHamiltonianFlow P g M hg T hT S) ∧
      lpHamiltonianFlow P g M hg T hT S 0 = S ∧
      ∀ t ∈ Icc 0 T, lpHamiltonianFlow P g M hg T hT S t - S =
        -(∫ s in 0..t, kineticNegativeDrift (ULA.lpDrift P g hg) 0 1 (lpHamiltonianFlow P g M hg T hT S s)) := by
  have hs := kineticFlow_spec (ULA.lpDrift P g hg) M 0 1 (ULA.lpDrift_lipschitz P g hg) T hT S 0
  refine ⟨hs.1,hs.2.1,?_⟩
  intro t ht
  simpa [lpHamiltonianFlow, normalizedForcing, Prod.mk_zero_zero] using hs.2.2 t ht

theorem lpHamiltonianFlow_coe (f : E → ℝ) (M : ℝ≥0) (hLip : LipschitzWith M (gradient f))
    (T : ℝ) (hT : 0 ≤ T) (S : Lp E 2 P × Lp E 2 P) (t : ℝ) (ht : t ∈ Icc 0 T) :
    lpPhaseCoe P (lpHamiltonianFlow P (gradient f) M hLip T hT S t) =ᵐ[P]
      fun ω ↦ hamiltonianFlow f M hLip t ht.1 (lpPhaseCoe P S ω) t := by
  let A := lpHamiltonianFlow P (gradient f) M hLip T hT S
  let Sn : ℕ → Lp E 2 P × Lp E 2 P := fun n ↦
    (verletStep (ULA.lpDrift P (gradient f) hLip) (t / ((n+1 : ℕ) : ℝ)))^[n+1] S
  have hs := lpHamiltonianFlow_spec P (gradient f) M hLip T hT S
  have hSn : Tendsto Sn atTop (𝓝 (A t)) :=
    verlet_iterate_tendsto_integral (ULA.lpDrift P (gradient f) hLip) M
      (ULA.lpDrift_lipschitz P (gradient f) hLip) t ht.1 S A hs.1
      (fun r hr ↦ hs.2.2 r ⟨hr.1,hr.2.trans ht.2⟩)
  let Y : Ω → E × E := fun ω ↦ hamiltonianFlow f M hLip t ht.1 (lpPhaseCoe P S ω) t
  have hY : Measurable Y := (hamiltonianFlow_endpoint_continuous f M hLip t ht.1).measurable.comp (measurable_lpPhaseCoe P S)
  let fn : ℕ → Ω → E × E := fun n ω ↦
    (verletStep (gradient f) (t / ((n+1 : ℕ) : ℝ)))^[n+1] (lpPhaseCoe P S ω)
  have hfn : ∀ n, Measurable (fn n) := by
    intro n
    have hV : Continuous (verletStep (gradient f) (t / ((n+1 : ℕ) : ℝ))) := by
      unfold verletStep kickStep driftStep
      have hg := hLip.continuous
      fun_prop
    exact ((hV.iterate (n+1)).measurable.comp (measurable_lpPhaseCoe P S))
  have hcoe : ∀ n, lpPhaseCoe P (Sn n) =ᵐ[P] fn n := fun n ↦
    lp_verlet_iterate_coe P (gradient f) M hLip _ S (n+1)
  exact lpPhaseCoe_eq_pointwise_limit P (A t) Sn hSn Y fn hfn hcoe
    (ae_of_all _ (fun ω ↦ verlet_iterate_tendsto_hamiltonianFlow f M hLip t ht.1 (lpPhaseCoe P S ω)))

theorem lpHamiltonianFlow_law (f : E → ℝ) (M : ℝ≥0) (hLip : LipschitzWith M (gradient f))
    (T : ℝ) (hT : 0 ≤ T) (S : Lp E 2 P × Lp E 2 P) (t : ℝ) (ht : t ∈ Icc 0 T) :
    P.map (lpPhaseCoe P (lpHamiltonianFlow P (gradient f) M hLip T hT S t)) =
      (P.map (lpPhaseCoe P S)).map (fun z ↦ hamiltonianFlow f M hLip t ht.1 z t) := by
  rw [Measure.map_map (hamiltonianFlow_endpoint_continuous f M hLip t ht.1).measurable
    (measurable_lpPhaseCoe P S)]
  exact Measure.map_congr (lpHamiltonianFlow_coe P f M hLip T hT S t ht)


theorem lpHamiltonianFlow_preserves_target [FiniteDimensional ℝ E]
    (f : E → ℝ) (m : ℝ) (hm : 0 < m) (M : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith M (gradient f))
    (T : ℝ) (hT : 0 ≤ T) (S : Lp E 2 P × Lp E 2 P)
    (hS : P.map (lpPhaseCoe P S) = kineticGibbsTarget f) (t : ℝ) (ht : t ∈ Icc 0 T) :
    P.map (lpPhaseCoe P (lpHamiltonianFlow P (gradient f) M hLip T hT S t)) = kineticGibbsTarget f := by
  rw [lpHamiltonianFlow_law P f M hLip T hT S t ht, hS,
    hamiltonianFlow_preserves_target f m hm M hf hsc hLip t ht.1]

theorem lpHamiltonianFlow_component_equations (g : E → E) (M : ℝ≥0) (hg : LipschitzWith M g)
    (T : ℝ) (hT : 0 ≤ T) (S : Lp E 2 P × Lp E 2 P) :
    let A := lpHamiltonianFlow P g M hg T hT S
    (∀ t ∈ Icc 0 T, (A t).1 - (A 0).1 = -(∫ s in 0..t, ULA.lpDrift P g hg (A s).2)) ∧
      (∀ t ∈ Icc 0 T, (A t).2 - (A 0).2 = ∫ s in 0..t, (A s).1) := by
  intro A
  have hs := lpHamiltonianFlow_spec P g M hg T hT S
  have hc : Continuous (fun s ↦ kineticNegativeDrift (ULA.lpDrift P g hg) 0 1 (A s)) :=
    (kineticNegativeDrift_lipschitz (ULA.lpDrift P g hg) M 0 1 (ULA.lpDrift_lipschitz P g hg)).continuous.comp hs.1
  constructor
  · intro t ht
    have hp : A t - A 0 = -(∫ s in 0..t, kineticNegativeDrift (ULA.lpDrift P g hg) 0 1 (A s)) := by
      rw [show A 0 = S from hs.2.1]
      exact hs.2.2 t ht
    have he := congrArg Prod.fst hp
    have hi := (ContinuousLinearMap.fst ℝ (Lp E 2 P) (Lp E 2 P)).intervalIntegral_comp_comm (hc.intervalIntegrable (μ := volume) 0 t)
    change (A t).1 - (A 0).1 = -(ContinuousLinearMap.fst ℝ (Lp E 2 P) (Lp E 2 P)) (∫ s in 0..t, kineticNegativeDrift (ULA.lpDrift P g hg) 0 1 (A s)) at he
    rw [← hi] at he
    change (A t).1 - (A 0).1 = -(∫ s in 0..t, (0 : ℝ) • (A s).1 + (1 : ℝ) • ULA.lpDrift P g hg (A s).2) at he
    simpa only [zero_smul,one_smul,zero_add] using he
  · intro t ht
    have hp : A t - A 0 = -(∫ s in 0..t, kineticNegativeDrift (ULA.lpDrift P g hg) 0 1 (A s)) := by
      rw [show A 0 = S from hs.2.1]
      exact hs.2.2 t ht
    have he := congrArg Prod.snd hp
    have hi := (ContinuousLinearMap.snd ℝ (Lp E 2 P) (Lp E 2 P)).intervalIntegral_comp_comm (hc.intervalIntegrable (μ := volume) 0 t)
    change (A t).2 - (A 0).2 = -(ContinuousLinearMap.snd ℝ (Lp E 2 P) (Lp E 2 P)) (∫ s in 0..t, kineticNegativeDrift (ULA.lpDrift P g hg) 0 1 (A s)) at he
    rw [← hi] at he
    change (A t).2 - (A 0).2 = -(∫ s in 0..t, -(A s).1) at he
    simpa only [intervalIntegral.integral_neg,neg_neg] using he
end Hilbert

section Euclidean
variable {ι : Type*} [Fintype ι]

theorem lpHamiltonianFlow_target_moments
    (f : EuclideanSpace ℝ ι → ℝ) (m : ℝ) (hm : 0 < m) (M : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith M (gradient f))
    (T : ℝ) (hT : 0 ≤ T) (S : Lp (EuclideanSpace ℝ ι) 2 P × Lp (EuclideanSpace ℝ ι) 2 P)
    (hS : P.map (lpPhaseCoe P S) = kineticGibbsTarget f) (t : ℝ) (ht : t ∈ Icc 0 T) :
    let A := lpHamiltonianFlow P (gradient f) M hLip T hT S
    ‖(A t).1‖ = Real.sqrt (Fintype.card ι : ℝ) ∧
      ‖ULA.lpDrift P (gradient f) hLip (A t).2‖ ≤ Real.sqrt ((M : ℝ) * (Fintype.card ι : ℝ)) := by
  intro A
  have hlaw := lpHamiltonianFlow_preserves_target P f m hm M hf hsc hLip T hT S hS t ht
  have hV : P.map (A t).1 = stdGaussian (EuclideanSpace ℝ ι) := by
    rw [← kineticGibbsTarget_velocity f m hm hf hsc, ← hlaw,
      Measure.map_map measurable_fst (measurable_lpPhaseCoe P (A t))]
    rfl
  have hX : P.map (A t).2 = ULA.gibbsMeasure f := by
    rw [← kineticGibbsTarget_position f m hm hf hsc, ← hlaw,
      Measure.map_map measurable_snd (measurable_lpPhaseCoe P (A t))]
    rfl
  constructor
  · exact gaussian_velocity_Lp_norm P (A t).1 ⟨(Lp.stronglyMeasurable _).measurable.aemeasurable,hV⟩
  · simpa using ULA.lpDrift_norm_le_of_strongConvex_gibbs_law P f m M hm hf hsc hLip (A t).2 hX

theorem lp_obabo_target_local_bound
    (f : EuclideanSpace ℝ ι → ℝ) (m γ h δ σ : ℝ) (M : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith M (gradient f))
    (hm : 0 < m) (hγ : 0 < γ) (hM : 0 < (M : ℝ)) (hh : 0 ≤ h)
    (hfriction : 4 * (M : ℝ) ≤ γ ^ 2) (hδ : |δ| ≤ 1)
    (Z : Lp (EuclideanSpace ℝ ι) 2 P × Lp (EuclideanSpace ℝ ι) 2 P)
    (Ξ Ξ' : Lp (EuclideanSpace ℝ ι) 2 P)
    (hlaw : P.map (lpPhaseCoe P (ornsteinStep δ σ Ξ Z)) = kineticGibbsTarget f) :
    let A := lpHamiltonianFlow P (gradient f) M hLip h hh (ornsteinStep δ σ Ξ Z)
    weightedPhaseNorm (1 / (M : ℝ)) (1 / γ)
      (obaboStep (ULA.lpDrift P (gradient f) hLip) h δ σ Z Ξ Ξ' - ornsteinStep δ σ Ξ' (A h)) ≤
        2 * h ^ 2 * (Real.sqrt ((M : ℝ) * (Fintype.card ι : ℝ)) +
          Real.sqrt (M : ℝ) * Real.sqrt (Fintype.card ι : ℝ) +
          Real.sqrt (M : ℝ) * Real.sqrt ((M : ℝ) * (Fintype.card ι : ℝ)) * h / 4) := by
  intro A
  have hs := lpHamiltonianFlow_spec P (gradient f) M hLip h hh (ornsteinStep δ σ Ξ Z)
  have hcomp := lpHamiltonianFlow_component_equations P (gradient f) M hLip h hh (ornsteinStep δ σ Ξ Z)
  have hmom := lpHamiltonianFlow_target_moments P f m hm M hf hsc hLip h hh (ornsteinStep δ σ Ξ Z) hlaw
  exact obabo_hamiltonian_local_bound (ULA.lpDrift P (gradient f) hLip) M (ULA.lpDrift_lipschitz P (gradient f) hLip)
    (fun t ↦ (A t).1) (fun t ↦ (A t).2) γ h δ σ (Real.sqrt (Fintype.card ι : ℝ))
    (Real.sqrt ((M : ℝ) * (Fintype.card ι : ℝ))) hγ hM hfriction hh (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hδ hs.1.fst hs.1.snd (fun t ht ↦ (hmom t ht).1.le) (fun t ht ↦ (hmom t ht).2)
    hcomp.1 hcomp.2 Z Ξ Ξ' hs.2.1
end Euclidean
end KineticLangevin
