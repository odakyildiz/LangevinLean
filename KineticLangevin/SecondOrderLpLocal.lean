import KineticLangevin.SecondOrderLocal
import KineticLangevin.LpHessian
import KineticLangevin.LpHamiltonianLaw

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace KineticLangevin
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P]

/-- Actual target time marginals supply every moment in the second-order local error bound. -/
theorem lp_secondOrder_stationary_local_bound
    (f : EuclideanSpace ℝ ι → ℝ)
    (H : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (m γ T : ℝ) (M M2 : ℝ≥0) (hm : 0<m) (hγ : 0≤γ) (hT : 0≤T)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hH : LipschitzWith M2 H)
    (hderiv : ∀ x,HasFDerivAt (gradient f) (H x) x)
    (V X U : ℝ → Lp (EuclideanSpace ℝ ι) 2 P)
    (hV : Continuous V) (hX : Continuous X) (hU : Continuous U)
    (hlaw : ∀ t∈Icc 0 T,P.map (lpPhaseCoe P (V t,X t))=kineticGibbsTarget f)
    (hmild : ∀ t∈Icc 0 T,V t=U t-dampedIntegral γ (fun s ↦ ULA.lpDrift P (gradient f) hLip (X s)) t)
    (hkin : ∀ t∈Icc 0 T,X t-X 0=∫ r in 0..t,V r) :
    let G := fun s ↦ ULA.lpDrift P (gradient f) hLip (X s)
    let H0 := lpHessian P (gradient f) H M M2 hLip hH hderiv (X 0)
    let C := (M2 : ℝ)*Real.sqrt ((Fintype.card ι : ℝ)^2+2*(Fintype.card ι : ℝ))+
      (M : ℝ)*Real.sqrt ((M : ℝ)*(Fintype.card ι : ℝ))
    ‖correctedVelocity γ U (G 0) H0 T-V T‖≤C*T^3/6 ∧
    ‖correctedPosition γ U (X 0) (G 0) H0 T-X T‖≤C*T^4/24 ∧
    (γ*T≤1/5 → transformNorm γ 0 (correctedVelocity γ U (G 0) H0 T-V T,
      correctedPosition γ U (X 0) (G 0) H0 T-X T)≤C*T^3/4) := by
  intro G H0 C
  have hG : Continuous G := (ULA.lpDrift_lipschitz P (gradient f) hLip).continuous.comp hX
  have hVlaw (t : ℝ) (ht : t∈Icc 0 T) : HasLaw (V t) (stdGaussian (EuclideanSpace ℝ ι)) P := by
    refine ⟨(Lp.stronglyMeasurable _).measurable.aemeasurable,?_⟩
    rw [← kineticGibbsTarget_velocity f m hm hf hsc,← hlaw t ht,
      Measure.map_map measurable_fst (measurable_lpPhaseCoe P (V t,X t))]
    rfl
  have hscore (t : ℝ) (ht : t∈Icc 0 T) :
      ‖G t‖≤Real.sqrt ((M : ℝ)*(Fintype.card ι : ℝ)) := by
    have hXlaw : P.map (X t)=ULA.gibbsMeasure f := by
      rw [← kineticGibbsTarget_position f m hm hf hsc,← hlaw t ht,
        Measure.map_map measurable_snd (measurable_lpPhaseCoe P (V t,X t))]
      rfl
    simpa [G] using ULA.lpDrift_norm_le_of_strongConvex_gibbs_law P f m M hm hf hsc hLip (X t) hXlaw
  let R : ℝ := (M2 : ℝ)/2*Real.sqrt ((Fintype.card ι : ℝ)^2+2*(Fintype.card ι : ℝ))
  have hR : 0≤R := by dsimp [R];positivity
  have hTaylor (t : ℝ) (ht : t∈Icc 0 T) : ‖G t-G 0-H0 (X t-X 0)‖≤R*t^2 :=
    lpHessian_stationary_taylor_bound P (gradient f) H M M2 hLip hH hderiv X V hV T hkin hVlaw ht
  have hC : 2*R+‖H0‖*Real.sqrt ((M : ℝ)*(Fintype.card ι : ℝ))≤C := by
    have hHnorm := lpHessian_norm_le P (gradient f) H M M2 hLip hH hderiv (X 0)
    have hh := mul_le_mul_of_nonneg_right hHnorm (Real.sqrt_nonneg ((M : ℝ)*(Fintype.card ι : ℝ)))
    dsimp [R,C,H0] at *
    linarith only [hh]
  constructor
  · exact (correctedVelocity_error_bound γ T R _ hγ hT V X U G hV hX hU hG H0 hmild hkin hTaylor hscore).trans
      (by gcongr)
  constructor
  · exact (correctedPosition_error_bound γ T R _ hγ hT V X U G hV hX hU hG H0 hmild hkin hTaylor hscore).trans
      (by gcongr)
  intro hsmall
  exact (correctedPhase_error_bound γ T R _ hγ hT hR (Real.sqrt_nonneg _) hsmall V X U G hV hX hU hG H0 hmild hkin hTaylor hscore).trans
    (by gcongr)

end KineticLangevin
