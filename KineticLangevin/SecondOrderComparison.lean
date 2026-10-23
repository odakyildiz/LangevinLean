import KineticLangevin.SecondOrderLinear
import KineticLangevin.LpContraction
import KineticLangevin.HessianDifference
import KineticLangevin.FreeOUCorrectionBound
import KineticLangevin.Integrator

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal RealInnerProductSpace
namespace KineticLangevin
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem transformNorm_neg (γ a : ℝ) (s : E×E) : transformNorm γ a (-s)=transformNorm γ a s := by
  have he : transform γ a (-s)=-transform γ a s := by
    ext <;> simp only [transform,Prod.fst_neg,Prod.snd_neg] <;> module
  unfold transformNorm
  rw [he,WithLp.toLp_neg,norm_neg]

/-- A centered force sector is exactly the ordinary strong-smooth interpolation inequality. -/
theorem interpolation_of_centered_bound (m M : ℝ) (hmM : m≤M) (x F : E)
    (hcenter : ‖F-((m+M)/2) • x‖≤((M-m)/2)*‖x‖) :
    m*M*‖x‖^2+‖F‖^2≤(m+M)*⟪F,x⟫ := by
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by linarith only [hmM]) (norm_nonneg x))).mpr hcenter
  rw [norm_sub_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,real_inner_smul_right] at hs
  nlinarith only [hs]

/-- The position projection cancels the two square-root factors in the Gaussian cutoff term. -/
theorem secondOrder_cutoff_projection (γ t M2 B α p D N : ℝ) (hγ : 0<γ)
    (hM2 : 0≤M2) (hD : D≤Real.sqrt 2/γ*N) :
    Real.sqrt 2*t^2*(M2*Real.sqrt α*D+2*B*Real.exp (-(α-p)/8))/2≤
      (M2*Real.sqrt α*t^2/γ)*N+Real.sqrt 2*t^2*B*Real.exp (-(α-p)/8) := by
  calc
    _ = (Real.sqrt 2*t^2/2)*(M2*Real.sqrt α*D)+Real.sqrt 2*t^2*B*Real.exp (-(α-p)/8) := by ring
    _ ≤ (Real.sqrt 2*t^2/2)*(M2*Real.sqrt α*(Real.sqrt 2/γ*N))+
        Real.sqrt 2*t^2*B*Real.exp (-(α-p)/8) := by gcongr
    _ = _ := by
      field_simp [hγ.ne']
      ring_nf
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)]
      ring

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  (P : Measure Ω) [IsProbabilityMeasure P]
open BrownianConvolution

/-- The actual four correlated innovations pulled onto an arbitrary concrete source. -/
def klmc2SourceInnovation
    (L : Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) →L[ℝ]
      Lp (EuclideanSpace ℝ ι) 2 P) (γ : ℝ) (a : ℝ≥0) (t : ℝ) : Fin 4 → Lp (EuclideanSpace ℝ ι) 2 P :=
  fun k ↦ L (vectorSegmentLp ι (klmc2Kernels γ k) (continuous_klmc2Kernels γ k) a t.toNNReal)

/-- KLMC2 on an actual source, with the complete free-OU Hessian response retained. -/
def klmc2SourceStep
    (g : Lp (EuclideanSpace ℝ ι) 2 P → Lp (EuclideanSpace ℝ ι) 2 P)
    (H : Lp (EuclideanSpace ℝ ι) 2 P → Lp (EuclideanSpace ℝ ι) 2 P →L[ℝ] Lp (EuclideanSpace ℝ ι) 2 P)
    (L : Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) →L[ℝ]
      Lp (EuclideanSpace ℝ ι) 2 P) (γ : ℝ) (a : ℝ≥0) (t : ℝ)
    (z : Lp (EuclideanSpace ℝ ι) 2 P×Lp (EuclideanSpace ℝ ι) 2 P) :=
  (freeOUResponse P L z.1 γ a 0 t-psi γ 1 t • g z.2-H z.2 (freeOUCorrection P L z.1 γ a 1 t),
   z.2+freeOUResponse P L z.1 γ a 1 t-psi γ 2 t • g z.2-H z.2 (freeOUCorrection P L z.1 γ a 2 t))

/-- The source formula is exactly the implemented four-innovation KLMC2 step. -/
theorem klmc2SourceStep_eq_klmc2Step
    (g : Lp (EuclideanSpace ℝ ι) 2 P → Lp (EuclideanSpace ℝ ι) 2 P)
    (H : Lp (EuclideanSpace ℝ ι) 2 P → Lp (EuclideanSpace ℝ ι) 2 P →L[ℝ] Lp (EuclideanSpace ℝ ι) 2 P)
    (L : Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) →L[ℝ]
      Lp (EuclideanSpace ℝ ι) 2 P) (γ : ℝ) (a : ℝ≥0) (t : ℝ)
    (z : Lp (EuclideanSpace ℝ ι) 2 P×Lp (EuclideanSpace ℝ ι) 2 P) :
    klmc2SourceStep P g H (Real.sqrt (2*γ) • L) γ a t z=
      klmc2Step g H γ t z (klmc2SourceInnovation P L γ a t) := by
  have h0 : klmc2Kernels γ 0=psi γ 0 := rfl
  have h1 : klmc2Kernels γ 1=psi γ 1 := rfl
  have h2 : klmc2Kernels γ 2=phi γ 2 := rfl
  have h3 : klmc2Kernels γ 3=phi γ 3 := rfl
  apply Prod.ext <;> simp only [klmc2SourceStep,freeOUResponse,freeOUCorrection,klmc2Step,klmc2SourceInnovation,
    ContinuousLinearMap.smul_apply,h0,h1,h2,h3,map_add,map_smul,Nat.reduceAdd] <;> module

/-- The actual comparison contains the stochastic Hessian difference terms omitted in the printed proof. -/
theorem klmc2SourceStep_difference
    (g : Lp (EuclideanSpace ℝ ι) 2 P → Lp (EuclideanSpace ℝ ι) 2 P)
    (H : Lp (EuclideanSpace ℝ ι) 2 P → Lp (EuclideanSpace ℝ ι) 2 P →L[ℝ] Lp (EuclideanSpace ℝ ι) 2 P)
    (L : Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) →L[ℝ]
      Lp (EuclideanSpace ℝ ι) 2 P) (γ : ℝ) (a : ℝ≥0) (t : ℝ)
    (z w : Lp (EuclideanSpace ℝ ι) 2 P×Lp (EuclideanSpace ℝ ι) 2 P) :
    klmc2SourceStep P g H L γ a t z-klmc2SourceStep P g H L γ a t w=
      frozenSecondOrderStep γ t (H w.2) (z.1-w.1) (z.2-w.2) (g z.2-g w.2)+
        (-((H z.2-H w.2) (freeOUCorrection P L z.1 γ a 1 t)),
         -((H z.2-H w.2) (freeOUCorrection P L z.1 γ a 2 t))) := by
  apply Prod.ext <;> simp only [klmc2SourceStep,frozenSecondOrderStep,freeOUResponse,freeOUCorrection,
    Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,sub_apply,map_sub,map_add,map_smul,smul_sub,Nat.reduceAdd] <;> module

/-- The actual L² force and Hessian satisfy the genuine frozen-linear contraction. -/
theorem lp_frozenSecondOrderStep_contract
    (f : EuclideanSpace ℝ ι → ℝ)
    (H : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (m γ t : ℝ) (M M2 : ℝ≥0) (hm : 0<m) (hmM : m≤(M : ℝ)) (hγ : 0<γ)
    (hfriction : m+(M : ℝ)≤γ^2) (ht : 0≤t) (hstep : 5*γ*(M : ℝ)*t≤m)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith M (gradient f))
    (hH : LipschitzWith M2 H) (hderiv : ∀ x,HasFDerivAt (gradient f) (H x) x)
    (z w : Lp (EuclideanSpace ℝ ι) 2 P×Lp (EuclideanSpace ℝ ι) 2 P) :
    transformNorm γ 0 (frozenSecondOrderStep γ t
      (lpHessian P (gradient f) H M M2 hLip hH hderiv w.2)
      (z.1-w.1) (z.2-w.2) (ULA.lpDrift P (gradient f) hLip z.2-ULA.lpDrift P (gradient f) hLip w.2))≤
      (1-m*t/(2*γ))*transformNorm γ 0 (z-w) := by
  apply frozenSecondOrderStep_contract γ m M t hγ hm hmM hfriction ht hstep _
    (lpHessian_norm_le P (gradient f) H M M2 hLip hH hderiv w.2)
  · exact (ULA.lpDrift_lipschitz P (gradient f) hLip).norm_sub_le z.2 w.2
  · exact interpolation_of_centered_bound m M hmM _ _
      (lpDrift_centered_bound P f m M hf hsc hLip hmM z.2 w.2)

/-- Combine the actual frozen-linear comparison and the actual complete Hessian correction by the transformed triangle inequality. -/
theorem klmc2SourceStep_norm_triangle
    (g : Lp (EuclideanSpace ℝ ι) 2 P → Lp (EuclideanSpace ℝ ι) 2 P)
    (H : Lp (EuclideanSpace ℝ ι) 2 P → Lp (EuclideanSpace ℝ ι) 2 P →L[ℝ] Lp (EuclideanSpace ℝ ι) 2 P)
    (L : Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) →L[ℝ]
      Lp (EuclideanSpace ℝ ι) 2 P) (γ : ℝ) (a : ℝ≥0) (t : ℝ)
    (z w : Lp (EuclideanSpace ℝ ι) 2 P×Lp (EuclideanSpace ℝ ι) 2 P) (q C : ℝ)
    (hBase : transformNorm γ 0 (frozenSecondOrderStep γ t (H w.2) (z.1-w.1) (z.2-w.2) (g z.2-g w.2))≤q)
    (hCorr : transformNorm γ 0 ((H z.2-H w.2) (freeOUCorrection P L z.1 γ a 1 t),
      (H z.2-H w.2) (freeOUCorrection P L z.1 γ a 2 t))≤C) :
    transformNorm γ 0 (klmc2SourceStep P g H L γ a t z-klmc2SourceStep P g H L γ a t w)≤q+C := by
  let R := ((H z.2-H w.2) (freeOUCorrection P L z.1 γ a 1 t),
    (H z.2-H w.2) (freeOUCorrection P L z.1 γ a 2 t))
  have he := klmc2SourceStep_difference P g H L γ a t z w
  have hneg : transformNorm γ 0 (-R)≤C := (transformNorm_neg γ 0 R).le.trans hCorr
  calc
    _ = transformNorm γ 0 (frozenSecondOrderStep γ t (H w.2) (z.1-w.1) (z.2-w.2) (g z.2-g w.2)+(-R)) := congrArg (transformNorm γ 0) he
    _ ≤ transformNorm γ 0 (frozenSecondOrderStep γ t (H w.2) (z.1-w.1) (z.2-w.2) (g z.2-g w.2))+transformNorm γ 0 (-R) := transformNorm_add_le γ 0 _ _
    _ ≤ _ := add_le_add hBase hneg

/-- Proposition 3 for the actual four-kernel source, including every stochastic Hessian correction. -/
theorem klmc2SourceStep_comparison_bound
    (f : EuclideanSpace ℝ ι → ℝ)
    (H : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (m γ t α : ℝ) (M M2 : ℝ≥0) (hm : 0<m) (hmM : m≤(M : ℝ)) (hγ : 0<γ)
    (hfriction : m+(M : ℝ)≤γ^2) (ht : 0≤t) (hstep : 5*γ*(M : ℝ)*t≤m)
    (hα : 5*(Fintype.card ι : ℝ)≤α)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith M (gradient f))
    (hH : LipschitzWith M2 H) (hderiv : ∀ x,HasFDerivAt (gradient f) (H x) x)
    (L : Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) →L[ℝ]
      Lp (EuclideanSpace ℝ ι) 2 P) (a : ℝ≥0)
    (z w : Lp (EuclideanSpace ℝ ι) 2 P×Lp (EuclideanSpace ℝ ι) 2 P)
    (hGaussian : ∀ r∈Icc 0 t,HasLaw (freeOUResponse P L z.1 γ a 0 r) (stdGaussian (EuclideanSpace ℝ ι)) P) :
    let G := ULA.lpDrift P (gradient f) hLip
    let A := lpHessian P (gradient f) H M M2 hLip hH hderiv
    transformNorm γ 0 (klmc2SourceStep P G A L γ a t z-klmc2SourceStep P G A L γ a t w)≤
      (1-m*t/(2*γ)+(M2 : ℝ)*Real.sqrt α*t^2/γ)*transformNorm γ 0 (z-w)+
        Real.sqrt 2*t^2*((M : ℝ)-m)*Real.exp (-(α-(Fintype.card ι : ℝ))/8) := by
  intro G A
  let D := A z.2-A w.2
  let C : ℝ := (M2 : ℝ)*Real.sqrt α*‖z.2-w.2‖+
    2*((M : ℝ)-m)*Real.exp (-(α-(Fintype.card ι : ℝ))/8)
  have hC : 0≤C := by dsimp only [C];have hg := sub_nonneg.mpr hmM;positivity
  have hbound (r : ℝ) (hr : r∈Icc 0 t) : ‖D (freeOUResponse P L z.1 γ a 0 r)‖≤C :=
    lpHessian_difference_gaussian_truncation P f H m M M2 hf hsc hLip hmM hH hderiv z.2 w.2
      (freeOUResponse P L z.1 γ a 0 r) (hGaussian r hr) α hα
  have hCorr := freeOUCorrection_transformNorm_bound P D L z.1 γ C a hγ.le hC t ht hbound
  have hPos := position_le_transformNorm γ hγ (z-w)
  have hCorr' : Real.sqrt 2*t^2*C/2≤
      ((M2 : ℝ)*Real.sqrt α*t^2/γ)*transformNorm γ 0 (z-w)+
        Real.sqrt 2*t^2*((M : ℝ)-m)*Real.exp (-(α-(Fintype.card ι : ℝ))/8) :=
    secondOrder_cutoff_projection γ t M2 ((M : ℝ)-m) α (Fintype.card ι) ‖z.2-w.2‖
      (transformNorm γ 0 (z-w)) hγ M2.coe_nonneg hPos
  have hBase := lp_frozenSecondOrderStep_contract P f H m γ t M M2 hm hmM hγ hfriction ht hstep hf hsc hLip hH hderiv z w
  have hh := klmc2SourceStep_norm_triangle P G A L γ a t z w _ _ hBase (hCorr.trans hCorr')
  exact hh.trans_eq (by ring)

end KineticLangevin
