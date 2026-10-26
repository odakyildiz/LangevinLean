import PBGSO.MomentumUniform
import PBGSO.MomentumIntegralConstruction

/-! # Time-uniform OBABO error for actual finite-particle forces and noises
All force constants come from the original independent F and G. Gaussian
half-noise radii and their physical Brownian coupling are derived.
-/
noncomputable section
open MeasureTheory Set
open scoped NNReal InnerProductSpace
namespace PBGSO.Methods
variable {Ω A X I H : Type*} {N : ℕ} [MeasurableSpace Ω] [Fintype I]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  (W : I → ℝ≥0 → Ω → ℝ) (hW : ∀ i, ProbabilityTheory.IsPreBrownianReal (W i) Q)
  (D : ParticleForceData A X (EuclideanSpace ℝ I) N)

/-- Global Lipschitz constant for the actual lifted empirical coupled force. -/
def momentumUniformForceLip : ℝ≥0 := 2*max D.meanLip D.samplerForceLip

omit [CompleteSpace A] [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A] in
/-- The original independent force assumptions imply the entire empirical
force Lipschitz estimate. -/
theorem momentumUniformForce_lipschitz : LipschitzWith (momentumUniformForceLip D)
    (coupledForce (D.meanForceLp Q) (D.samplerForceLp Q)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [dist_eq_norm]
  simpa [momentumUniformForceLip,coupledLipschitzConstant] using
    coupledForce_lipschitz (D.meanForceLp Q) (D.samplerForceLp Q)
      D.meanLip D.samplerForceLip D.meanLip.coe_nonneg D.samplerForceLip.coe_nonneg
      (D.meanForceLp_bound Q) (D.samplerForceLp_bound Q) z w

/-- The actual kinetic Brownian input's uniform increment coefficient. -/
def momentumUniformBrownianRadius (γ : ℝ≥0) : ℝ :=
  Real.sqrt (γ : ℝ) * Real.sqrt (2*(Fintype.card I : ℝ))

omit [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A] in
/-- Time-uniform actual finite-particle M-MFPO discretisation. The only
stability condition is primitive monotonicity of the original kinetic drift
in its physical quadratic metric. The numerical stability/error conclusions
are derived, and no reference-moment or local-defect hypothesis remains. -/
theorem momentumParticle_time_uniform
    (γ : ℝ≥0)
    (C : MethodSegments.MomentumState (A := A) (I := I) Q →L[ℝ] H)
    (m ρ : ℝ) (hm : 0 < m) (hρ : 0 < ρ)
    (hcoerc : ∀ x, m*‖x‖ ≤ ‖C x‖)
    (hmono : ∀ x y, ⟪C (x-y),C (MethodSegments.momentumDrift Q D γ x-
      MethodSegments.momentumDrift Q D γ y)⟫_ℝ ≤ -ρ*‖C (x-y)‖^2)
    (Y : ℝ → MethodSegments.MomentumState (A := A) (I := I) Q) (hY : Continuous Y)
    (heq : ∀ t, 0 ≤ t → Y t-Y 0 =
      (∫ r in 0..t, MethodSegments.momentumDrift Q D γ (Y r))+
        MethodSegments.momentumInput Q W hW γ t)
    (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) (hρh : ρ*h ≤ 1)
    (hsmall : (momentumMetricDefect (momentumUniformForceLip D) γ
      ‖coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) 0‖
      (Real.sqrt (Fintype.card I : ℝ)) (momentumUniformBrownianRadius (I := I) γ) C m).2 *
        Real.sqrt h ≤ ρ/4) (n : ℕ) :
    ‖momentumParticleIterate Q W hW D γ h (Y 0) n-Y (n*h)‖ ≤
      momentumUniformErrorConstant (momentumUniformForceLip D) γ
        ‖coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) 0‖
        (Real.sqrt (Fintype.card I : ℝ)) (momentumUniformBrownianRadius (I := I) γ)
        ρ C m (Y 0)*Real.sqrt h := by
  let b : ℝ → Lp A 2 Q × Lp (EuclideanSpace ℝ I) 2 Q := fun t ↦
    (0,Real.sqrt (γ : ℝ) • ULA.brownianLangevinNoise Q W hW 0 t)
  have hnoise : Continuous (fun t ↦ Real.sqrt (γ : ℝ) • ULA.brownianLangevinNoise Q W hW 0 t) := by
    have hs : Continuous (fun z : Lp (EuclideanSpace ℝ I) 2 Q ↦ Real.sqrt (γ : ℝ) • z) :=
      continuous_const_smul (Real.sqrt (γ : ℝ))
    exact hs.comp (ULA.brownianLangevinNoise_continuous Q W hW 0)
  have hb : Continuous b := continuous_const.prodMk hnoise
  have hincrement (a s : ℝ) (ha : 0 ≤ a) (hs : s ∈ Icc 0 1) :
      ‖b (a+s)-b a‖ ≤ momentumUniformBrownianRadius (I := I) γ*Real.sqrt s := by
    change ‖((0 : Lp A 2 Q),Real.sqrt (γ : ℝ) • ULA.brownianLangevinNoise Q W hW 0 (a+s))-
      (0,Real.sqrt (γ : ℝ) • ULA.brownianLangevinNoise Q W hW 0 a)‖ ≤ _
    change max ‖(0 : Lp A 2 Q)-0‖
      ‖Real.sqrt (γ : ℝ) • ULA.brownianLangevinNoise Q W hW 0 (a+s)-
        Real.sqrt (γ : ℝ) • ULA.brownianLangevinNoise Q W hW 0 a‖ ≤ _
    rw [← smul_sub,MethodSegments.brownianNoise_increment Q W hW a s]
    simp only [sub_self,norm_zero,norm_smul,
      Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
      ULA.brownianLangevinNoise_norm Q W hW a s ha hs.1]
    rw [max_eq_right (by positivity)]
    dsimp [momentumUniformBrownianRadius]
    exact le_of_eq (by ring)
  have hξ (k : ℕ) :
      ‖(momentumGaussianNoise (Θ := Lp A 2 Q) Q W hW h k).1‖ ≤ Real.sqrt (Fintype.card I : ℝ) ∧
      ‖(momentumGaussianNoise (Θ := Lp A 2 Q) Q W hW h k).2‖ ≤ Real.sqrt (Fintype.card I : ℝ) := by
    simp [momentumGaussianNoise,momentumHalfNoise_norm Q W hW h hh]
  have hbrown (k : ℕ) : b ((k : ℝ)*h+h)-b ((k : ℝ)*h) =
      Real.sqrt ((γ : ℝ)*h) •
        ((momentumGaussianNoise (Θ := Lp A 2 Q) Q W hW h k).1+
          (momentumGaussianNoise (Θ := Lp A 2 Q) Q W hW h k).2) := by
    have he := congrArg Prod.fst (MethodSegments.momentumInput_increment
      (A := A) Q W hW γ h γ.coe_nonneg hh k)
    exact he
  exact obabo_time_uniform (coupledForce (D.meanForceLp Q) (D.samplerForceLp Q))
    (momentumUniformForceLip D) γ (momentumUniformForce_lipschitz Q D)
    C m ρ hm hρ hcoerc hmono Y b hY hb heq
    (Real.sqrt (Fintype.card I : ℝ)) (momentumUniformBrownianRadius (I := I) γ)
    (Real.sqrt_nonneg _) (by unfold momentumUniformBrownianRadius; positivity)
    hincrement h hh hh1 hρh hsmall (momentumGaussianNoise (Θ := Lp A 2 Q) Q W hW h) hξ hbrown n
end PBGSO.Methods
