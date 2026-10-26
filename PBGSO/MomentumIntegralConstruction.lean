import PBGSO.MethodIntegralSegments
import PBGSO.ImplementationLpCoordinates
import PBGSO.GlobalMeshRegularity
import PBGSO.MethodDiffusionCoordinates

/-! # Constructing the original kinetic numerical reference from global dynamics
The step equations are derived from the actual global integral equation.
Node force/momentum bounds and step moduli follow from mesh-uniform state,
drift and increment radii; no numerical recurrence or error bound is assumed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace PBGSO.MethodSegments
open Methods

variable {Ω A X I : Type*} {N : ℕ} [MeasurableSpace Ω] [Fintype I]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  (W : I → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) Q)
  (D : ParticleForceData A X (EuclideanSpace ℝ I) N)

abbrev MomentumState := ((Lp A 2 Q × Lp (EuclideanSpace ℝ I) 2 Q) ×
  (Lp A 2 Q × Lp (EuclideanSpace ℝ I) 2 Q))

/-- The original continuous kinetic implementation drift. -/
def momentumDrift (γ : ℝ) (z : MomentumState (A := A) (I := I) Q) : MomentumState (A := A) (I := I) Q :=
  (-coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) z.2 - γ • z.1, z.1)

/-- Both original kinetic step equations follow from the actual global
integral equation and its physical Brownian input. -/
theorem momentum_global_step (γ h : ℝ) (hγ : 0 ≤ γ) (hh : 0 < h)
    (z : ℝ → MomentumState (A := A) (I := I) Q)
    (hDrift : Continuous (fun t ↦ momentumDrift Q D γ (z t)))
    (heq : ∀ t, 0 ≤ t → z t - z 0 = (∫ r in 0..t, momentumDrift Q D γ (z r)) +
      momentumInput Q W hW γ t) (k : ℕ) :
    (z ((k : ℝ) * h + h)).1 = (z ((k : ℝ) * h)).1 -
      (∫ t in 0..h, coupledForce (D.meanForceLp Q) (D.samplerForceLp Q)
        (z ((k : ℝ) * h + t)).2 + γ • (z ((k : ℝ) * h + t)).1) +
      momentumGaussianIncrement (Θ := Lp A 2 Q) Q W hW γ h k ∧
    (z ((k : ℝ) * h + h)).2 = (z ((k : ℝ) * h)).2 +
      (∫ t in 0..h, (z ((k : ℝ) * h + t)).1) := by
  have hs := integral_shift z (fun t ↦ momentumDrift Q D γ (z t))
    (momentumInput (A := A) Q W hW γ) hDrift heq ((k : ℝ) * h) h
      (mul_nonneg (Nat.cast_nonneg k) hh.le) hh.le
  rw [momentumInput_increment Q W hW γ h hγ hh k] at hs
  have hi : IntervalIntegrable (fun r ↦ momentumDrift Q D γ (z ((k : ℝ) * h + r))) volume 0 h :=
    (hDrift.comp (continuous_const.add continuous_id)).intervalIntegrable 0 h
  have hp := congrArg Prod.fst hs
  have hq := congrArg Prod.snd hs
  have hip := (ContinuousLinearMap.fst ℝ (Lp A 2 Q × Lp (EuclideanSpace ℝ I) 2 Q)
    (Lp A 2 Q × Lp (EuclideanSpace ℝ I) 2 Q)).intervalIntegral_comp_comm hi
  have hiq := (ContinuousLinearMap.snd ℝ (Lp A 2 Q × Lp (EuclideanSpace ℝ I) 2 Q)
    (Lp A 2 Q × Lp (EuclideanSpace ℝ I) 2 Q)).intervalIntegral_comp_comm hi
  simp only [Prod.fst_sub, Prod.fst_add] at hp
  simp only [Prod.snd_sub, Prod.snd_add, add_zero] at hq
  change (∫ r in 0..h, (momentumDrift Q D γ (z ((k : ℝ) * h + r))).1) =
    (∫ r in 0..h, momentumDrift Q D γ (z ((k : ℝ) * h + r))).1 at hip
  change (∫ r in 0..h, (momentumDrift Q D γ (z ((k : ℝ) * h + r))).2) =
    (∫ r in 0..h, momentumDrift Q D γ (z ((k : ℝ) * h + r))).2 at hiq
  rw [← hip] at hp
  rw [← hiq] at hq
  change (z ((k : ℝ) * h + h)).2 - (z ((k : ℝ) * h)).2 =
    (∫ r in 0..h, (momentumDrift Q D γ (z ((k : ℝ) * h + r))).2) + 0 at hq
  rw [add_zero] at hq
  have hm : (fun r ↦ (momentumDrift Q D γ (z ((k : ℝ) * h + r))).1) =
      fun r ↦ -(coupledForce (D.meanForceLp Q) (D.samplerForceLp Q)
        (z ((k : ℝ) * h + r)).2 + γ • (z ((k : ℝ) * h + r)).1) := by
    funext r
    dsimp [momentumDrift]
    module
  change (z ((k : ℝ) * h + h)).1 - (z ((k : ℝ) * h)).1 =
    (∫ r in 0..h, (momentumDrift Q D γ (z ((k : ℝ) * h + r))).1) + _ at hp
  rw [hm, intervalIntegral.integral_neg] at hp
  constructor
  · rw [sub_eq_iff_eq_add] at hp
    rw [hp]
    module
  · change (z ((k : ℝ) * h + h)).2 - (z ((k : ℝ) * h)).2 =
      ∫ r in 0..h, (z ((k : ℝ) * h + r)).1 at hq
    rw [sub_eq_iff_eq_add] at hq
    rw [hq]
    module

/-- A force radius is derived from actual state and kinetic-drift radii. -/
theorem momentum_force_radius (γ P G : ℝ) (hγ : 0 ≤ γ)
    (z : MomentumState (A := A) (I := I) Q) (hP : ‖z‖ ≤ P)
    (hG : ‖momentumDrift Q D γ z‖ ≤ G) :
    ‖coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) z.2‖ ≤ G + γ * P := by
  have he : coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) z.2 =
      -(momentumDrift Q D γ z).1 - γ • z.1 := by
    dsimp [momentumDrift]
    module
  rw [he]
  have hb := norm_sub_le (-(momentumDrift Q D γ z).1) (γ • z.1)
  rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ] at hb
  exact hb.trans (add_le_add ((norm_fst_le _).trans hG)
    (mul_le_mul_of_nonneg_left ((norm_fst_le z).trans hP) hγ))

/-- Construct the original kinetic reference on every mesh in the fixed
horizon, deriving its node and step regularity from global mesh-uniform radii. -/
def momentumReferenceOfGlobal (γ h T R P G : ℝ) (hγ : 0 ≤ γ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hR : 0 ≤ R) (hP : 0 ≤ P) (hG : 0 ≤ G)
    (z : ℝ → MomentumState (A := A) (I := I) Q) (hz : Continuous z)
    (hDrift : Continuous (fun t ↦ momentumDrift Q D γ (z t)))
    (heq : ∀ t, 0 ≤ t → z t - z 0 = (∫ r in 0..t, momentumDrift Q D γ (z r)) +
      momentumInput Q W hW γ t)
    (hbound : ∀ t ∈ Icc 0 T, ‖z t‖ ≤ P ∧ ‖momentumDrift Q D γ (z t)‖ ≤ G)
    (hmod : ∀ a s : ℝ, 0 ≤ a → 0 ≤ s → s ≤ 1 → a + s ≤ T →
      ‖z (a + s) - z a‖ ≤ R * Real.sqrt s)
    (hpaths : iIndepFun (fun i ω (j : ℕ) ↦ W i ((j : ℝ≥0) * (h / 2).toNNReal) ω) Q)
    (n : ℕ) (hn : (n : ℝ) * h ≤ T) : MomentumIntegralReference Q W hW D γ h R P (G + γ * P) n := by
  let p := fun k : ℕ ↦ fun t : ℝ ↦ (z ((k : ℝ) * h + t)).1
  let q := fun k : ℕ ↦ fun t : ℝ ↦ (z ((k : ℝ) * h + t)).2
  have hclock (k : ℕ) (hk : k < n) : (k : ℝ) * h + h ≤ T := by
    calc
      _ = ((k + 1 : ℕ) : ℝ) * h := by push_cast; ring
      _ ≤ (n : ℝ) * h := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hk) hh.le
      _ ≤ T := hn
  have htime (k : ℕ) (hk : k < n) : (k : ℝ) * h ∈ Icc 0 T :=
    ⟨mul_nonneg (Nat.cast_nonneg k) hh.le, (by linarith [hclock k hk])⟩
  have hcontp (k : ℕ) : Continuous (p k) :=
    continuous_fst.comp (hz.comp (continuous_const.add continuous_id))
  have hcontq (k : ℕ) : Continuous (q k) :=
    continuous_snd.comp (hz.comp (continuous_const.add continuous_id))
  have hforce (k : ℕ) : Continuous (fun t ↦
      coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) (q k t) + γ • p k t) := by
    have h : Continuous (fun t : ℝ ↦ -(momentumDrift Q D γ (z ((k : ℝ) * h + t))).1) :=
      (continuous_fst.comp (hDrift.comp (continuous_const.add continuous_id))).neg
    convert h using 1
    funext t
    dsimp [p, q, momentumDrift]
    module
  refine {
    friction_nonneg := hγ
    step_pos := hh
    step_le_one := hh1
    modulus_nonneg := hR
    momentum_nonneg := hP
    force_nonneg := add_nonneg hG (mul_nonneg hγ hP)
    independent_paths := hpaths
    p := p
    q := q
    momentum_integrable := fun k _ ↦ (hcontp k).intervalIntegrable 0 h
    force_integrable := fun k _ ↦ (hforce k).intervalIntegrable 0 h
    momentum_equation := ?_
    position_equation := ?_
    grid_compatible := ?_
    modulus := ?_
    momentum_bound := ?_
    force_bound := ?_ }
  · intro k _
    simpa only [p, q, add_zero] using (momentum_global_step Q W hW D γ h hγ hh z hDrift heq k).1
  · intro k _
    simpa only [p, q, add_zero] using (momentum_global_step Q W hW D γ h hγ hh z hDrift heq k).2
  · intro k _
    have he : ((k + 1 : ℕ) : ℝ) * h + 0 = (k : ℝ) * h + h := by push_cast; ring
    exact ⟨congrArg Prod.fst (congrArg z he), congrArg Prod.snd (congrArg z he)⟩
  · intro k hk t ht
    have hs := hmod ((k : ℝ) * h) t (htime k hk).1 ht.1 (ht.2.trans hh1)
      (by linarith [ht.2, hclock k hk])
    constructor
    · simpa only [p, add_zero, Prod.fst_sub] using (norm_fst_le (z ((k : ℝ) * h + t) - z ((k : ℝ) * h))).trans hs
    · simpa only [q, add_zero, Prod.snd_sub] using (norm_snd_le (z ((k : ℝ) * h + t) - z ((k : ℝ) * h))).trans hs
  · intro k hk
    simpa only [p, add_zero] using (norm_fst_le (z ((k : ℝ) * h))).trans (hbound _ (htime k hk)).1
  · intro k hk
    simpa only [q, add_zero] using momentum_force_radius Q D γ P G hγ (z ((k : ℝ) * h))
      (hbound _ (htime k hk)).1 (hbound _ (htime k hk)).2

end PBGSO.MethodSegments

namespace PBGSO.MethodSegments
open Methods ImplementationDynamics
section ActualSource
variable {Ω A J : Type*} {N : ℕ} [MeasurableSpace Ω] [Fintype J]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  (W : (Fin N × J) → ℝ≥0 → Ω → ℝ)
  (hW : ∀ i, IsPreBrownianReal (W i) Q)
  (D : ParticleForceData A (EuclideanSpace ℝ J) (EuclideanSpace ℝ (Fin N × J)) N)
  (hcloud : D.cloud = euclideanParticleEncoding N J)
include hcloud

/-- Every actual global particle integral trajectory has original kinetic
references on all meshes in a finite horizon. All force, momentum and modulus
constants are derived from that trajectory and are independent of the mesh.
The physical noise and state coordinates are proved equal to the original
implementation inputs and variables. -/
theorem exists_momentum_references_from_source (γ : ℝ) (hγ : 0 ≤ γ)
    (Y : ℝ → Lp (HypocoercivePhase A × (Fin N → HypocoercivePhase (EuclideanSpace ℝ J))) 2 Q)
    (hY : Continuous Y)
    (heq : ∀ t, 0 ≤ t → Y t - Y 0 =
      (∫ r in 0..t, ULA.lpDrift Q ((momentumForceDynamics D γ).particleField N)
        ((momentumForceDynamics D γ).particleField_lipschitz N D.nonempty) (Y r)) +
      samplerBrownianInput Q (ParticleBrownianInput.diffusion (A := HypocoercivePhase A) N
        (momentumPhysicalDiffusion (J := J) γ)) W hW 0 t)
    (hpaths : ∀ h : ℝ≥0, iIndepFun (fun i ω (j : ℕ) ↦ W i ((j : ℝ≥0) * h) ω) Q)
    (T : ℝ) :
    ∃ P G R : ℝ, 0 ≤ P ∧ 0 ≤ G ∧ 0 ≤ R ∧
      ∀ (h : ℝ), 0 < h → h ≤ 1 → ∀ n : ℕ, (n : ℝ) * h ≤ T →
        ∃ Ref : MomentumIntegralReference Q W hW D γ h R P (G + γ * P) n,
          ∀ k t, Ref.p k t = (momentumUnpackLp Q D (Y ((k : ℝ) * h + t))).1 ∧
            Ref.q k t = (momentumUnpackLp Q D (Y ((k : ℝ) * h + t))).2 := by
  let L := momentumForceDynamics D γ
  let f := ULA.lpDrift Q (L.particleField N) (L.particleField_lipschitz N D.nonempty)
  let U := momentumUnpackLp Q D
  let K := ParticleBrownianInput.diffusion (A := HypocoercivePhase A) N (momentumPhysicalDiffusion (J := J) γ)
  have hf : LipschitzWith L.fieldLip f := ULA.lpDrift_lipschitz Q _ _
  obtain ⟨P0, G0, R0, hP0, hG0, hR0, hbound, hmod⟩ := exists_brownian_mesh_regularity
    Q f L.fieldLip hf Y hY K W hW T (fun t ht ↦ heq t ht.1)
  let c : ℝ := ‖U‖
  let z := fun t ↦ U (Y t)
  have hzc : Continuous z := U.continuous.comp hY
  have hd (t : ℝ) : momentumDrift Q D γ (z t) = U (f (Y t)) :=
    (momentumUnpackLp_drift Q D γ (Y t)).symm
  have hdc : Continuous (fun t ↦ momentumDrift Q D γ (z t)) := by
    simp_rw [hd]
    exact U.continuous.comp (hf.continuous.comp hY)
  have hze (t : ℝ) (ht : 0 ≤ t) : z t - z 0 =
      (∫ r in 0..t, momentumDrift Q D γ (z r)) + momentumInput Q W hW γ t := by
    have h := momentumUnpackLp_integral Q D γ Y (samplerBrownianInput Q K W hW 0) hY heq t ht
    rw [momentumUnpackLp_brownian Q D hcloud W hW γ 0 t] at h
    exact h
  have hzb (t : ℝ) (ht : t ∈ Icc 0 T) : ‖z t‖ ≤ c * P0 ∧
      ‖momentumDrift Q D γ (z t)‖ ≤ c * G0 := by
    constructor
    · exact (U.le_opNorm (Y t)).trans (mul_le_mul_of_nonneg_left (hbound t ht).1 (norm_nonneg U))
    · rw [hd]
      exact (U.le_opNorm (f (Y t))).trans (mul_le_mul_of_nonneg_left (hbound t ht).2 (norm_nonneg U))
  have hzm (a s : ℝ) (ha : 0 ≤ a) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hasT : a + s ≤ T) :
      ‖z (a + s) - z a‖ ≤ (c * R0) * Real.sqrt s := by
    change ‖U (Y (a + s)) - U (Y a)‖ ≤ _
    rw [← map_sub]
    exact (U.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (hmod a s ha hs hs1 hasT).1
      (norm_nonneg U)).trans_eq (by dsimp [c]; ring))
  refine ⟨c * P0, c * G0, c * R0, mul_nonneg (norm_nonneg U) hP0,
    mul_nonneg (norm_nonneg U) hG0, mul_nonneg (norm_nonneg U) hR0, ?_⟩
  intro h hh hh1 n hn
  let Ref := momentumReferenceOfGlobal Q W hW D γ h T (c * R0) (c * P0) (c * G0) hγ hh hh1
    (mul_nonneg (norm_nonneg U) hR0) (mul_nonneg (norm_nonneg U) hP0)
    (mul_nonneg (norm_nonneg U) hG0) z hzc hdc hze hzb hzm (hpaths (h / 2).toNNReal) n hn
  exact ⟨Ref, fun _ _ ↦ ⟨rfl, rfl⟩⟩

end ActualSource
end PBGSO.MethodSegments
