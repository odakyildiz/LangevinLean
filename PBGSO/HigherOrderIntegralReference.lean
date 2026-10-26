import PBGSO.MethodIntegralSegments
import PBGSO.MethodDiffusionCoordinates
import PBGSO.GlobalMeshRegularity

/-! # Actual HOL integral segments
An actual global integral trajectory supplies the original HOL reference
segments. All node force and auxiliary bounds follow from complete state
and drift bounds; the shifted-force bound uses the primitive force Lipschitz
constant. No reference equation or innovation matching is assumed separately.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace PBGSO.MethodSegments
open Methods

variable {Ω A X I : Type*} {N : ℕ} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [Fintype I] [DecidableEq I]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  {f : Ω → ULA.CanonicalBrownian.VectorSample I}
  (hf : MeasurePreserving f Q (ULA.CanonicalBrownian.vectorProbability I))
  (D : ParticleForceData A X (EuclideanSpace ℝ I) N)

private theorem node_in_horizon (h : ℝ≥0) {n k : ℕ} (hk : k < n)
    {T s : ℝ} (hs0 : 0 ≤ s) (hsh : s ≤ (h : ℝ)) (hn : n * (h : ℝ) ≤ T) :
    (k : ℝ) * (h : ℝ) + s ∈ Icc 0 T := by
  constructor
  · positivity
  · have hk' : (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hk
    calc
      (k : ℝ) * (h : ℝ) + s ≤ ((k : ℝ) + 1) * (h : ℝ) := by nlinarith
      _ ≤ (n : ℝ) * (h : ℝ) := mul_le_mul_of_nonneg_right hk' h.coe_nonneg
      _ ≤ T := hn

/-- Construct the actual original HOL integral reference by segmenting a
single global trajectory. Its force and moment bounds are derived from
complete state/drift bounds, uniformly over every mesh in the horizon. -/
def higherOrderReference_of_integral
    (α γ P G C T : ℝ) (hα : 0 < α) (hγ : 0 ≤ γ)
    (hP : 0 ≤ P) (hG : 0 ≤ G) (hC : 0 ≤ C)
    (z : ℝ → HOLState (Lp A 2 Q) (Lp (EuclideanSpace ℝ I) 2 Q))
    (hd : Continuous (fun t ↦ holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ (z t)))
    (heq : ∀ t, 0 ≤ t → z t - z 0 =
      (∫ r in 0..t, holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ (z r)) +
        higherOrderInput Q hf α t)
    (hstate : ∀ t ∈ Icc 0 T, ‖z t‖ ≤ P)
    (hdrift : ∀ t ∈ Icc 0 T,
      ‖holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ (z t)‖ ≤ G)
    (hmod : ∀ a s : ℝ, 0 ≤ a → 0 ≤ s → s ≤ 1 → a + s ≤ T →
      ‖holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ (z (a + s)) -
        holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ (z a)‖ ≤ C * Real.sqrt s)
    (h : ℝ≥0) (n : ℕ) (hh : 0 < (h : ℝ)) (hh1 : (h : ℝ) ≤ 1)
    (hn : n * (h : ℝ) ≤ T) :
    HigherOrderPullbackIntegralReference I Q hf D α γ G
      (G + γ * P + (D.samplerForceLip : ℝ) * G) P P C h n where
  auxiliary_friction_pos := hα
  momentum_coupling_nonneg := hγ
  step_pos := hh
  step_le_one := hh1
  optimizer_force_nonneg := hG
  sampler_force_nonneg := by positivity
  first_auxiliary_nonneg := hP
  second_auxiliary_nonneg := hP
  modulus_nonneg := hC
  r k s := z ((k : ℝ) * (h : ℝ) + s)
  drift_integrable k hk := hd.comp (continuous_const.add continuous_id) |>.intervalIntegrable _ _
  equation k hk := by
    have hs := integral_shift z _ (higherOrderInput (A := A) Q hf α) hd heq
      ((k : ℝ) * (h : ℝ)) (h : ℝ) (by positivity) h.coe_nonneg
    rw [higherOrderInput_increment Q hf α γ hα.le h k] at hs
    simpa only [add_zero] using (sub_eq_iff_eq_add.mp hs).trans (by abel)
  grid_compatible k hk := by congr 1; push_cast; ring
  drift_modulus k hk s hs := by
    simpa only [add_zero] using hmod ((k : ℝ) * (h : ℝ)) s
      (by positivity) hs.1 (hs.2.trans hh1) (node_in_horizon h hk hs.1 hs.2 hn).2
  optimizer_force_bound k hk := by
    simpa only [add_zero, holDrift, norm_neg] using
      (norm_fst_le (holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ
        (z ((k : ℝ) * (h : ℝ))))).trans
        (hdrift _ (by simpa using node_in_horizon h hk (le_refl (0 : ℝ)) h.coe_nonneg hn))
  sampler_force_bound k hk := by
    let w := z ((k : ℝ) * (h : ℝ))
    let d := holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ w
    have hw : ‖w‖ ≤ P := hstate _
      (by simpa using node_in_horizon h hk (le_refl (0 : ℝ)) h.coe_nonneg hn)
    have hdg : ‖d‖ ≤ G := hdrift _
      (by simpa using node_in_horizon h hk (le_refl (0 : ℝ)) h.coe_nonneg hn)
    have hv : ‖w.2.2.2‖ ≤ P :=
      (norm_snd_le w.2.2).trans ((norm_snd_le w.2).trans ((norm_snd_le w).trans hw))
    have hdu : ‖d.2.2.1‖ ≤ G :=
      (norm_fst_le d.2.2).trans ((norm_snd_le d.2).trans ((norm_snd_le d).trans hdg))
    have hforce : ‖D.samplerForceLp Q w.1 w.2.1‖ ≤ G + γ * P := by
      have hid : D.samplerForceLp Q w.1 w.2.1 = -d.2.2.1 + γ • w.2.2.2 := by
        dsimp [d, holDrift]; module
      rw [hid]
      calc
        _ ≤ ‖-d.2.2.1‖ + ‖γ • w.2.2.2‖ := norm_add_le _ _
        _ = ‖d.2.2.1‖ + γ * ‖w.2.2.2‖ := by rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ]
        _ ≤ G + γ * P := add_le_add hdu (mul_le_mul_of_nonneg_left hv hγ)
    have hopt : ‖D.meanForceLp Q w.1 w.2.1‖ ≤ G := by
      simpa only [d, holDrift, norm_neg] using (norm_fst_le d).trans hdg
    have hpert := D.samplerForceLp_bound Q
      (w.1 - (h : ℝ) • D.meanForceLp Q w.1 w.2.1) w.1 w.2.1 w.2.1
    have hdiff : ‖(w.1 - (h : ℝ) • D.meanForceLp Q w.1 w.2.1) - w.1‖ ≤ G := by
      rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg h.coe_nonneg]
      exact (mul_le_mul_of_nonneg_left hopt h.coe_nonneg).trans (by nlinarith)
    have hpert' : ‖D.samplerForceLp Q
        (w.1 - (h : ℝ) • D.meanForceLp Q w.1 w.2.1) w.2.1 -
        D.samplerForceLp Q w.1 w.2.1‖ ≤ (D.samplerForceLip : ℝ) * G := by
      exact hpert.trans (by simpa only [sub_self, norm_zero, add_zero] using
        mul_le_mul_of_nonneg_left hdiff D.samplerForceLip.coe_nonneg)
    simp only [add_zero]
    change ‖D.samplerForceLp Q (w.1 - (h : ℝ) • D.meanForceLp Q w.1 w.2.1) w.2.1‖ ≤ _
    exact (norm_le_norm_sub_add _ _).trans (by linarith)
  first_auxiliary_bound k hk := by
    simpa only [add_zero] using
      (norm_fst_le (z ((k : ℝ) * (h : ℝ))).2.2).trans
        ((norm_snd_le (z ((k : ℝ) * (h : ℝ))).2).trans
          ((norm_snd_le (z ((k : ℝ) * (h : ℝ)))).trans
            (hstate _ (by simpa using node_in_horizon h hk (le_refl (0 : ℝ)) h.coe_nonneg hn))))
  second_auxiliary_bound k hk := by
    simpa only [add_zero] using
      (norm_snd_le (z ((k : ℝ) * (h : ℝ))).2.2).trans
        ((norm_snd_le (z ((k : ℝ) * (h : ℝ))).2).trans
          ((norm_snd_le (z ((k : ℝ) * (h : ℝ)))).trans
            (hstate _ (by simpa using node_in_horizon h hk (le_refl (0 : ℝ)) h.coe_nonneg hn))))

end PBGSO.MethodSegments


namespace PBGSO.MethodSegments
open Methods ImplementationDynamics
section ActualSource
variable {Ω A J : Type*} {N : ℕ} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [Fintype J] [DecidableEq J]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  {f : Ω → ULA.CanonicalBrownian.VectorSample (Fin N × J)}
  (hf : MeasurePreserving f Q (ULA.CanonicalBrownian.vectorProbability (Fin N × J)))
  (D : ParticleForceData A (EuclideanSpace ℝ J) (EuclideanSpace ℝ (Fin N × J)) N)

/-- The actual full empirical HOL integral process supplies reference
segments for every mesh in a fixed horizon. State, force and modulus
constants are derived once from that process and are independent of the
mesh. All raw/model coordinates and Gaussian-input matching are proved. -/
theorem exists_higherOrderReference_of_particle_integral
    (hcloud : D.cloud = euclideanParticleEncoding N J)
    (α γ : ℝ) (hα : 0 < α) (hγ : 0 ≤ γ)
    (Y : ℝ → Lp (A × (Fin N → HigherOrderSampler (EuclideanSpace ℝ J))) 2 Q)
    (hY : Continuous Y)
    (heq : ∀ t, 0 ≤ t → Y t - Y 0 =
      (∫ r in 0..t, ULA.lpDrift Q ((higherOrderForceDynamics D α γ).particleField N)
        ((higherOrderForceDynamics D α γ).particleField_lipschitz N D.nonempty) (Y r)) +
      samplerBrownianInput Q (ParticleBrownianInput.diffusion (A := A) N
        (higherOrderPhysicalDiffusion (J := J) α))
        (canonicalPullbackCoordinate (Fin N × J) hf)
        (canonicalPullbackCoordinate_isPreBrownian (Fin N × J) hf) 0 t)
    (T : ℝ) :
    ∃ P G C : ℝ, 0 ≤ P ∧ 0 ≤ G ∧ 0 ≤ C ∧
      ∀ (h : ℝ≥0) (n : ℕ), 0 < (h : ℝ) → (h : ℝ) ≤ 1 → n * (h : ℝ) ≤ T →
        ∃ Ref : HigherOrderPullbackIntegralReference (Fin N × J) Q hf D α γ G
          (G + γ * P + (D.samplerForceLip : ℝ) * G) P P C h n,
          ∀ k s, Ref.r k s = higherOrderUnpackLp Q D (Y ((k : ℝ) * (h : ℝ) + s)) := by
  let L := higherOrderForceDynamics D α γ
  let F := ULA.lpDrift Q (L.particleField N) (L.particleField_lipschitz N D.nonempty)
  have hF : LipschitzWith L.fieldLip F := ULA.lpDrift_lipschitz Q _ _
  let U := higherOrderUnpackLp Q D
  let K := ParticleBrownianInput.diffusion (A := A) N (higherOrderPhysicalDiffusion (J := J) α)
  let W := canonicalPullbackCoordinate (Fin N × J) hf
  let hW := canonicalPullbackCoordinate_isPreBrownian (Fin N × J) hf
  obtain ⟨P0, G0, R0, hP0, hG0, hR0, hbounds, hmod⟩ :=
    exists_brownian_mesh_regularity Q F L.fieldLip hF Y hY K W hW T
      (fun t ht ↦ heq t ht.1)
  have hcoord (V : Lp (A × (Fin N → HigherOrderSampler (EuclideanSpace ℝ J))) 2 Q) :
      U (F V) = holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ (U V) :=
    higherOrderUnpackLp_drift Q D α γ V
  have hd : Continuous (fun t ↦ holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ (U (Y t))) := by
    have hc := U.continuous.comp (hF.continuous.comp hY)
    exact hc.congr fun t ↦ hcoord (Y t)
  have hraw : ∀ t, 0 ≤ t → U (Y t) - U (Y 0) =
      (∫ r in 0..t, holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ (U (Y r))) +
        higherOrderInput Q hf α t := by
    intro t ht
    have he := higherOrderUnpackLp_integral Q D α γ Y
      (samplerBrownianInput Q K W hW 0) hY heq t ht
    rw [higherOrderUnpackLp_brownian Q D hcloud W hW] at he
    exact he
  refine ⟨‖U‖ * P0, ‖U‖ * G0, ‖U‖ * (L.fieldLip : ℝ) * R0,
    by positivity, by positivity, by positivity, ?_⟩
  intro h n hh hh1 hn
  let Ref := higherOrderReference_of_integral Q hf D α γ
    (‖U‖ * P0) (‖U‖ * G0) (‖U‖ * (L.fieldLip : ℝ) * R0) T
    hα hγ (by positivity) (by positivity) (by positivity) (fun t ↦ U (Y t)) hd hraw
    (fun t ht ↦ (U.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hbounds t ht).1 (norm_nonneg U)))
    (fun t ht ↦ by
      rw [← hcoord]
      exact (U.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (hbounds t ht).2 (norm_nonneg U)))
    (fun a s ha hs hs1 haT ↦ by
      rw [← hcoord, ← hcoord, ← map_sub]
      exact (U.le_opNorm _).trans ((mul_le_mul_of_nonneg_left
        (hmod a s ha hs hs1 haT).2 (norm_nonneg U)).trans_eq (by ring)))
    h n hh hh1 hn
  exact ⟨Ref, fun _ _ ↦ rfl⟩
end ActualSource
end PBGSO.MethodSegments
