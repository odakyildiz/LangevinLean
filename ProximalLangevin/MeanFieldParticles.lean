import ProximalLangevin.MeanFieldCopies
import ProximalLangevin.MeanFieldForcing
import ProximalLangevin.MeanFieldNoise

set_option linter.style.header false

/-! # Constructed iid finite-particle mean-field comparison

Both continuous L² integral solutions are constructed by Picard. The iid
copies use the actual finite product law, and their empirical force defect is
proved from exact independent-sampling variance. The resulting estimate is
uniform in time for each coordinate L² norm. It does not move the time
supremum inside an expectation, as in source Proposition C.2. The two
process norms are generally non-comparable.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped NNReal ENNReal
namespace ProximalLangevin

section Comparison
variable {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
  {dθ dx : ℕ} (V : IPLA.Joint dθ dx → ℝ) {L : ℝ≥0}
  (hLip : LipschitzWith L (gradient V))

/-- The centered actual parameter force of one mean-field copy. -/
def centeredMeanFieldForce (X : Lp (IPLA.Joint dθ dx) 2 Q) :
    Lp (EuclideanSpace ℝ (Fin dθ)) 2 Q :=
  lpCenterCLM Q (jointParameterCLM.compLp (ULA.lpDrift Q (gradient V) hLip X))

theorem centeredMeanFieldForce_continuous : Continuous (centeredMeanFieldForce Q V hLip) :=
  (lpCenterCLM Q).continuous.comp
    (((@jointParameterCLM dθ dx).compLpL 2 Q).continuous.comp
      (ULA.lpDrift_lipschitz Q (gradient V) hLip).continuous)

/-- Continuity of the constructed reference supplies a finite force coefficient
on a compact horizon. This coefficient is independent of particle count. -/
theorem exists_centeredMeanFieldForce_bound
    (Y : ℝ → Lp (IPLA.Joint dθ dx) 2 Q) (hY : Continuous Y) (T : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ t∈Icc 0 T,‖centeredMeanFieldForce Q V hLip (Y t)‖≤C := by
  have hc := (centeredMeanFieldForce_continuous Q V hLip).comp hY
  obtain ⟨C,hC⟩ := ((isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).image hc).isBounded.exists_norm_le
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro t ht
  exact (hC _ (mem_image_of_mem _ ht)).trans (le_max_left _ _)

/-- The actual iid reference inherits its integral equation by a bounded
linear map, so its forcing is constructed from the mean-field solution. -/
theorem iidMeanFieldCopies_integral_equation {N : ℕ}
    (initial : Lp (IPLA.Joint dθ dx) 2 Q)
    (B Y : ℝ → Lp (IPLA.Joint dθ dx) 2 Q) (hY : Continuous Y) (T : ℝ)
    (hYe : ∀ t∈Icc 0 T,Y t-initial=-(∫ s in 0..t,lpMeanFieldDrift Q V hLip (Y s))+B t)
    (t : ℝ) (ht : t∈Icc 0 T) :
    iidMeanFieldCopiesCLM Q (N := N) (Y t)-iidMeanFieldCopiesCLM Q initial=
      -(∫ s in 0..t,iidMeanFieldCopiesCLM Q (lpMeanFieldDrift Q V hLip (Y s)))+
        iidMeanFieldCopiesCLM Q (B t) := by
  let C := @iidMeanFieldCopiesCLM Ω _ Q _ N dθ dx
  have hi : IntervalIntegrable (fun s => lpMeanFieldDrift Q V hLip (Y s)) volume 0 t :=
    ((lpMeanFieldDrift_lipschitz Q V hLip).continuous.comp hY).intervalIntegrable 0 t
  have h := congrArg C (hYe t ht)
  rw [map_sub,map_add,map_neg,← C.intervalIntegral_comp_comm (μ := volume) hi] at h
  exact h

/-- Finite-horizon coefficient in the tagged-coordinate L² comparison.
`C` bounds the actual centered reference force, and `b` bounds the parameter
Brownian input after multiplication by `sqrt N`. -/
def meanFieldParticleConstant (L : ℝ≥0) (C b T : ℝ) : ℝ :=
  2*(gronwallBound 0 (2*(L : ℝ)) (C+2*(L : ℝ)*b) T+b)

/-- The constructed particle solution is uniformly close, in each coordinate
L² norm, to the genuine iid copies of an actual mean-field integral solution.
The reference force coefficient is finite and independent of `N`. -/
theorem exists_particle_comparison_of_meanField_solution
    (initial : Lp (IPLA.Joint dθ dx) 2 Q)
    (B Y : ℝ → Lp (IPLA.Joint dθ dx) 2 Q) (hB : Continuous B) (hB0 : B 0=0)
    (hY : Continuous Y) (θ : ℝ → EuclideanSpace ℝ (Fin dθ)) (T : ℝ) (hT : 0≤T)
    (hYe : ∀ t∈Icc 0 T,Y t-initial=-(∫ s in 0..t,lpMeanFieldDrift Q V hLip (Y s))+B t)
    (hθ : ∀ t∈Icc 0 T,jointParameterCLM.compLp (Y t)=Lp.const 2 Q (θ t)) :
    ∃ C : ℝ,0≤C ∧ ∀ (N : ℕ) (_hN : 0<N)
      (Bθ : ℝ → Lp (EuclideanSpace ℝ (Fin dθ)) 2 (Measure.pi (fun _ : Fin N => Q))),
      Continuous Bθ → Bθ 0=0 → ∀ b : ℝ,0≤b →
      (∀ t∈Icc 0 T,‖Bθ t‖≤b/Real.sqrt (N : ℝ)) →
      ∃ Z : ℝ → MeanFieldParticleState (Measure.pi (fun _ : Fin N => Q)) N dθ dx,
        Continuous Z ∧ Z 0=iidMeanFieldCopiesCLM Q initial ∧
        (∀ t∈Icc 0 T,Z t-iidMeanFieldCopiesCLM Q initial=
          -(∫ s in 0..t,lpParticleDrift (Measure.pi (fun _ : Fin N => Q)) V hLip (Z s))+
            iidMeanFieldCopiesCLM Q (B t)+(Bθ t,fun _ => 0)) ∧
        (∀ t∈Icc 0 T,∀ i : Fin N,
          ‖(Z t).1-Lp.const 2 (Measure.pi (fun _ : Fin N => Q)) (θ t)‖+
          ‖(Z t).2 i-(iidMeanFieldCopiesCLM Q (N := N) (Y t)).2 i‖≤
          meanFieldParticleConstant L C b T/Real.sqrt (N : ℝ)) := by
  obtain ⟨C,hC,hforce⟩ := exists_centeredMeanFieldForce_bound Q V hLip Y hY T
  refine ⟨C,hC,?_⟩
  intro N hN Bθ hBθ hBθ0 b hb hnoise
  let P := Measure.pi (fun _ : Fin N => Q)
  let M := @iidMeanFieldCopiesCLM Ω _ Q _ N dθ dx
  let R := fun t => M (Y t)
  let A := fun t => (Bθ t,fun _ : Fin N => (0 : Lp (EuclideanSpace ℝ (Fin dx)) 2 P))
  let B' := fun t => M (B t)
  let G := fun t => M (lpMeanFieldDrift Q V hLip (Y t))
  have hA : Continuous A := hBθ.prodMk continuous_const
  have hB' : Continuous B' := M.continuous.comp hB
  have hR : Continuous R := M.continuous.comp hY
  have hG : Continuous G := M.continuous.comp
    ((lpMeanFieldDrift_lipschitz Q V hLip).continuous.comp hY)
  have hBnoise : Continuous (fun t => B' t+A t) := hB'.add hA
  have hBnoise0 : B' 0+A 0=0 := by
    simp only [B',A,hB0,hBθ0,map_zero,zero_add]
    rfl
  obtain ⟨Z,hZ,hZ0,hZe⟩ := exists_lp_particle_integral P hN V hLip (M initial)
    (fun t => B' t+A t) hBnoise hBnoise0 T hT
  have hA_bound (t : ℝ) (ht : t∈Icc 0 T) : ‖A t‖≤b/Real.sqrt (N : ℝ) := by
    change max ‖Bθ t‖ ‖(0 : Fin N → Lp (EuclideanSpace ℝ (Fin dx)) 2 P)‖≤_
    rw [norm_zero,max_eq_left (norm_nonneg _)]
    exact hnoise t ht
  have hdefect (t : ℝ) (ht : t∈Icc 0 T) :
      ‖lpParticleDrift P V hLip (R t)-G t‖≤C/Real.sqrt (N : ℝ) := by
    rw [iidMeanFieldCopies_drift_residual_norm Q hN V hLip (Y t) (θ t) (hθ t ht)]
    exact div_le_div_of_nonneg_right (hforce t ht) (Real.sqrt_nonneg _)
  have hRe (t : ℝ) (ht : t∈Icc 0 T) :
      R t-M initial=-(∫ s in 0..t,G s)+B' t :=
    iidMeanFieldCopies_integral_equation Q V hLip initial B Y hY T hYe t ht
  have hZeq (t : ℝ) (ht : t∈Icc 0 T) :
      Z t-M initial=-(∫ s in 0..t,lpParticleDrift P V hLip (Z s))+B' t+A t := by
    have hh := hZe t ht
    simpa only [add_assoc] using hh
  have hn : (0 : ℝ)<N := by exact_mod_cast hN
  have hbound := integral_forcing_perturbation_scaled (lpParticleDrift P V hLip) (2*L)
    (lpParticleDrift_lipschitz P hN V hLip) (M initial) B' A G Z R hA hG hZ hR T hT
    C b (Real.sqrt (N : ℝ)) hC hb (Real.sqrt_pos.mpr hn) hA_bound hdefect hZeq hRe
  refine ⟨Z,hZ,hZ0,?_,?_⟩
  · intro t ht
    exact hZeq t ht
  · intro t ht i
    have h₁ : ‖(Z t).1-(R t).1‖≤‖Z t-R t‖ := norm_fst_le (Z t-R t)
    have h₂ : ‖(Z t).2 i-(R t).2 i‖≤‖Z t-R t‖ :=
      (norm_le_pi_norm ((Z t).2-(R t).2) i).trans (norm_snd_le (Z t-R t))
    have hθR : (R t).1=Lp.const 2 P (θ t) :=
      iidMeanFieldCopiesCLM_parameter_const Q (Y t) (θ t) (hθ t ht)
    rw [← hθR]
    calc
      _ ≤ 2*‖Z t-R t‖ := by change ‖(Z t).1-(R t).1‖+‖(Z t).2 i-(R t).2 i‖≤_; linarith
      _ ≤ 2*((gronwallBound 0 ((2*L : ℝ≥0) : ℝ)
          (C+((2*L : ℝ≥0) : ℝ)*b) T+b)/Real.sqrt (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (hbound t ht) (by norm_num)
      _ = _ := by simp only [meanFieldParticleConstant,NNReal.coe_mul,NNReal.coe_ofNat]; ring

/-- Both the mean-field reference and finite-particle coordinate processes are
constructed from actual Brownian-coordinate inputs. The parameter-noise
`N⁻¹/²` bound is proved from those laws by `empiricalParameterNoise_bound`.
The conclusion controls each time's L² norm uniformly over the horizon. -/
theorem exists_brownian_meanField_particle_comparison
    (initial : Lp (IPLA.Joint dθ dx) 2 Q) (θ₀ : EuclideanSpace ℝ (Fin dθ))
    (hinitial : jointParameterCLM.compLp initial=Lp.const 2 Q θ₀)
    (W : (Fin dθ ⊕ Fin dx) → ℝ≥0 → Ω → ℝ)
    (hW : ∀ j,ProbabilityTheory.IsPreBrownianReal (W j) Q)
    (T : ℝ) (hT : 0≤T) :
    ∃ (Y : ℝ → Lp (IPLA.Joint dθ dx) 2 Q)
      (θ : ℝ → EuclideanSpace ℝ (Fin dθ)) (C : ℝ),
      0≤C ∧ Continuous Y ∧ Continuous θ ∧ Y 0=initial ∧ θ 0=θ₀ ∧
      (∀ t∈Icc 0 T,Y t-initial=
        -(∫ s in 0..t,lpMeanFieldDrift Q V hLip (Y s))+meanFieldBrownianNoise Q W hW 0 t) ∧
      (∀ t∈Icc 0 T,jointParameterCLM.compLp (Y t)=Lp.const 2 Q (θ t)) ∧
      (∀ t∈Icc 0 T,θ t-θ₀=
        -(∫ s in 0..t,meanFieldDrift V (θ s) (Q.map (jointLatentCLM.compLp (Y s))))) ∧
      ∀ (N : ℕ) (hN : 0<N),
      ∃ Z : ℝ → MeanFieldParticleState (Measure.pi (fun _ : Fin N => Q)) N dθ dx,
        Continuous Z ∧ Z 0=iidMeanFieldCopiesCLM Q initial ∧
        (∀ t∈Icc 0 T,Z t-iidMeanFieldCopiesCLM Q initial=
          -(∫ s in 0..t,lpParticleDrift (Measure.pi (fun _ : Fin N => Q)) V hLip (Z s))+
            iidMeanFieldCopiesCLM Q (meanFieldBrownianNoise Q W hW 0 t)+
            (empiricalParameterNoise Q hN (fun j => W (Sum.inl j))
              (fun j => hW (Sum.inl j)) t,fun _ => 0)) ∧
        (∀ t∈Icc 0 T,∀ i : Fin N,
          ‖(Z t).1-Lp.const 2 (Measure.pi (fun _ : Fin N => Q)) (θ t)‖+
          ‖(Z t).2 i-(iidMeanFieldCopiesCLM Q (N := N) (Y t)).2 i‖≤
          meanFieldParticleConstant L C (Real.sqrt (2*(dθ : ℝ))*Real.sqrt T) T/
            Real.sqrt (N : ℝ)) := by
  let B := meanFieldBrownianNoise Q W hW 0
  have hB : Continuous B := meanFieldBrownianNoise_continuous Q W hW 0
  have hB0 : B 0=0 := meanFieldBrownianNoise_zero Q W hW 0
  have hBθ : ∀ t,jointParameterCLM.compLp (B t)=0 := meanFieldBrownianNoise_parameter Q W hW 0
  obtain ⟨Y,θ,hY,hθ,hY0,hθ0,hYe,hθdet,hθeq,_⟩ :=
    exists_lp_meanField_equations Q V hLip initial θ₀ hinitial B hB hB0 hBθ T hT
  obtain ⟨C,hC,hcompare⟩ := exists_particle_comparison_of_meanField_solution Q V hLip
    initial B Y hB hB0 hY θ T hT hYe hθdet
  refine ⟨Y,θ,C,hC,hY,hθ,hY0,hθ0,hYe,hθdet,hθeq,?_⟩
  intro N hN
  exact hcompare N hN (empiricalParameterNoise Q hN (fun j => W (Sum.inl j))
      (fun j => hW (Sum.inl j)))
    (empiricalParameterNoise_continuous Q hN _ _) (empiricalParameterNoise_zero Q hN _ _)
    (Real.sqrt (2*(dθ : ℝ))*Real.sqrt T) (by positivity)
    (fun t ht => empiricalParameterNoise_bound Q hN _ _ T t ht)

end Comparison
end ProximalLangevin
