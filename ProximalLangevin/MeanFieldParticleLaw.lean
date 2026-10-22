import ProximalLangevin.MeanFieldCanonical

set_option linter.style.header false

/-! # One-time propagation of chaos for the constructed particle laws

The law estimate uses an explicit coupling with the actual iid reference
copy. Its `1/sqrt N` bound follows from the constructed coordinate process
comparison; it is never supplied as a convergence premise. The public
canonical theorem retains the actual particle integral equation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace ProximalLangevin

/-- An actual iid L² copy has exactly the original law. -/
theorem iidCopyCLM_law {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (Q : Measure Ω) [IsProbabilityMeasure Q]
    {N : ℕ} (i : Fin N) (X : Lp E 2 Q) :
    (Measure.pi (fun _ : Fin N => Q)).map (iidCopyCLM Q i X)=Q.map X := by
  let P := Measure.pi (fun _ : Fin N => Q)
  rw [Measure.map_congr (iidCopyCLM_coe Q i X)]
  have heval : P.map (fun ω : Fin N → Ω => ω i)=Q :=
    (measurePreserving_eval (fun _ : Fin N => Q) i).map_eq
  have hX : AEMeasurable X (P.map (fun ω : Fin N → Ω => ω i)) := by
    rw [heval]
    exact (Lp.aestronglyMeasurable X).aemeasurable
  have hh := AEMeasurable.map_map_of_aemeasurable hX
    (measurable_pi_apply i).aemeasurable
  rw [heval] at hh
  exact hh.symm

/-- The actual tagged-particle pair and the genuine iid copy provide a finite
transport coupling. This helper only translates coordinate L² distances. -/
theorem tagged_particle_wasserstein_le {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] {N dθ dx : ℕ}
    (Y : Lp (IPLA.Joint dθ dx) 2 Q) (θ : EuclideanSpace ℝ (Fin dθ))
    (hθ : jointParameterCLM.compLp Y=Lp.const 2 Q θ)
    (Z : MeanFieldParticleState (Measure.pi (fun _ : Fin N => Q)) N dθ dx) (i : Fin N) :
    ULA.wasserstein2
      ((Measure.pi (fun _ : Fin N => Q)).map (lpJointPair _ Z.1 (Z.2 i))) (Q.map Y) ≠ ⊤ ∧
    ULA.wasserstein2Real
      ((Measure.pi (fun _ : Fin N => Q)).map (lpJointPair _ Z.1 (Z.2 i))) (Q.map Y) ≤
      ‖Z.1-Lp.const 2 (Measure.pi (fun _ : Fin N => Q)) θ‖+
      ‖Z.2 i-(iidMeanFieldCopiesCLM Q (N := N) Y).2 i‖ := by
  let P := Measure.pi (fun _ : Fin N => Q)
  let X := lpJointPair P Z.1 (Z.2 i)
  let R := iidCopyCLM Q i Y
  have hcost := ULA.wasserstein2_le_Lp_cost P X R
  have hreal := ULA.wasserstein2_le_Lp_cost_real P X R
  rw [iidCopyCLM_law Q i Y] at hcost hreal
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcost,hreal.trans ?_⟩
  have hpair := iidMeanFieldCopies_joint Q Y θ hθ i
  have hbound := lpJointPair_difference_le P Z.1
    (iidMeanFieldCopiesCLM Q (N := N) Y).1 (Z.2 i) ((iidMeanFieldCopiesCLM Q Y).2 i)
  rw [hpair,iidMeanFieldCopiesCLM_parameter_const Q Y θ hθ] at hbound
  exact hbound

/-- The actual Brownian input in the particle coordinate equations. The
parameter noise is scaled by `1/sqrt N`; every latent copy keeps its noise. -/
def particleBrownianInput {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] {N dθ dx : ℕ} (hN : 0<N)
    (W : (Fin dθ ⊕ Fin dx) → ℝ≥0 → Ω → ℝ)
    (hW : ∀ j,IsPreBrownianReal (W j) Q) (t : ℝ) :
    MeanFieldParticleState (Measure.pi (fun _ : Fin N => Q)) N dθ dx :=
  iidMeanFieldCopiesCLM Q (meanFieldBrownianNoise Q W hW 0 t)+
    (empiricalParameterNoise Q hN (fun j => W (Sum.inl j))
      (fun j => hW (Sum.inl j)) t,fun _ => 0)

/-- From an arbitrary finite-second-moment latent law and independent
canonical Brownian source, construct both integral solutions and prove the
actual tagged-particle one-time Wasserstein bound, uniformly over the horizon.
This uses a different process norm from the source's expected path supremum
and does not establish that printed bound. -/
theorem exists_canonical_meanField_particle_law_comparison
    {dθ dx : ℕ} (V : IPLA.Joint dθ dx → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L (gradient V))
    (μ : Measure (EuclideanSpace ℝ (Fin dx))) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun x : EuclideanSpace ℝ (Fin dx) => x) 2 μ)
    (θ₀ : EuclideanSpace ℝ (Fin dθ)) (T : ℝ) (hT : 0≤T) :
    let Q := meanFieldInitialSource dθ μ
    let initial := meanFieldInitialLp μ θ₀ hμ
    let W := @meanFieldInitialBrownian dθ dx
    let hW := meanFieldInitialBrownian_preBrownian (dθ := dθ) μ
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
            particleBrownianInput Q hN W hW t) ∧
        (∀ t∈Icc 0 T,∀ i : Fin N,
          ULA.wasserstein2 ((Measure.pi (fun _ : Fin N => Q)).map
            (lpJointPair _ (Z t).1 ((Z t).2 i))) (Q.map (Y t)) ≠ ⊤ ∧
          ULA.wasserstein2Real ((Measure.pi (fun _ : Fin N => Q)).map
            (lpJointPair _ (Z t).1 ((Z t).2 i))) (Q.map (Y t)) ≤
            meanFieldParticleConstant L C (Real.sqrt (2*(dθ : ℝ))*Real.sqrt T) T/
              Real.sqrt (N : ℝ)) := by
  obtain ⟨Y,θ,C,hC,hY,hθ,hY0,hθ0,hYe,hθdet,hθeq,hparticles⟩ :=
    exists_canonical_meanField_particle_comparison V hLip μ hμ θ₀ T hT
  refine ⟨Y,θ,C,hC,hY,hθ,hY0,hθ0,hYe,hθdet,hθeq,?_⟩
  intro N hN
  obtain ⟨Z,hZ,hZ0,hZe,hbound⟩ := hparticles N hN
  refine ⟨Z,hZ,hZ0,?_,?_⟩
  · intro t ht
    have hh := hZe t ht
    simpa only [particleBrownianInput,add_assoc] using hh
  · intro t ht i
    have hh := tagged_particle_wasserstein_le (meanFieldInitialSource dθ μ)
      (Y t) (θ t) (hθdet t ht) (Z t) i
    exact ⟨hh.1,hh.2.trans (hbound t ht i)⟩

end ProximalLangevin
