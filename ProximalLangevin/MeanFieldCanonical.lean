import ProximalLangevin.MeanFieldParticles
import ProximalLangevin.MeanFieldInitialSource

set_option linter.style.header false

/-! # A concrete finite-particle mean-field comparison from primitive data

The source is the supplied latent law times the canonical joint Brownian
probability space. Initial square integrability, deterministic parameter,
Brownian laws, full coordinate independence, and initialization/noise
independence are derived. The finite-time constant and actual particle
integral solutions are then constructed by the proved comparison theorem.
The conclusion is uniform-in-time L² control, rather than an expectation of a
pathwise supremum.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace ProximalLangevin

/-- Actual interacting-particle Brownian coordinates on the iid initialized
canonical source: every coordinate is standard Brownian and all full paths
are independent, including common-parameter and first-particle coordinates. -/
theorem initialized_particleBrownianFamily {N dθ dx : ℕ} (hN : 0 < N)
    (μ : Measure (EuclideanSpace ℝ (Fin dx))) [IsProbabilityMeasure μ] :
    (∀ a : Fin dθ ⊕ (Fin N × Fin dx),
      IsPreBrownianReal (particleBrownianFamily hN (@meanFieldInitialBrownian dθ dx) a)
        (Measure.pi (fun _ : Fin N => meanFieldInitialSource dθ μ))) ∧
    iIndepFun (fun a ω t => particleBrownianFamily hN (@meanFieldInitialBrownian dθ dx) a t ω)
      (Measure.pi (fun _ : Fin N => meanFieldInitialSource dθ μ)) := by
  exact ⟨particleBrownianFamily_preBrownian (meanFieldInitialSource dθ μ) hN _
    (meanFieldInitialBrownian_preBrownian μ),
    particleBrownianFamily_paths_independent (meanFieldInitialSource dθ μ) hN _
      meanFieldInitialBrownian_measurable (meanFieldInitialBrownian_paths_independent μ)⟩

/-- From a latent probability law with finite second moment, construct the
mean-field reference and actual interacting-particle processes for every
positive particle count. The displayed constant is independent of that count;
its existence follows from proved finite-horizon moments of the reference. -/
theorem exists_canonical_meanField_particle_comparison
    {dθ dx : ℕ} (V : IPLA.Joint dθ dx → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L (gradient V))
    (μ : Measure (EuclideanSpace ℝ (Fin dx))) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun x : EuclideanSpace ℝ (Fin dx) => x) 2 μ)
    (θ₀ : EuclideanSpace ℝ (Fin dθ)) (T : ℝ) (hT : 0 ≤ T) :
    let Q := meanFieldInitialSource dθ μ
    let initial := meanFieldInitialLp μ θ₀ hμ
    let W := @meanFieldInitialBrownian dθ dx
    let hW := meanFieldInitialBrownian_preBrownian (dθ := dθ) μ
    ∃ (Y : ℝ → Lp (IPLA.Joint dθ dx) 2 Q)
      (θ : ℝ → EuclideanSpace ℝ (Fin dθ)) (C : ℝ),
      0 ≤ C ∧ Continuous Y ∧ Continuous θ ∧ Y 0 = initial ∧ θ 0 = θ₀ ∧
      (∀ t ∈ Icc 0 T, Y t - initial =
        -(∫ s in 0..t, lpMeanFieldDrift Q V hLip (Y s)) + meanFieldBrownianNoise Q W hW 0 t) ∧
      (∀ t ∈ Icc 0 T, jointParameterCLM.compLp (Y t) = Lp.const 2 Q (θ t)) ∧
      (∀ t ∈ Icc 0 T, θ t - θ₀ =
        -(∫ s in 0..t, meanFieldDrift V (θ s) (Q.map (jointLatentCLM.compLp (Y s))))) ∧
      ∀ (N : ℕ) (hN : 0 < N),
      ∃ Z : ℝ → MeanFieldParticleState (Measure.pi (fun _ : Fin N => Q)) N dθ dx,
        Continuous Z ∧ Z 0 = iidMeanFieldCopiesCLM Q initial ∧
        (∀ t ∈ Icc 0 T, Z t - iidMeanFieldCopiesCLM Q initial =
          -(∫ s in 0..t, lpParticleDrift (Measure.pi (fun _ : Fin N => Q)) V hLip (Z s)) +
            iidMeanFieldCopiesCLM Q (meanFieldBrownianNoise Q W hW 0 t) +
            (empiricalParameterNoise Q hN (fun j => W (Sum.inl j))
              (fun j => hW (Sum.inl j)) t, fun _ => 0)) ∧
        (∀ t ∈ Icc 0 T, ∀ i : Fin N,
          ‖(Z t).1 - Lp.const 2 (Measure.pi (fun _ : Fin N => Q)) (θ t)‖ +
          ‖(Z t).2 i - (iidMeanFieldCopiesCLM Q (N := N) (Y t)).2 i‖ ≤
          meanFieldParticleConstant L C (Real.sqrt (2 * (dθ : ℝ)) * Real.sqrt T) T /
            Real.sqrt (N : ℝ)) := by
  exact exists_brownian_meanField_particle_comparison (meanFieldInitialSource dθ μ) V hLip
    (meanFieldInitialLp μ θ₀ hμ) θ₀ (meanFieldInitialLp_parameter μ θ₀ hμ)
    meanFieldInitialBrownian (meanFieldInitialBrownian_preBrownian μ) T hT

end ProximalLangevin
