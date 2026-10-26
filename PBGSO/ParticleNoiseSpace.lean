import PBGSO.IndependentCopies
import UnadjustedLangevin.CanonicalBrownian

/-! # The actual particle-seed space has the flattened canonical noise law

Each seed pairs an initial sampler variable with its independent canonical
Brownian-coordinate source. Projecting out the initial variables and flattening
the particle/spatial indices preserves the full canonical Brownian source
measure. Hence every Gaussian block law and L² bound proved there transports
to the actual random-initial particle construction.
-/
noncomputable section
open MeasureTheory
namespace PBGSO
namespace ParticleNoiseSpace

variable {Z J : Type*} [MeasurableSpace Z]
  (μ : Measure Z) [IsProbabilityMeasure μ] (N : ℕ)

/-- The canonical product seed measure used for all reference copies. -/
def probability : Measure (Fin N → Z × ULA.CanonicalBrownian.VectorSample J) :=
  IndependentCopies.seeds (μ.prod (ULA.CanonicalBrownian.vectorProbability J))

instance : IsProbabilityMeasure (probability (J := J) μ N) := by
  unfold probability
  infer_instance

/-- Forget initial states and flatten particle and spatial noise indices. -/
def noise (ω : Fin N → Z × ULA.CanonicalBrownian.VectorSample J) :
    ULA.CanonicalBrownian.VectorSample (Fin N × J) :=
  fun ij => (ω ij.1).2 ij.2

/-- The *entire* Brownian source is canonical after flattening, not only
one-time Gaussian marginals. -/
theorem noise_preserving :
    MeasurePreserving (noise (Z := Z) (J := J) (N := N)) (probability (J := J) μ N)
      (ULA.CanonicalBrownian.vectorProbability (Fin N × J)) := by
  have hp := measurePreserving_pi
    (fun _ : Fin N => μ.prod (ULA.CanonicalBrownian.vectorProbability J))
    (fun _ : Fin N => ULA.CanonicalBrownian.vectorProbability J)
    (fun _ => measurePreserving_snd (μ := μ) (ν := ULA.CanonicalBrownian.vectorProbability J))
  have hc : MeasurePreserving
      (MeasurableEquiv.curry (Fin N) J ULA.CanonicalBrownian.Sample).symm
      (Measure.pi (fun _ : Fin N => ULA.CanonicalBrownian.vectorProbability J))
      (ULA.CanonicalBrownian.vectorProbability (Fin N × J)) := by
    constructor
    · exact (MeasurableEquiv.curry (Fin N) J ULA.CanonicalBrownian.Sample).symm.measurable
    · rw [← Measure.infinitePi_eq_pi]
      exact Measure.infinitePi_map_curry_symm
        (fun (_ : Fin N) (_ : J) => ULA.CanonicalBrownian.probability)
  exact hc.comp hp

/-- The complete random initial cloud, before the evolution is constructed. -/
def initial (ω : Fin N → Z × ULA.CanonicalBrownian.VectorSample J) : Fin N → Z :=
  fun i => (ω i).1

theorem initial_preserving :
    MeasurePreserving (initial (Z := Z) (J := J) (N := N)) (probability (J := J) μ N)
      (Measure.pi (fun _ : Fin N => μ)) :=
  measurePreserving_pi _ _ (fun _ : Fin N =>
    measurePreserving_fst (μ := μ) (ν := ULA.CanonicalBrownian.vectorProbability J))

/-- The actual joint law is the product of the initial cloud and the full
flattened Brownian source, proving their independence at the source level. -/
theorem initial_noise_preserving :
    MeasurePreserving (fun ω => (initial (Z := Z) (J := J) (N := N) ω, noise (N := N) ω))
      (probability (J := J) μ N)
      ((Measure.pi (fun _ : Fin N => μ)).prod
        (ULA.CanonicalBrownian.vectorProbability (Fin N × J))) := by
  have hs := measurePreserving_arrowProdEquivProdArrow Z
    (ULA.CanonicalBrownian.VectorSample J) (Fin N)
    (fun _ => μ) (fun _ => ULA.CanonicalBrownian.vectorProbability J)
  have hc : MeasurePreserving
      (MeasurableEquiv.curry (Fin N) J ULA.CanonicalBrownian.Sample).symm
      (Measure.pi (fun _ : Fin N => ULA.CanonicalBrownian.vectorProbability J))
      (ULA.CanonicalBrownian.vectorProbability (Fin N × J)) := by
    constructor
    · exact (MeasurableEquiv.curry (Fin N) J ULA.CanonicalBrownian.Sample).symm.measurable
    · rw [← Measure.infinitePi_eq_pi]
      exact Measure.infinitePi_map_curry_symm
        (fun (_ : Fin N) (_ : J) => ULA.CanonicalBrownian.probability)
  exact ((MeasurePreserving.id (Measure.pi (fun _ : Fin N => μ))).prod hc).comp hs

/-- The actual initial cloud is independent of the entire Brownian source,
so in particular of all its later innovations and coordinates. -/
theorem initial_noise_independent :
    ProbabilityTheory.IndepFun (initial (Z := Z) (J := J) (N := N)) (noise (Z := Z) (J := J) (N := N))
      (probability (J := J) μ N) := by
  apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    (initial_preserving μ N).measurable.aemeasurable (noise_preserving μ N).measurable.aemeasurable).mpr
  rw [(initial_noise_preserving μ N).map_eq, (initial_preserving μ N).map_eq,
    (noise_preserving μ N).map_eq]

end ParticleNoiseSpace
end PBGSO
