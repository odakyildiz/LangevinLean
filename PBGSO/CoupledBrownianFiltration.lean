import PBGSO.FilteredIntegralEnlargement
import PBGSO.FilteredBrownianPullback
import PBGSO.CanonicalBrownianDriver
import PBGSO.AdditiveCanonicalRealization

/-! # One full initial-coupling filtration for the two actual marginal laws
The full coupled initial variable and shared vector Brownian past generate
one genuine filtration. Each marginal's pulled filtration is a subfiltration;
the same actual Brownian coordinates remain independent of the full past.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace PBGSO.CanonicalInitialFiltration
variable {Z Y I : Type*} [Fintype I]
  [NormedAddCommGroup Z] [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [NormedAddCommGroup Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]

/-- Projecting the initial state uses only the original full initial/noise
past. Hence its actual pulled natural filtration is contained in the full one. -/
theorem projection_filtration_le (j : Z → Y) (hj : Continuous j) (t : ℝ≥0) :
    (filtration (Z := Y) (I := I) t).comap
      (fun p : Z × ULA.CanonicalBrownian.VectorSample I ↦ (j p.1, p.2)) ≤
      filtration (Z := Z) (I := I) t := by
  simp only [filtration, Filtration.natural_eq_comap, MeasurableSpace.comap_comp]
  let H : (Iic t → Z × (I → ℝ)) → (Iic t → Y × (I → ℝ)) :=
    fun h r ↦ (j (h r).1, (h r).2)
  have hH : Measurable H := measurable_pi_iff.mpr fun r ↦
    (hj.measurable.comp ((measurable_pi_apply r).fst)).prodMk (measurable_pi_apply r).snd
  have hh := MeasurableSpace.comap_mono (g := fun p (r : Iic t) ↦ process r p) hH.comap_le
  simpa only [MeasurableSpace.comap_comp, H, Function.comp_def, process] using hh

end PBGSO.CanonicalInitialFiltration

namespace PBGSO.CoupledBrownianFiltration
variable {Z I : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (μ ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  (c : ULA.Coupling μ ν)

local instance jointProbability : IsProbabilityMeasure c.joint := c.isProbabilityMeasure
local instance extensionProbability : IsProbabilityMeasure
    (ULA.initialExtension c (ULA.CanonicalBrownian.vectorProbability I)) :=
  ULA.initialExtension_isProbabilityMeasure c (ULA.CanonicalBrownian.vectorProbability I)

/-- The actual Driver of the entire coupled initial variable and common
vector Brownian source. -/
def fullDriver : FilteredBrownian.Driver (I := I)
    (ULA.initialExtension c (ULA.CanonicalBrownian.vectorProbability I)) :=
  CanonicalBrownianDriver.driver (I := I) c.joint

/-- The left canonical law process pulled to the actual coupled source. -/
def leftDriver : FilteredBrownian.Driver (I := I)
    (ULA.initialExtension c (ULA.CanonicalBrownian.vectorProbability I)) :=
  FilteredBrownian.pullbackDriver
    (AdditiveCanonical.extension_left_preserving (ULA.CanonicalBrownian.vectorProbability I) μ ν c)
    (CanonicalBrownianDriver.driver (I := I) μ)

/-- The right canonical law process pulled to the same actual coupled source. -/
def rightDriver : FilteredBrownian.Driver (I := I)
    (ULA.initialExtension c (ULA.CanonicalBrownian.vectorProbability I)) :=
  FilteredBrownian.pullbackDriver
    (AdditiveCanonical.extension_right_preserving (ULA.CanonicalBrownian.vectorProbability I) μ ν c)
    (CanonicalBrownianDriver.driver (I := I) ν)

/-- Both marginal constructions use literally the full Driver's coordinates. -/
theorem left_process_eq : (leftDriver (I := I) μ ν c).process = (fullDriver (I := I) μ ν c).process := rfl

theorem right_process_eq : (rightDriver (I := I) μ ν c).process = (fullDriver (I := I) μ ν c).process := rfl

/-- All left initial/noise information is part of the actual full coupled past. -/
theorem left_filtration_le (t : ℝ≥0) :
    (leftDriver (I := I) μ ν c).filtration t ≤ (fullDriver μ ν c).filtration t :=
  CanonicalInitialFiltration.projection_filtration_le Prod.fst continuous_fst t

/-- The same inclusion holds for the right initial/noise past. -/
theorem right_filtration_le (t : ℝ≥0) :
    (rightDriver (I := I) μ ν c).filtration t ≤ (fullDriver μ ν c).filtration t :=
  CanonicalInitialFiltration.projection_filtration_le Prod.snd continuous_snd t

section Integral
variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- The left marginal's actual integral domain, placed in the full coupled
filtration without changing its actual pulled time integrand. -/
def leftFullDomain (G : GridIntegralCompletion.RefiningGrids)
    (u : FilteredBrownian.IntegralDomain (Z := H) (μ.prod (ULA.CanonicalBrownian.vectorProbability I))
      (CanonicalBrownianDriver.driver (I := I) μ) G) :
    FilteredBrownian.IntegralDomain (Z := H)
      (ULA.initialExtension c (ULA.CanonicalBrownian.vectorProbability I)) (fullDriver μ ν c) G :=
  FilteredBrownian.enlargeDomain _ (leftDriver μ ν c) (fullDriver μ ν c)
    (left_filtration_le μ ν c) G
    (FilteredBrownian.pullbackDomain
      (AdditiveCanonical.extension_left_preserving (ULA.CanonicalBrownian.vectorProbability I) μ ν c)
      (CanonicalBrownianDriver.driver (I := I) μ) G u)

/-- The right marginal's actual domain in the same full coupled filtration. -/
def rightFullDomain (G : GridIntegralCompletion.RefiningGrids)
    (u : FilteredBrownian.IntegralDomain (Z := H) (ν.prod (ULA.CanonicalBrownian.vectorProbability I))
      (CanonicalBrownianDriver.driver (I := I) ν) G) :
    FilteredBrownian.IntegralDomain (Z := H)
      (ULA.initialExtension c (ULA.CanonicalBrownian.vectorProbability I)) (fullDriver μ ν c) G :=
  FilteredBrownian.enlargeDomain _ (rightDriver μ ν c) (fullDriver μ ν c)
    (right_filtration_le μ ν c) G
    (FilteredBrownian.pullbackDomain
      (AdditiveCanonical.extension_right_preserving (ULA.CanonicalBrownian.vectorProbability I) μ ν c)
      (CanonicalBrownianDriver.driver (I := I) ν) G u)

/-- The actual constructed left Itô integral in the full coupled filtration
is exactly the pulled marginal integral, not a supplied law identity. -/
theorem integral_left (G : GridIntegralCompletion.RefiningGrids)
    (u : FilteredBrownian.IntegralDomain (Z := H) (μ.prod (ULA.CanonicalBrownian.vectorProbability I))
      (CanonicalBrownianDriver.driver (I := I) μ) G) :
    FilteredBrownian.stochasticIntegral
      (ULA.initialExtension c (ULA.CanonicalBrownian.vectorProbability I)) (fullDriver μ ν c) G
      (leftFullDomain μ ν c G u) =
      lpPullbackCLM
        (AdditiveCanonical.extension_left_preserving (ULA.CanonicalBrownian.vectorProbability I) μ ν c)
        (FilteredBrownian.stochasticIntegral (μ.prod (ULA.CanonicalBrownian.vectorProbability I))
          (CanonicalBrownianDriver.driver (I := I) μ) G u) := by
  rw [leftFullDomain, FilteredBrownian.stochasticIntegral_enlarge _ _ _
    (left_process_eq μ ν c) (left_filtration_le μ ν c)]
  exact FilteredBrownian.stochasticIntegral_pullback _ _ G u

/-- Both actual marginal integrals therefore live on the same complete
initial-coupling/shared-Brownian filtration with their original output laws. -/
theorem integral_right (G : GridIntegralCompletion.RefiningGrids)
    (u : FilteredBrownian.IntegralDomain (Z := H) (ν.prod (ULA.CanonicalBrownian.vectorProbability I))
      (CanonicalBrownianDriver.driver (I := I) ν) G) :
    FilteredBrownian.stochasticIntegral
      (ULA.initialExtension c (ULA.CanonicalBrownian.vectorProbability I)) (fullDriver μ ν c) G
      (rightFullDomain μ ν c G u) =
      lpPullbackCLM
        (AdditiveCanonical.extension_right_preserving (ULA.CanonicalBrownian.vectorProbability I) μ ν c)
        (FilteredBrownian.stochasticIntegral (ν.prod (ULA.CanonicalBrownian.vectorProbability I))
          (CanonicalBrownianDriver.driver (I := I) ν) G u) := by
  rw [rightFullDomain, FilteredBrownian.stochasticIntegral_enlarge _ _ _
    (right_process_eq μ ν c) (right_filtration_le μ ν c)]
  exact FilteredBrownian.stochasticIntegral_pullback _ _ G u

/-- The left integral retains its actual original marginal law on the full
coupled filtration. This is derived from its L² pullback identity. -/
theorem integral_left_law (G : GridIntegralCompletion.RefiningGrids)
    (u : FilteredBrownian.IntegralDomain (Z := H) (μ.prod (ULA.CanonicalBrownian.vectorProbability I))
      (CanonicalBrownianDriver.driver (I := I) μ) G) :
    (ULA.initialExtension c (ULA.CanonicalBrownian.vectorProbability I)).map
      (FilteredBrownian.stochasticIntegral _ (fullDriver μ ν c) G (leftFullDomain μ ν c G u)) =
      (μ.prod (ULA.CanonicalBrownian.vectorProbability I)).map
        (FilteredBrownian.stochasticIntegral _ (CanonicalBrownianDriver.driver (I := I) μ) G u) := by
  rw [integral_left]
  exact lpPullback_law _ _

/-- The right actual marginal law is preserved simultaneously. -/
theorem integral_right_law (G : GridIntegralCompletion.RefiningGrids)
    (u : FilteredBrownian.IntegralDomain (Z := H) (ν.prod (ULA.CanonicalBrownian.vectorProbability I))
      (CanonicalBrownianDriver.driver (I := I) ν) G) :
    (ULA.initialExtension c (ULA.CanonicalBrownian.vectorProbability I)).map
      (FilteredBrownian.stochasticIntegral _ (fullDriver μ ν c) G (rightFullDomain μ ν c G u)) =
      (ν.prod (ULA.CanonicalBrownian.vectorProbability I)).map
        (FilteredBrownian.stochasticIntegral _ (CanonicalBrownianDriver.driver (I := I) ν) G u) := by
  rw [integral_right]
  exact lpPullback_law _ _

end Integral

end PBGSO.CoupledBrownianFiltration
