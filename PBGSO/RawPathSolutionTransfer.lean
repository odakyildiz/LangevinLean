import PBGSO.BrownianPathDriver
import PBGSO.RawLocalSolutionTransport

/-! # Strong solution laws and frozen weak stationarity on actual path space

A genuine initial/Wiener-path map transports original raw local equations.
Pathwise uniqueness then identifies their original marginal laws. Applying
this twice transfers a stationary weak frozen sampler on any source to the
coupled strong solution on any other source. No common frozen strong solver,
law-matching interface, global moment bound or energy identity is assumed.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.RawLocalStationarity
open FilteredBrownian
variable {Ω S Θ Z X I : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)
  {M : Model S Θ Z X I} {T : ℝ≥0}

/-- The same original raw solution in a proved valid null-augmented past
and continuous Brownian modification. The raw state and optimizer are kept. -/
def Data.continuousAugmented (U : Data Q D M T) :
    Data Q (nullAugmentedDriver Q (continuousDriver Q D)) M T :=
  U.pullback (MeasurePreserving.id Q) (nullAugmentedDriver Q (continuousDriver Q D))
    (fun t => by
      change MeasurableSpace.comap id (D.filtration t) ≤ nullAugmentedFiltration Q D.filtration t
      simpa only [MeasurableSpace.comap_id] using filtration_le_nullAugmented Q D.filtration t)
    (fun i t => (continuousDriver_process_ae Q D i t).symm)

variable {Q D}

/-- The actual initial/path probability map for a natural raw solution.
Only its original initial law is specified; output laws are not premises. -/
def Data.pathInputPreserving (U : Data Q D M T) (μ : Measure Z)
    (hμ : Q.map (U.sampler.state 0) = μ) :
    MeasurePreserving (BrownianPathDriver.inputMap Q D (U.sampler.state 0)) Q
      (BrownianPathDriver.probability (I := I) μ) := by
  have hf := BrownianPathDriver.inputMap_preserving Q D (U.sampler.state 0)
    (U.sampler.measurable 0 ⟨le_rfl, T.coe_nonneg⟩) (U.sampler.adapted 0)
  simpa only [hμ] using hf

/-- A1 same-driver uniqueness proves equality with the actual canonical
path-space strong solution. Brownian matching, the probability input map,
and original local-equation transport are all proved internally. -/
theorem Data.law_eq_pathspace_solution (U : Data Q D M T)
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (hμ : Q.map (U.sampler.state 0) = μ)
    (hunique : PathwiseUniqueness Q (nullAugmentedDriver Q (continuousDriver Q D)) M T)
    (V : Data (BrownianPathDriver.probability (I := I) μ) (BrownianPathDriver.driver μ) M T)
    (hs : U.optimizer 0 = V.optimizer 0)
    (hz : V.sampler.state 0 =ᵐ[BrownianPathDriver.probability (I := I) μ] Prod.fst)
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    U.optimizer t = V.optimizer t ∧ Q.map (U.sampler.state t) =
      (BrownianPathDriver.probability (I := I) μ).map (V.sampler.state t) := by
  let E := nullAugmentedDriver Q (continuousDriver Q D)
  let hf := U.pathInputPreserving μ hμ
  have hF : ∀ r, (pullbackDriver hf (BrownianPathDriver.driver μ)).filtration r ≤ E.filtration r := by
    intro r
    change MeasurableSpace.comap (BrownianPathDriver.inputMap Q D (U.sampler.state 0))
      (BrownianPathDriver.filtration r) ≤ E.filtration r
    exact BrownianPathDriver.inputMap_past Q D (U.sampler.state 0)
      (U.sampler.measurable 0 ⟨le_rfl, T.coe_nonneg⟩) (U.sampler.adapted 0) r
  have hp : ∀ i r, (pullbackDriver hf (BrownianPathDriver.driver μ)).process i r =ᵐ[Q]
      E.process i r := by
    intro i r
    exact BrownianPathDriver.inputMap_coordinate_ae Q D (U.sampler.state 0)
      (U.sampler.measurable 0 ⟨le_rfl, T.coe_nonneg⟩) i r
  have hz' : (U.continuousAugmented Q D).sampler.state 0 =ᵐ[Q]
      fun ω => V.sampler.state 0 (BrownianPathDriver.inputMap Q D (U.sampler.state 0) ω) :=
    (hf.quasiMeasurePreserving.ae_eq_comp hz).symm
  exact law_unique_of_initial_noise_map hf E hF hp hunique V (U.continuousAugmented Q D)
    hs hz' t ht

section WeakFrozen
variable {Ωw : Type*} [MeasurableSpace Ωw]
  (Qw : Measure Ωw) [IsProbabilityMeasure Qw]
  (Dw : Driver (I := I) Qw)

/-- Source stationarity from an invariant frozen weak sampler on SOME
probability space, and A1 existence/uniqueness for the coupled strong system.
The canonical existence input is only the direct A1 instance on the genuine
independent initial-law / Wiener-path driver constructed above. It does not
assert a frozen strong realization or any stationary output law. -/
theorem stationary_of_weak_frozen {sStar : S} {νStar : Measure Z}
    [IsProbabilityMeasure νStar]
    (F : FrozenSamplerData Qw Dw M T sStar νStar)
    (hint : Integrable (fun z => M.observation (M.parameter sStar) (M.position z)) νStar)
    (hg : M.meanGradient νStar sStar = 0)
    (hfix : ∀ t ∈ Icc 0 (T : ℝ), M.optimizer t sStar 0 = 0)
    (huniquew : PathwiseUniqueness Qw (nullAugmentedDriver Qw (continuousDriver Qw Dw)) M T)
    (hexists : ∃ V : Data (BrownianPathDriver.probability (I := I) νStar)
        (BrownianPathDriver.driver νStar) M T,
      V.optimizer 0 = sStar ∧ V.sampler.state 0 =ᵐ[
        BrownianPathDriver.probability (I := I) νStar] Prod.fst)
    (U : Data Q D M T)
    (hunique : PathwiseUniqueness Q (nullAugmentedDriver Q (continuousDriver Q D)) M T)
    (hs : U.optimizer 0 = sStar) (hν : Q.map (U.sampler.state 0) = νStar)
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    U.optimizer t = sStar ∧ Q.map (U.sampler.state t) = νStar := by
  obtain ⟨V, hsV, hzV⟩ := hexists
  let W := F.constantData hint hg hfix
  have hw := W.law_eq_pathspace_solution νStar
    (F.invariant_law 0 ⟨le_rfl, T.coe_nonneg⟩) huniquew V hsV.symm hzV t ht
  have hvopt : V.optimizer t = sStar := hw.1.symm
  have hvlaw : (BrownianPathDriver.probability (I := I) νStar).map (V.sampler.state t) = νStar :=
    hw.2.symm.trans (F.invariant_law t ht)
  have hu := U.law_eq_pathspace_solution νStar hν hunique V (hs.trans hsV.symm) hzV t ht
  exact ⟨hu.1.trans hvopt, hu.2.trans hvlaw⟩

/-- The complete-state stationary product law, retaining original optimizer
and sampler auxiliary variables on the arbitrary original probability space. -/
theorem stationary_product_law_of_weak_frozen [MeasurableSpace S]
    {sStar : S} {νStar : Measure Z} [IsProbabilityMeasure νStar]
    (F : FrozenSamplerData Qw Dw M T sStar νStar)
    (hint : Integrable (fun z => M.observation (M.parameter sStar) (M.position z)) νStar)
    (hg : M.meanGradient νStar sStar = 0)
    (hfix : ∀ t ∈ Icc 0 (T : ℝ), M.optimizer t sStar 0 = 0)
    (huniquew : PathwiseUniqueness Qw (nullAugmentedDriver Qw (continuousDriver Qw Dw)) M T)
    (hexists : ∃ V : Data (BrownianPathDriver.probability (I := I) νStar)
        (BrownianPathDriver.driver νStar) M T,
      V.optimizer 0 = sStar ∧ V.sampler.state 0 =ᵐ[
        BrownianPathDriver.probability (I := I) νStar] Prod.fst)
    (U : Data Q D M T)
    (hunique : PathwiseUniqueness Q (nullAugmentedDriver Q (continuousDriver Q D)) M T)
    (hs : U.optimizer 0 = sStar) (hν : Q.map (U.sampler.state 0) = νStar)
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    Q.map (fun ω => (U.optimizer t, U.sampler.state t ω)) = (Measure.dirac sStar).prod νStar := by
  obtain ⟨ho, hl⟩ := stationary_of_weak_frozen Qw Dw F hint hg hfix huniquew hexists
    U hunique hs hν t ht
  rw [ho, Measure.dirac_prod, ← hl,
    Measure.map_map measurable_prodMk_left (U.sampler.measurable t ht)]
  rfl

end WeakFrozen
end PBGSO.RawLocalStationarity
