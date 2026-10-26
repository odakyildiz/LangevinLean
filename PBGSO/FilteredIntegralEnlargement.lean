import PBGSO.FilteredIntegralContinuity
import PBGSO.FilteredIntegralPullback

/-! # Actual Brownian integration under enlargement of the filtration
The same Brownian coordinates and coefficient columns give the same finite
sums and the same completed integral. Enlargement changes only the proved
adaptedness witnesses; no stochastic-integral equality is a premise.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.FilteredBrownian
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  (D E : Driver (I := I) Q)
  (hprocess : D.process = E.process)
  (henlarge : ∀ t, D.filtration t ≤ E.filtration t)

/-- A genuine predictable coefficient remains predictable in the larger
filtration. Its actual values and L² variables do not change. -/
def enlargeCoefficient {t : ℝ≥0} (A : Coefficient (Z := Z) Q D t) :
    Coefficient (Z := Z) Q E t where
  value := A.value
  adapted i := (A.adapted i).mono (henlarge t)
  square := A.square

@[simp] theorem enlargeCoefficient_toLp {t : ℝ≥0} (A : Coefficient (Z := Z) Q D t) :
    (enlargeCoefficient Q D E henlarge A).toLp = A.toLp := rfl

def enlargeCoefficients (τ : ℕ → ℝ≥0) (A : Coefficients (Z := Z) Q D τ) :
    Coefficients (Z := Z) Q E τ := fun k ↦ enlargeCoefficient Q D E henlarge (A k)

@[simp] theorem coefficientStep_enlarge (τ : ℕ → ℝ≥0) (A : Coefficients (Z := Z) Q D τ) (n : ℕ) :
    coefficientStep Q E τ (enlargeCoefficients Q D E henlarge τ A) n = coefficientStep Q D τ A n := rfl

include hprocess henlarge

/-- Actual finite sums are unchanged when the Brownian coordinates are the
same; this is a pointwise identity, not merely equality of covariance. -/
theorem stochasticStep_enlarge (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (A : Coefficients (Z := Z) Q D τ) (n : ℕ) :
    stochasticStep Q E τ hτ (enlargeCoefficients Q D E henlarge τ A) n =
      stochasticStep Q D τ hτ A n := by
  apply Lp.ext
  filter_upwards [(gridSum_memLp Q E τ hτ (enlargeCoefficients Q D E henlarge τ A) n).coeFn_toLp,
    (gridSum_memLp Q D τ hτ A n).coeFn_toLp] with ω hE hD
  dsimp only [stochasticStep]
  rw [hE, hD]
  simp only [gridSum, noiseStep, PredictableIsometry.stepSum, increment, enlargeCoefficients, enlargeCoefficient]
  rw [hprocess]

omit hprocess

/-- The actual represented integral domain embeds in the larger filtration
without changing its literal time-L² coefficient function. -/
def enlargeDomain (G : GridIntegralCompletion.RefiningGrids)
    (u : IntegralDomain (Z := Z) Q D G) : IntegralDomain (Z := Z) Q E G := by
  refine ⟨u.val, ?_⟩
  obtain ⟨A, hA⟩ := u.property
  exact ⟨fun n ↦ enlargeCoefficients Q D E henlarge (G.time n) (A n), hA⟩

include hprocess

/-- Completion preserves the actual finite-sum equality under filtration
enlargement. No limiting equality or stochastic isometry is assumed. -/
theorem stochasticIntegral_enlarge (G : GridIntegralCompletion.RefiningGrids)
    (u : IntegralDomain (Z := Z) Q D G) :
    stochasticIntegral Q E G (enlargeDomain Q D E henlarge G u) = stochasticIntegral Q D G u := by
  obtain ⟨A, hA⟩ := u.property
  have h1 := stochasticIntegral_tendsto Q E G (enlargeDomain Q D E henlarge G u)
    (fun n ↦ enlargeCoefficients Q D E henlarge (G.time n) (A n)) hA
  have h2 := stochasticIntegral_tendsto Q D G u A hA
  apply tendsto_nhds_unique h1
  simpa only [stochasticStep_enlarge Q D E hprocess henlarge] using h2

/-- Any two actual domain entries with the same time integrand have equal
constructed integrals under the larger/smaller filtrations. -/
theorem stochasticIntegral_eq_of_enlargement (G : GridIntegralCompletion.RefiningGrids)
    (u : IntegralDomain (Z := Z) Q D G) (v : IntegralDomain (Z := Z) Q E G)
    (hval : v.val = u.val) : stochasticIntegral Q E G v = stochasticIntegral Q D G u := by
  have hv : v = enlargeDomain Q D E henlarge G u := Subtype.ext hval
  rw [hv]
  exact stochasticIntegral_enlarge Q D E hprocess henlarge G u

/-- The actual completed continuous-integrand process is invariant under
enlargement to any valid full-driver filtration with the same coordinates. -/
theorem continuousIntegral_enlarge (T : ℝ≥0)
    (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q) (hu : Continuous u)
    (hD : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q)
    (hE : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[E.filtration t] (u t i) Q)
    (t : ℝ≥0) : continuousIntegral Q E T u hu hE t = continuousIntegral Q D T u hu hD t := by
  apply stochasticIntegral_eq_of_enlargement Q D E hprocess henlarge
    (GridIntegralCompletion.dyadicGrids T) (continuousCutDomain Q D T u hu hD t)
    (continuousCutDomain Q E T u hu hE t)
  apply Lp.ext
  exact (continuousCutDomain_coe Q E T u hu hE t).trans
    (continuousCutDomain_coe Q D T u hu hD t).symm

end PBGSO.FilteredBrownian
