import PBGSO.FilteredWeightedCompletion
import PBGSO.MartingaleL2Limit

/-! # Actual timewise martingales for stopped predictable Brownian sums -/
noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology RealInnerProductSpace InnerProductSpace
namespace PBGSO.FilteredBrownian
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

def Coefficient.raise {a s : ℝ≥0} (A : Coefficient (Z := Z) Q D a) (has : a ≤ s) :
    Coefficient (Z := Z) Q D s :=
  ⟨A.value, fun i => (A.adapted i).mono (D.filtration.mono has), A.square⟩

theorem noiseStep_split (a s t : ℝ≥0) (has : a ≤ s) (A : Coefficient (Z := Z) Q D a) (ω : Ω) :
    noiseStep Q D a t A ω = noiseStep Q D a s A ω + noiseStep Q D s t (A.raise Q D has) ω := by
  simp only [noiseStep, PredictableIsometry.stepSum, Coefficient.raise,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← add_smul]
  congr 1
  simp only [increment]
  ring

/-- The elementary integral is stopped exactly at its observation time. -/
def stoppedStep (a b : ℝ≥0) (A : Coefficient (Z := Z) Q D a) (t : ℝ≥0) (ω : Ω) : Z :=
  if a ≤ t then noiseStep Q D a (min t b) A ω else 0

theorem stoppedStep_memLp (a b : ℝ≥0) (hab : a ≤ b) (A : Coefficient (Z := Z) Q D a) (t : ℝ≥0) :
    MemLp (stoppedStep Q D a b A t) 2 Q := by
  by_cases hat : a ≤ t
  · have he : stoppedStep Q D a b A t = noiseStep Q D a (min t b) A := by
      funext ω
      simp only [stoppedStep, hat, ite_true]
    rw [he]
    exact noiseStep_memLp Q D a (min t b) (le_min hat hab) A
  · have he : stoppedStep Q D a b A t = (0 : Ω → Z) := by
      funext ω
      simp only [stoppedStep, hat, ite_false, Pi.zero_apply]
    rw [he]
    exact MemLp.zero

theorem stoppedStep_adapted (a b : ℝ≥0) (A : Coefficient (Z := Z) Q D a) (t : ℝ≥0) :
    StronglyMeasurable[D.filtration t] (stoppedStep Q D a b A t) := by
  by_cases hat : a ≤ t
  · have he : stoppedStep Q D a b A t = noiseStep Q D a (min t b) A := by
      funext ω
      simp only [stoppedStep, hat, ite_true]
    rw [he]
    apply Finset.stronglyMeasurable_fun_sum
    intro i _
    exact (((D.adapted i (min t b)).mono (D.filtration.mono (min_le_left _ _))).sub
      ((D.adapted i a).mono (D.filtration.mono hat))).smul
      ((A.adapted i).mono (D.filtration.mono hat))
  · have he : stoppedStep Q D a b A t = (0 : Ω → Z) := by
      funext ω
      simp only [stoppedStep, hat, ite_false, Pi.zero_apply]
    rw [he]
    exact stronglyMeasurable_zero

/-- Every elementary predictable Brownian integral is a genuine
continuous-time martingale, including times before its left endpoint. -/
theorem stoppedStep_martingale (a b : ℝ≥0) (hab : a ≤ b) (A : Coefficient (Z := Z) Q D a) :
    Martingale (stoppedStep Q D a b A) D.filtration Q := by
  refine ⟨stoppedStep_adapted Q D a b A, ?_⟩
  intro s t hst
  by_cases has : a ≤ s
  · have hat := has.trans hst
    by_cases hsb : s ≤ b
    · let C := A.raise Q D has
      have hy := noiseStep_condExp_zero Q D s (min t b) (le_min hst hsb) C
      have hsplit : stoppedStep Q D a b A t = stoppedStep Q D a b A s +
          noiseStep Q D s (min t b) C := by
        funext ω
        simp only [stoppedStep, has, hat, ite_true, min_eq_left hsb, Pi.add_apply]
        exact noiseStep_split Q D a s (min t b) has A ω
      rw [hsplit]
      have ha := (stoppedStep_memLp Q D a b hab A s).integrable (by norm_num)
      have hb := (noiseStep_memLp Q D s (min t b) (le_min hst hsb) C).integrable (by norm_num)
      have hc := condExp_add ha hb (D.filtration s)
      have hx := condExp_of_stronglyMeasurable (D.filtration.le s)
        (stoppedStep_adapted Q D a b A s) ha
      filter_upwards [hc, hy] with ω hc hy
      simpa only [Pi.add_apply, hx, hy, Pi.zero_apply, add_zero] using hc
    · have hbs : b ≤ s := le_of_not_ge hsb
      have hbt : b ≤ t := hbs.trans hst
      have he : stoppedStep Q D a b A t = stoppedStep Q D a b A s := by
        funext ω
        simp only [stoppedStep, has, hat, ite_true, min_eq_right hbs, min_eq_right hbt]
      rw [he]
      exact ae_of_all Q fun ω => congrFun (condExp_of_stronglyMeasurable (D.filtration.le s)
        (stoppedStep_adapted Q D a b A s)
        ((stoppedStep_memLp Q D a b hab A s).integrable (by norm_num))) ω
  · have hsa : s ≤ a := le_of_not_ge has
    have heS : stoppedStep Q D a b A s = (0 : Ω → Z) := by
      funext ω
      simp only [stoppedStep, has, ite_false, Pi.zero_apply]
    rw [heS]
    by_cases hat : a ≤ t
    · have heT : stoppedStep Q D a b A t = noiseStep Q D a (min t b) A := by
        funext ω
        simp only [stoppedStep, hat, ite_true]
      rw [heT]
      have hy := noiseStep_condExp_zero Q D a (min t b) (le_min hat hab) A
      have htower := condExp_condExp_of_le (μ := Q) (f := noiseStep Q D a (min t b) A)
        (D.filtration.mono hsa) (D.filtration.le a)
      exact htower.symm.trans ((condExp_congr_ae hy).trans (by rw [condExp_zero]))
    · have heT : stoppedStep Q D a b A t = (0 : Ω → Z) := by
        funext ω
        simp only [stoppedStep, hat, ite_false, Pi.zero_apply]
      rw [heT, condExp_zero]



/-- The actual finite step integral stopped at every real observation time. -/
def stoppedGridSum (τ : ℕ → ℝ≥0) (A : Coefficients (Z := Z) Q D τ)
    (n : ℕ) (t : ℝ≥0) (ω : Ω) : Z :=
  ∑ k : Fin n, stoppedStep Q D (τ k) (τ (k + 1)) (A k) t ω

theorem stoppedGridSum_memLp (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (A : Coefficients (Z := Z) Q D τ) (n : ℕ) (t : ℝ≥0) :
    MemLp (stoppedGridSum Q D τ A n t) 2 Q := by
  apply memLp_finsetSum Finset.univ
  intro k _
  exact stoppedStep_memLp Q D _ _ (hτ (Nat.le_succ k)) (A k) t

theorem stoppedGridSum_succ (τ : ℕ → ℝ≥0) (A : Coefficients (Z := Z) Q D τ)
    (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    stoppedGridSum Q D τ A (n + 1) t ω = stoppedGridSum Q D τ A n t ω +
      stoppedStep Q D (τ n) (τ (n + 1)) (A n) t ω := by
  simp only [stoppedGridSum, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

theorem stoppedGridSum_martingale (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (A : Coefficients (Z := Z) Q D τ) (n : ℕ) :
    Martingale (stoppedGridSum Q D τ A n) D.filtration Q := by
  induction n with
  | zero =>
    have he : stoppedGridSum Q D τ A 0 = (0 : ℝ≥0 → Ω → Z) := by
      funext t ω
      simp [stoppedGridSum]
    rw [he]
    exact martingale_zero Z D.filtration Q
  | succ n ih =>
    have he : stoppedGridSum Q D τ A (n + 1) = stoppedGridSum Q D τ A n +
        stoppedStep Q D (τ n) (τ (n + 1)) (A n) := by
      funext t ω
      exact stoppedGridSum_succ Q D τ A n t ω
    rw [he]
    exact ih.add (stoppedStep_martingale Q D _ _ (hτ (Nat.le_succ n)) (A n))

/-- The selected representative of any timewise L² limit of the actual
stopped predictable sums is a genuine martingale. -/
theorem stoppedGridSum_limit_martingale (G : RefiningGrids)
    (A : ∀ n, Coefficients (Z := Z) Q D (G.time n)) (M : ℝ≥0 → Lp Z 2 Q)
    (hM : ∀ t, Tendsto (fun n =>
      (stoppedGridSum_memLp Q D (G.time n) (G.monotone n) (A n) (G.count n) t).toLp
        (stoppedGridSum Q D (G.time n) (A n) (G.count n) t)) atTop (𝓝 (M t))) :
    Martingale (MartingaleL2Limit.representative Q D.filtration M) D.filtration Q :=
  MartingaleL2Limit.martingale_representative Q D.filtration
    (fun n => stoppedGridSum Q D (G.time n) (A n) (G.count n))
    (fun n => stoppedGridSum_martingale Q D (G.time n) (G.monotone n) (A n) (G.count n))
    (fun n t => stoppedGridSum_memLp Q D (G.time n) (G.monotone n) (A n) (G.count n) t) M hM



theorem timeCut_norm_le (u : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ))
    (s t : ℝ) : ‖timeCut Q u s t‖ ≤ ‖u‖ := by
  rw [timeCut, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top u) (eLpNorm_indicator_le u measurableSet_Ioc)

theorem timeCut_subtract (u v : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ))
    (s t : ℝ) : timeCut Q (u - v) s t = timeCut Q u s t - timeCut Q v s t := by
  apply Lp.ext
  filter_upwards [timeCut_coe Q (u - v) s t, timeCut_coe Q u s t, timeCut_coe Q v s t,
    Lp.coeFn_sub u v, Lp.coeFn_sub (timeCut Q u s t) (timeCut Q v s t)]
    with r hsub hu hv huv hcut
  rw [hcut, Pi.sub_apply, hsub, hu, hv]
  by_cases hr : r ∈ Ioc s t
  · simp only [Set.indicator_of_mem hr, huv, Pi.sub_apply]
  · simp only [Set.indicator_of_notMem hr, sub_zero]

theorem timeCut_lipschitz (s t : ℝ) :
    LipschitzWith 1 (fun u : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ) =>
      timeCut Q u s t) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  rw [← timeCut_subtract]
  exact timeCut_norm_le Q (u - v) s t

end PBGSO.FilteredBrownian
