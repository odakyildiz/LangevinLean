import PBGSO.QuadraticMartingale
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! # Actual martingales survive pointwise L² completion
Conditional projection is continuous on the genuine L² space. Its martingale
identities pass to each timewise limit. Conditional expectations of the limit
supply adapted representatives, so no adaptedness or conditional-expectation
identity is assumed for the completed process.
-/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.MartingaleL2Limit
variable {Ω Z ι : Type*} [mΩ : MeasurableSpace Ω] [Preorder ι]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- Conditional projection, viewed in the ambient actual L² space. -/
def project (m : MeasurableSpace Ω) (hm : m ≤ mΩ) : Lp Z 2 Q →L[ℝ] Lp Z 2 Q :=
  letI : MeasurableSpace Ω := mΩ
  (lpMeas Z ℝ m 2 Q).subtypeL.comp (condExpL2 Z ℝ hm)

/-- The Hilbert projection agrees with the actual conditional expectation. -/
theorem project_coe (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (U : Lp Z 2 Q) :
    letI : MeasurableSpace Ω := mΩ
    project Q m hm U =ᵐ[Q] Q[U | m] := by
  letI : MeasurableSpace Ω := mΩ
  have h := (Lp.memLp U).condExpL2_ae_eq_condExp (𝕜 := ℝ) hm
  change (condExpL2 Z ℝ hm U : Ω → Z) =ᵐ[Q] Q[U | m]
  simpa only [Lp.toLp_coeFn] using h

/-- Actual conditional martingale identities give literal L² projection identities. -/
theorem project_toLp (F : Filtration ι mΩ) (f : ι → Ω → Z)
    (hf : Martingale f F Q) (h2 : ∀ t, MemLp (f t) 2 Q)
    (s t : ι) (hst : s ≤ t) :
    project Q (F s) (F.le s) ((h2 t).toLp (f t)) = (h2 s).toLp (f s) := by
  apply Lp.ext
  exact (project_coe Q (F s) (F.le s) _).trans
    ((condExp_congr_ae (h2 t).coeFn_toLp).trans
      ((hf.condExp_ae_eq hst).trans (h2 s).coeFn_toLp.symm))

/-- The actual limiting conditional identities follow from continuity of
projection and uniqueness of limits. -/
theorem project_limit (F : Filtration ι mΩ)
    (f : ℕ → ι → Ω → Z) (hf : ∀ n, Martingale (f n) F Q)
    (h2 : ∀ n t, MemLp (f n t) 2 Q) (X : ι → Lp Z 2 Q)
    (hlim : ∀ t, Tendsto (fun n => (h2 n t).toLp (f n t)) atTop (𝓝 (X t)))
    (s t : ι) (hst : s ≤ t) : project Q (F s) (F.le s) (X t) = X s := by
  have hp := ((project Q (F s) (F.le s)).continuous.tendsto (X t)).comp (hlim t)
  have he : (fun n => project Q (F s) (F.le s) ((h2 n t).toLp (f n t))) =
      (fun n => (h2 n s).toLp (f n s)) :=
    funext fun n => project_toLp Q F (f n) (hf n) (h2 n) s t hst
  change Tendsto (fun n => project Q (F s) (F.le s) ((h2 n t).toLp (f n t))) _ _ at hp
  rw [he] at hp
  exact tendsto_nhds_unique hp (hlim s)

/-- An adapted actual representative of a timewise L² limit. -/
def representative (F : Filtration ι mΩ) (X : ι → Lp Z 2 Q) (t : ι) : Ω → Z :=
  Q[X t | F t]

/-- The selected adapted representative has exactly the supplied L² limit. -/
theorem representative_ae (F : Filtration ι mΩ)
    (f : ℕ → ι → Ω → Z) (hf : ∀ n, Martingale (f n) F Q)
    (h2 : ∀ n t, MemLp (f n t) 2 Q) (X : ι → Lp Z 2 Q)
    (hlim : ∀ t, Tendsto (fun n => (h2 n t).toLp (f n t)) atTop (𝓝 (X t)))
    (t : ι) : representative Q F X t =ᵐ[Q] X t := by
  have he := project_limit Q F f hf h2 X hlim t t le_rfl
  exact (project_coe Q (F t) (F.le t) (X t)).symm.trans (by rw [he])

/-- Completing actual square-integrable martingales gives an actual
martingale with derived adaptedness and conditional identities. -/
theorem martingale_representative (F : Filtration ι mΩ)
    (f : ℕ → ι → Ω → Z) (hf : ∀ n, Martingale (f n) F Q)
    (h2 : ∀ n t, MemLp (f n t) 2 Q) (X : ι → Lp Z 2 Q)
    (hlim : ∀ t, Tendsto (fun n => (h2 n t).toLp (f n t)) atTop (𝓝 (X t))) :
    Martingale (representative Q F X) F Q := by
  constructor
  · intro t
    exact stronglyMeasurable_condExp
  · intro s t hst
    have ht := representative_ae Q F f hf h2 X hlim t
    have hs := representative_ae Q F f hf h2 X hlim s
    have he := project_limit Q F f hf h2 X hlim s t hst
    exact (condExp_congr_ae ht).trans
      ((project_coe Q (F s) (F.le s) (X t)).symm.trans
        ((by rw [he] : project Q (F s) (F.le s) (X t) =ᵐ[Q] X s).trans hs.symm))

/-- The actual completed martingale is square integrable at every time. -/
theorem representative_memLp (F : Filtration ι mΩ)
    (f : ℕ → ι → Ω → Z) (hf : ∀ n, Martingale (f n) F Q)
    (h2 : ∀ n t, MemLp (f n t) 2 Q) (X : ι → Lp Z 2 Q)
    (hlim : ∀ t, Tendsto (fun n => (h2 n t).toLp (f n t)) atTop (𝓝 (X t)))
    (t : ι) : MemLp (representative Q F X t) 2 Q :=
  (memLp_congr_ae (representative_ae Q F f hf h2 X hlim t)).mpr (Lp.memLp (X t))

end PBGSO.MartingaleL2Limit
