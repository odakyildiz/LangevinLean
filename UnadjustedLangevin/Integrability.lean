import UnadjustedLangevin.Coupling
import UnadjustedLangevin.Dynamics
import UnadjustedLangevin.SharpContraction

/-!
# Propagation of finite coupling moments

Square integrability of every ULA coupling error follows from square
integrability of the initial error and the local defects. It does not need to
be included as a separate assumption in a convergence theorem.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace ULA

variable {Ω : Type*} [MeasurableSpace Ω]
variable {H : Type*} [NormedAddCommGroup H]

/-- An almost-everywhere contracted term minus a finite-moment defect still
has finite moments. This works at every `Lp` exponent. -/
theorem synchronous_memLp (P : Measure Ω) (D A V E : Ω → H)
    (p : ℝ≥0∞) (q : ℝ)
    (hA : AEStronglyMeasurable A P)
    (hidentity : E =ᵐ[P] (fun ω ↦ A ω - V ω))
    (hcontract : ∀ᵐ ω ∂P, ‖A ω‖ ≤ q * ‖D ω‖)
    (hD : MemLp D p P) (hV : MemLp V p P) : MemLp E p P := by
  have hAmem : MemLp A p P := hD.of_le_mul hA hcontract
  exact MemLp.ae_eq hidentity.symm (hAmem.sub hV)

/-- Initial square integrability and square-integrable reference defects
propagate to every actual ULA coupling error. Stationarity and a contraction
factor below one are not needed for this finite-moment statement. -/
theorem ulaChain_error_memLp
    {d : ℕ} (P : Measure Ω) (U : E d → ℝ) (h : ℝ) (L q : ℝ≥0)
    (hLip : LipschitzWith L (gradient U))
    (initial : Ω → E d) (noise : ℕ → Ω → E d)
    (Y V : ℕ → Ω → E d)
    (hinitial : Measurable initial) (hnoise : ∀ n, Measurable (noise n))
    (hY : ∀ n, Measurable (Y n))
    (hreference : ∀ n, ∀ᵐ ω ∂P,
      Y (n + 1) ω = ulaUpdate U h (Y n ω) (noise n ω) + V n ω)
    (hcontract : ∀ x y z,
      ‖ulaUpdate U h x z - ulaUpdate U h y z‖ ≤ (q : ℝ) * ‖x - y‖)
    (hfinite0 : MemLp (fun ω ↦ initial ω - Y 0 ω) 2 P)
    (hVfinite : ∀ n, MemLp (V n) 2 P) (n : ℕ) :
    MemLp
      (fun ω ↦ ulaChain U h (initial ω) (fun k ↦ noise k ω) n - Y n ω) 2 P := by
  let X : ℕ → Ω → E d := fun k ω ↦ ulaChain U h (initial ω) (fun j ↦ noise j ω) k
  have hX (k : ℕ) : Measurable (X k) :=
    ulaChain_measurable U h L hLip initial noise hinitial hnoise k
  change MemLp (fun ω ↦ X n ω - Y n ω) 2 P
  induction n with
  | zero => exact hfinite0
  | succ n ih =>
      let A : Ω → E d := fun ω ↦
        ulaUpdate U h (X n ω) (noise n ω) - ulaUpdate U h (Y n ω) (noise n ω)
      have hA : AEStronglyMeasurable A P := by
        have hg : Measurable (gradient U) := hLip.continuous.measurable
        have hm : Measurable A := by
          dsimp [A, ulaUpdate]
          fun_prop
        exact hm.aestronglyMeasurable
      have hi : (fun ω ↦ X (n + 1) ω - Y (n + 1) ω) =ᵐ[P]
          (fun ω ↦ A ω - V n ω) := by
        filter_upwards [hreference n] with ω hω
        dsimp [X]
        rw [hω]
        dsimp [A, X]
        abel
      have hc : ∀ᵐ ω ∂P, ‖A ω‖ ≤ (q : ℝ) * ‖X n ω - Y n ω‖ :=
        Filter.Eventually.of_forall fun ω ↦ hcontract (X n ω) (Y n ω) (noise n ω)
      exact synchronous_memLp P (fun ω ↦ X n ω - Y n ω) A (V n)
        (fun ω ↦ X (n + 1) ω - Y (n + 1) ω) 2 q hA hi hc ih (hVfinite n)

end ULA
