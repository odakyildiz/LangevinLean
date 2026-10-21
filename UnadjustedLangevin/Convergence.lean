import UnadjustedLangevin.Dynamics
import UnadjustedLangevin.SharpContraction
import UnadjustedLangevin.Coupling
import UnadjustedLangevin.Recurrence
import UnadjustedLangevin.Integrability

/-! # Conditional Wasserstein bounds for the actual ULA chain

This is the last part of Dalalyan's argument, with the reference-process
obligations written explicitly in the theorem statement. It proves the bound
from common-noise reference updates and finite local-error moments. It does
not construct a stationary Langevin diffusion or identify its law with the
normalized Gibbs density. See `README.md` for the remaining foundations.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace ULA

/-- Actual ULA iterates have a finite-horizon transport bound against any
stationary common-noise reference with bounded square-integrable defects. -/
theorem ula_wasserstein_bound_of_reference
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (U : E d → ℝ) (h : ℝ) (L q : ℝ≥0) (b : ℝ)
    (hLip : LipschitzWith L (gradient U)) (hq1 : (q : ℝ) < 1) (hb : 0 ≤ b)
    (initial : Ω → E d) (noise : ℕ → Ω → E d)
    (Y V : ℕ → Ω → E d) (π : Measure (E d))
    (hinitial : Measurable initial) (hnoise : ∀ n, Measurable (noise n))
    (hY : ∀ n, Measurable (Y n)) (hlaw : ∀ n, P.map (Y n) = π)
    (hreference : ∀ n, ∀ᵐ ω ∂P,
      Y (n + 1) ω = ulaUpdate U h (Y n ω) (noise n ω) + V n ω)
    (hcontract : ∀ x y z,
      ‖ulaUpdate U h x z - ulaUpdate U h y z‖ ≤ (q : ℝ) * ‖x - y‖)
    (hfinite0 : MemLp (fun ω ↦ initial ω - Y 0 ω) 2 P)
    (hVfinite : ∀ n, MemLp (V n) 2 P)
    (hdefect : ∀ n, (eLpNorm (V n) 2 P).toReal ≤ b) (n : ℕ) :
    wasserstein2Real
      (P.map (fun ω ↦ ulaChain U h (initial ω) (fun k ↦ noise k ω) n)) π ≤
      (q : ℝ) ^ n * (eLpNorm (fun ω ↦ initial ω - Y 0 ω) 2 P).toReal +
        b / (1 - (q : ℝ)) := by
  let X : ℕ → Ω → E d := fun k ω ↦ ulaChain U h (initial ω) (fun j ↦ noise j ω) k
  let e : ℕ → ℝ := fun k ↦ (eLpNorm (fun ω ↦ X k ω - Y k ω) 2 P).toReal
  have hfinite (k : ℕ) := ulaChain_error_memLp P U h L q hLip initial noise Y V
    hinitial hnoise hY hreference hcontract hfinite0 hVfinite k
  have hX (k : ℕ) : Measurable (X k) :=
    ulaChain_measurable U h L hLip initial noise hinitial hnoise k
  have hstep (k : ℕ) : e (k + 1) ≤ (q : ℝ) * e k + b := by
    let A : Ω → E d := fun ω ↦
      ulaUpdate U h (X k ω) (noise k ω) - ulaUpdate U h (Y k ω) (noise k ω)
    have hA : AEStronglyMeasurable A P := by
      have hg : Measurable (gradient U) := hLip.continuous.measurable
      have hm : Measurable A := by
        dsimp [A, ulaUpdate]
        fun_prop
      exact hm.aestronglyMeasurable
    have hi : ∀ᵐ ω ∂P, X (k + 1) ω - Y (k + 1) ω = A ω - V k ω := by
      filter_upwards [hreference k] with ω hω
      dsimp [X]
      rw [hω]
      dsimp [A, X]
      abel
    have hc : ∀ᵐ ω ∂P, ‖A ω‖ ≤ (q : ℝ) * ‖X k ω - Y k ω‖ :=
      Filter.Eventually.of_forall fun ω ↦ hcontract (X k ω) (Y k ω) (noise k ω)
    exact (synchronous_l2_bound_real P (X k) (Y k) (X (k + 1)) (Y (k + 1))
      A (V k) q hA hi hc (hfinite k) (hVfinite k)).trans
      (add_le_add_right (hdefect k) _)
  have hw := wasserstein2_le_random_cost_real P (X n) (Y n) (hX n) (hY n) (hfinite n)
  rw [hlaw n] at hw
  exact hw.trans (affine_recurrence_bound e q b q.coe_nonneg hq1 hb hstep n)

end ULA
