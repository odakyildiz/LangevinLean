import UnadjustedLangevin.GradientStep
import UnadjustedLangevin.StrongConvexity
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Shared-noise bounds for one step of the unadjusted Langevin algorithm.
See `ULAupdate.tex` for the corresponding mathematical proof. -/

noncomputable section

open scoped NNReal

/-- The Euclidean state space of dimension `d`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- One ULA step `x ↦ x - h ∇U(x) + √(2h) z`, with noise vector `z`. -/
def ulaUpdate {d : ℕ} (U : E d → ℝ) (h : ℝ) (x z : E d) : E d :=
  x - h • gradient U x + Real.sqrt (2 * h) • z

/-- Shared noise cancels from the difference of two ULA updates. -/
lemma ulaUpdate_sub {d : ℕ} (U : E d → ℝ) (h : ℝ) (x y z : E d) :
    ulaUpdate U h x z - ulaUpdate U h y z =
      (x - h • gradient U x) - (y - h • gradient U y) := by
  simp only [ulaUpdate, add_sub_add_right_eq_sub]

/--
Shared-noise norm bound for one ULA step with a differentiable,
`m`-strongly convex potential and `L`-Lipschitz gradient:

    ‖X' - Y'‖
      ≤ √(1 - 2hm + h²L²) ‖x - y‖.

This is the deterministic contraction lemma underlying the
standard synchronous-coupling Wasserstein argument.
The bound is strictly contractive when `h > 0` and `h * L² < 2m`.
-/
theorem ula_shared_noise_contract {d : ℕ} (U : E d → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U)
    (hsm : LipschitzWith L (gradient U))
    (hh : 0 ≤ h)
    (x y z : E d) :
    ‖ulaUpdate U h x z - ulaUpdate U h y z‖ ≤
      Real.sqrt (1 - 2 * h * m + h ^ 2 * (L : ℝ) ^ 2) * ‖x - y‖ := by
  rw [ulaUpdate_sub]
  exact ULA.gradient_step_contract x y (gradient U x) (gradient U y) m h L hh
    (ULA.strong_gradient_monotone hdiff hsc x y)
    (by simpa only [dist_eq_norm] using hsm.dist_le_mul x y)
