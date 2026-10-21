import UnadjustedLangevin.SharpContraction
import UnadjustedLangevin.LocalError
import UnadjustedLangevin.Dynamics
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Lifting the actual gradient to square-integrable random variables

The local-error theorem works in a Banach space. Here we construct its intended
L² drift from the potential's actual gradient. Centering the vector field before
using mathlib's `compLp` removes any need to assume `gradient U 0 = 0`.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace ULA

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] (P : Measure Ω) [IsFiniteMeasure P]

/-- Subtracting a fixed offset preserves a Lipschitz constant. -/
theorem centered_lipschitz {L : ℝ≥0} {g : H → H} (hLip : LipschitzWith L g) :
    LipschitzWith L (fun x ↦ g x - g 0) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hLip.dist_le_mul x y

/-- A Lipschitz vector field acts on L² random variables, including nonzero
constant offsets. The finite measure ensures that this offset lies in L². -/
def lpDrift (g : H → H) {L : ℝ≥0} (hLip : LipschitzWith L g)
    (X : Lp H 2 P) : Lp H 2 P :=
  (centered_lipschitz hLip).compLp (by simp) X + Lp.const 2 P (g 0)

/-- The L² drift represents pointwise application of the original vector field. -/
theorem lpDrift_coe (g : H → H) {L : ℝ≥0} (hLip : LipschitzWith L g)
    (X : Lp H 2 P) : lpDrift P g hLip X =ᵐ[P] fun ω ↦ g (X ω) := by
  unfold lpDrift
  filter_upwards [Lp.coeFn_add ((centered_lipschitz hLip).compLp (by simp) X)
      (Lp.const 2 P (g 0)),
    (centered_lipschitz hLip).coeFn_compLp (by simp) X,
    Lp.coeFn_const (μ := P) (p := 2) (c := g 0)] with ω hadd hcomp hconst
  simp only [hadd, hcomp, hconst, Function.comp_apply, Pi.add_apply, Function.const_apply]
  exact sub_add_cancel _ _

/-- Lipschitz composition preserves square integrability for finite measures. -/
theorem lpDrift_memLp (g : H → H) {L : ℝ≥0} (hLip : LipschitzWith L g)
    (X : Lp H 2 P) : MemLp (fun ω ↦ g (X ω)) 2 P :=
  (Lp.memLp (lpDrift P g hLip X)).ae_eq (lpDrift_coe P g hLip X)

/-- The actual vector field keeps its Lipschitz constant in L². -/
theorem lpDrift_lipschitz (g : H → H) {L : ℝ≥0} (hLip : LipschitzWith L g) :
    LipschitzWith L (lpDrift P g hLip) := by
  apply LipschitzWith.of_dist_le_mul
  intro X Y
  simp only [lpDrift, dist_eq_norm, add_sub_add_right_eq_sub]
  exact (centered_lipschitz hLip).norm_compLp_sub_le (by simp) X Y

variable [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The sharp small-step gradient contraction passes to actual random-variable
gradients in L², by integrating the pointwise norm bound. -/
theorem lpDrift_gradient_contract
    (U : H → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (hLip : LipschitzWith L (gradient U)) (hmL : m ≤ (L : ℝ))
    (hpos : 0 < m + (L : ℝ)) (hh : 0 ≤ h) (hsmall : h ≤ 2 / (m + (L : ℝ)))
    (X Y : Lp H 2 P) :
    ‖(X - h • lpDrift P (gradient U) hLip X) -
      (Y - h • lpDrift P (gradient U) hLip Y)‖ ≤ (1 - m * h) * ‖X - Y‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub
      (X - h • lpDrift P (gradient U) hLip X)
      (Y - h • lpDrift P (gradient U) hLip Y),
    Lp.coeFn_sub X (h • lpDrift P (gradient U) hLip X),
    Lp.coeFn_sub Y (h • lpDrift P (gradient U) hLip Y),
    Lp.coeFn_smul h (lpDrift P (gradient U) hLip X),
    Lp.coeFn_smul h (lpDrift P (gradient U) hLip Y),
    lpDrift_coe P (gradient U) hLip X, lpDrift_coe P (gradient U) hLip Y,
    Lp.coeFn_sub X Y] with ω hsub hX hY hsX hsY hgX hgY hXY
  simp only [hsub, hX, hY, hsX, hsY, hgX, hgY, hXY, Pi.sub_apply, Pi.smul_apply]
  exact strong_smooth_gradient_step_contract U m h L hdiff hsc hLip hmL hpos hh hsmall
    (X ω) (Y ω)

/-- The second sharp step-size regime also passes to L². -/
theorem lpDrift_gradient_contract_large
    (U : H → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (hLip : LipschitzWith L (gradient U)) (hmL : m ≤ (L : ℝ))
    (hpos : 0 < m + (L : ℝ)) (hh : 0 ≤ h) (hlarge : 2 / (m + (L : ℝ)) ≤ h)
    (X Y : Lp H 2 P) :
    ‖(X - h • lpDrift P (gradient U) hLip X) -
      (Y - h • lpDrift P (gradient U) hLip Y)‖ ≤ ((L : ℝ) * h - 1) * ‖X - Y‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub
      (X - h • lpDrift P (gradient U) hLip X)
      (Y - h • lpDrift P (gradient U) hLip Y),
    Lp.coeFn_sub X (h • lpDrift P (gradient U) hLip X),
    Lp.coeFn_sub Y (h • lpDrift P (gradient U) hLip Y),
    Lp.coeFn_smul h (lpDrift P (gradient U) hLip X),
    Lp.coeFn_smul h (lpDrift P (gradient U) hLip Y),
    lpDrift_coe P (gradient U) hLip X, lpDrift_coe P (gradient U) hLip Y,
    Lp.coeFn_sub X Y] with ω hsub hX hY hsX hsY hgX hgY hXY
  simp only [hsub, hX, hY, hsX, hsY, hgX, hgY, hXY, Pi.sub_apply, Pi.smul_apply]
  exact strong_smooth_gradient_step_contract_large U m h L hdiff hsc hLip
    hmL hpos hh hlarge (X ω) (Y ω)

/-- Dalalyan's local defect theorem instantiated with the actual gradient in L². -/
theorem lpDrift_localDefect_bound
    (U : H → ℝ) (L : ℝ≥0) (h d : ℝ)
    (hLip : LipschitzWith L (gradient U)) (Y B : ℝ → Lp H 2 P)
    (hh : 0 ≤ h) (hd : 0 ≤ d) (hstep : (L : ℝ) * h ≤ 2)
    (hG : ∀ t ∈ Set.Icc 0 h, ‖lpDrift P (gradient U) hLip (Y t)‖ ≤
      Real.sqrt ((L : ℝ) * d))
    (hB : ∀ t ∈ Set.Icc 0 h, ‖B t‖ ≤ Real.sqrt (2 * d) * Real.sqrt t)
    (heq : ∀ t ∈ Set.Icc 0 h, Y t - Y 0 =
      -(∫ s in 0..t, lpDrift P (gradient U) hLip (Y s)) + B t) :
    ‖localDefect (lpDrift P (gradient U) hLip) Y h‖ ≤
      (33 / 20 : ℝ) * (L : ℝ) * h * Real.sqrt (h * d) :=
  localDefect_dalalyan_bound (lpDrift P (gradient U) hLip) Y B L h d hh hd hstep
    (lpDrift_lipschitz P (gradient U) hLip) hG hB heq

omit [CompleteSpace H] in
/-- The L² norm of the lifted drift is the usual square-root score moment. -/
theorem lpDrift_norm_sq (g : H → H) {L : ℝ≥0} (hLip : LipschitzWith L g)
    (X : Lp H 2 P) :
    ‖lpDrift P g hLip X‖ ^ 2 = ∫ ω, ‖g (X ω)‖ ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [lpDrift_coe P g hLip X] with ω hω
  rw [hω, real_inner_self_eq_norm_sq]

omit [CompleteSpace H] in
/-- A score second-moment bound supplies the norm assumption in the local-error
theorem, with the square root justified by the L² identity. -/
theorem lpDrift_norm_le_sqrt (g : H → H) {L : ℝ≥0} (hLip : LipschitzWith L g)
    (X : Lp H 2 P) (C : ℝ) (hmoment : (∫ ω, ‖g (X ω)‖ ^ 2 ∂P) ≤ C) :
    ‖lpDrift P g hLip X‖ ≤ Real.sqrt C := by
  exact Real.le_sqrt_of_sq_le ((lpDrift_norm_sq P g hLip X).trans_le hmoment)

/-- One ULA update as an operation on actual L² random variables. -/
def lpUlaUpdate (U : H → ℝ) (h : ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L (gradient U)) (X Z : Lp H 2 P) : Lp H 2 P :=
  X - h • lpDrift P (gradient U) hLip X + Real.sqrt (2 * h) • Z

/-- The random-variable update agrees almost everywhere with the pointwise
ULA formula. -/
theorem lpUlaUpdate_coe (U : H → ℝ) (h : ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L (gradient U)) (X Z : Lp H 2 P) :
    lpUlaUpdate P U h hLip X Z =ᵐ[P] fun ω ↦
      X ω - h • gradient U (X ω) + Real.sqrt (2 * h) • Z ω := by
  unfold lpUlaUpdate
  filter_upwards [Lp.coeFn_add (X - h • lpDrift P (gradient U) hLip X)
      (Real.sqrt (2 * h) • Z),
    Lp.coeFn_sub X (h • lpDrift P (gradient U) hLip X),
    Lp.coeFn_smul h (lpDrift P (gradient U) hLip X),
    Lp.coeFn_smul (Real.sqrt (2 * h)) Z,
    lpDrift_coe P (gradient U) hLip X] with ω ha hs hsm hn hg
  simp only [ha, hs, hsm, hn, hg, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]

/-- The genuine noise-driven ULA chain in the L² space. -/
def lpUlaChain {d : ℕ} (U : E d → ℝ) (h : ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L (gradient U)) (initial : Lp (E d) 2 P)
    (noise : ℕ → Lp (E d) 2 P) : ℕ → Lp (E d) 2 P
  | 0 => initial
  | n + 1 => lpUlaUpdate P U h hLip (lpUlaChain U h hLip initial noise n) (noise n)

@[simp] theorem lpUlaChain_zero {d : ℕ} (U : E d → ℝ) (h : ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L (gradient U)) (initial : Lp (E d) 2 P)
    (noise : ℕ → Lp (E d) 2 P) : lpUlaChain P U h hLip initial noise 0 = initial := rfl

@[simp] theorem lpUlaChain_succ {d : ℕ} (U : E d → ℝ) (h : ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L (gradient U)) (initial : Lp (E d) 2 P)
    (noise : ℕ → Lp (E d) 2 P) (n : ℕ) :
    lpUlaChain P U h hLip initial noise (n + 1) =
      lpUlaUpdate P U h hLip (lpUlaChain P U h hLip initial noise n) (noise n) := rfl

/-- Every L² iterate represents the original pointwise ULA chain almost
everywhere, so the lifting does not introduce a different algorithm. -/
theorem lpUlaChain_coe {d : ℕ} (U : E d → ℝ) (h : ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L (gradient U)) (initial : Lp (E d) 2 P)
    (noise : ℕ → Lp (E d) 2 P) (n : ℕ) :
    lpUlaChain P U h hLip initial noise n =ᵐ[P] fun ω ↦
      ulaChain U h (initial ω) (fun k ↦ noise k ω) n := by
  induction n with
  | zero => exact Filter.Eventually.of_forall fun _ ↦ rfl
  | succ n ih =>
      filter_upwards [lpUlaUpdate_coe P U h hLip
        (lpUlaChain P U h hLip initial noise n) (noise n), ih] with ω hupdate hprev
      simpa only [lpUlaChain_succ, ulaChain_succ, ulaUpdate, hprev] using hupdate

end ULA
