import PBGSO.UniversalMomentGrowth
import Mathlib.MeasureTheory.Function.L2Space

/-! # The finite signed-work convention is a substantive source assumption
A finite-second-moment law need not have finite fourth moment. Consequently
uniform finite signed work over all P2 laws excludes even some elementary
strongly dissipative superlinear drifts. This is a scope audit, not a claimed
counterexample to the paper's contraction conclusion.
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace PBGSO.FiniteWorkScopeAudit

/-- An actual probability law can have integrable quadratic weight and
nonintegrable fourth power. The law is constructed by the proved atomic
contradiction underlying universal finite-moment growth. -/
theorem exists_quadratic_not_quartic :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      Integrable (fun x : ℝ => 1 + x ^ 2) μ ∧ ¬ Integrable (fun x : ℝ => x ^ 4) μ := by
  by_contra hn
  have h : ∀ μ : Measure ℝ, IsProbabilityMeasure μ →
      Integrable (fun x : ℝ => 1 + x ^ 2) μ → Integrable (fun x : ℝ => x ^ 4) μ := by
    intro μ hp hw
    by_contra hq
    exact hn ⟨μ,hp,hw,hq⟩
  obtain ⟨C,hC,hbound⟩ := UniversalMomentGrowth.growth_of_probability_integrability
    (fun x : ℝ => 1 + x ^ 2) (fun x => by nlinarith [sq_nonneg x])
    (fun x : ℝ => x ^ 4) h
  let x := Real.sqrt (C+1)
  have hs : x ^ 2 = C+1 := Real.sq_sqrt (by linarith)
  have hb := hbound x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ x ^ 4)] at hb
  nlinarith [sq_nonneg C]

def drift (x : ℝ) : ℝ := -x-x^3

/-- The source's elementary dissipativity inequality does allow this
superlinear drift pointwise. -/
theorem drift_strongly_dissipative (x y : ℝ) :
    (x-y)*(drift x-drift y) ≤ -(x-y)^2 := by
  have h : 0 ≤ x^2+x*y+y^2 := by nlinarith [sq_nonneg (x+y),sq_nonneg x,sq_nonneg y]
  have hp := mul_nonneg (sq_nonneg (x-y)) h
  dsimp [drift]
  nlinarith

/-- Nevertheless, universal finite signed coupling-work integrability is
strictly stronger than P2 plus pointwise strong dissipativity. -/
theorem exists_p2_nonintegrable_work :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ MemLp (fun x : ℝ => x) 2 μ ∧
      ¬ Integrable (fun x : ℝ => x*(drift x-drift 0)) μ := by
  obtain ⟨μ,hp,hw,hq⟩ := exists_quadratic_not_quartic
  letI := hp
  have h2 : Integrable (fun x : ℝ => x^2) μ := by
    apply hw.mono' (by fun_prop)
    exact Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg x)]; linarith)
  refine ⟨μ,hp,(memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr ?_,?_⟩
  · simpa only [Real.norm_eq_abs,sq_abs] using h2
  · intro hi
    apply hq
    have he : (fun x : ℝ => -(x*(drift x-drift 0))-x^2) = fun x : ℝ => x^4 := by
      funext x
      dsimp [drift]
      ring
    rw [← he]
    exact hi.neg.sub h2
end PBGSO.FiniteWorkScopeAudit
