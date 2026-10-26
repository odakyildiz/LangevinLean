import PBGSO.CanonicalProjectedCriterion
import PBGSO.DiracOptimizerGrowth

/-! # The projected source criterion with its explicit finite signed domain
The source U5 sampler inequality contains a signed drift-work integral for
every P2 coupling. Reading those integrals as finite is stated independently
of the inequality. Constant diffusion turns this domain directly into the
universal finite-work convention needed by the constant-noise law theorem.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Matrix MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator BigOperators
namespace PBGSO.CanonicalProjected
open GeneralizedSpectrum
variable {a u x v I : Type*}
  [Fintype a] [DecidableEq a] [Nonempty a] [Fintype u] [DecidableEq u]
  [Fintype x] [DecidableEq x] [Nonempty x] [Fintype v] [DecidableEq v] [Fintype I]

/-- Explicit ordinary finite signed-integral domain of the universal U5
sampler inequality. This is not a consequence of the conditional inequality. -/
def FiniteSamplerDriftDomain
    (M : Model (BlockSpace a u) (EuclideanSpace ℝ a) (BlockSpace x v) (EuclideanSpace ℝ x) I)
    (D : TwistedGeometry (BlockSpace a u) (BlockSpace x v)) : Prop :=
  ∀ s s' (Λ : Measure (BlockSpace x v × BlockSpace x v)),
    IsProbabilityMeasure Λ → Integrable (fun p => 1+‖p.1‖ ^ 2+‖p.2‖ ^ 2) Λ →
      Integrable (samplerDriftWork M D s s') Λ

/-- No stochastic energy conclusion is assumed: constant columns cancel
algebraically, so the U5 finite domain gives precisely finite sampler work. -/
theorem finiteCouplingWork_of_U5_domain
    (M : Model (BlockSpace a u) (EuclideanSpace ℝ a) (BlockSpace x v) (EuclideanSpace ℝ x) I)
    (D : TwistedGeometry (BlockSpace a u) (BlockSpace x v))
    (σ : I → BlockSpace x v) (hσ : ∀ θ z, M.diffusion θ z = σ)
    (hfinite : FiniteSamplerDriftDomain M D) : DiracOptimizerGrowth.FiniteCouplingWork M D := by
  intro s s' Λ hp hw
  rw [samplerCouplingWork_eq_drift_of_constant M D σ hσ]
  exact hfinite s s' Λ hp hw

/-- The literal canonical projected source criterion supplies both the joint
inequality and its finite-work domain when U5 is read with ordinary finite
signed integrals. The domain is visible, not inferred from monotonicity. -/
theorem canonical_projected_source_criterion_finite
    (M : Model (BlockSpace a u) (EuclideanSpace ℝ a) (BlockSpace x v) (EuclideanSpace ℝ x) I)
    (hparameter : M.parameter = WithLp.fst) (hposition : M.position = WithLp.fst)
    (H : EuclideanSpace ℝ a → EuclideanSpace ℝ x → EuclideanSpace ℝ x)
    (DOpt : Matrix (a ⊕ u) (a ⊕ u) ℝ) (DSam : Matrix (x ⊕ v) (x ⊕ v) ℝ)
    (Dm : Matrix u u ℝ) (Dv : Matrix v v ℝ)
    (hDOpt : DOpt.PosDef) (hDSam : DSam.PosDef) (hDm : Dm.PosDef) (hDv : Dv.PosDef)
    (β r AOpt ASam : ℝ) (hβ : 0 ≤ β) (hc : 0 < β * r - AOpt - ASam)
    (hmono : (canonicalData M hparameter hposition H Dm Dv).StrongMonotonicity r)
    (haux : ProjectedAuxiliaryDissipation M (canonicalGeometry DOpt DSam hDOpt hDSam)
      (canonicalData M hparameter hposition H Dm Dv) β AOpt ASam)
    (σ : I → BlockSpace x v) (hσ : ∀ θ z, M.diffusion θ z = σ)
    (hInt : ∀ s s' ν ν' Λ,
      ProjectedAdmissibleCoupling M (canonicalGeometry DOpt DSam hDOpt hDSam) s s' ν ν' Λ →
      (canonicalData M hparameter hposition H Dm Dv).Integrability s s' Λ)
    (hfinite : FiniteSamplerDriftDomain M (canonicalGeometry DOpt DSam hDOpt hDSam)) :
    let ρ := min
      (generalizedMinimum hDOpt (blockK_posDef (a := a) _ hc Dm hDm))
      (generalizedMinimum hDSam (blockK_posDef (a := x) _ hc Dv hDv))
    0 < ρ ∧ TwistedJointMonotonicity M (canonicalGeometry DOpt DSam hDOpt hDSam) ρ ∧
      DiracOptimizerGrowth.FiniteCouplingWork M (canonicalGeometry DOpt DSam hDOpt hDSam) := by
  have h := canonical_projected_source_criterion M hparameter hposition H DOpt DSam Dm Dv
    hDOpt hDSam hDm hDv β r AOpt ASam hβ hc hmono haux σ hσ hInt
  exact ⟨h.1,h.2,finiteCouplingWork_of_U5_domain M _ σ hσ hfinite⟩

end PBGSO.CanonicalProjected
