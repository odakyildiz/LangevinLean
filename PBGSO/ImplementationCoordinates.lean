import PBGSO.ImplementationDynamics

/-! # Invertible continuous-linear implementation coordinates

The exact raw implementation state and complete optimiser/individual-sampler
state are related by explicit continuous linear equivalences. Both directions
are available for transporting actual L² integral trajectories and deriving
the numerical reference equations, rather than assuming a coordinate law.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PBGSO.ImplementationDynamics
variable {A X : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Repack the original momentum-position phase with a continuous inverse. -/
def momentumStateEquiv (N : ℕ) :
    ((A × (Fin N → X)) × (A × (Fin N → X))) ≃L[ℝ]
      (HypocoercivePhase A × (Fin N → HypocoercivePhase X)) where
  toFun := momentumParticleState
  invFun := fun z => ((z.1.snd, fun i => (z.2 i).snd), (z.1.fst, fun i => (z.2 i).fst))
  left_inv := by intro z; rfl
  right_inv := by
    intro z
    apply Prod.ext
    · exact WithLp.toLp_ofLp 2 z.1
    · funext i
      exact WithLp.toLp_ofLp 2 (z.2 i)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  continuous_toFun := by unfold momentumParticleState; fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem momentumStateEquiv_apply (N : ℕ)
    (z : (A × (Fin N → X)) × (A × (Fin N → X))) :
    momentumStateEquiv N z = momentumParticleState z := rfl

@[simp] theorem momentumStateEquiv_symm_apply (N : ℕ)
    (z : HypocoercivePhase A × (Fin N → HypocoercivePhase X)) :
    (momentumStateEquiv N).symm z =
      ((z.1.snd, fun i => (z.2 i).snd), (z.1.fst, fun i => (z.2 i).fst)) := rfl

/-- Repack the original HOL phase, with its complete continuous inverse. -/
def higherOrderStateEquiv (N : ℕ) :
    Methods.HOLState A (Fin N → X) ≃L[ℝ] (A × (Fin N → HigherOrderSampler X)) where
  toFun := higherOrderParticleState
  invFun := fun z => (z.1, (fun i => (z.2 i).fst),
    (fun i => (z.2 i).snd.fst), (fun i => (z.2 i).snd.snd))
  left_inv := by intro z; rfl
  right_inv := by
    intro z
    apply Prod.ext
    · rfl
    · funext i
      apply WithLp.ofLp_injective 2
      apply Prod.ext
      · rfl
      · exact WithLp.toLp_ofLp 2 (z.2 i).snd
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  continuous_toFun := by unfold higherOrderParticleState; fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem higherOrderStateEquiv_apply (N : ℕ) (z : Methods.HOLState A (Fin N → X)) :
    higherOrderStateEquiv N z = higherOrderParticleState z := rfl

@[simp] theorem higherOrderStateEquiv_symm_apply (N : ℕ)
    (z : A × (Fin N → HigherOrderSampler X)) :
    (higherOrderStateEquiv N).symm z = (z.1, (fun i => (z.2 i).fst),
      (fun i => (z.2 i).snd.fst), (fun i => (z.2 i).snd.snd)) := rfl

end PBGSO.ImplementationDynamics
