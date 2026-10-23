import KineticLangevin.LpHamiltonianLaw
import KineticLangevin.LpWeightedGeometry

/-! # The actual integrated local OBABO coupling cost

The exact Hamiltonian representative and both thermostat noises are retained
on the same probability space. The weighted L² phase identity converts the
genuine local state estimate into the actual finite-dimensional coupling cost.
-/

noncomputable section
set_option linter.style.header false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace KineticLangevin
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  (P : Measure Ω) [IsProbabilityMeasure P]

def obaboLocalBudget (M h d : ℝ) : ℝ :=
  2 * h ^ 2 * (Real.sqrt (M * d) + Real.sqrt M * Real.sqrt d + Real.sqrt M * Real.sqrt (M * d) * h / 4)

theorem obaboLocalBudget_nonneg (M h d : ℝ) (hh : 0 ≤ h) : 0 ≤ obaboLocalBudget M h d := by
  unfold obaboLocalBudget
  positivity

theorem lp_obabo_hamiltonian_local_cost
    (f : EuclideanSpace ℝ ι → ℝ) (m γ h δ σ : ℝ) (M : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith M (gradient f))
    (hm : 0 < m) (hγ : 0 < γ) (hM : 0 < (M : ℝ)) (hh : 0 ≤ h)
    (hfriction : 4 * (M : ℝ) ≤ γ ^ 2) (hδ : |δ| ≤ 1)
    (Z : Lp (EuclideanSpace ℝ ι) 2 P × Lp (EuclideanSpace ℝ ι) 2 P)
    (Ξ Ξ' : Lp (EuclideanSpace ℝ ι) 2 P)
    (hlaw : P.map (lpPhaseCoe P (ornsteinStep δ σ Ξ Z)) = kineticGibbsTarget f) :
    eLpNorm (fun ω ↦ weightedPhaseTransform (1 / (M : ℝ)) (1 / γ)
      (obaboStep (gradient f) h δ σ (lpPhaseCoe P Z ω) (Ξ ω) (Ξ' ω) -
        ornsteinStep δ σ (Ξ' ω)
          (hamiltonianFlow f M hLip h hh (ornsteinStep δ σ (Ξ ω) (lpPhaseCoe P Z ω)) h))) 2 P ≤
      ENNReal.ofReal (obaboLocalBudget M h (Fintype.card ι : ℝ)) := by
  let A := lpHamiltonianFlow P (gradient f) M hLip h hh (ornsteinStep δ σ Ξ Z)
  let N := obaboStep (ULA.lpDrift P (gradient f) hLip) h δ σ Z Ξ Ξ'
  let R := ornsteinStep δ σ Ξ' (A h)
  have hlocal := lp_obabo_target_local_bound P f m γ h δ σ M hf hsc hLip hm hγ hM hh hfriction hδ Z Ξ Ξ' hlaw
  have hN := lp_obaboStep_coe P (gradient f) M hLip h δ σ Z Ξ Ξ'
  have hR : lpPhaseCoe P R =ᵐ[P] fun ω ↦ ornsteinStep δ σ (Ξ' ω)
      (hamiltonianFlow f M hLip h hh (ornsteinStep δ σ (Ξ ω) (lpPhaseCoe P Z ω)) h) := by
    filter_upwards [lp_ornsteinStep_coe P δ σ Ξ' (A h),
      lpHamiltonianFlow_coe P f M hLip h hh (ornsteinStep δ σ Ξ Z) h ⟨hh,le_rfl⟩,
      lp_ornsteinStep_coe P δ σ Ξ Z] with ω hlast hflow hfirst
    change lpPhaseCoe P (ornsteinStep δ σ Ξ' (A h)) ω = _
    rw [hlast,hflow,hfirst]
  have hcoe : (fun ω ↦ weightedPhaseTransform (1 / (M : ℝ)) (1 / γ) (lpPhaseCoe P (N - R) ω)) =ᵐ[P]
      fun ω ↦ weightedPhaseTransform (1 / (M : ℝ)) (1 / γ)
        (obaboStep (gradient f) h δ σ (lpPhaseCoe P Z ω) (Ξ ω) (Ξ' ω) -
          ornsteinStep δ σ (Ξ' ω)
            (hamiltonianFlow f M hLip h hh (ornsteinStep δ σ (Ξ ω) (lpPhaseCoe P Z ω)) h)) := by
    filter_upwards [lpPhaseCoe_sub P N R,hN,hR] with ω hsub hnum href
    rw [hsub,hnum,href]
  rw [← eLpNorm_congr_ae hcoe, eLpNorm_weightedPhaseCoe]
  exact ENNReal.ofReal_le_ofReal hlocal

end KineticLangevin
