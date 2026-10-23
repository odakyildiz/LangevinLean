import KineticLangevin.Coefficients

noncomputable section
open MeasureTheory Set
namespace KineticLangevin

/-- Every positive-length integrated exponential velocity response is strictly positive. -/
theorem psi_one_pos (γ h : ℝ) (hh : 0<h) : 0<psi γ 1 h := by
  rw [psi_succ]
  apply intervalIntegral.integral_pos hh (continuous_psi γ 0).continuousOn
  · intro t _
    exact (Real.exp_pos _).le
  · exact ⟨0,⟨le_rfl,hh.le⟩,Real.exp_pos _⟩

/-- The two exponential-integrator kernels are linearly independent on every positive-length interval. -/
theorem klmcKernels_nonzero_on_interval (γ h : ℝ) (hh : 0<h)
    (z : Fin 2→ℝ) (hz : z≠0) :
    ∃ t∈Icc 0 h,0<(∑ i,z i*klmcKernels γ i t)^2 := by
  by_cases h0 : z 0=0
  · have h1 : z 1≠0 := by
      intro hz1
      apply hz
      funext i
      fin_cases i <;> simp [h0,hz1]
    refine ⟨h,⟨hh.le,le_rfl⟩,?_⟩
    simp only [Fin.sum_univ_two,klmcKernels,Matrix.cons_val_zero,Matrix.cons_val_one,h0,zero_mul,zero_add]
    exact sq_pos_of_ne_zero (mul_ne_zero h1 (ne_of_gt (psi_one_pos γ h hh)))
  · refine ⟨0,⟨le_rfl,hh.le⟩,?_⟩
    simpa [Fin.sum_univ_two,klmcKernels,psi_at_zero] using sq_pos_of_ne_zero h0

/-- The literal KIPLMC1 covariance admits a genuine positive-definite Cholesky factor. -/
theorem klmcCovariance_posDef (γ h : ℝ) (hh : 0<h) : (klmcCovariance γ h).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨Matrix.isHermitian_iff_isSymm.mpr (gramCovariance_symmetric (klmcKernels γ) h),?_⟩
  intro z hz
  simp only [dotProduct,Matrix.mulVec,star_trivial,Finset.mul_sum]
  have he : (∑ i,∑ j,z i*(gramCovariance (klmcKernels γ) h i j*z j))=
      ∑ i,∑ j,z i*gramCovariance (klmcKernels γ) h i j*z j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  change 0<∑ i,∑ j,z i*(gramCovariance (klmcKernels γ) h i j*z j)
  rw [he,gramCovariance_quadratic (klmcKernels γ) (continuous_klmcKernels γ)]
  have hc : Continuous (fun t : ℝ ↦ (∑ i,z i*klmcKernels γ i t)^2) :=
    (continuous_finsetSum _ (fun i _ ↦ continuous_const.mul (continuous_klmcKernels γ i))).pow 2
  exact intervalIntegral.integral_pos hh hc.continuousOn (fun _ _ ↦ sq_nonneg _)
    (klmcKernels_nonzero_on_interval γ h hh z hz)

end KineticLangevin
