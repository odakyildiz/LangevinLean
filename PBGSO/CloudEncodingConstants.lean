import PBGSO.MethodMetricComparisons

/-! # Numerical norms of the standard Euclidean particle encoding
The flattened Euclidean-to-sup array map has norm at most one, and its
inverse has norm at most `sqrt N`. Both values are attained when the particle
and physical coordinate sets are nonempty. -/
noncomputable section
open scoped BigOperators
namespace PBGSO.Methods
variable (N : ℕ) (J : Type*) [Fintype J]

/-- The standard Euclidean cloud encoding is nonexpansive into the array sup norm. -/
theorem cloudEncoding_norm_le (x : EuclideanSpace ℝ (Fin N × J)) :
    ‖euclideanParticleEncoding N J x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← MethodMetricComparisons.cloud_norm_sq x]
  exact Finset.single_le_sum (f := fun j : Fin N =>
    ‖euclideanParticleEncoding N J x j‖^2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)

/-- The inverse standard encoding costs at most the square root of population. -/
theorem cloudEncoding_inverse_norm_le (x : Fin N → EuclideanSpace ℝ J) :
    ‖(euclideanParticleEncoding N J).symm x‖≤Real.sqrt (N:ℝ)*‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤Real.sqrt (N:ℝ)*‖x‖)).mp
  rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg N),
    ← MethodMetricComparisons.cloud_norm_sq ((euclideanParticleEncoding N J).symm x)]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  calc
    ∑ i, ‖x i‖^2 ≤ ∑ _i : Fin N, ‖x‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_le_pi_norm x i)
    _ = (N:ℝ)*‖x‖^2 := by simp

/-- Exact numeric upper bound for the encoding operator norm, including zero dimension. -/
theorem cloudEncoding_opNorm_le_one :
    ‖(euclideanParticleEncoding N J).toContinuousLinearMap‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖euclideanParticleEncoding N J x‖≤1*‖x‖
  simpa only [one_mul] using cloudEncoding_norm_le N J x

/-- Exact numeric upper bound for the inverse encoding, including zero dimension. -/
theorem cloudEncoding_inverse_opNorm_le_sqrt :
    ‖(euclideanParticleEncoding N J).symm.toContinuousLinearMap‖≤Real.sqrt (N:ℝ) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (cloudEncoding_inverse_norm_le N J)

/-- A single nonzero physical coordinate attains the encoding norm. -/
theorem cloudEncoding_opNorm_eq_one (hN : 0 < N) [Nonempty J] :
    ‖(euclideanParticleEncoding N J).toContinuousLinearMap‖ = 1 := by
  classical
  obtain ⟨j⟩ := ‹Nonempty J›
  let i : Fin N := ⟨0,hN⟩
  let x : EuclideanSpace ℝ (Fin N × J) := PiLp.single 2 (i,j) (1:ℝ)
  have hx : ‖x‖=1 := by simp [x,PiLp.norm_single]
  have hi : euclideanParticleEncoding N J x i=PiLp.single 2 j (1:ℝ) := by
    ext k
    simp [x,euclideanParticleEncoding_apply,PiLp.single_apply]
  apply le_antisymm (cloudEncoding_opNorm_le_one N J)
  calc
    1 = ‖euclideanParticleEncoding N J x i‖ := by rw [hi]; simp [PiLp.norm_single]
    _ ≤ ‖euclideanParticleEncoding N J x‖ := norm_le_pi_norm _ _
    _ ≤ ‖(euclideanParticleEncoding N J).toContinuousLinearMap‖*‖x‖ :=
      (euclideanParticleEncoding N J).toContinuousLinearMap.le_opNorm x
    _ = _ := by rw [hx,mul_one]

/-- A constant unit particle cloud attains the inverse encoding norm. -/
theorem cloudEncoding_inverse_opNorm_eq_sqrt (hN : 0 < N) [Nonempty J] :
    ‖(euclideanParticleEncoding N J).symm.toContinuousLinearMap‖ = Real.sqrt (N:ℝ) := by
  classical
  obtain ⟨j⟩ := ‹Nonempty J›
  let i : Fin N := ⟨0,hN⟩
  let _ : Nonempty (Fin N) := ⟨i⟩
  let e : EuclideanSpace ℝ J := PiLp.single 2 j (1:ℝ)
  let x : Fin N → EuclideanSpace ℝ J := fun _ => e
  have he : ‖e‖=1 := by simp [e,PiLp.norm_single]
  have hx : ‖x‖=1 := by simp [x,he]
  have hi : ‖(euclideanParticleEncoding N J).symm x‖=Real.sqrt (N:ℝ) := by
    apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (Nat.cast_nonneg N),
      ← MethodMetricComparisons.cloud_norm_sq ((euclideanParticleEncoding N J).symm x)]
    simp [x,he]
  apply le_antisymm (cloudEncoding_inverse_opNorm_le_sqrt N J)
  calc
    Real.sqrt (N:ℝ)=‖(euclideanParticleEncoding N J).symm x‖ := hi.symm
    _ ≤ ‖(euclideanParticleEncoding N J).symm.toContinuousLinearMap‖*‖x‖ :=
      (euclideanParticleEncoding N J).symm.toContinuousLinearMap.le_opNorm x
    _ = _ := by rw [hx,mul_one]

/-- Empty physical coordinates give the zero encoding operator. -/
theorem cloudEncoding_opNorm_eq_zero [IsEmpty J] :
    ‖(euclideanParticleEncoding N J).toContinuousLinearMap‖ = 0 := by
  have he : (euclideanParticleEncoding N J).toContinuousLinearMap = 0 := by
    ext x i j
    exact isEmptyElim j
  rw [he,norm_zero]

/-- Empty physical coordinates give the zero inverse encoding operator. -/
theorem cloudEncoding_inverse_opNorm_eq_zero [IsEmpty J] :
    ‖(euclideanParticleEncoding N J).symm.toContinuousLinearMap‖ = 0 := by
  have he : (euclideanParticleEncoding N J).symm.toContinuousLinearMap = 0 := by
    ext x ij
    exact isEmptyElim ij.2
  rw [he,norm_zero]

section ForceConstants
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  (D : ParticleForceData A (EuclideanSpace ℝ J) (EuclideanSpace ℝ (Fin N × J)) N)

/-- The exact displayed empirical force constant in positive physical dimension. -/
theorem meanLip_euclidean [Nonempty J]
    (hcloud : D.cloud = euclideanParticleEncoding N J) :
    (D.meanLip : ℝ) = 2*(D.parameterLip : ℝ) := by
  change (D.parameterLip : ℝ)*(1+‖D.cloud.toContinuousLinearMap‖)=_
  rw [hcloud,cloudEncoding_opNorm_eq_one N J D.nonempty]
  ring

/-- The exact displayed sampler force constant in positive physical dimension. -/
theorem samplerForceLip_euclidean [Nonempty J]
    (hcloud : D.cloud = euclideanParticleEncoding N J) :
    (D.samplerForceLip : ℝ) = 2*Real.sqrt (N:ℝ)*(D.samplerLip : ℝ) := by
  change ‖D.cloud.symm.toContinuousLinearMap‖*(D.samplerLip : ℝ)*
    (1+‖D.cloud.toContinuousLinearMap‖)=_
  rw [hcloud,cloudEncoding_opNorm_eq_one N J D.nonempty,
    cloudEncoding_inverse_opNorm_eq_sqrt N J D.nonempty]
  ring

/-- The exact empirical force constant when the physical position space is zero. -/
theorem meanLip_euclidean_zero [IsEmpty J]
    (hcloud : D.cloud = euclideanParticleEncoding N J) :
    (D.meanLip : ℝ) = (D.parameterLip : ℝ) := by
  change (D.parameterLip : ℝ)*(1+‖D.cloud.toContinuousLinearMap‖)=_
  rw [hcloud,cloudEncoding_opNorm_eq_zero]
  ring

/-- The exact sampler force constant when the physical position space is zero. -/
theorem samplerForceLip_euclidean_zero [IsEmpty J]
    (hcloud : D.cloud = euclideanParticleEncoding N J) :
    (D.samplerForceLip : ℝ) = 0 := by
  change ‖D.cloud.symm.toContinuousLinearMap‖*(D.samplerLip : ℝ)*
    (1+‖D.cloud.toContinuousLinearMap‖)=_
  rw [hcloud,cloudEncoding_inverse_opNorm_eq_zero]
  ring
end ForceConstants

end PBGSO.Methods
