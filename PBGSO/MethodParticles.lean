import PBGSO.HigherOrderMethod

/-! # Identifying the implementation maps with actual particle forces
The optimiser uses `N⁻¹∑F(θ,xᵢ)` and the sampler uses the unaveraged force on
each particle. The dimension-free Lipschitz bounds use the cloud sup norm.
-/
noncomputable section
namespace PBGSO.Methods
variable {Θ X : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Actual empirical optimiser force. A nonempty cloud is required in the
bound below; the map itself follows Lean's total real division convention. -/
def particleMeanForce {N : ℕ} (F : Θ → X → Θ) (θ : Θ) (x : Fin N → X) : Θ :=
  (N : ℝ)⁻¹ • ∑ i, F θ (x i)

/-- Actual sampler force on the entire particle cloud. -/
def particleSamplerForce {N : ℕ} (G : Θ → X → X) (θ : Θ) (x : Fin N → X) : Fin N → X :=
  fun i ↦ G θ (x i)

/-- M-MFPO with the actual empirical force and a thermostat only on sampler
momenta. The optimiser innovation is definitionally zero. -/
def particleMomentumStep {N : ℕ} (F : Θ → X → Θ) (G : Θ → X → X)
    (γ h : ℝ) (z : (Θ × (Fin N → X)) × (Θ × (Fin N → X)))
    (ξ ξ' : Fin N → X) :=
  momentumStep (particleMeanForce F) (particleSamplerForce G) γ h z ξ ξ'

/-- HOL-MYPGD with the actual average optimiser force and the sampler force
applied separately to each particle. -/
def particleHigherOrderStep {N : ℕ} (F : Θ → X → Θ) (G : Θ → X → X)
    (α γ h : ℝ) (z : HOLState Θ (Fin N → X)) (ξ : (Fin N → X) × (Fin N → X) × (Fin N → X)) :=
  higherOrderStep (particleMeanForce F) (particleSamplerForce G) α γ h z ξ

/-- Averaging does not amplify the Lipschitz constant in the cloud sup norm. -/
theorem particleMeanForce_lipschitz {N : ℕ} (hN : 0 < N) (F : Θ → X → Θ)
    (L : ℝ) (hL : 0 ≤ L)
    (hF : ∀ θ θ' x x', ‖F θ x - F θ' x'‖ ≤ L * (‖θ - θ'‖ + ‖x - x'‖))
    (θ θ' : Θ) (x y : Fin N → X) :
    ‖particleMeanForce F θ x - particleMeanForce F θ' y‖ ≤
      L * (‖θ - θ'‖ + ‖x - y‖) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have he : particleMeanForce F θ x - particleMeanForce F θ' y =
      (N : ℝ)⁻¹ • ∑ i, (F θ (x i) - F θ' (y i)) := by
    simp only [particleMeanForce, ← smul_sub, Finset.sum_sub_distrib]
  rw [he, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg hNr.le]
  calc
    _ ≤ (N : ℝ)⁻¹ * ∑ i, ‖F θ (x i) - F θ' (y i)‖ := by
      gcongr; exact norm_sum_le _ _
    _ ≤ (N : ℝ)⁻¹ * ∑ _i : Fin N, L * (‖θ - θ'‖ + ‖x - y‖) := by
      gcongr with i
      exact (hF θ θ' (x i) (y i)).trans (by
        gcongr
        exact norm_le_pi_norm (x - y) i)
    _ = _ := by simp; field_simp

/-- Applying the sampler force coordinatewise preserves its Lipschitz bound. -/
theorem particleSamplerForce_lipschitz {N : ℕ} (G : Θ → X → X) (L : ℝ)
    (hL : 0 ≤ L)
    (hG : ∀ θ θ' x x', ‖G θ x - G θ' x'‖ ≤ L * (‖θ - θ'‖ + ‖x - x'‖))
    (θ θ' : Θ) (x y : Fin N → X) :
    ‖particleSamplerForce G θ x - particleSamplerForce G θ' y‖ ≤
      L * (‖θ - θ'‖ + ‖x - y‖) := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  exact (hG θ θ' (x i) (y i)).trans (by
    gcongr
    exact norm_le_pi_norm (x - y) i)

/-- A Lipschitz condition for the whole coupled force follows from separate
conditions on `F` and `G`, with no compatibility or potential assumption. -/
theorem particleCoupledForce_lipschitz {N : ℕ} (hN : 0 < N)
    (F : Θ → X → Θ) (G : Θ → X → X) (LF LG : ℝ)
    (hLF : 0 ≤ LF) (hLG : 0 ≤ LG)
    (hF : ∀ θ θ' x x', ‖F θ x - F θ' x'‖ ≤ LF * (‖θ - θ'‖ + ‖x - x'‖))
    (hG : ∀ θ θ' x x', ‖G θ x - G θ' x'‖ ≤ LG * (‖θ - θ'‖ + ‖x - x'‖))
    (z w : Θ × (Fin N → X)) :
    ‖coupledForce (particleMeanForce F) (particleSamplerForce G) z -
      coupledForce (particleMeanForce F) (particleSamplerForce G) w‖ ≤
      (2 * max LF LG) * ‖z - w‖ := by
  have hs : ‖z.1 - w.1‖ + ‖z.2 - w.2‖ ≤ 2 * ‖z - w‖ := by
    have h1 : ‖z.1 - w.1‖ ≤ ‖z - w‖ := norm_fst_le (z - w)
    have h2 : ‖z.2 - w.2‖ ≤ ‖z - w‖ := norm_snd_le (z - w)
    linarith
  have h1 := particleMeanForce_lipschitz hN F LF hLF hF z.1 w.1 z.2 w.2
  have h2 := particleSamplerForce_lipschitz G LG hLG hG z.1 w.1 z.2 w.2
  change max _ _ ≤ _
  apply max_le
  · apply h1.trans
    calc
      _ ≤ LF * (2 * ‖z - w‖) := mul_le_mul_of_nonneg_left hs hLF
      _ ≤ (max LF LG) * (2 * ‖z - w‖) := by gcongr; exact le_max_left _ _
      _ = _ := by ring
  · apply h2.trans
    calc
      _ ≤ LG * (2 * ‖z - w‖) := mul_le_mul_of_nonneg_left hs hLG
      _ ≤ (max LF LG) * (2 * ‖z - w‖) := by gcongr; exact le_max_right _ _
      _ = _ := by ring

end PBGSO.Methods
