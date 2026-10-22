import IPLA.Dynamics

set_option linter.style.header false

/-!
# The pairwise proximal interacting particle algorithms

The proximity map here is an arbitrary supplied map on one parameter-particle
pair. `Proximal.lean` constructs that map from its actual minimization problem.
In particular, averaging the pairwise parameter outputs is part of the
algorithm; it is not identified with the proximity map of the lifted sum.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace ProximalLangevin

/-- Apply a joint map to each common-parameter/particle pair, then average its
parameter outputs and rescale its particle outputs. -/
def pairwiseMap {N dθ dx : ℕ} (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx)
    (z : IPLA.State N dθ dx) : IPLA.State N dθ dx :=
  WithLp.toLp 2 (Sum.elim
    (fun j ↦ (N : ℝ)⁻¹ * ∑ i : Fin N, P (IPLA.joint i z) (Sum.inl j))
    (fun ij ↦ (Real.sqrt N)⁻¹ * P (IPLA.joint ij.1 z) (Sum.inr ij.2)))

@[simp] theorem pairwiseMap_parameter {N dθ dx : ℕ}
    (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx)
    (z : IPLA.State N dθ dx) (j : Fin dθ) :
    pairwiseMap P z (Sum.inl j) =
      (N : ℝ)⁻¹ * ∑ i : Fin N, P (IPLA.joint i z) (Sum.inl j) := rfl

@[simp] theorem pairwiseMap_particle {N dθ dx : ℕ}
    (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx)
    (z : IPLA.State N dθ dx) (i : Fin N) (j : Fin dx) :
    pairwiseMap P z (Sum.inr (i, j)) =
      (Real.sqrt N)⁻¹ * P (IPLA.joint i z) (Sum.inr j) := rfl

/-- PIPULA: pairwise proximity, followed by noise. -/
def pipulaUpdate {N dθ dx : ℕ} (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx)
    (γ : ℝ) (z ξ : IPLA.State N dθ dx) : IPLA.State N dθ dx :=
  pairwiseMap P z + Real.sqrt (2 * γ / N) • ξ

/-- MYIPLA, with independent smoothing and time steps. -/
def myiplaUpdate {N dθ dx : ℕ} (g₁ : IPLA.Joint dθ dx → ℝ)
    (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx) (η γ : ℝ)
    (z ξ : IPLA.State N dθ dx) : IPLA.State N dθ dx :=
  (1 - γ / η) • z - (γ / N) • gradient (IPLA.potential g₁) z +
    (γ / η) • pairwiseMap P z + Real.sqrt (2 * γ / N) • ξ

/-- PIPGLA: the noisy smooth forward step is followed by
the pairwise proximal map. The common parameter is averaged only at the end. -/
def pipglaUpdate {N dθ dx : ℕ} (g₁ : IPLA.Joint dθ dx → ℝ)
    (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx) (γ : ℝ)
    (z ξ : IPLA.State N dθ dx) : IPLA.State N dθ dx :=
  pairwiseMap P (IPLA.scaledUpdate g₁ γ z ξ)

/-- Iterate the displayed state update against a specified innovation sequence. -/
def algorithmChain {E : Type*} (update : E → E → E) (initial : E)
    (noise : ℕ → E) : ℕ → E
  | 0 => initial
  | n + 1 => update (algorithmChain update initial noise n) (noise n)

@[simp] theorem algorithmChain_zero {E : Type*} (update : E → E → E)
    (initial : E) (noise : ℕ → E) : algorithmChain update initial noise 0 = initial := rfl

@[simp] theorem algorithmChain_succ {E : Type*} (update : E → E → E)
    (initial : E) (noise : ℕ → E) (n : ℕ) :
    algorithmChain update initial noise (n + 1) =
      update (algorithmChain update initial noise n) (noise n) := rfl

/-- The full MYIPLA recursion, without any convergence assumption. -/
def myiplaChain {N dθ dx : ℕ} (g₁ : IPLA.Joint dθ dx → ℝ)
    (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx) (η γ : ℝ)
    (initial : IPLA.State N dθ dx) (noise : ℕ → IPLA.State N dθ dx) :=
  algorithmChain (myiplaUpdate g₁ P η γ) initial noise

/-- The full PIPULA recursion. -/
def pipulaChain {N dθ dx : ℕ} (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx)
    (γ : ℝ) (initial : IPLA.State N dθ dx) (noise : ℕ → IPLA.State N dθ dx) :=
  algorithmChain (pipulaUpdate P γ) initial noise

/-- The full PIPGLA recursion. -/
def pipglaChain {N dθ dx : ℕ} (g₁ : IPLA.Joint dθ dx → ℝ)
    (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx) (γ : ℝ)
    (initial : IPLA.State N dθ dx) (noise : ℕ → IPLA.State N dθ dx) :=
  algorithmChain (pipglaUpdate g₁ P γ) initial noise

/-- PIPULA's parameter component is precisely the averaged joint proximal
parameter output, followed by the parameter Gaussian noise. -/
theorem pipulaUpdate_parameter {N dθ dx : ℕ}
    (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx) (γ : ℝ)
    (z ξ : IPLA.State N dθ dx) (j : Fin dθ) :
    pipulaUpdate P γ z ξ (Sum.inl j) =
      (N : ℝ)⁻¹ * ∑ i : Fin N, P (IPLA.joint i z) (Sum.inl j) +
        Real.sqrt (2 * γ / N) * ξ (Sum.inl j) := rfl

/-- Removing the smooth part and equating the two time scales recovers
PIPULA exactly, including its noise placement. -/
theorem pipulaUpdate_eq_myiplaUpdate {N dθ dx : ℕ}
    (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx) {γ : ℝ} (hγ : γ ≠ 0)
    (z ξ : IPLA.State N dθ dx) :
    pipulaUpdate P γ z ξ = myiplaUpdate (fun _ ↦ 0) P γ γ z ξ := by
  have hpot : IPLA.potential (fun _ : IPLA.Joint dθ dx ↦ (0 : ℝ)) =
      fun _ : IPLA.State N dθ dx ↦ (0 : ℝ) := by
    funext w
    simp [IPLA.potential]
  simp [pipulaUpdate, myiplaUpdate, hγ, hpot, gradient_fun_const]

/-- The exact PIPULA/MYIPLA specialization holds for every iteration. -/
theorem pipulaChain_eq_myiplaChain {N dθ dx : ℕ}
    (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx) {γ : ℝ} (hγ : γ ≠ 0)
    (initial : IPLA.State N dθ dx) (noise : ℕ → IPLA.State N dθ dx) (n : ℕ) :
    pipulaChain P γ initial noise n = myiplaChain (fun _ ↦ 0) P γ γ initial noise n := by
  have hu : pipulaUpdate (N := N) P γ = myiplaUpdate (fun _ ↦ 0) P γ γ :=
    funext fun z ↦ funext fun ξ ↦ pipulaUpdate_eq_myiplaUpdate P hγ z ξ
  simp only [pipulaChain, myiplaChain, hu]

/-- The MYIPLA parameter coordinate is the displayed averaged pairwise formula. -/
theorem myiplaUpdate_parameter {N dθ dx : ℕ} {g₁ : IPLA.Joint dθ dx → ℝ}
    (hg₁ : Differentiable ℝ g₁) (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx)
    (η γ : ℝ) (z ξ : IPLA.State N dθ dx) (j : Fin dθ) :
    myiplaUpdate g₁ P η γ z ξ (Sum.inl j) =
      (1 - γ / η) * z (Sum.inl j) -
        (γ / N) * ∑ i : Fin N, gradient g₁ (IPLA.joint i z) (Sum.inl j) +
        (γ / η) * ((N : ℝ)⁻¹ * ∑ i : Fin N, P (IPLA.joint i z) (Sum.inl j)) +
        Real.sqrt (2 * γ / N) * ξ (Sum.inl j) := by
  simp [myiplaUpdate, IPLA.gradient_potential_parameter hg₁]

/-- The MYIPLA physical-particle coordinate is exactly the displayed physical-particle formula. -/
theorem myiplaUpdate_particle {N dθ dx : ℕ} (hN : 0 < N)
    {g₁ : IPLA.Joint dθ dx → ℝ} (hg₁ : Differentiable ℝ g₁)
    (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx) (η γ : ℝ)
    (z ξ : IPLA.State N dθ dx) (i : Fin N) (j : Fin dx) :
    Real.sqrt N * myiplaUpdate g₁ P η γ z ξ (Sum.inr (i, j)) =
      (1 - γ / η) * (Real.sqrt N * z (Sum.inr (i, j))) -
        γ * gradient g₁ (IPLA.joint i z) (Sum.inr j) +
        (γ / η) * P (IPLA.joint i z) (Sum.inr j) +
        Real.sqrt (2 * γ) * ξ (Sum.inr (i, j)) := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hN)).ne'
  have hnoise : Real.sqrt N * Real.sqrt (2 * γ / N) = Real.sqrt (2 * γ) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg N)]
    congr 1
    field_simp
  simp only [myiplaUpdate, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
    smul_eq_mul, pairwiseMap_particle, IPLA.gradient_potential_particle hg₁]
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg N)
  calc
    _ = (1 - γ / η) * (Real.sqrt N * z (Sum.inr (i, j))) -
        (γ / N) * (Real.sqrt N ^ 2) * gradient g₁ (IPLA.joint i z) (Sum.inr j) +
        (γ / η) * (Real.sqrt N * (Real.sqrt N)⁻¹) * P (IPLA.joint i z) (Sum.inr j) +
        (Real.sqrt N * Real.sqrt (2 * γ / N)) * ξ (Sum.inr (i, j)) := by ring
    _ = _ := by rw [hs2, mul_inv_cancel₀ hs, hnoise]; field_simp

/-- A pairwise residual gradient becomes the corresponding lifted Euler step.
This is an equality of actual coordinate maps, not an assumed law identity. -/
theorem pairwiseMap_eq_gradient_step {N dθ dx : ℕ} (hN : 0 < N)
    {e : IPLA.Joint dθ dx → ℝ} (he : Differentiable ℝ e)
    (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx) {η : ℝ} (hη : η ≠ 0)
    (hgrad : ∀ x, gradient e x = η⁻¹ • (x - P x))
    (z : IPLA.State N dθ dx) :
    pairwiseMap P z = z - (η / N) • gradient (IPLA.potential e) z := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hN)).ne'
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg N)
  have hroot : (Real.sqrt (N : ℝ))⁻¹ = Real.sqrt N / N := by
    field_simp
    nlinarith
  have hP (x : IPLA.Joint dθ dx) : P x = x - η • gradient e x := by
    rw [hgrad]
    ext a
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp
    ring
  ext a
  rcases a with j | ⟨i, j⟩
  · simp only [pairwiseMap_parameter, hP, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul, IPLA.gradient_potential_parameter he, IPLA.joint_parameter,
      Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · simp only [pairwiseMap_particle, hP, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul, IPLA.gradient_potential_particle he, IPLA.joint_particle, hroot]
    field_simp
    linear_combination (z (Sum.inr (i, j))) * hs2

/-- The gradient of a sum, with the differentiability hypotheses explicit. -/
theorem gradient_add_of_differentiable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {f g : E → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (x : E) :
    gradient (fun y ↦ f y + g y) x = gradient f x + gradient g x := by
  simp only [gradient, fderiv_fun_add (hf x) (hg x), map_add]

/-- The expanded MYIPLA step is exactly IPLA for `g₁ + e` whenever `e` has
the genuine proximal residual gradient. -/
theorem myiplaUpdate_eq_scaledUpdate {N dθ dx : ℕ} (hN : 0 < N)
    {g₁ e : IPLA.Joint dθ dx → ℝ} (hg₁ : Differentiable ℝ g₁)
    (he : Differentiable ℝ e)
    (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx) {η : ℝ} (hη : η ≠ 0)
    (hgrad : ∀ x, gradient e x = η⁻¹ • (x - P x))
    (γ : ℝ) (z ξ : IPLA.State N dθ dx) :
    myiplaUpdate g₁ P η γ z ξ = IPLA.scaledUpdate (fun x ↦ g₁ x + e x) γ z ξ := by
  have hpot : IPLA.potential (fun x ↦ g₁ x + e x) =
      fun z : IPLA.State N dθ dx ↦ IPLA.potential g₁ z + IPLA.potential e z := by
    funext w
    simp [IPLA.potential, Finset.sum_add_distrib]
  rw [myiplaUpdate, pairwiseMap_eq_gradient_step hN he P hη hgrad,
    IPLA.scaledUpdate, hpot,
    gradient_add_of_differentiable (IPLA.potential_differentiable hg₁)
      (IPLA.potential_differentiable he)]
  ext a
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- The entire expanded recursion agrees pointwise with the existing IPLA
recursion for the smoothed potential. -/
theorem myiplaChain_eq_scaledChain {N dθ dx : ℕ} (hN : 0 < N)
    {g₁ e : IPLA.Joint dθ dx → ℝ} (hg₁ : Differentiable ℝ g₁)
    (he : Differentiable ℝ e)
    (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx) {η : ℝ} (hη : η ≠ 0)
    (hgrad : ∀ x, gradient e x = η⁻¹ • (x - P x))
    (γ : ℝ) (initial : IPLA.State N dθ dx)
    (noise : ℕ → IPLA.State N dθ dx) (n : ℕ) :
    myiplaChain g₁ P η γ initial noise n =
      IPLA.scaledChain (fun x ↦ g₁ x + e x) γ initial noise n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [myiplaChain, algorithmChain_succ, IPLA.scaledChain_succ] at ih ⊢
    rw [ih, myiplaUpdate_eq_scaledUpdate hN hg₁ he P hη hgrad]

end ProximalLangevin
