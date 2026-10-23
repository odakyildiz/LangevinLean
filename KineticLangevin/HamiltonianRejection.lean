import KineticLangevin.HamiltonianTests

/-! # Quadratic rejection estimates for the actual Verlet map -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal ENNReal
namespace KineticLangevin
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The actual Verlet rejection is bounded by its actual Hamiltonian defect. -/
theorem verlet_rejection_le_energy_defect (f : E → ℝ) (h : ℝ) (z : E×E) :
    1-verletAcceptance f h z ≤
      |hamiltonianEnergy f (verletStep (gradient f) h z)-hamiltonianEnergy f z| := by
  exact metropolis_rejection_le_abs_energy _

/-- On steps at most one, a single quadratic phase envelope controls the
entire Verlet energy defect. -/
theorem verlet_energy_defect_quadratic (f : E → ℝ) (M : ℝ≥0)
    (hf : Differentiable ℝ f) (hLip : LipschitzWith M (gradient f))
    (h : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1) (z : E×E) :
    |hamiltonianEnergy f (verletStep (gradient f) h z)-hamiltonianEnergy f z| ≤
      h^2*((M : ℝ)*(2*(M : ℝ)+11)/8)*(‖z.1‖^2+‖gradient f z.2‖^2) := by
  let w := z.1-(h/2) • gradient f z.2
  let a := ‖z.1‖
  let b := ‖gradient f z.2‖
  let W := ‖w‖
  let q := a^2+b^2
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hW : 0 ≤ W := norm_nonneg _
  have hM : 0 ≤ (M : ℝ) := M.coe_nonneg
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hw : W ≤ a+b := by
    have ht := norm_sub_le z.1 ((h/2) • gradient f z.2)
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ h/2)] at ht
    dsimp [W,w,a,b]
    nlinarith
  have hw2 : W^2 ≤ 2*q := by
    have hs : (a+b)^2 ≤ 2*(a^2+b^2) := by nlinarith [sq_nonneg (a-b)]
    exact (sq_le_sq₀ hW (by positivity) |>.mpr hw).trans hs
  have hfac : W*(2*b+(M : ℝ)*h*W) ≤ (2*(M : ℝ)+3)*q := by
    have hhW : (M : ℝ)*h*W ≤ (M : ℝ)*W := by
      calc
        _ = ((M : ℝ)*W)*h := by ring
        _ ≤ ((M : ℝ)*W)*1 := mul_le_mul_of_nonneg_left hh1 (by positivity)
        _ = _ := by ring
    have htmp : W*(2*b+(M : ℝ)*h*W) ≤ W*(2*b+(M : ℝ)*W) :=
      mul_le_mul_of_nonneg_left (by linarith) hW
    have hcross : 2*W*b ≤ W^2+b^2 := by nlinarith [sq_nonneg (W-b)]
    have hqB : b^2 ≤ q := by dsimp [q]; nlinarith [sq_nonneg a]
    have hscale := mul_le_mul_of_nonneg_left hw2 (by positivity : 0 ≤ 1+(M : ℝ))
    nlinarith
  have hterm : (M : ℝ)*(h*W)*(2*b+(M : ℝ)*(h*W)) ≤
      (M : ℝ)*(2*(M : ℝ)+3)*q := by
    have hinner : 0 ≤ W*(2*b+(M : ℝ)*h*W) := by positivity
    have hs : h*(W*(2*b+(M : ℝ)*h*W)) ≤ W*(2*b+(M : ℝ)*h*W) := by nlinarith
    have hsM := mul_le_mul_of_nonneg_left (hs.trans hfac) hM
    nlinarith
  have hd := verlet_energy_defect_abs f M hf hLip h z
  change _ ≤ (M : ℝ)/2*h^2*W^2 + h^2/8*((M : ℝ)*(|h| * W)*
    (2*b+(M : ℝ)*(|h| * W))) at hd
  rw [abs_of_nonneg hh] at hd
  have hfirst := mul_le_mul_of_nonneg_left hw2 (by positivity : 0 ≤ (M : ℝ)/2*h^2)
  have hsecond := mul_le_mul_of_nonneg_left hterm (by positivity : 0 ≤ h^2/8)
  change _ ≤ h^2*((M : ℝ)*(2*(M : ℝ)+11)/8)*q
  nlinarith

/-- The actual rejection probability has the same quadratic envelope. -/
theorem verlet_rejection_le_quadratic (f : E → ℝ) (M : ℝ≥0)
    (hf : Differentiable ℝ f) (hLip : LipschitzWith M (gradient f))
    (h : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1) (z : E×E) :
    1-verletAcceptance f h z ≤
      h^2*((M : ℝ)*(2*(M : ℝ)+11)/8)*(‖z.1‖^2+‖gradient f z.2‖^2) :=
  (verlet_rejection_le_energy_defect f h z).trans
    (verlet_energy_defect_quadratic f M hf hLip h hh hh1 z)

/-- Integrating the actual rejection bound requires only the displayed
quadratic phase moment, not an assumed numerical error estimate. -/
theorem verlet_rejection_integral_le (π : Measure (E×E)) [IsFiniteMeasure π]
    (f : E → ℝ) (M : ℝ≥0) (hf : Differentiable ℝ f)
    (hLip : LipschitzWith M (gradient f))
    (henv : Integrable (fun z : E×E ↦ ‖z.1‖^2+‖gradient f z.2‖^2) π)
    (h : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    (∫ z, 1-verletAcceptance f h z ∂π) ≤
      h^2*((M : ℝ)*(2*(M : ℝ)+11)/8)*
        (∫ z, ‖z.1‖^2+‖gradient f z.2‖^2 ∂π) := by
  have hmeas := verletAcceptance_measurable f hf.continuous.measurable hLip.continuous.measurable h
  have hi : Integrable (fun z ↦ 1-verletAcceptance f h z) π := by
    apply Integrable.of_bound (show Measurable (fun z ↦ 1-verletAcceptance f h z) from
      measurable_const.sub hmeas).aestronglyMeasurable 1
    filter_upwards [] with z
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (verletAcceptance_le_one f h z))]
    linarith [verletAcceptance_nonneg f h z]
  calc
    _ ≤ ∫ z, (h^2*((M : ℝ)*(2*(M : ℝ)+11)/8))*
        (‖z.1‖^2+‖gradient f z.2‖^2) ∂π :=
      integral_mono hi (henv.const_mul _) (fun z ↦
        verlet_rejection_le_quadratic f M hf hLip h hh hh1 z)
    _ = _ := integral_const_mul _ _

end KineticLangevin
