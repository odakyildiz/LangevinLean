import KineticLangevin.CoupledSegments
import KineticLangevin.IntegralCoupling

noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace KineticLangevin
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The selected local kinetic solution equals the actual shifted global solution driven by the same increment. -/
theorem kineticSegmentFlow_eq_shift (g : E → E) (L γ u : ℝ≥0) (hg : LipschitzWith L g)
    (Y : ℝ → E × E) (B W : ℝ → E) (hY : Continuous Y) (hW : Continuous W) (hW0 : W 0 = 0)
    (T a h : ℝ) (ha : 0 ≤ a) (hh : 0 ≤ h) (hah : a+h ≤ T)
    (heq : ∀ t ∈ Icc 0 T, Y t - Y 0 =
      -(∫ s in 0..t, kineticNegativeDrift g γ u (Y s)) + (B t,0))
    (hWseg : ∀ t ∈ Icc 0 h, W t = B (a+t)-B a)
    (t : ℝ) (ht : t ∈ Icc 0 h) :
    kineticSegmentFlow g L γ u hg h hh (Y a) W hW t = Y (a+t) := by
  let A := kineticSegmentFlow g L γ u hg h hh (Y a) W hW
  let Z := fun s => Y (a+s)
  have hs := kineticSegmentFlow_spec g L γ u hg h hh (Y a) W hW hW0
  have hAeq : ∀ s ∈ Icc 0 h, A s-A 0 =
      -(∫ r in 0..s, kineticNegativeDrift g γ u (A r)) + (W s,0) := by
    intro s hs'
    simpa only [A,hs.2.1] using hs.2.2 s hs'
  have hZeq : ∀ s ∈ Icc 0 h, Z s-Z 0 =
      -(∫ r in 0..s, kineticNegativeDrift g γ u (Z r)) + (W s,0) := by
    intro s hs'
    have he := additive_integral_segment (kineticNegativeDrift g γ u)
      (kineticNegativeDrift_lipschitz g L γ u hg).continuous Y (fun t => (B t,0)) hY T a h ha hh hah heq s hs'
    simpa only [Z,add_zero,Prod.mk_sub_mk,sub_self,← hWseg s hs'] using he
  have hstart : A 0 = Z 0 := by simpa only [A,Z,add_zero] using hs.2.1
  exact integral_solution_unique (kineticNegativeDrift g γ u) (γ+u*L+1)
    (kineticNegativeDrift_lipschitz g L γ u hg) A Z (fun s => (W s,0)) hs.1
    (hY.comp (continuous_const.add continuous_id)) h hAeq hZeq hstart t ht

/-- Stitching actual exact local solutions gives the global kinetic solution at every numerical grid point. -/
theorem kineticReferenceChain_eq_global (g : E → E) (L γ u : ℝ≥0) (hg : LipschitzWith L g)
    (h : ℝ) (hh : 0 ≤ h) (initial : E × E) (W : ℕ → ℝ → E)
    (hW : ∀ n, Continuous (W n)) (hW0 : ∀ n, W n 0 = 0)
    (Y : ℝ → E × E) (B : ℝ → E) (hY : Continuous Y) (T : ℝ)
    (hY0 : Y 0 = initial)
    (heq : ∀ t ∈ Icc 0 T, Y t-Y 0 =
      -(∫ s in 0..t, kineticNegativeDrift g γ u (Y s)) + (B t,0))
    (hsegments : ∀ k t, t ∈ Icc 0 h → W k t = B ((k : ℝ)*h+t)-B ((k : ℝ)*h))
    (n : ℕ) (hn : (n : ℝ)*h ≤ T) :
    kineticReferenceChain g L γ u hg h hh initial W hW n = Y ((n : ℝ)*h) := by
  induction n with
  | zero => simpa only [kineticReferenceChain,Nat.cast_zero,zero_mul] using hY0.symm
  | succ n ih =>
    have hnh : (n : ℝ)*h ≤ T := by
      simp only [Nat.cast_add,Nat.cast_one] at hn
      nlinarith
    have he := kineticSegmentFlow_eq_shift g L γ u hg Y B (W n) hY (hW n) (hW0 n)
      T ((n : ℝ)*h) h (mul_nonneg (Nat.cast_nonneg _) hh) hh
      (by simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul] using hn) heq
      (hsegments n) h ⟨hh,le_rfl⟩
    change kineticSegmentFlow g L γ u hg h hh
      (kineticReferenceChain g L γ u hg h hh initial W hW n) (W n) (hW n) h = _
    rw [ih hnh]
    simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul] using he

/-- Every continuous stitched reference segment is the corresponding restriction of the actual global solution. -/
theorem kineticReferenceSegment_eq_global (g : E → E) (L γ u : ℝ≥0) (hg : LipschitzWith L g)
    (h : ℝ) (hh : 0 ≤ h) (initial : E × E) (W : ℕ → ℝ → E)
    (hW : ∀ n, Continuous (W n)) (hW0 : ∀ n, W n 0 = 0)
    (Y : ℝ → E × E) (B : ℝ → E) (hY : Continuous Y) (T : ℝ)
    (hY0 : Y 0 = initial)
    (heq : ∀ t ∈ Icc 0 T, Y t-Y 0 =
      -(∫ s in 0..t, kineticNegativeDrift g γ u (Y s)) + (B t,0))
    (hsegments : ∀ k t, t ∈ Icc 0 h → W k t = B ((k : ℝ)*h+t)-B ((k : ℝ)*h))
    (n : ℕ) (hn : ((n : ℝ)+1)*h ≤ T) (t : ℝ) (ht : t ∈ Icc 0 h) :
    kineticReferenceSegment g L γ u hg h hh initial W hW n t = Y ((n : ℝ)*h+t) := by
  have hn0 : (n : ℝ)*h ≤ T := by nlinarith
  unfold kineticReferenceSegment
  rw [kineticReferenceChain_eq_global g L γ u hg h hh initial W hW hW0 Y B hY T hY0 heq hsegments n hn0]
  exact kineticSegmentFlow_eq_shift g L γ u hg Y B (W n) hY (hW n) (hW0 n)
    T ((n : ℝ)*h) h (mul_nonneg (Nat.cast_nonneg _) hh) hh (by nlinarith) heq (hsegments n) t ht

end KineticLangevin
