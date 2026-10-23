import KineticLangevin.Flow
import KineticLangevin.MildEquation
import KineticLangevin.Integrator

noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace KineticLangevin
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Restarting an actual additive integral solution produces the actual shifted-input equation. -/
theorem additive_integral_segment (g : E → E) (hg : Continuous g)
    (Y W : ℝ → E) (hY : Continuous Y) (T a h : ℝ)
    (ha : 0 ≤ a) (hh : 0 ≤ h) (hah : a+h ≤ T)
    (heq : ∀ t ∈ Icc 0 T, Y t - Y 0 = -(∫ s in 0..t, g (Y s)) + W t)
    (t : ℝ) (ht : t ∈ Icc 0 h) :
    Y (a+t) - Y a = -(∫ s in 0..t, g (Y (a+s))) + (W (a+t)-W a) := by
  have hat : a+t ∈ Icc 0 T := ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have haT : a ∈ Icc 0 T := ⟨ha,by linarith⟩
  have hc : Continuous (fun s => g (Y s)) := hg.comp hY
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a (a+t))
  have hs : (∫ s in 0..t, g (Y (a+s))) = ∫ s in a..(a+t), g (Y s) := by
    simpa only [add_zero] using intervalIntegral.integral_comp_add_left (fun s => g (Y s)) a (a := 0) (b := t)
  rw [hs]
  have hya := (sub_eq_iff_eq_add).mp (heq a haT)
  have hyat := (sub_eq_iff_eq_add).mp (heq (a+t) hat)
  rw [hyat,hya,← hi]
  abel

/-- Restrict a continuous velocity input to a compact solution horizon. -/
def compactVelocityInput (T : ℝ) (W : ℝ → E) (hW : Continuous W) : VelocityForcing (E := E) T :=
  ⟨fun t => W t,hW.comp continuous_subtype_val⟩

/-- On its horizon, the normalized compact input is the original input when it starts at zero. -/
theorem normalizedForcing_compactVelocityInput (T : ℝ) (hT : 0 ≤ T)
    (W : ℝ → E) (hW : Continuous W) (hW0 : W 0 = 0) (t : ℝ) (ht : t ∈ Icc 0 T) :
    normalizedForcing T hT (compactVelocityInput T W hW) t = W t := by
  change W (projIcc 0 T hT t) - W 0 = W t
  rw [projIcc_of_mem hT ht,hW0,sub_zero]

/-- The selected actual kinetic solution on one time interval with a raw continuous input. -/
def kineticSegmentFlow (g : E → E) (L γ u : ℝ≥0) (hg : LipschitzWith L g)
    (T : ℝ) (hT : 0 ≤ T) (initial : E × E) (W : ℝ → E) (hW : Continuous W) : ℝ → E × E :=
  kineticFlow g L γ u hg T hT initial (compactVelocityInput T W hW)

/-- The segment constructor supplies its genuine continuous integral equation. -/
theorem kineticSegmentFlow_spec (g : E → E) (L γ u : ℝ≥0) (hg : LipschitzWith L g)
    (T : ℝ) (hT : 0 ≤ T) (initial : E × E) (W : ℝ → E) (hW : Continuous W)
    (hW0 : W 0 = 0) :
    Continuous (kineticSegmentFlow g L γ u hg T hT initial W hW) ∧
      kineticSegmentFlow g L γ u hg T hT initial W hW 0 = initial ∧
      ∀ t ∈ Icc 0 T,
        kineticSegmentFlow g L γ u hg T hT initial W hW t - initial =
          -(∫ s in 0..t, kineticNegativeDrift g γ u
            (kineticSegmentFlow g L γ u hg T hT initial W hW s)) + (W t,0) := by
  have hs := kineticFlow_spec g L γ u hg T hT initial (compactVelocityInput T W hW)
  refine ⟨hs.1,hs.2.1,?_⟩
  intro t ht
  simpa only [kineticSegmentFlow, normalizedForcing_compactVelocityInput T hT W hW hW0 t ht] using hs.2.2 t ht

/-- Projecting the actual kinetic equation gives its force-velocity integral equation. -/
theorem kinetic_integral_velocity (g : E → E) (γ u T : ℝ) (Y : ℝ → E × E)
    (W : ℝ → E) (hY : Continuous Y) (hg : Continuous g)
    (heq : ∀ t ∈ Icc 0 T, Y t - Y 0 =
      -(∫ s in 0..t, kineticNegativeDrift g γ u (Y s)) + (W t,0))
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    (Y t).1 - (Y 0).1 = -(∫ s in 0..t, γ • (Y s).1 + u • g (Y s).2) + W t := by
  have hc : Continuous (fun s => kineticNegativeDrift g γ u (Y s)) := by
    unfold kineticNegativeDrift
    exact ((hY.fst.const_smul γ).add ((hg.comp hY.snd).const_smul u)).prodMk hY.fst.neg
  have hp := congrArg (ContinuousLinearMap.fst ℝ E E) (heq t ht)
  rw [map_sub,map_add,map_neg,← ContinuousLinearMap.intervalIntegral_comp_comm _ (hc.intervalIntegrable _ _)] at hp
  exact hp

/-- Position is the actual time primitive of velocity; there is no direct positional Brownian input. -/
theorem kinetic_integral_kinematic (g : E → E) (γ u T : ℝ) (Y : ℝ → E × E)
    (W : ℝ → E) (hY : Continuous Y) (hg : Continuous g)
    (heq : ∀ t ∈ Icc 0 T, Y t - Y 0 =
      -(∫ s in 0..t, kineticNegativeDrift g γ u (Y s)) + (W t,0))
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    (Y t).2 - (Y 0).2 = ∫ s in 0..t, (Y s).1 := by
  have hc : Continuous (fun s => kineticNegativeDrift g γ u (Y s)) := by
    unfold kineticNegativeDrift
    exact ((hY.fst.const_smul γ).add ((hg.comp hY.snd).const_smul u)).prodMk hY.fst.neg
  have hp := congrArg (ContinuousLinearMap.snd ℝ E E) (heq t ht)
  rw [map_sub,map_add,map_neg,← ContinuousLinearMap.intervalIntegral_comp_comm _ (hc.intervalIntegrable _ _)] at hp
  change (Y t).2-(Y 0).2 = -(∫ s in 0..t, -(Y s).1) + 0 at hp
  simpa only [intervalIntegral.integral_neg,neg_neg,add_zero] using hp

/-- The actual kinetic integral equation implies the mild force formula with the same filtered input. -/
theorem kinetic_integral_mild (g : E → E) (γ u T : ℝ) (hT : 0 ≤ T)
    (Y : ℝ → E × E) (W B : ℝ → E) (hY : Continuous Y) (hg : Continuous g)
    (hB : Continuous B)
    (heq : ∀ t ∈ Icc 0 T, Y t - Y 0 =
      -(∫ s in 0..t, kineticNegativeDrift g γ u (Y s)) + (W t,0))
    (hnoise : ∀ t ∈ Icc 0 T, B t = W t - γ • ∫ s in 0..t, B s) :
    (Y T).1 = psi γ 0 T • (Y 0).1 -
      (∫ s in 0..T, Real.exp (-γ*(T-s)) • (u • g (Y s).2)) + B T := by
  exact damped_integral_eq_mild γ T hT (fun s => (Y s).1) (fun s => u • g (Y s).2) W B
    hY.fst ((hg.comp hY.snd).const_smul u) hB
    (kinetic_integral_velocity g γ u T Y W hY hg heq) hnoise

/-- Stitch exact segment endpoints to construct the reference chain. -/
def kineticReferenceChain (g : E → E) (L γ u : ℝ≥0) (hg : LipschitzWith L g)
    (h : ℝ) (hh : 0 ≤ h) (initial : E × E) (W : ℕ → ℝ → E)
    (hW : ∀ n, Continuous (W n)) : ℕ → E × E
  | 0 => initial
  | n+1 => kineticSegmentFlow g L γ u hg h hh
      (kineticReferenceChain g L γ u hg h hh initial W hW n) (W n) (hW n) h

/-- The continuous reference segment begins at its actual preceding endpoint. -/
def kineticReferenceSegment (g : E → E) (L γ u : ℝ≥0) (hg : LipschitzWith L g)
    (h : ℝ) (hh : 0 ≤ h) (initial : E × E) (W : ℕ → ℝ → E)
    (hW : ∀ n, Continuous (W n)) (n : ℕ) : ℝ → E × E :=
  kineticSegmentFlow g L γ u hg h hh (kineticReferenceChain g L γ u hg h hh initial W hW n) (W n) (hW n)

/-- The implemented frozen-force method uses the constructed filtered velocity input and its position primitive. -/
def exponentialInputChain (g : E → E) (γ h : ℝ) (initial : E × E)
    (B : ℕ → ℝ → E) : ℕ → E × E
  | 0 => initial
  | n+1 => exponentialStep g γ h (exponentialInputChain g γ h initial B n)
      (B n h,∫ s in 0..h, B n s)

/-- The auxiliary exact segment restarts from the actual numerical state with the same Brownian input. -/
def kineticAuxiliarySegment (g : E → E) (L γ : ℝ≥0) (hg : LipschitzWith L g)
    (h : ℝ) (hh : 0 ≤ h) (initial : E × E) (W B : ℕ → ℝ → E)
    (hW : ∀ n, Continuous (W n)) (n : ℕ) : ℝ → E × E :=
  kineticSegmentFlow g L γ 1 hg h hh (exponentialInputChain g γ h initial B n) (W n) (hW n)

/-- All exact reference segments satisfy continuity, initialization, endpoint matching and the actual integral equation. -/
theorem kineticReferenceSegment_spec (g : E → E) (L γ u : ℝ≥0) (hg : LipschitzWith L g)
    (h : ℝ) (hh : 0 ≤ h) (initial : E × E) (W : ℕ → ℝ → E)
    (hW : ∀ n, Continuous (W n)) (hW0 : ∀ n, W n 0 = 0) (n : ℕ) :
    Continuous (kineticReferenceSegment g L γ u hg h hh initial W hW n) ∧
      kineticReferenceSegment g L γ u hg h hh initial W hW n 0 =
        kineticReferenceChain g L γ u hg h hh initial W hW n ∧
      kineticReferenceSegment g L γ u hg h hh initial W hW n h =
        kineticReferenceChain g L γ u hg h hh initial W hW (n+1) ∧
      ∀ t ∈ Icc 0 h,
        kineticReferenceSegment g L γ u hg h hh initial W hW n t -
          kineticReferenceSegment g L γ u hg h hh initial W hW n 0 =
          -(∫ s in 0..t, kineticNegativeDrift g γ u
            (kineticReferenceSegment g L γ u hg h hh initial W hW n s)) + (W n t,0) := by
  have hs := kineticSegmentFlow_spec g L γ u hg h hh
    (kineticReferenceChain g L γ u hg h hh initial W hW n) (W n) (hW n) (hW0 n)
  refine ⟨hs.1,hs.2.1,rfl,?_⟩
  intro t ht
  simpa only [kineticReferenceSegment,hs.2.1] using hs.2.2 t ht


/-- The auxiliary constructor supplies its exact initial state and common-input equation. -/
theorem kineticAuxiliarySegment_spec (g : E → E) (L γ : ℝ≥0) (hg : LipschitzWith L g)
    (h : ℝ) (hh : 0 ≤ h) (initial : E × E) (W B : ℕ → ℝ → E)
    (hW : ∀ n, Continuous (W n)) (hW0 : ∀ n, W n 0 = 0) (n : ℕ) :
    Continuous (kineticAuxiliarySegment g L γ hg h hh initial W B hW n) ∧
      kineticAuxiliarySegment g L γ hg h hh initial W B hW n 0 =
        exponentialInputChain g γ h initial B n ∧
      ∀ t ∈ Icc 0 h,
        kineticAuxiliarySegment g L γ hg h hh initial W B hW n t -
          kineticAuxiliarySegment g L γ hg h hh initial W B hW n 0 =
          -(∫ s in 0..t, kineticNegativeDrift g γ 1
            (kineticAuxiliarySegment g L γ hg h hh initial W B hW n s)) + (W n t,0) := by
  have hs := kineticSegmentFlow_spec g L γ 1 hg h hh
    (exponentialInputChain g γ h initial B n) (W n) (hW n) (hW0 n)
  refine ⟨hs.1,hs.2.1,?_⟩
  intro t ht
  simpa only [kineticAuxiliarySegment,hs.2.1,NNReal.coe_one] using hs.2.2 t ht

/-- Every actual auxiliary segment has the kinematic identity required by the local-error proof. -/
theorem kineticAuxiliarySegment_kinematic (g : E → E) (L γ : ℝ≥0) (hg : LipschitzWith L g)
    (h : ℝ) (hh : 0 ≤ h) (initial : E × E) (W B : ℕ → ℝ → E)
    (hW : ∀ n, Continuous (W n)) (hW0 : ∀ n, W n 0 = 0) (n : ℕ)
    (t : ℝ) (ht : t ∈ Icc 0 h) :
    (kineticAuxiliarySegment g L γ hg h hh initial W B hW n t).2 -
      (kineticAuxiliarySegment g L γ hg h hh initial W B hW n 0).2 =
      ∫ s in 0..t, (kineticAuxiliarySegment g L γ hg h hh initial W B hW n s).1 := by
  have hs := kineticAuxiliarySegment_spec g L γ hg h hh initial W B hW hW0 n
  exact kinetic_integral_kinematic g γ 1 h _ (W n) hs.1 hg.continuous hs.2.2 t ht

/-- The required mild identity is derived for the constructed auxiliary path, not supplied as a premise. -/
theorem kineticAuxiliarySegment_mild (g : E → E) (L γ : ℝ≥0) (hg : LipschitzWith L g)
    (h : ℝ) (hh : 0 ≤ h) (initial : E × E) (W B : ℕ → ℝ → E)
    (hW : ∀ n, Continuous (W n)) (hW0 : ∀ n, W n 0 = 0)
    (hB : ∀ n, Continuous (B n))
    (hnoise : ∀ n t, t ∈ Icc 0 h → B n t = W n t - (γ : ℝ) • ∫ s in 0..t, B n s)
    (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 h) :
    (kineticAuxiliarySegment g L γ hg h hh initial W B hW n t).1 =
      psi γ 0 t • (kineticAuxiliarySegment g L γ hg h hh initial W B hW n 0).1 -
      (∫ s in 0..t, Real.exp (-(γ : ℝ)*(t-s)) •
        g (kineticAuxiliarySegment g L γ hg h hh initial W B hW n s).2) + B n t := by
  have hs := kineticAuxiliarySegment_spec g L γ hg h hh initial W B hW hW0 n
  have heq : ∀ s ∈ Icc 0 t,
      kineticAuxiliarySegment g L γ hg h hh initial W B hW n s -
        kineticAuxiliarySegment g L γ hg h hh initial W B hW n 0 =
      -(∫ r in 0..s, kineticNegativeDrift g γ 1
        (kineticAuxiliarySegment g L γ hg h hh initial W B hW n r)) + (W n s,0) := by
    intro s hs'
    exact hs.2.2 s ⟨hs'.1,hs'.2.trans ht.2⟩
  have hb : ∀ s ∈ Icc 0 t, B n s = W n s - (γ : ℝ) • ∫ r in 0..s, B n r := by
    intro s hs'
    exact hnoise n s ⟨hs'.1,hs'.2.trans ht.2⟩
  simpa only [one_smul] using kinetic_integral_mild g γ 1 t ht.1
    (kineticAuxiliarySegment g L γ hg h hh initial W B hW n) (W n) (B n)
    hs.1 hg.continuous (hB n) heq hb

/-- At every step the constructed numerical chain has exactly the exponential-integrator update. -/
theorem exponentialInputChain_succ (g : E → E) (γ h : ℝ) (initial : E × E)
    (B : ℕ → ℝ → E) (n : ℕ) :
    exponentialInputChain g γ h initial B (n+1) =
      exponentialStep g γ h (exponentialInputChain g γ h initial B n)
        (B n h,∫ s in 0..h, B n s) := rfl

end KineticLangevin
