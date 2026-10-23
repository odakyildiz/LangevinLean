import KineticLangevin.CanonicalGlobalSegments
import KineticLangevin.LpConvergence
import UnadjustedLangevin.InitialCoupling

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace KineticLangevin.CanonicalCoupling
open BrownianConvolution
variable {d : ℕ} {μ π : Measure (H d)} [IsProbabilityMeasure μ]

/-- The actual KLMC position law from an independent Gaussian-velocity and canonical Brownian source. -/
def klmcLaw (f : H d → ℝ) (γ : ℝ) (h : ℝ≥0) (μ : Measure (H d)) (n : ℕ) : Measure (H d) :=
  productKLMCLaw (canonicalSourceProbability d) f γ h μ Prod.fst
    (fun k p => canonicalKLMCInnovation d γ h k p.2) n

/-- The constructed numerical chain has one actual output law for all initial transport couplings. -/
theorem numericalChain_outputLaw (c : ULA.Coupling μ π) (hc : ULA.couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (id : H d → H d) 2 π) (f : H d → ℝ) (M : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    (probability c).map (numericalChain c hc hπ f M hLip γ h n).2 = klmcLaw f γ h μ n := by
  have hn : innovation c γ h = extensionInnovation (canonicalSourceProbability d) c
      (fun k p => canonicalKLMCInnovation d γ h k p.2)
      (fun k => (canonicalSourceInnovation_memLp d γ h k).1)
      (fun k => (canonicalSourceInnovation_memLp d γ h k).2) :=
    funext (innovation_eq_extensionInnovation c γ h)
  unfold numericalChain numericalInitial initialVelocity
  rw [hn]
  exact product_klmcChain_outputLaw (canonicalSourceProbability d) c hc hπ f M hLip γ h
    Prod.fst (canonicalSourceVelocity_memLp d) (fun k p => canonicalKLMCInnovation d γ h k p.2)
    (fun k => (canonicalSourceInnovation_memLp d γ h k).1)
    (fun k => (canonicalSourceInnovation_memLp d γ h k).2) n

/-- State the sole remaining probabilistic reference-law property on the actual full constructed flow. -/
def GlobalReferenceStationary (c : ULA.Coupling μ π) (hπ : MemLp (id : H d → H d) 2 π)
    (f : H d → ℝ) (M γ : ℝ≥0) (hLip : LipschitzWith M (gradient f)) : Prop :=
  ∀ T (hT : 0 ≤ T) t, t ∈ Icc 0 T →
    HasLaw (fun p => lpPhaseCoe (probability c) (globalReferenceFlow c hπ f M γ hLip T hT t) p)
      ((stdGaussian (H d)).prod π) (probability c)

/-- A stationary actual global phase law supplies the stationary grid position law. -/
theorem referenceChain_position_law (c : ULA.Coupling μ π)
    (hπ : MemLp (id : H d → H d) 2 π) (f : H d → ℝ) (M γ : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (h : ℝ≥0)
    (hglobal : GlobalReferenceStationary c hπ f M γ hLip) (n : ℕ) :
    (probability c).map (referenceChain c hπ f M γ hLip h n).2 = π := by
  haveI : IsProbabilityMeasure π := by
    have hl : HasLaw (fun p : Sample d => p.1.2) π (probability c) :=
      ⟨(measurable_fst.snd).aemeasurable,ULA.initialExtension_reference c (canonicalSourceProbability d)⟩
    exact hl.isProbabilityMeasure_iff.mp inferInstance
  let T : ℝ := (n : ℝ)*(h : ℝ)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  rw [referenceChain_eq_globalReferenceFlow c hπ f M γ hLip h T hT n le_rfl]
  have hl := hglobal T hT T ⟨hT,le_rfl⟩
  have hp : HasLaw Prod.snd π ((stdGaussian (H d)).prod π) := measurePreserving_snd.hasLaw
  exact (hp.comp hl).map_eq

/-- The stationary full phase law also supplies Gaussian velocities at every intermediate reference time. -/
theorem referenceSegment_velocity_law (c : ULA.Coupling μ π)
    (hπ : MemLp (id : H d → H d) 2 π) (f : H d → ℝ) (M γ : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (h : ℝ≥0)
    (hglobal : GlobalReferenceStationary c hπ f M γ hLip)
    (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 (h : ℝ)) :
    HasLaw ((referenceSegment c hπ f M γ hLip h n t).1) (stdGaussian (H d)) (probability c) := by
  have hπprob : IsProbabilityMeasure π := by
    have hxl : HasLaw (fun p : Sample d => p.1.2) π (probability c) :=
      ⟨(measurable_fst.snd).aemeasurable,ULA.initialExtension_reference c (canonicalSourceProbability d)⟩
    exact hxl.isProbabilityMeasure_iff.mp inferInstance
  let T : ℝ := ((n : ℝ)+1)*(h : ℝ)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have htime : (n : ℝ)*(h : ℝ)+t ∈ Icc 0 T := by
    constructor
    · exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) h.coe_nonneg) ht.1
    · dsimp [T]; nlinarith [ht.2]
  rw [referenceSegment_eq_globalReferenceFlow c hπ f M γ hLip h T hT n le_rfl t ht]
  have hp : HasLaw Prod.fst (stdGaussian (H d)) ((stdGaussian (H d)).prod π) :=
    measurePreserving_fst.hasLaw
  exact hp.comp (hglobal T hT _ htime)

/-- The initial L² position discrepancy is the actual cost of the supplied transport plan. -/
theorem initial_position_cost (c : ULA.Coupling μ π) (hc : ULA.couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (id : H d → H d) 2 π) (f : H d → ℝ) (M γ : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (h : ℝ≥0) :
    ‖(numericalChain c hc hπ f M hLip γ h 0).2-(referenceChain c hπ f M γ hLip h 0).2‖ =
      (ULA.couplingCost c.joint).toReal := by
  exact ULA.initialExtension_lp_cost c (canonicalSourceProbability d) hc hπ

/-- The first-order KLMC bound for one actual initial coupling, conditional only on stationarity of the actual full reference flow. -/
theorem klmc_bound_of_globalStationarity (c : ULA.Coupling μ π)
    (hc : ULA.couplingCost c.joint ≠ ⊤) (hπ : MemLp (id : H d → H d) 2 π)
    (f : H d → ℝ) (m : ℝ) (M γ : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ)) (hm : 0 < m)
    (hγ : 0 < (γ : ℝ)) (hfriction : m+(M : ℝ) ≤ (γ : ℝ)^2)
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (hstep : 4*(γ : ℝ)*(M : ℝ)*(h : ℝ) ≤ m)
    (hglobal : GlobalReferenceStationary c hπ f M γ hLip) (n : ℕ) :
    ULA.wasserstein2Real (klmcLaw f γ h μ n) π ≤
      Real.sqrt 2 * (1-3*m*(h : ℝ)/(4*(γ : ℝ)))^n * (ULA.couplingCost c.joint).toReal +
        (M : ℝ)*(h : ℝ)*Real.sqrt (2*(d : ℝ))/m := by
  rcases segments_spec c hc hπ f M γ hLip h with
    ⟨hA,hZ,hB,hA0,hZ0,hZh,hupdate,heA,heZ,hmild,hkin,hvelocity⟩
  have hb := lp_klmc_reference_wasserstein_bound (probability c) f m M γ hdiff hsc hLip hmM hm
    hγ hfriction h hh hstep (numericalChain c hc hπ f M hLip γ h)
    (referenceChain c hπ f M γ hLip h) (auxiliarySegment c hc hπ f M γ hLip h)
    (referenceSegment c hπ f M γ hLip h) (fun k t => (input c γ h k t,0)) (filtered c γ h)
    hA hZ hB hA0 hZ0 hZh hupdate heA heZ hmild hkin
    (referenceSegment_velocity_law c hπ f M γ hLip h hglobal)
    π (referenceChain_position_law c hπ f M γ hLip h hglobal) hvelocity n
  rw [numericalChain_outputLaw c hc hπ f M hLip γ h n,initial_position_cost c hc hπ f M γ hLip h] at hb
  simpa only [Fintype.card_fin] using hb

/-- The output has finite transport distance, proved from actual square-integrable coupled states. -/
theorem klmcLaw_wasserstein2_ne_top (hπ : MemLp (id : H d → H d) 2 π)
    (f : H d → ℝ) (M γ : ℝ≥0) (hLip : LipschitzWith M (gradient f)) (h : ℝ≥0)
    (hfinite : ULA.wasserstein2 μ π ≠ ⊤)
    (hglobal : ∀ c : ULA.Coupling μ π, GlobalReferenceStationary c hπ f M γ hLip) (n : ℕ) :
    ULA.wasserstein2 (klmcLaw f γ h μ n) π ≠ ⊤ := by
  obtain ⟨c,hc⟩ := ULA.exists_finiteCost_coupling μ π hfinite
  have hb := ULA.wasserstein2_le_Lp_cost (probability c)
    (numericalChain c (ne_of_lt hc) hπ f M hLip γ h n).2
    (referenceChain c hπ f M γ hLip h n).2
  rw [numericalChain_outputLaw c (ne_of_lt hc) hπ f M hLip γ h n,
    referenceChain_position_law c hπ f M γ hLip h (hglobal c) n] at hb
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb

/-- Taking the genuine transport infimum gives the paper's KLMC bound with the true initial Wasserstein distance. -/
theorem klmc_wasserstein_bound_of_globalStationarity
    (hπ : MemLp (id : H d → H d) 2 π) (f : H d → ℝ) (m : ℝ) (M γ : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ)) (hm : 0 < m)
    (hγ : 0 < (γ : ℝ)) (hfriction : m+(M : ℝ) ≤ (γ : ℝ)^2)
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (hstep : 4*(γ : ℝ)*(M : ℝ)*(h : ℝ) ≤ m)
    (hfinite : ULA.wasserstein2 μ π ≠ ⊤)
    (hglobal : ∀ c : ULA.Coupling μ π, GlobalReferenceStationary c hπ f M γ hLip) (n : ℕ) :
    ULA.wasserstein2Real (klmcLaw f γ h μ n) π ≤
      Real.sqrt 2 * (1-3*m*(h : ℝ)/(4*(γ : ℝ)))^n * ULA.wasserstein2Real μ π +
        (M : ℝ)*(h : ℝ)*Real.sqrt (2*(d : ℝ))/m := by
  obtain ⟨hc,hs⟩ := kinetic_scalar_conditions m M γ h hm hmM hγ hfriction hh.le hstep
  have hcoeff := firstOrder_coefficient_bound (m/(γ : ℝ)) M h (div_nonneg hm.le hγ.le)
    M.coe_nonneg h.coe_nonneg hc hs
  have hq : 0 ≤ 1-3*m*(h : ℝ)/(4*(γ : ℝ)) := by
    have he := Real.exp_pos (-(m/(γ : ℝ))*(h : ℝ))
    have hp : 0 ≤ (3/4 : ℝ)*(M : ℝ)*(h : ℝ)^2 := by positivity
    have hid : 1-3*m*(h : ℝ)/(4*(γ : ℝ)) = 1-(3/4 : ℝ)*(m/(γ : ℝ))*(h : ℝ) := by ring
    rw [hid]
    linarith
  let a : ℝ≥0 := ⟨Real.sqrt 2 * (1-3*m*(h : ℝ)/(4*(γ : ℝ)))^n,by positivity⟩
  let b : ℝ≥0 := ⟨(M : ℝ)*(h : ℝ)*Real.sqrt (2*(d : ℝ))/m,by positivity⟩
  apply ULA.wasserstein2_affine_bound_real_of_finite_couplings μ π (klmcLaw f γ h μ n) π a b hfinite
    (klmcLaw_wasserstein2_ne_top hπ f M γ hLip h hfinite hglobal n)
  intro c hc
  exact klmc_bound_of_globalStationarity c hc hπ f m M γ hdiff hsc hLip hmM hm hγ hfriction h hh hstep (hglobal c) n

end KineticLangevin.CanonicalCoupling
