import LatentDiffusion.RegularTransport

set_option linter.style.header false

/-! # Actual regular Wasserstein geodesics

The distance is always the infimum over genuine quadratic couplings.  The
regular domain below requests finite-cost optimal Monge maps between its
positive smooth laws; it never postulates a geodesic or a distance formula.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped ENNReal NNReal

namespace LatentDiffusion.RegularTransport

variable {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [CompleteSpace Z] [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {μ ν : Measure Z}

/-- The displacement laws of an actual optimal map. -/
def optimalInterpolation (T : OptimalMap μ ν) (s : ℝ) : Measure Z :=
  μ.map (interpolate T.transport s)

@[simp] theorem optimalInterpolation_zero (T : OptimalMap μ ν) :
    optimalInterpolation T 0 = μ := by simp [optimalInterpolation]

@[simp] theorem optimalInterpolation_one (T : OptimalMap μ ν) :
    optimalInterpolation T 1 = ν := by simp [optimalInterpolation, T.pushes]

theorem interpolation_difference (T : Z → Z) (s t : ℝ) (z : Z) :
    interpolate T s z - interpolate T t z = (t - s) • (z - T z) := by
  unfold interpolate
  module

/-- The actual random-variable coupling of two interpolated laws bounds their
Wasserstein distance. No optimality of the intermediate coupling is assumed. -/
theorem interpolation_distance_le (T : OptimalMap μ ν) (s t : ℝ) :
    ULA.wasserstein2Real (optimalInterpolation T s) (optimalInterpolation T t) ≤
      |t - s| * ULA.wasserstein2Real μ ν := by
  have hmem : MemLp (fun z ↦ interpolate T.transport s z - interpolate T.transport t z) 2 μ := by
    convert T.finite_cost.const_smul (t - s) using 1
    funext z
    exact interpolation_difference _ _ _ _
  have h := ULA.wasserstein2_le_random_cost_real μ
    (interpolate T.transport s) (interpolate T.transport t)
    (interpolate_measurable _ T.measurable_transport s)
    (interpolate_measurable _ T.measurable_transport t) hmem
  rw [show (fun z ↦ interpolate T.transport s z - interpolate T.transport t z) =
    (t - s) • (fun z ↦ z - T.transport z) by
      funext z
      exact interpolation_difference _ _ _ _] at h
  rw [eLpNorm_const_smul, ENNReal.toReal_mul] at h
  simpa only [optimalInterpolation, ULA.wasserstein2Real, T.wasserstein_eq_cost,
    enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm, Real.norm_eq_abs] using h

/-- Ordered-time formulation of constant-speed geodesicity in the genuine
Wasserstein distance. It includes both endpoints and all subintervals. -/
def IsConstantSpeedGeodesic (q : ℝ → Measure Z) : Prop :=
  ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, s ≤ t →
    ULA.wasserstein2Real (q s) (q t) = (t - s) * ULA.wasserstein2Real (q 0) (q 1)

/-- Smooth optimal-map existence at intermediate densities is the additional
transport regularity required to glue couplings inside the regular domain. -/
def OptimalMapRegularity (q : ℝ → Measure Z) : Prop :=
  ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, Nonempty (OptimalMap (q s) (q t))

/-- The classical smooth Brenier regularity certificate. The potential is
convex and its actual Fréchet gradient realizes the actual optimal map. -/
structure RegularBrenierMap (μ ν : Measure Z) extends OptimalMap μ ν where
  potential : Z → ℝ
  potential_convex : ConvexOn ℝ univ potential
  hasGradientAt : ∀ z, HasGradientAt potential (transport z) z

/-- Linear displacement by a regular optimal map is an actual constant-speed
Wasserstein geodesic. Constant speed follows from constructed couplings and
the proved optimal-map triangle inequality. -/
theorem optimalInterpolation_geodesic (T : OptimalMap μ ν)
    (hregular : OptimalMapRegularity (optimalInterpolation T)) :
    IsConstantSpeedGeodesic (optimalInterpolation T) := by
  intro s hs t ht hst
  have hupper := interpolation_distance_le T s t
  rw [abs_of_nonneg (sub_nonneg.mpr hst)] at hupper
  simp only [optimalInterpolation_zero, optimalInterpolation_one]
  apply le_antisymm hupper
  obtain ⟨A⟩ := hregular 0 (by constructor <;> norm_num) s hs
  obtain ⟨B⟩ := hregular s hs 1 (by constructor <;> norm_num)
  obtain ⟨C⟩ := hregular s hs t ht
  obtain ⟨D⟩ := hregular t ht 1 (by constructor <;> norm_num)
  have htriangle1 := A.wassersteinReal_triangle B
  have htriangle2 := C.wassersteinReal_triangle D
  simp only [optimalInterpolation_zero, optimalInterpolation_one] at htriangle1 htriangle2
  have hleft := interpolation_distance_le T 0 s
  have hright := interpolation_distance_le T t 1
  simp only [sub_zero, abs_of_nonneg hs.1, optimalInterpolation_zero,
    optimalInterpolation_one, abs_of_nonneg (sub_nonneg.mpr ht.2)] at hleft hright
  nlinarith

/-- Equality in the Hilbert triangle geometry forces the affine point. This
is applied to the actual L² transport displacement in the converse theorem. -/
theorem affine_of_scaled_distances {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a b : H) (s D : ℝ) (ha : ‖a‖ = s * D) (hb : ‖b‖ = D)
    (hba : ‖b - a‖ = (1 - s) * D) : a = s • b := by
  have hsq : ‖a - s • b‖ ^ 2 = 0 := by
    have hba' := norm_sub_sq_real b a
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_right, ha, hb]
    rw [hba, ha, hb] at hba'
    have hi : inner ℝ a b = s * D ^ 2 := by
      nlinarith only [hba', real_inner_comm a b]
    rw [hi]
    ring
  exact sub_eq_zero.mp (norm_eq_zero.mp ((sq_eq_zero_iff).mp hsq))

namespace OptimalMap

/-- Gluing two optimal Monge maps across a geodesic split gives another
endpoint-optimal map. This is a construction, not an optimality assumption on
the composed coupling. -/
def compose_of_additive_distance {η : Measure Z}
    (T : OptimalMap μ ν) (A : OptimalMap μ η) (B : OptimalMap η ν)
    (hadd : ULA.wasserstein2Real μ ν =
      ULA.wasserstein2Real μ η + ULA.wasserstein2Real η ν) : OptimalMap μ ν := by
  have hB : MemLp (fun z ↦ A.transport z - B.transport (A.transport z)) 2 μ := by
    have hbmap : MemLp (fun z ↦ z - B.transport z) 2 (μ.map A.transport) := by
      simpa only [A.pushes] using B.finite_cost
    exact hbmap.comp_of_map A.measurable_transport.aemeasurable
  have hcomp : MemLp (fun z ↦ z - B.transport (A.transport z)) 2 μ := by
    convert A.finite_cost.add hB using 1
    funext z
    simp
  have hcost : eLpNorm (fun z ↦ z - B.transport (A.transport z)) 2 μ ≤
      eLpNorm (fun z ↦ z - A.transport z) 2 μ+
        eLpNorm (fun z ↦ z - B.transport z) 2 η := by
    calc
      _ = eLpNorm ((fun z ↦ z - A.transport z)+
          (fun z ↦ A.transport z - B.transport (A.transport z))) 2 μ := by
        congr 1
        funext z
        simp
      _ ≤ _ := eLpNorm_add_le (by norm_num)
      _ = _ := by
        congr 1
        have hm := eLpNorm_map_measure (μ := μ) (p := 2)
          (g := fun z ↦ z - B.transport z)
          (measurable_id.sub B.measurable_transport).aestronglyMeasurable
          A.measurable_transport.aemeasurable
        simpa only [A.pushes, Function.comp_def] using hm.symm
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨A.finite_cost.eLpNorm_ne_top, B.finite_cost.eLpNorm_ne_top⟩) hcost
  rw [ENNReal.toReal_add A.finite_cost.eLpNorm_ne_top B.finite_cost.eLpNorm_ne_top] at hreal
  have hbound : eLpNorm (fun z ↦ z - B.transport (A.transport z)) 2 μ ≤
      ULA.wasserstein2 μ ν := by
    apply (ENNReal.toReal_le_toReal hcomp.eLpNorm_ne_top T.wasserstein_ne_top).mp
    change (eLpNorm (fun z ↦ z - B.transport (A.transport z)) 2 μ).toReal ≤
      ULA.wasserstein2Real μ ν
    rw [hadd]
    simpa only [ULA.wasserstein2Real, A.wasserstein_eq_cost, B.wasserstein_eq_cost] using hreal
  exact {
    transport := B.transport ∘ A.transport
    measurable_transport := B.measurable_transport.comp A.measurable_transport
    pushes := by
      rw [← Measure.map_map B.measurable_transport A.measurable_transport,
        A.pushes, B.pushes]
    finite_cost := hcomp
    minimal := fun c ↦ hbound.trans (ULA.wasserstein2_le_couplingCost c) }

end OptimalMap

/-- On the regular optimal-map domain, every constant-speed geodesic is
exactly the displacement interpolation of the endpoint Brenier map. Endpoint
uniqueness is stated for actual optimal maps, and no intermediate affine or
geodesic representation is assumed. -/
theorem geodesic_eq_optimalInterpolation
    (q : ℝ → Measure Z) (T : OptimalMap (q 0) (q 1))
    (hunique : ∀ S : OptimalMap (q 0) (q 1), S.transport =ᵐ[q 0] T.transport)
    (hregular : OptimalMapRegularity q) (hgeodesic : IsConstantSpeedGeodesic q)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    q s = optimalInterpolation T s := by
  obtain ⟨A⟩ := hregular 0 (by constructor <;> norm_num) s hs
  obtain ⟨B⟩ := hregular s hs 1 (by constructor <;> norm_num)
  let D := ULA.wasserstein2Real (q 0) (q 1)
  have hA : ULA.wasserstein2Real (q 0) (q s) = s * D := by
    simpa [D] using hgeodesic 0 (by constructor <;> norm_num) s hs hs.1
  have hB : ULA.wasserstein2Real (q s) (q 1) = (1 - s) * D :=
    hgeodesic s hs 1 (by constructor <;> norm_num) hs.2
  have hadd : ULA.wasserstein2Real (q 0) (q 1) =
      ULA.wasserstein2Real (q 0) (q s) + ULA.wasserstein2Real (q s) (q 1) := by
    rw [hA, hB]
    dsimp [D]
    ring
  let C := T.compose_of_additive_distance A B hadd
  have hC : ∀ᵐ z ∂q 0, B.transport (A.transport z) = T.transport z := hunique C
  let a := A.finite_cost.toLp (fun z ↦ z - A.transport z)
  let b := T.finite_cost.toLp (fun z ↦ z - T.transport z)
  have ha : ‖a‖ = s * D := by
    rw [Lp.norm_toLp]
    simpa only [ULA.wasserstein2Real, A.wasserstein_eq_cost] using hA
  have hb : ‖b‖ = D := by
    rw [Lp.norm_toLp]
    exact (congrArg ENNReal.toReal T.wasserstein_eq_cost).symm
  have hba : ‖b - a‖ = (1 - s) * D := by
    have heq : (fun z ↦ (b - a) z) =ᵐ[q 0]
        (fun z ↦ A.transport z - B.transport (A.transport z)) := by
      filter_upwards [Lp.coeFn_sub b a, A.finite_cost.coeFn_toLp,
        T.finite_cost.coeFn_toLp, hC] with z hsub ha hb hc
      rw [hsub]
      simp only [Pi.sub_apply]
      change a z = z - A.transport z at ha
      change b z = z - T.transport z at hb
      rw [ha, hb, ← hc]
      simp
    rw [Lp.norm_def, eLpNorm_congr_ae heq]
    have hm := eLpNorm_map_measure (μ := q 0) (p := 2)
      (g := fun z ↦ z - B.transport z)
      (measurable_id.sub B.measurable_transport).aestronglyMeasurable
      A.measurable_transport.aemeasurable
    have hcost : eLpNorm (fun z ↦ A.transport z - B.transport (A.transport z)) 2 (q 0) =
        eLpNorm (fun z ↦ z - B.transport z) 2 (q s) := by
      simpa only [A.pushes, Function.comp_def] using hm.symm
    rw [hcost]
    rw [ULA.wasserstein2Real, B.wasserstein_eq_cost] at hB
    exact hB
  have hab := affine_of_scaled_distances a b s D ha hb hba
  have hmap : A.transport =ᵐ[q 0] interpolate T.transport s := by
    have hLp : (fun z ↦ a z) =ᵐ[q 0] (fun z ↦ (s • b) z) := by
      rw [hab]
    filter_upwards [hLp, A.finite_cost.coeFn_toLp, T.finite_cost.coeFn_toLp,
      Lp.coeFn_smul s b] with z hab ha hb hsmul
    rw [hsmul] at hab
    simp only [Pi.smul_apply] at hab
    change a z = z - A.transport z at ha
    change b z = z - T.transport z at hb
    rw [ha, hb] at hab
    unfold interpolate
    have hz : z - A.transport z = s • (z - T.transport z) := hab
    calc
      A.transport z = z - (z - A.transport z) := by abel
      _ = z - s • (z - T.transport z) := by rw [hz]
      _ = (1 - s) • z + s • T.transport z := by module
  exact A.pushes.symm.trans (Measure.map_congr hmap)

/-- Corrected source geodesic characterization on the explicitly regular
optimal-map domain. Both implications concern the actual coupling-infimum
Wasserstein distance, and the affine law representation is proved in the
converse rather than included as an assumption. -/
theorem geodesic_iff_optimalInterpolation
    (q : ℝ → Measure Z) (T : OptimalMap (q 0) (q 1))
    (hunique : ∀ S : OptimalMap (q 0) (q 1), S.transport =ᵐ[q 0] T.transport)
    (hregular : OptimalMapRegularity q) :
    IsConstantSpeedGeodesic q ↔
      ∀ s ∈ Icc (0 : ℝ) 1, q s = optimalInterpolation T s := by
  constructor
  · exact geodesic_eq_optimalInterpolation q T hunique hregular
  · intro hq
    have hreg : OptimalMapRegularity (optimalInterpolation T) := by
      intro s hs t ht
      simpa only [← hq s hs, ← hq t ht] using hregular s hs t ht
    have hg := optimalInterpolation_geodesic T hreg
    intro s hs t ht hst
    simpa only [← hq s hs, ← hq t ht, optimalInterpolation_zero, optimalInterpolation_one]
      using hg s hs t ht hst

section Product

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  {M : ℕ}

def productDistance (a : ℝ → P) (q : ℝ → Fin M → Measure Z) (s t : ℝ) : ℝ :=
  Real.sqrt (‖a s - a t‖ ^ 2 + (M : ℝ)⁻¹ * ∑ m,
    ULA.wasserstein2Real (q s m) (q t m) ^ 2)

def IsProductGeodesic (a : ℝ → P) (q : ℝ → Fin M → Measure Z) : Prop :=
  ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, s ≤ t →
    productDistance a q s t = (t - s) * productDistance a q 0 1

/-- Each component is an actual transport distance. The parameter coordinate
has weight one and each latent law has weight `sqrt(1/M)`. -/
def distanceComponents (a : ℝ → P) (q : ℝ → Fin M → Measure Z) (s t : ℝ) :
    Option (Fin M) → ℝ
  | none => ‖a s - a t‖
  | some m => Real.sqrt (M : ℝ)⁻¹ * ULA.wasserstein2Real (q s m) (q t m)

theorem distanceComponents_nonneg (a : ℝ → P) (q : ℝ → Fin M → Measure Z)
    (s t : ℝ) (i : Option (Fin M)) : 0 ≤ distanceComponents a q s t i := by
  cases i <;> simp only [distanceComponents]
  · exact norm_nonneg _
  · exact mul_nonneg (Real.sqrt_nonneg _) ENNReal.toReal_nonneg

theorem distanceComponents_norm (a : ℝ → P) (q : ℝ → Fin M → Measure Z) (s t : ℝ) :
    ‖(WithLp.toLp 2 (distanceComponents a q s t) :
      EuclideanSpace ℝ (Option (Fin M)))‖ = productDistance a q s t := by
  rw [← Real.sqrt_sq (norm_nonneg _), EuclideanSpace.real_norm_sq_eq]
  unfold productDistance
  congr 1
  rw [Fintype.sum_option]
  simp only [distanceComponents, mul_pow,
    Real.sq_sqrt (inv_nonneg.mpr (Nat.cast_nonneg M))]
  rw [Finset.mul_sum]

theorem nonnegative_vector_norm_mono {I : Type*} [Fintype I]
    (x y : I → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hxy : ∀ i, x i ≤ y i) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ I)‖ ≤ ‖(WithLp.toLp 2 y : EuclideanSpace ℝ I)‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  exact Finset.sum_le_sum fun i _ ↦ (sq_le_sq₀ (hx i) (hy i)).mpr (hxy i)

theorem nonnegative_vector_eq_of_norm_eq {I : Type*} [Fintype I]
    (x y : I → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hxy : ∀ i, x i ≤ y i)
    (hnorm : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ I)‖ =
      ‖(WithLp.toLp 2 y : EuclideanSpace ℝ I)‖) : x = y := by
  have hs : (∑ i, (y i ^ 2 - x i ^ 2)) = 0 := by
    have h := congrArg (fun r : ℝ ↦ r ^ 2) hnorm
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at h
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr h.symm
  have hnonneg (i : I) : 0 ≤ y i ^ 2 - x i ^ 2 :=
    sub_nonneg.mpr ((sq_le_sq₀ (hx i) (hy i)).mpr (hxy i))
  funext i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ hnonneg i)).mp hs i (Finset.mem_univ i)
  exact (sq_eq_sq₀ (hx i) (hy i)).mp (sub_eq_zero.mp hi).symm

theorem component_split_of_product_split {I : Type*} [Fintype I]
    (d x y : I → ℝ) (hd : ∀ i, 0 ≤ d i) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (htri : ∀ i, d i ≤ x i + y i) (s D : ℝ)
    (hnormd : ‖(WithLp.toLp 2 d : EuclideanSpace ℝ I)‖ = D)
    (hnormx : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ I)‖ = s * D)
    (hnormy : ‖(WithLp.toLp 2 y : EuclideanSpace ℝ I)‖ = (1 - s) * D) :
    ∀ i, x i = s * d i := by
  let X : EuclideanSpace ℝ I := WithLp.toLp 2 x
  let Y : EuclideanSpace ℝ I := WithLp.toLp 2 y
  let V : EuclideanSpace ℝ I := WithLp.toLp 2 d
  have hlo : ‖V‖ ≤ ‖X + Y‖ := by
    exact nonnegative_vector_norm_mono d (fun i ↦ x i + y i) hd
      (fun i ↦ add_nonneg (hx i) (hy i)) htri
  have hhi : ‖X + Y‖ ≤ ‖V‖ := by
    have h := norm_add_le X Y
    have hx' : ‖X‖ = s * D := hnormx
    have hy' : ‖Y‖ = (1 - s) * D := hnormy
    have hd' : ‖V‖ = D := hnormd
    rw [hx', hy'] at h
    rw [hd']
    nlinarith
  have heq : V = X + Y := by
    have hfun := nonnegative_vector_eq_of_norm_eq d (fun i ↦ x i + y i) hd
      (fun i ↦ add_nonneg (hx i) (hy i)) htri (le_antisymm hlo hhi)
    exact congrArg (WithLp.toLp 2) hfun
  have hdiff : ‖V - X‖ = (1 - s) * D := by
    rw [heq, add_sub_cancel_left]
    exact hnormy
  have haff := affine_of_scaled_distances X V s D hnormx hnormd hdiff
  intro i
  exact congrArg (fun z : EuclideanSpace ℝ I ↦ z i) haff

theorem distanceComponents_triangle
    (a : ℝ → P) (q : ℝ → Fin M → Measure Z)
    (hregular : ∀ m, OptimalMapRegularity (fun t ↦ q t m))
    (s t u : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Icc (0 : ℝ) 1) (i : Option (Fin M)) :
    distanceComponents a q s u i ≤ distanceComponents a q s t i + distanceComponents a q t u i := by
  cases i with
  | none =>
    change ‖a s - a u‖ ≤ ‖a s - a t‖ + ‖a t - a u‖
    calc
      _ = ‖(a s - a t) + (a t - a u)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  | some m =>
    obtain ⟨A⟩ := hregular m s hs t ht
    obtain ⟨B⟩ := hregular m t ht u hu
    have h := mul_le_mul_of_nonneg_left (A.wassersteinReal_triangle B)
      (Real.sqrt_nonneg (M : ℝ)⁻¹)
    simpa only [distanceComponents, mul_add] using h

theorem product_geodesic_endpoint_scaling
    (a : ℝ → P) (q : ℝ → Fin M → Measure Z)
    (hregular : ∀ m, OptimalMapRegularity (fun t ↦ q t m))
    (hg : IsProductGeodesic a q) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    ∀ i, distanceComponents a q 0 s i = s * distanceComponents a q 0 1 i ∧
      distanceComponents a q s 1 i = (1 - s) * distanceComponents a q 0 1 i := by
  have hzero : (0 : ℝ) ∈ Icc 0 1 := by constructor <;> norm_num
  have hone : (1 : ℝ) ∈ Icc 0 1 := by constructor <;> norm_num
  have hnx : ‖(WithLp.toLp 2 (distanceComponents a q 0 s) :
      EuclideanSpace ℝ (Option (Fin M)))‖ = s * productDistance a q 0 1 := by
    rw [distanceComponents_norm]
    simpa only [sub_zero] using hg 0 hzero s hs hs.1
  have hny : ‖(WithLp.toLp 2 (distanceComponents a q s 1) :
      EuclideanSpace ℝ (Option (Fin M)))‖ = (1 - s) * productDistance a q 0 1 := by
    rw [distanceComponents_norm]
    exact hg s hs 1 hone hs.2
  have hfirst := component_split_of_product_split
    (distanceComponents a q 0 1) (distanceComponents a q 0 s) (distanceComponents a q s 1)
    (distanceComponents_nonneg a q 0 1) (distanceComponents_nonneg a q 0 s)
    (distanceComponents_nonneg a q s 1)
    (distanceComponents_triangle a q hregular 0 s 1 hzero hs hone) s
    (productDistance a q 0 1) (distanceComponents_norm a q 0 1) hnx hny
  have hsecond := component_split_of_product_split
    (distanceComponents a q 0 1) (distanceComponents a q s 1) (distanceComponents a q 0 s)
    (distanceComponents_nonneg a q 0 1) (distanceComponents_nonneg a q s 1)
    (distanceComponents_nonneg a q 0 s)
    (fun i ↦ by simpa only [add_comm] using
      distanceComponents_triangle a q hregular 0 s 1 hzero hs hone i) (1 - s)
    (productDistance a q 0 1) (distanceComponents_norm a q 0 1) hny
    (by simpa only [sub_sub_cancel] using hnx)
  exact fun i ↦ ⟨hfirst i, hsecond i⟩

theorem product_geodesic_component_scaling
    (a : ℝ → P) (q : ℝ → Fin M → Measure Z)
    (hregular : ∀ m, OptimalMapRegularity (fun t ↦ q t m))
    (hg : IsProductGeodesic a q) (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t) (i : Option (Fin M)) :
    distanceComponents a q s t i = (t - s) * distanceComponents a q 0 1 i := by
  let low : Option (Fin M) → ℝ := fun i ↦ (t - s) * distanceComponents a q 0 1 i
  let high := distanceComponents a q s t
  have hlo : ∀ i, 0 ≤ low i := fun i ↦ mul_nonneg (sub_nonneg.mpr hst)
    (distanceComponents_nonneg a q 0 1 i)
  have hhi : ∀ i, 0 ≤ high i := distanceComponents_nonneg a q s t
  have hpoint (i : Option (Fin M)) : low i ≤ high i := by
    have h0 : (0 : ℝ) ∈ Icc 0 1 := by constructor <;> norm_num
    have h1 : (1 : ℝ) ∈ Icc 0 1 := by constructor <;> norm_num
    have hleft := distanceComponents_triangle a q hregular 0 s 1 h0 hs h1 i
    have hright := distanceComponents_triangle a q hregular s t 1 hs ht h1 i
    have hxs := (product_geodesic_endpoint_scaling a q hregular hg s hs i).1
    have hyt := (product_geodesic_endpoint_scaling a q hregular hg t ht i).2
    dsimp only [low, high]
    nlinarith
  have hnorm : ‖(WithLp.toLp 2 low : EuclideanSpace ℝ (Option (Fin M)))‖ =
      ‖(WithLp.toLp 2 high : EuclideanSpace ℝ (Option (Fin M)))‖ := by
    have hvec : (WithLp.toLp 2 low : EuclideanSpace ℝ (Option (Fin M))) =
        (t - s) • (WithLp.toLp 2 (distanceComponents a q 0 1)) := rfl
    rw [hvec, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hst),
      distanceComponents_norm]
    change (t - s) * productDistance a q 0 1 =
      ‖(WithLp.toLp 2 (distanceComponents a q s t) : EuclideanSpace ℝ (Option (Fin M)))‖
    rw [distanceComponents_norm]
    exact (hg s hs t ht hst).symm
  have heq := nonnegative_vector_eq_of_norm_eq low high hlo hhi hpoint hnorm
  exact (congrFun heq i).symm

/-- A normalized product geodesic has affine Euclidean coordinates and each
actual law is a constant-speed Wasserstein geodesic. -/
theorem product_geodesic_components (hM : 0 < M)
    (a : ℝ → P) (q : ℝ → Fin M → Measure Z)
    (hregular : ∀ m, OptimalMapRegularity (fun t ↦ q t m))
    (hg : IsProductGeodesic a q) :
    (∀ s ∈ Icc (0 : ℝ) 1, a s = parameterInterpolate (a 0) (a 1) s) ∧
      ∀ m, IsConstantSpeedGeodesic (fun t ↦ q t m) := by
  constructor
  · intro s hs
    have hends := product_geodesic_endpoint_scaling a q hregular hg s hs none
    change ‖a 0 - a s‖ = s * ‖a 0 - a 1‖ ∧ ‖a s - a 1‖ = (1 - s) * ‖a 0 - a 1‖ at hends
    have ha : ‖a s - a 0‖ = s * ‖a 1 - a 0‖ := by simpa only [norm_sub_rev] using hends.1
    have hb : ‖a 1 - a 0‖ = ‖a 1 - a 0‖ := rfl
    have hba : ‖(a 1 - a 0) - (a s - a 0)‖ = (1 - s) * ‖a 1 - a 0‖ := by
      have he : (a 1 - a 0) - (a s - a 0) = a 1 - a s := by abel
      rw [he]
      simpa only [norm_sub_rev] using hends.2
    have heq := affine_of_scaled_distances (a s - a 0) (a 1 - a 0) s _ ha hb hba
    calc
      a s = a 0 + (a s - a 0) := by abel
      _ = a 0 + s • (a 1 - a 0) := by rw [heq]
      _ = parameterInterpolate (a 0) (a 1) s := by unfold parameterInterpolate; module
  · intro m s hs t ht hst
    have h := product_geodesic_component_scaling a q hregular hg s t hs ht hst (some m)
    change Real.sqrt (M : ℝ)⁻¹ * ULA.wasserstein2Real (q s m) (q t m) =
      (t - s) * (Real.sqrt (M : ℝ)⁻¹ * ULA.wasserstein2Real (q 0 m) (q 1 m)) at h
    have hw : Real.sqrt (M : ℝ)⁻¹ ≠ 0 :=
      (Real.sqrt_pos.mpr (inv_pos.mpr (Nat.cast_pos.mpr hM))).ne'
    apply mul_left_cancel₀ hw
    convert h using 1
    ring

/-- Conversely, affine parameters and constant-speed latent laws give a
constant-speed geodesic for the actual normalized product distance. -/
theorem product_geodesic_of_components
    (a : ℝ → P) (q : ℝ → Fin M → Measure Z)
    (ha : ∀ s ∈ Icc (0 : ℝ) 1, a s = parameterInterpolate (a 0) (a 1) s)
    (hq : ∀ m, IsConstantSpeedGeodesic (fun t ↦ q t m)) : IsProductGeodesic a q := by
  intro s hs t ht hst
  have hparam : ‖a s - a t‖ ^ 2 = (t - s) ^ 2 * ‖a 0 - a 1‖ ^ 2 := by
    have he : a s - a t = (t - s) • (a 0 - a 1) := by
      rw [ha s hs, ha t ht]
      unfold parameterInterpolate
      module
    rw [he, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hlatent (m : Fin M) : ULA.wasserstein2Real (q s m) (q t m) =
      (t - s) * ULA.wasserstein2Real (q 0 m) (q 1 m) := hq m s hs t ht hst
  unfold productDistance
  rw [hparam]
  simp_rw [hlatent, mul_pow]
  rw [← Finset.mul_sum]
  have hfactor : (t - s) ^ 2 * ‖a 0 - a 1‖ ^ 2 + (M : ℝ)⁻¹*
      ((t - s) ^ 2 * ∑ m, ULA.wasserstein2Real (q 0 m) (q 1 m) ^ 2) =
      (t - s) ^ 2 * (‖a 0 - a 1‖ ^ 2 + (M : ℝ)⁻¹ * ∑ m,
        ULA.wasserstein2Real (q 0 m) (q 1 m) ^ 2) := by ring
  rw [hfactor, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sub_nonneg.mpr hst)]

/-- The source finite-product geodesic iff, fully proved for the actual
normalized optimizer/Wasserstein distance on the regular optimal-map domain. -/
theorem product_geodesic_iff_components (hM : 0 < M)
    (a : ℝ → P) (q : ℝ → Fin M → Measure Z)
    (hregular : ∀ m, OptimalMapRegularity (fun t ↦ q t m)) :
    IsProductGeodesic a q ↔
      (∀ s ∈ Icc (0 : ℝ) 1, a s = parameterInterpolate (a 0) (a 1) s) ∧
        ∀ m, IsConstantSpeedGeodesic (fun t ↦ q t m) := by
  exact ⟨product_geodesic_components hM a q hregular,
    fun h ↦ product_geodesic_of_components a q h.1 h.2⟩

/-- The complete regular source geodesic representation: a normalized product
geodesic has exactly affine parameters and the actual optimal-map pushforward
laws, and every such representation is a product geodesic. -/
theorem product_geodesic_iff_optimalInterpolation (hM : 0 < M)
    (a : ℝ → P) (q : ℝ → Fin M → Measure Z)
    (T : ∀ m, OptimalMap (q 0 m) (q 1 m))
    (hunique : ∀ m, ∀ S : OptimalMap (q 0 m) (q 1 m), S.transport =ᵐ[q 0 m] (T m).transport)
    (hregular : ∀ m, OptimalMapRegularity (fun t ↦ q t m)) :
    IsProductGeodesic a q ↔
      (∀ s ∈ Icc (0 : ℝ) 1, a s = parameterInterpolate (a 0) (a 1) s) ∧
        ∀ m s, s ∈ Icc (0 : ℝ) 1 → q s m = optimalInterpolation (T m) s := by
  rw [product_geodesic_iff_components hM a q hregular]
  constructor
  · rintro ⟨ha, hq⟩
    exact ⟨ha, fun m ↦ (geodesic_iff_optimalInterpolation (fun t ↦ q t m)
      (T m) (hunique m) (hregular m)).mp (hq m)⟩
  · rintro ⟨ha, hq⟩
    exact ⟨ha, fun m ↦ (geodesic_iff_optimalInterpolation (fun t ↦ q t m)
      (T m) (hunique m) (hregular m)).mpr (hq m)⟩

/-- The source's convex-potential formulation follows from an explicit smooth
Brenier certificate. Its final interpolation uses the actual Lean gradient. -/
theorem product_geodesic_iff_gradientInterpolation (hM : 0 < M)
    (a : ℝ → P) (q : ℝ → Fin M → Measure Z)
    (T : ∀ m, RegularBrenierMap (q 0 m) (q 1 m))
    (hunique : ∀ m, ∀ S : OptimalMap (q 0 m) (q 1 m),
      S.transport =ᵐ[q 0 m] (T m).transport)
    (hregular : ∀ m, OptimalMapRegularity (fun t ↦ q t m)) :
    IsProductGeodesic a q ↔
      (∀ s ∈ Icc (0 : ℝ) 1, a s = parameterInterpolate (a 0) (a 1) s) ∧
        ∀ m s, s ∈ Icc (0 : ℝ) 1 → q s m = (q 0 m).map
          (fun z ↦ (1 - s) • z + s • gradient (T m).potential z) := by
  have hgrad (m : Fin M) : gradient (T m).potential = (T m).transport :=
    gradient_eq (T m).hasGradientAt
  simp only [hgrad]
  exact product_geodesic_iff_optimalInterpolation hM a q (fun m ↦ (T m).toOptimalMap)
    hunique hregular

end Product

end LatentDiffusion.RegularTransport
