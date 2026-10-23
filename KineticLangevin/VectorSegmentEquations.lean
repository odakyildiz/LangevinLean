import KineticLangevin.CanonicalVectorSegments

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace KineticLangevin.BrownianConvolution

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- Compose one scalar L² variable with each independent coordinate source, then assemble the vector. -/
def spatialLift : Lp ℝ 2 probability →L[ℝ]
    Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) :=
  ∑ i : ι, (((ContinuousLinearMap.id ℝ ℝ).smulRight ((PiLp.single 2 i (1 : ℝ) : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι)).compLpL
    2 (ULA.CanonicalBrownian.vectorProbability ι)).comp
      (Lp.compMeasurePreservingₗᵢ ℝ (fun ω : ULA.CanonicalBrownian.VectorSample ι => ω i)
        (measurePreserving_eval_infinitePi (fun _ : ι => probability) i)).toContinuousLinearMap

lemma coe_finset_sum {α E Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [NormedAddCommGroup E] (s : Finset α) (Z : α → Lp E 2 P) :
    (∑ i ∈ s, Z i : Lp E 2 P) =ᵐ[P] fun ω => ∑ i ∈ s, Z i ω := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero E 2 P] with ω hω
    exact hω
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (Z i) (∑ j ∈ s, Z j),ih] with ω ha hs
    rw [ha, Pi.add_apply, hs]

theorem spatialLift_coe (Z : Lp ℝ 2 probability) :
    spatialLift ι Z =ᵐ[ULA.CanonicalBrownian.vectorProbability ι]
      fun ω => WithLp.toLp 2 (fun i => Z (ω i)) := by
  classical
  let Y : ι → Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) := fun i =>
    ((ContinuousLinearMap.id ℝ ℝ).smulRight ((PiLp.single 2 i (1 : ℝ) : EuclideanSpace ℝ ι))).compLpL
      2 (ULA.CanonicalBrownian.vectorProbability ι)
      ((Lp.compMeasurePreservingₗᵢ ℝ (fun ω : ULA.CanonicalBrownian.VectorSample ι => ω i)
        (measurePreserving_eval_infinitePi (fun _ : ι => probability) i)) Z)
  have hY (i : ι) : Y i =ᵐ[ULA.CanonicalBrownian.vectorProbability ι]
      fun ω => Z (ω i) • (PiLp.single 2 i (1 : ℝ) : EuclideanSpace ℝ ι) := by
    filter_upwards [ContinuousLinearMap.coeFn_compLpL
        ((ContinuousLinearMap.id ℝ ℝ).smulRight ((PiLp.single 2 i (1 : ℝ) : EuclideanSpace ℝ ι)))
        ((Lp.compMeasurePreservingₗᵢ ℝ (fun ω : ULA.CanonicalBrownian.VectorSample ι => ω i)
          (measurePreserving_eval_infinitePi (fun _ : ι => probability) i)) Z),
      Lp.coeFn_compMeasurePreserving Z (measurePreserving_eval_infinitePi (fun _ : ι => probability) i)]
      with ω hmap hcomp
    change Y i ω = _
    change Y i ω = _ at hmap
    rw [hmap]
    exact congrArg (fun r : ℝ => r • (PiLp.single 2 i (1 : ℝ) : EuclideanSpace ℝ ι)) hcomp
  have he : spatialLift ι Z = ∑ i : ι, Y i := by
    simp only [spatialLift, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
    rfl
  rw [he]
  filter_upwards [coe_finset_sum (Finset.univ : Finset ι) Y, ae_all_iff.mpr hY] with ω hsum hall
  rw [hsum]
  simp_rw [hall]
  apply PiLp.ext
  intro j
  change (EuclideanSpace.proj j) (∑ i : ι, Z (ω i) • (PiLp.single 2 i (1 : ℝ) : EuclideanSpace ℝ ι)) = _
  rw [map_sum]
  simp

/-- The exact vector response on one interval, as an L² variable. -/
def vectorSegmentLp (k : ℝ → ℝ) (hk : Continuous k) (a t : ℝ≥0) :
    Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) :=
  spatialLift ι (segmentConvolutionLp k hk a t)

/-- The actual increment of the coordinatewise canonical vector Brownian motion. -/
def vectorBrownianIncrementLp (a t : ℝ≥0) :
    Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) :=
  spatialLift ι (segmentBrownianLp a t)

theorem vectorSegmentLp_coe (k : ℝ → ℝ) (hk : Continuous k) (a t : ℝ≥0) :
    vectorSegmentLp ι k hk a t =ᵐ[ULA.CanonicalBrownian.vectorProbability ι]
      fun ω => WithLp.toLp 2 (fun i => segmentConvolutionLp k hk a t (ω i)) :=
  spatialLift_coe ι _

theorem continuous_vectorSegmentLp (k : ℝ → ℝ) (hk : Continuous k) (a : ℝ≥0) :
    Continuous (vectorSegmentLp ι k hk a) :=
  (spatialLift ι).continuous.comp (continuous_segmentConvolutionLp k hk a)

/-- The vector position innovation is the primitive of the vector velocity innovation. -/
theorem vectorSegmentLp_primitive (γ : ℝ) (hγ : 0 ≤ γ) (a t : ℝ≥0) :
    vectorSegmentLp ι (psi γ 1) (continuous_psi γ 1) a t =
      ∫ s in 0..(t : ℝ), vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) a s.toNNReal := by
  unfold vectorSegmentLp
  rw [segmentConvolutionLp_primitive γ hγ]
  exact ((spatialLift ι).intervalIntegral_comp_comm
    (((continuous_segmentConvolutionLp (psi γ 0) (continuous_psi γ 0) a).comp
      continuous_real_toNNReal).intervalIntegrable _ _)).symm

/-- The constructed vector noise solves the required filtered Brownian equation. -/
theorem vectorSegmentLp_integral_equation (γ : ℝ) (hγ : 0 ≤ γ) (a t : ℝ≥0) :
    vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) a t = vectorBrownianIncrementLp ι a t -
      γ • ∫ s in 0..(t : ℝ), vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) a s.toNNReal := by
  unfold vectorSegmentLp vectorBrownianIncrementLp
  rw [segmentConvolutionLp_integral_equation γ hγ, map_sub, map_smul,
    ← (spatialLift ι).intervalIntegral_comp_comm
      (f := fun s : ℝ => segmentConvolutionLp (psi γ 0) (continuous_psi γ 0) a s.toNNReal)
      (((continuous_segmentConvolutionLp (psi γ 0) (continuous_psi γ 0) a).comp
        continuous_real_toNNReal).intervalIntegrable _ _)]


/-- The lifted increment is the actual increment of the canonical vector coordinate process. -/
theorem vectorBrownianIncrementLp_coe (a t : ℝ≥0) :
    vectorBrownianIncrementLp ι a t =ᵐ[ULA.CanonicalBrownian.vectorProbability ι]
      fun ω => WithLp.toLp 2 (fun i => ULA.CanonicalBrownian.coordinate i (a+t) ω -
        ULA.CanonicalBrownian.coordinate i a ω) := by
  have hc (i : ι) : ∀ᵐ ω ∂ULA.CanonicalBrownian.vectorProbability ι,
      segmentBrownianLp a t (ω i) = ULA.CanonicalBrownian.coordinate i (a+t) ω -
        ULA.CanonicalBrownian.coordinate i a ω :=
    (measurePreserving_eval_infinitePi (fun _ : ι => probability) i).quasiMeasurePreserving.ae_eq_comp
      (Lp.coeFn_sub (ULA.CanonicalBrownian.valueLp (a+t)) (ULA.CanonicalBrownian.valueLp a))
  filter_upwards [spatialLift_coe ι (segmentBrownianLp a t),ae_all_iff.mpr hc] with ω hl hc
  change spatialLift ι (segmentBrownianLp a t) ω = _
  rw [hl]
  apply PiLp.ext
  exact hc

theorem continuous_vectorBrownianIncrementLp (a : ℝ≥0) :
    Continuous (vectorBrownianIncrementLp ι a) := by
  have he : vectorBrownianIncrementLp ι a = vectorSegmentLp ι (fun _ => 1) continuous_const a := by
    funext t
    unfold vectorBrownianIncrementLp vectorSegmentLp
    rw [segmentConvolutionLp_one]
  rw [he]
  exact continuous_vectorSegmentLp ι (fun _ => 1) continuous_const a


/-- The vector velocity response is exactly the integration-by-parts OU innovation. -/
theorem vectorSegmentLp_velocity_eq_brownian_sub_convolution (γ : ℝ) (hγ : 0 ≤ γ)
    (a t : ℝ≥0) :
    vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) a t = vectorBrownianIncrementLp ι a t -
      γ • ∫ s in 0..(t : ℝ), Real.exp (-γ*((t : ℝ)-s)) •
        vectorBrownianIncrementLp ι a s.toNNReal := by
  have hc : Continuous (fun s : ℝ => Real.exp (-γ*((t : ℝ)-s)) • segmentBrownianLp a s.toNNReal) := by
    have hb : Continuous (segmentBrownianLp a) := by
      rw [show segmentBrownianLp a = segmentConvolutionLp (fun _ => 1) continuous_const a from
        funext fun s => (segmentConvolutionLp_one a s).symm]
      exact continuous_segmentConvolutionLp (fun _ => 1) continuous_const a
    exact (by fun_prop : Continuous (fun s : ℝ => Real.exp (-γ*((t : ℝ)-s)))).smul
      (hb.comp continuous_real_toNNReal)
  unfold vectorSegmentLp vectorBrownianIncrementLp
  rw [segmentConvolutionLp_velocity_eq_brownian_sub_convolution γ hγ, map_sub, map_smul,
    ← (spatialLift ι).intervalIntegral_comp_comm
      (f := fun s : ℝ => Real.exp (-γ*((t : ℝ)-s)) • segmentBrownianLp a s.toNNReal)
      (hc.intervalIntegrable _ _)]
  congr 2
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  exact map_smul (spatialLift ι) _ _

/-- The actual L² response endpoints are the existing pointwise canonical KLMC innovation. -/
theorem vectorSegmentLp_klmcInnovation_coe (d : ℕ) (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    (fun ω : ULA.CanonicalBrownian.VectorSample (Fin d) =>
      (vectorSegmentLp (Fin d) (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) h ω,
       vectorSegmentLp (Fin d) (psi γ 1) (continuous_psi γ 1) ((n : ℝ≥0)*h) h ω))
      =ᵐ[ULA.CanonicalBrownian.vectorProbability (Fin d)] canonicalKLMCInnovation d γ h n := by
  filter_upwards [vectorSegmentLp_coe (Fin d) (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) h,
    vectorSegmentLp_coe (Fin d) (psi γ 1) (continuous_psi γ 1) ((n : ℝ≥0)*h) h] with ω hv hx
  exact Prod.ext hv hx

end KineticLangevin.BrownianConvolution
