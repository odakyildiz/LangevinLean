import UnadjustedLangevin.ProductReference
import UnadjustedLangevin.BrownianReference
import UnadjustedLangevin.PotentialAssumptions
import UnadjustedLangevin.BrownianInnovations

set_option linter.style.header false

/-!
# Brownian references on every concrete initial-coupling extension

Brownian finite-dimensional laws pull back along measure-preserving maps.
The Brownian noise constructed on a coupling extension is proved equal to
the lifted source noise. The earlier actual integral-solution construction
therefore supplies `ProductReference` from just its explicit stationarity
obligation. No output-law equality or initial-cost bound is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace ULA.Hilbert
open ULA

section Pullback

variable {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype ι]
  {P : Measure Ω} {P' : Measure Ω'} {f : Ω' → Ω}

/-- Brownian finite-dimensional distributions are preserved by a
measure-preserving change of sample space. -/
theorem preBrownian_comp_measurePreserving (hf : MeasurePreserving f P' P)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P) :
    IsPreBrownianReal (fun t ω ↦ B t (f ω)) P' where
  hasLaw I := (hB.hasLaw I).comp hf.hasLaw

/-- The canonical `L²` Brownian vectors commute with pullback. -/
theorem brownianCoordinatesLp_pullback (hf : MeasurePreserving f P' P)
    (B : ι → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P) (t : ℝ≥0) :
    Lp.compMeasurePreserving f hf (brownianCoordinatesLp P B hB t) =
      brownianCoordinatesLp P' (fun i t ω ↦ B i t (f ω))
        (fun i ↦ preBrownian_comp_measurePreserving hf (B i) (hB i)) t := by
  apply Lp.ext
  have hs := hf.quasiMeasurePreserving.ae_eq_comp (brownianCoordinatesLp_coe P B hB t)
  filter_upwards [Lp.coeFn_compMeasurePreserving (brownianCoordinatesLp P B hB t) hf,
    hs, brownianCoordinatesLp_coe P' (fun i t ω ↦ B i t (f ω))
      (fun i ↦ preBrownian_comp_measurePreserving hf (B i) (hB i)) t]
    with ω hcomp hsource htarget
  exact hcomp.trans (hsource.trans htarget.symm)

/-- The normalized Brownian Euler noise also commutes with pullback. -/
theorem brownianEulerNoise_pullback (hf : MeasurePreserving f P' P)
    (B : ι → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P)
    (h : ℝ) (n : ℕ) :
    Lp.compMeasurePreserving f hf (brownianEulerNoise P B hB h n) =
      brownianEulerNoise P' (fun i t ω ↦ B i t (f ω))
        (fun i ↦ preBrownian_comp_measurePreserving hf (B i) (hB i)) h n := by
  let T : Lp (EuclideanSpace ℝ ι) 2 P →ₗ[ℝ] Lp (EuclideanSpace ℝ ι) 2 P' :=
    Lp.compMeasurePreservingₗ ℝ f hf
  have hT (t : ℝ≥0) : T (brownianCoordinatesLp P B hB t) =
      brownianCoordinatesLp P' (fun i t ω ↦ B i t (f ω))
        (fun i ↦ preBrownian_comp_measurePreserving hf (B i) (hB i)) t :=
    brownianCoordinatesLp_pullback hf B hB t
  change T (brownianEulerNoise P B hB h n) = _
  simp only [brownianEulerNoise, brownianLangevinNoise, brownianCoordinatesRealLp,
    map_smul, map_sub, hT]

end Pullback

section Product

variable {S ι : Type*} [MeasurableSpace S] [Fintype ι]
  (Q : Measure S) [IsProbabilityMeasure Q]
  {μ : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure μ]

local instance brownianProductProbability {π : Measure (EuclideanSpace ℝ ι)} (c : Coupling μ π) :
    IsProbabilityMeasure (initialExtension c Q) := initialExtension_isProbabilityMeasure c Q

/-- The source noise for the canonical product algorithm is the actual Euler
noise already constructed from the given Brownian coordinates. -/
def sourceEulerNoise (B : ι → ℝ≥0 → S → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) Q) (h : ℝ) (n : ℕ) : S → EuclideanSpace ℝ ι :=
  brownianEulerNoise Q B hB h n

omit [IsProbabilityMeasure Q] in
/-- Its square integrability follows from its construction as an `L²` vector. -/
theorem sourceEulerNoise_memLp (B : ι → ℝ≥0 → S → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) Q) (h : ℝ) (n : ℕ) :
    MemLp (sourceEulerNoise Q B hB h n) 2 Q := Lp.memLp _

omit [IsProbabilityMeasure Q] in
/-- The source Euler vector is the normalized raw Brownian increment almost
everywhere; all choices of `L²` representatives disappear from this formula. -/
theorem sourceEulerNoise_coe (B : ι → ℝ≥0 → S → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) Q) (h : ℝ) (n : ℕ) :
    sourceEulerNoise Q B hB h n =ᵐ[Q] fun ω ↦
      (Real.sqrt (2 * h))⁻¹ • (Real.sqrt 2 •
        (brownianCoordinates B (((n : ℝ) * h + h).toNNReal) ω -
          brownianCoordinates B (((n : ℝ) * h).toNNReal) ω)) := by
  unfold sourceEulerNoise brownianEulerNoise brownianLangevinNoise brownianCoordinatesRealLp
  filter_upwards [Lp.coeFn_smul (Real.sqrt (2 * h))⁻¹
      (Real.sqrt 2 • (brownianCoordinatesLp Q B hB (((n : ℝ) * h + h).toNNReal) -
        brownianCoordinatesLp Q B hB (((n : ℝ) * h).toNNReal))),
    Lp.coeFn_smul (Real.sqrt 2)
      (brownianCoordinatesLp Q B hB (((n : ℝ) * h + h).toNNReal) -
        brownianCoordinatesLp Q B hB (((n : ℝ) * h).toNNReal)),
    Lp.coeFn_sub (brownianCoordinatesLp Q B hB (((n : ℝ) * h + h).toNNReal))
      (brownianCoordinatesLp Q B hB (((n : ℝ) * h).toNNReal)),
    brownianCoordinatesLp_coe Q B hB (((n : ℝ) * h + h).toNNReal),
    brownianCoordinatesLp_coe Q B hB (((n : ℝ) * h).toNNReal)]
    with ω houter hinner hsub hnext hprev
  simp only [houter, hinner, hsub, hnext, hprev, Pi.smul_apply, Pi.sub_apply]

omit [IsProbabilityMeasure Q] in
/-- Each Euler innovation coordinate is the usual Brownian increment divided
by the square root of the time step. -/
theorem sourceEulerNoise_coordinate_coe (B : ι → ℝ≥0 → S → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) Q) (h : ℝ) (hh : 0 < h) (n : ℕ) (i : ι) :
    (fun ω ↦ sourceEulerNoise Q B hB h n ω i) =ᵐ[Q] fun ω ↦
      (B i ((((n : ℝ) + 1) * h).toNNReal) ω -
        B i (((n : ℝ) * h).toNNReal) ω) / Real.sqrt h := by
  have hs2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hsh : Real.sqrt h ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hh)
  filter_upwards [sourceEulerNoise_coe Q B hB h n] with ω hω
  have hi := congrArg (fun z : EuclideanSpace ℝ ι ↦ z i) hω
  change sourceEulerNoise Q B hB h n ω i = (Real.sqrt (2 * h))⁻¹ * (Real.sqrt 2 *
    (B i (((n : ℝ) * h + h).toNNReal) ω - B i (((n : ℝ) * h).toNNReal) ω)) at hi
  rw [hi, show (n : ℝ) * h + h = ((n : ℝ) + 1) * h by ring,
    Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
  field_simp

omit [IsProbabilityMeasure Q] in
/-- The same normalized-coordinate formula on the nonnegative Brownian time grid. -/
theorem sourceEulerNoise_coordinate_coe_nnreal (B : ι → ℝ≥0 → S → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) Q) (h : ℝ≥0) (hh : 0 < h) (n : ℕ) (i : ι) :
    (fun ω ↦ sourceEulerNoise Q B hB (h : ℝ) n ω i) =ᵐ[Q] fun ω ↦
      (B i (((n + 1 : ℕ) : ℝ≥0) * h) ω - B i ((n : ℝ≥0) * h) ω) /
        Real.sqrt (h : ℝ) := by
  have ht (k : ℕ) : ((k : ℝ) * (h : ℝ)).toNNReal = (k : ℝ≥0) * h := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (mul_nonneg (Nat.cast_nonneg k) h.coe_nonneg)]
    simp
  have hn : (((n : ℝ) + 1) * (h : ℝ)).toNNReal = ((n + 1 : ℕ) : ℝ≥0) * h := by
    simpa only [Nat.cast_add, Nat.cast_one] using ht (n + 1)
  simpa only [hn, ht n] using
    sourceEulerNoise_coordinate_coe Q B hB (h : ℝ) (by exact_mod_cast hh) n i

omit [IsProbabilityMeasure Q] in
/-- Identification with the standard normalized Brownian-increment definition. -/
theorem sourceEulerNoise_normalized_coordinate (B : ι → ℝ≥0 → S → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) Q) (h : ℝ) (hh : 0 < h) (n : ℕ) (i : ι) :
    (fun ω ↦ sourceEulerNoise Q B hB h n ω i) =ᵐ[Q]
      normalizedBrownianIncrement (B i) h.toNNReal n := by
  have hn := sourceEulerNoise_coordinate_coe_nnreal Q B hB h.toNNReal
    (Real.toNNReal_pos.mpr hh) n i
  unfold normalizedBrownianIncrement
  simpa only [Real.coe_toNNReal h hh.le] using hn

omit [IsProbabilityMeasure Q] in
/-- Each source innovation coordinate has the standard real Gaussian law. -/
theorem sourceEulerNoise_coordinateLaw (B : ι → ℝ≥0 → S → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) Q) (h : ℝ) (hh : 0 < h) (n : ℕ) (i : ι) :
    HasLaw (fun ω ↦ sourceEulerNoise Q B hB h n ω i) (gaussianReal 0 1) Q :=
  (normalizedBrownianIncrement_hasLaw Q (B i) (hB i) h.toNNReal
    (Real.toNNReal_pos.mpr hh) n).congr
      (sourceEulerNoise_normalized_coordinate Q B hB h hh n i)

omit [IsProbabilityMeasure Q] in
/-- Independent Brownian coordinate grid paths give independent innovations
across every iteration-coordinate pair. -/
theorem sourceEulerNoise_independent (B : ι → ℝ≥0 → S → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) Q) (h : ℝ) (hh : 0 < h)
    (hpaths : iIndepFun (fun i ω (n : ℕ) ↦ B i ((n : ℝ≥0) * h.toNNReal) ω) Q) :
    iIndepFun (fun p : ℕ × ι ↦ fun ω ↦ sourceEulerNoise Q B hB h p.1 ω p.2) Q := by
  have hind := normalizedBrownianIncrements_independent Q B hB h.toNNReal
    (Real.toNNReal_pos.mpr hh) hpaths
  have hswap := hind.precomp (g := fun p : ℕ × ι ↦ (p.2, p.1)) (by
    intro a b hab
    exact Prod.ext (congrArg Prod.snd hab) (congrArg Prod.fst hab))
  exact hswap.congr (fun p ↦ (sourceEulerNoise_normalized_coordinate Q B hB h hh p.1 p.2).symm)

omit [Fintype ι] in
/-- The source Brownian coordinates remain Brownian on every coupling extension. -/
theorem productPreBrownian {π : Measure (EuclideanSpace ℝ ι)} (c : Coupling μ π)
    (B : ι → ℝ≥0 → S → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) Q) (i : ι) :
    IsPreBrownianReal (fun t (p : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) × S) ↦ B i t p.2)
      (initialExtension c Q) := by
  have := c.isProbabilityMeasure
  exact preBrownian_comp_measurePreserving measurePreserving_snd (B i) (hB i)

/-- The common lifted source noise is exactly the Euler noise used by the
Brownian reference on the coupling extension. This equality is proved from
the actual coordinate construction. -/
theorem productNoise_eq_brownianEulerNoise
    {π : Measure (EuclideanSpace ℝ ι)} (c : Coupling μ π)
    (B : ι → ℝ≥0 → S → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) Q)
    (h : ℝ) (n : ℕ) :
    productNoise Q c (sourceEulerNoise Q B hB h) (sourceEulerNoise_memLp Q B hB h) n =
      brownianEulerNoise (initialExtension c Q) (fun i t p ↦ B i t p.2)
        (productPreBrownian Q c B hB) h n := by
  have := c.isProbabilityMeasure
  calc
    _ = Lp.compMeasurePreserving Prod.snd
        (measurePreserving_snd (μ := c.joint) (ν := Q)) (brownianEulerNoise Q B hB h n) := by
      apply Lp.ext
      exact (productNoise_coe Q c (sourceEulerNoise Q B hB h)
        (sourceEulerNoise_memLp Q B hB h) n).trans
          (Lp.coeFn_compMeasurePreserving (brownianEulerNoise Q B hB h n)
            (measurePreserving_snd (μ := c.joint) (ν := Q))).symm
    _ = _ := brownianEulerNoise_pullback measurePreserving_snd B hB h n

/-- The lifted Brownian noise has the actual standard Gaussian coordinate law. -/
theorem productEulerNoise_coordinateLaw
    {π : Measure (EuclideanSpace ℝ ι)} (c : Coupling μ π)
    (B : ι → ℝ≥0 → S → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) Q)
    (h : ℝ) (hh : 0 < h) (n : ℕ) (i : ι) :
    HasLaw (fun p ↦ productNoise Q c (sourceEulerNoise Q B hB h)
      (sourceEulerNoise_memLp Q B hB h) n p i) (gaussianReal 0 1)
        (initialExtension c Q) := by
  have := c.isProbabilityMeasure
  exact ((sourceEulerNoise_coordinateLaw Q B hB h hh n i).comp
    (measurePreserving_snd (μ := c.joint) (ν := Q)).hasLaw).congr
      ((productNoise_coe Q c (sourceEulerNoise Q B hB h)
        (sourceEulerNoise_memLp Q B hB h) n).fun_comp (fun z ↦ z i))

/-- Independence across all innovation coordinates and times is preserved
on the concrete product extension. -/
theorem productEulerNoise_independent
    {π : Measure (EuclideanSpace ℝ ι)} (c : Coupling μ π)
    (B : ι → ℝ≥0 → S → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) Q)
    (h : ℝ) (hh : 0 < h)
    (hpaths : iIndepFun (fun i ω (n : ℕ) ↦ B i ((n : ℝ≥0) * h.toNNReal) ω) Q) :
    iIndepFun (fun j : ℕ × ι ↦ fun p ↦
      productNoise Q c (sourceEulerNoise Q B hB h)
        (sourceEulerNoise_memLp Q B hB h) j.1 p j.2) (initialExtension c Q) := by
  have := c.isProbabilityMeasure
  have hsource : HasLaw
      (fun s (j : ℕ × ι) ↦ sourceEulerNoise Q B hB h j.1 s j.2)
      (Measure.infinitePi (fun _ : ℕ × ι ↦ gaussianReal 0 1)) Q :=
    (sourceEulerNoise_independent Q B hB h hh hpaths).hasLaw_infinitePi
    (fun j : ℕ × ι ↦ sourceEulerNoise_coordinateLaw Q B hB h hh j.1 j.2)
    (aemeasurable_pi_iff.mpr fun j ↦
      (sourceEulerNoise_coordinateLaw Q B hB h hh j.1 j.2).aemeasurable)
  have hpull : HasLaw
      (fun p (j : ℕ × ι) ↦ sourceEulerNoise Q B hB h j.1 p.2 j.2)
      (Measure.infinitePi (fun _ : ℕ × ι ↦ gaussianReal 0 1)) (initialExtension c Q) :=
    hsource.comp (measurePreserving_snd (μ := c.joint) (ν := Q)).hasLaw
  have hraw : iIndepFun (fun j : ℕ × ι ↦ fun p : (EuclideanSpace ℝ ι ×
      EuclideanSpace ℝ ι) × S ↦ sourceEulerNoise Q B hB h j.1 p.2 j.2)
        (initialExtension c Q) := by
    have hcoord (j : ℕ × ι) : HasLaw
        (fun p : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) × S ↦
          sourceEulerNoise Q B hB h j.1 p.2 j.2) (gaussianReal 0 1) (initialExtension c Q) :=
      (sourceEulerNoise_coordinateLaw Q B hB h hh j.1 j.2).comp
        (measurePreserving_snd (μ := c.joint) (ν := Q)).hasLaw
    apply (iIndepFun_iff_map_fun_eq_infinitePi_map₀'
      (fun j ↦ (hcoord j).aemeasurable)).mpr
    rw [hpull.map_eq]
    congr 1
    funext j
    exact (hcoord j).map_eq.symm
  exact hraw.congr fun j ↦ ((productNoise_coe Q c (sourceEulerNoise Q B hB h)
    (sourceEulerNoise_memLp Q B hB h) j.1).fun_comp (fun z ↦ z j.2)).symm

/-- The constructed initialization is independent of the complete lifted
noise sequence, including the actual representatives used by `lpChain`. -/
theorem productEulerNoise_independentInitial
    {π : Measure (EuclideanSpace ℝ ι)} (c : Coupling μ π)
    (hc : couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (fun x : EuclideanSpace ℝ ι ↦ x) 2 π)
    (B : ι → ℝ≥0 → S → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) Q) (h : ℝ) :
    IndepFun (initialExtension_lpInitial c Q hc hπ)
      (fun p n ↦ productNoise Q c (sourceEulerNoise Q B hB h)
        (sourceEulerNoise_memLp Q B hB h) n p) (initialExtension c Q) := by
  have := c.isProbabilityMeasure
  have hnoise : (fun p n ↦ productNoise Q c (sourceEulerNoise Q B hB h)
      (sourceEulerNoise_memLp Q B hB h) n p) =ᵐ[initialExtension c Q]
        fun p n ↦ sourceEulerNoise Q B hB h n p.2 := by
    have hall : ∀ᵐ p ∂initialExtension c Q, ∀ n,
        productNoise Q c (sourceEulerNoise Q B hB h)
          (sourceEulerNoise_memLp Q B hB h) n p = sourceEulerNoise Q B hB h n p.2 :=
      ae_all_iff.mpr fun n ↦ productNoise_coe Q c (sourceEulerNoise Q B hB h)
        (sourceEulerNoise_memLp Q B hB h) n
    exact hall.mono fun p hp ↦ funext hp
  have hraw : IndepFun (fun p : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) × S ↦ p.1.1)
      (fun p n ↦ sourceEulerNoise Q B hB h n p.2) (initialExtension c Q) :=
    indepFun_prod₀ measurable_fst.aemeasurable (aemeasurable_pi_iff.mpr fun n ↦
      (sourceEulerNoise_memLp Q B hB h n).aestronglyMeasurable.aemeasurable)
  exact hraw.congr (initialExtension_memLp_initial c Q hc hπ).coeFn_toLp.symm hnoise.symm

/-- The coupled reference initial state is also independent of all fresh noise. -/
theorem productEulerNoise_independentReference
    {π : Measure (EuclideanSpace ℝ ι)} (c : Coupling μ π)
    (hπ : MemLp (fun x : EuclideanSpace ℝ ι ↦ x) 2 π)
    (B : ι → ℝ≥0 → S → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) Q) (h : ℝ) :
    IndepFun (initialExtension_lpReference c Q hπ)
      (fun p n ↦ productNoise Q c (sourceEulerNoise Q B hB h)
        (sourceEulerNoise_memLp Q B hB h) n p) (initialExtension c Q) := by
  have := c.isProbabilityMeasure
  have hnoise : (fun p n ↦ productNoise Q c (sourceEulerNoise Q B hB h)
      (sourceEulerNoise_memLp Q B hB h) n p) =ᵐ[initialExtension c Q]
        fun p n ↦ sourceEulerNoise Q B hB h n p.2 := by
    have hall : ∀ᵐ p ∂initialExtension c Q, ∀ n,
        productNoise Q c (sourceEulerNoise Q B hB h)
          (sourceEulerNoise_memLp Q B hB h) n p = sourceEulerNoise Q B hB h n p.2 :=
      ae_all_iff.mpr fun n ↦ productNoise_coe Q c (sourceEulerNoise Q B hB h)
        (sourceEulerNoise_memLp Q B hB h) n
    exact hall.mono fun p hp ↦ funext hp
  have hraw : IndepFun (fun p : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) × S ↦ p.1.2)
      (fun p n ↦ sourceEulerNoise Q B hB h n p.2) (initialExtension c Q) :=
    indepFun_prod₀ measurable_snd.aemeasurable (aemeasurable_pi_iff.mpr fun n ↦
      (sourceEulerNoise_memLp Q B hB h n).aestronglyMeasurable.aemeasurable)
  exact hraw.congr (initialExtension_memLp_reference c Q hπ).coeFn_toLp.symm hnoise.symm

variable (U : EuclideanSpace ℝ ι → ℝ) (m : ℝ) (L : ℝ≥0)
  (hm : 0 < m) (hdiff : Differentiable ℝ U)
  (hsc : StrongConvexOn Set.univ m U) (hLip : LipschitzWith L (gradient U))
  (B : ι → ℝ≥0 → S → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) Q)
  (h : ℝ) (hh : 0 < h)

/-- The already proved finite Gibbs second moment, named for the construction. -/
abbrev productGibbsMemLp : MemLp (fun x : EuclideanSpace ℝ ι ↦ x) 2 (gibbsMeasure U) :=
  memLp_id_gibbsMeasure U m hm hdiff hsc

/-- The actual Brownian reference on a given product extension, with its
noise parameter identified with the common source noise. Only stationarity
of the explicitly constructed segments is supplied. -/
def brownianProductL2Reference (c : Coupling μ (gibbsMeasure U))
    (hstationary : ∀ n t, t ∈ Icc 0 h →
      (initialExtension c Q).map
        (brownianSegments (initialExtension c Q) U L hLip
          (fun i t p ↦ B i t p.2) (productPreBrownian Q c B hB) h hh.le
          (initialExtension_lpReference c Q (productGibbsMemLp U m hm hdiff hsc)) n t) =
        gibbsMeasure U) :
    L2Reference (initialExtension c Q) (Fintype.card ι) U h L hLip
      (productNoise Q c (sourceEulerNoise Q B hB h) (sourceEulerNoise_memLp Q B hB h))
      (gibbsMeasure U) := by
  let ref := brownianReference_of_strongConvex (initialExtension c Q) U m L hm hdiff hsc hLip
    (fun i t p ↦ B i t p.2) (productPreBrownian Q c B hB) h hh
    (initialExtension_lpReference c Q (productGibbsMemLp U m hm hdiff hsc)) hstationary
  exact {
    segment := ref.segment
    increment := ref.increment
    continuous := ref.continuous
    join := ref.join
    noiseEndpoint := fun n ↦ by
      rw [productNoise_eq_brownianEulerNoise]
      exact ref.noiseEndpoint n
    stationary := ref.stationary
    integralEquation := ref.integralEquation
    scoreBound := ref.scoreBound
    noiseBound := ref.noiseBound }

/-- Every field of `ProductReference` is constructed from the given Brownian
source and the original potential assumptions, except the displayed law of
the actual constructed solution. In particular the initial coupling and
output-law obligations add no hypotheses. -/
def productReference_of_constructed_brownian
    (hstationary : ∀ (c : Coupling μ (gibbsMeasure U)) (_ : couplingCost c.joint ≠ ⊤)
      n t, t ∈ Icc 0 h →
      (initialExtension c Q).map
        (brownianSegments (initialExtension c Q) U L hLip
          (fun i t p ↦ B i t p.2) (productPreBrownian Q c B hB) h hh.le
          (initialExtension_lpReference c Q (productGibbsMemLp U m hm hdiff hsc)) n t) =
        gibbsMeasure U) :
    ProductReference Q (Fintype.card ι) U h L hLip μ (gibbsMeasure U)
      (productGibbsMemLp U m hm hdiff hsc)
      (sourceEulerNoise Q B hB h) (sourceEulerNoise_memLp Q B hB h) where
  reference c hc := brownianProductL2Reference Q U m L hm hdiff hsc hLip B hB h hh c
    (hstationary c hc)
  start c hc := by
    exact brownianSegments_initial (initialExtension c Q) U L hLip
      (fun i t p ↦ B i t p.2) (productPreBrownian Q c B hB) h hh.le
      (initialExtension_lpReference c Q (productGibbsMemLp U m hm hdiff hsc))

/-- The constructed Brownian endpoint with the genuine initial Wasserstein
distance. Every coupling is realized on its concrete product space. The only
remaining process-law premise is the explicitly displayed stationarity of
the actual constructed integral solution. -/
theorem dalalyan_of_constructed_product_brownian [Nonempty ι]
    (hsmall : h ≤ 2 / (m + (L : ℝ)))
    (hfinite : wasserstein2 μ (gibbsMeasure U) ≠ ⊤)
    (hstationary : ∀ (c : Coupling μ (gibbsMeasure U)) (_ : couplingCost c.joint ≠ ⊤)
      n t, t ∈ Icc 0 h →
      (initialExtension c Q).map
        (brownianSegments (initialExtension c Q) U L hLip
          (fun i t p ↦ B i t p.2) (productPreBrownian Q c B hB) h hh.le
          (initialExtension_lpReference c Q (productGibbsMemLp U m hm hdiff hsc)) n t) =
        gibbsMeasure U) (n : ℕ) :
    wasserstein2Real
      (productOutputLaw Q U h μ (sourceEulerNoise Q B hB h) n) (gibbsMeasure U) ≤
      (1 - m * h) ^ n * wasserstein2Real μ (gibbsMeasure U) +
        (33 / 20 : ℝ) * ((L : ℝ) / m) * Real.sqrt (h * (Fintype.card ι : ℝ)) := by
  exact dalalyan_small_step_of_product_reference Q (Fintype.card ι) U m h L hdiff hsc hLip
    hm (strongConvex_le_lipschitz hdiff hsc hLip) hh hsmall
    (productGibbsMemLp U m hm hdiff hsc) (sourceEulerNoise Q B hB h)
    (sourceEulerNoise_memLp Q B hB h) hfinite
    (productReference_of_constructed_brownian Q U m L hm hdiff hsc hLip B hB h hh hstationary) n

end Product

end ULA.Hilbert
