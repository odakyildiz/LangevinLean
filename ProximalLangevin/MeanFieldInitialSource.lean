import ProximalLangevin.MeanFieldProcess
import ProximalLangevin.MeanFieldBrownianFamily

set_option linter.style.header false

/-! # A concrete independent initialization and Brownian source

For any finite-second-moment latent law, its product with the canonical joint
Brownian source carries an actual L² initial joint variable with deterministic
parameter. Its latent law is the supplied law, and it is independent of every
Brownian coordinate path. Finite iid copies can therefore be formed directly.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace ProximalLangevin

/-- The supplied latent initialization law times the explicit Gaussian Brownian source. -/
def meanFieldInitialSource (dθ : ℕ) {dx : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin dx))) :
    Measure (EuclideanSpace ℝ (Fin dx) × ULA.CanonicalBrownian.VectorSample (Fin dθ ⊕ Fin dx)) :=
  μ.prod (ULA.CanonicalBrownian.vectorProbability (Fin dθ ⊕ Fin dx))

instance meanFieldInitialSource_isProbability (dθ : ℕ) {dx : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin dx))) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (meanFieldInitialSource dθ μ) := by
  unfold meanFieldInitialSource
  infer_instance

/-- Brownian coordinates use the independent second factor of the source. -/
def meanFieldInitialBrownian {dθ dx : ℕ} (a : Fin dθ ⊕ Fin dx) (t : ℝ≥0)
    (ω : EuclideanSpace ℝ (Fin dx) × ULA.CanonicalBrownian.VectorSample (Fin dθ ⊕ Fin dx)) : ℝ :=
  ULA.CanonicalBrownian.coordinate a t ω.2

theorem meanFieldInitialBrownian_measurable {dθ dx : ℕ}
    (a : Fin dθ ⊕ Fin dx) (t : ℝ≥0) : Measurable (meanFieldInitialBrownian a t) := by
  have he : Measurable (fun ω : EuclideanSpace ℝ (Fin dx) ×
      ULA.CanonicalBrownian.VectorSample (Fin dθ ⊕ Fin dx) => ω.2 a) :=
    (measurable_pi_apply a).comp measurable_snd
  exact (ULA.CanonicalBrownian.process_measurable t).comp he

section Source
variable {dθ dx : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin dx))) [IsProbabilityMeasure μ]

/-- Each coordinate has the actual standard Brownian law on the product source. -/
theorem meanFieldInitialBrownian_preBrownian (a : Fin dθ ⊕ Fin dx) :
    IsPreBrownianReal (meanFieldInitialBrownian a) (meanFieldInitialSource dθ μ) :=
  ULA.Hilbert.preBrownian_comp_measurePreserving measurePreserving_snd
    (ULA.CanonicalBrownian.coordinate a) (ULA.CanonicalBrownian.coordinate_isPreBrownian a)

/-- The entire coordinate paths remain independent after adding initialization. -/
theorem meanFieldInitialBrownian_paths_independent :
    iIndepFun (fun a ω t => @meanFieldInitialBrownian dθ dx a t ω)
      (meanFieldInitialSource dθ μ) := by
  let Q := ULA.CanonicalBrownian.vectorProbability (Fin dθ ⊕ Fin dx)
  let P := meanFieldInitialSource dθ μ
  have hcoord (a : Fin dθ ⊕ Fin dx) (t : ℝ≥0) :
      Measurable (fun ω : ULA.CanonicalBrownian.VectorSample (Fin dθ ⊕ Fin dx) =>
        ULA.CanonicalBrownian.coordinate a t ω) :=
    (ULA.CanonicalBrownian.process_measurable t).comp (measurable_pi_apply a)
  have hfull : Measurable (fun ω : ULA.CanonicalBrownian.VectorSample (Fin dθ ⊕ Fin dx) =>
      fun a t => ULA.CanonicalBrownian.coordinate a t ω) := by
    refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun t => ?_
    exact hcoord a t
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun a => (measurable_pi_iff.mpr fun t => meanFieldInitialBrownian_measurable a t).aemeasurable)).mpr
  have hpull : P.map (fun ω a t => @meanFieldInitialBrownian dθ dx a t ω) =
      Q.map (fun ω a t => ULA.CanonicalBrownian.coordinate a t ω) := by
    change (μ.prod Q).map ((fun ω a t => ULA.CanonicalBrownian.coordinate a t ω) ∘ Prod.snd) = _
    rw [← Measure.map_map hfull measurable_snd, measurePreserving_snd.map_eq]
  rw [hpull, (ULA.CanonicalBrownian.coordinate_paths_independent (Fin dθ ⊕ Fin dx)).map_fun_eq_pi_map
    (fun a => (measurable_pi_iff.mpr fun t => hcoord a t).aemeasurable)]
  congr 1
  funext a
  change Q.map (fun ω t => ULA.CanonicalBrownian.coordinate a t ω) =
    (μ.prod Q).map ((fun ω t => ULA.CanonicalBrownian.coordinate a t ω) ∘ Prod.snd)
  rw [← Measure.map_map (measurable_pi_iff.mpr fun t => hcoord a t) measurable_snd,
    measurePreserving_snd.map_eq]

/-- Holding the parameter fixed embeds latent vectors isometrically into pairs. -/
theorem meanFieldInitialPair_lipschitz (θ : EuclideanSpace ℝ (Fin dθ)) :
    LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin dx) => IPLA.pair θ x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm_sub, sub_self, norm_zero, zero_add, NNReal.coe_one, one_mul] using
    pair_norm_sub_le θ θ x y

/-- A fixed parameter and the actual latent initialization form an L² joint vector. -/
theorem meanFieldInitial_memLp (θ : EuclideanSpace ℝ (Fin dθ))
    (hμ : MemLp (fun x : EuclideanSpace ℝ (Fin dx) => x) 2 μ) :
    MemLp (fun ω => IPLA.pair θ ω.1) 2 (meanFieldInitialSource dθ μ) := by
  exact memLp_lipschitz_observable _ (meanFieldInitialPair_lipschitz (dx := dx) θ) (hμ.comp_fst _)

/-- The actual square-integrable initialization used by the integral constructors. -/
def meanFieldInitialLp (θ : EuclideanSpace ℝ (Fin dθ))
    (hμ : MemLp (fun x : EuclideanSpace ℝ (Fin dx) => x) 2 μ) :
    Lp (IPLA.Joint dθ dx) 2 (meanFieldInitialSource dθ μ) :=
  (meanFieldInitial_memLp μ θ hμ).toLp (fun ω => IPLA.pair θ ω.1)

/-- The parameter block is exactly the constant initial parameter in L². -/
theorem meanFieldInitialLp_parameter (θ : EuclideanSpace ℝ (Fin dθ))
    (hμ : MemLp (fun x : EuclideanSpace ℝ (Fin dx) => x) 2 μ) :
    jointParameterCLM.compLp (meanFieldInitialLp μ θ hμ) =
      Lp.const 2 (meanFieldInitialSource dθ μ) θ := by
  apply Lp.ext
  filter_upwards [jointParameterCLM.coeFn_compLp (meanFieldInitialLp μ θ hμ),
    (meanFieldInitial_memLp μ θ hμ).coeFn_toLp,
    Lp.coeFn_const (μ := meanFieldInitialSource dθ μ) (p := 2) (c := θ)] with ω hp hi hc
  change meanFieldInitialLp μ θ hμ ω = IPLA.pair θ ω.1 at hi
  rw [hp, hi, hc]
  rfl

/-- Its latent marginal is exactly the supplied finite-second-moment law. -/
theorem meanFieldInitialLp_latent_law (θ : EuclideanSpace ℝ (Fin dθ))
    (hμ : MemLp (fun x : EuclideanSpace ℝ (Fin dx) => x) 2 μ) :
    (meanFieldInitialSource dθ μ).map
      (jointLatentCLM.compLp (meanFieldInitialLp μ θ hμ)) = μ := by
  have heq : jointLatentCLM.compLp (meanFieldInitialLp μ θ hμ) =ᵐ[meanFieldInitialSource dθ μ]
      Prod.fst := by
    filter_upwards [jointLatentCLM.coeFn_compLp (meanFieldInitialLp μ θ hμ),
      (meanFieldInitial_memLp μ θ hμ).coeFn_toLp] with ω hl hi
    change meanFieldInitialLp μ θ hμ ω = IPLA.pair θ ω.1 at hi
    rw [hl, hi]
    rfl
  rw [Measure.map_congr heq]
  exact measurePreserving_fst.map_eq

/-- Initialization is independent of every Brownian coordinate at every time. -/
theorem meanFieldInitialLp_independent_paths (θ : EuclideanSpace ℝ (Fin dθ))
    (hμ : MemLp (fun x : EuclideanSpace ℝ (Fin dx) => x) 2 μ) :
    IndepFun (meanFieldInitialLp μ θ hμ)
      (fun ω (a : Fin dθ ⊕ Fin dx) t => meanFieldInitialBrownian a t ω)
      (meanFieldInitialSource dθ μ) := by
  have hpair : Measurable (fun x : EuclideanSpace ℝ (Fin dx) => IPLA.pair θ x) :=
    (meanFieldInitialPair_lipschitz (dx := dx) θ).continuous.measurable
  have hfull : Measurable (fun ω : ULA.CanonicalBrownian.VectorSample (Fin dθ ⊕ Fin dx) =>
      fun a t => ULA.CanonicalBrownian.coordinate a t ω) := by
    refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun t => ?_
    exact (ULA.CanonicalBrownian.process_measurable t).comp (measurable_pi_apply a)
  have hi : IndepFun (fun ω => IPLA.pair θ ω.1)
      (fun ω (a : Fin dθ ⊕ Fin dx) t => meanFieldInitialBrownian a t ω)
      (meanFieldInitialSource dθ μ) := indepFun_prod hpair hfull
  exact hi.congr (meanFieldInitial_memLp μ θ hμ).coeFn_toLp.symm (ae_of_all _ fun _ => rfl)

end Source
end ProximalLangevin
