# Latent diffusion: corrected source results and explicit regularity

The source is **Training Latent Diffusion Models with Interacting Particle Algorithms**, Tim Y. J. Wang, Juan Kuntz and O. Deniz Akyildiz, in `papers/Latent_diffusion/main_aistats.tex` and `supp_aistats.tex`. The machine-readable `reference_audit.json` preserves exact TeX, line locations and source hashes for all **19 named theorem/proposition/lemma statements**, including appendix repetitions. The main webpage presents the corrected mathematical statements, precise corrections and extracted Lean contracts before the separate new theory.

The source theorem statements are proved on an explicit regular domain. This does not assert that false or inconsistent printed statements are literally true. The ledger distinguishes `corrected_statement_fully_proved` from `original_statement_fully_reconstructed`; a correction can have a complete proof while its exact printed predecessor remains false. Original assumptions A1–A4 are green, added source regularity R1–R7 is blue, formula corrections are rose, and independent new-theory assumptions N1–N7 are orange.

## Source setting and assumptions

For datum $m$, let $U_m(a,z)=-\log\widetilde p_a(x^m,z)$, $Z_m(a)=\int e^{-U_m(a,z)}\,dz$ and $\pi_a^m=Z_m(a)^{-1}e^{-U_m(a,\cdot)}\,dz$. The actual normalized free energy is

$$
\begin{aligned}
\widetilde F(a,q)&=-\frac1M\sum_m\log Z_m(a)+\frac1M\sum_m\mathrm{KL}(q^m\Vert\pi_a^m),\\
d((a,q),(b,r))^2&=\|a-b\|^2+\frac1M\sum_mW_2(q^m,r^m)^2.
\end{aligned}
$$

Finite KL is established before conversion to real arithmetic. Normalizers, posterior probability laws and their finite second moments are constructed from actual density integrals. The normalized geometry retains the source strong-convexity constant independently of the number of data or particle replicas.

- **A1: model regularity**, main lines 143–150: differentiable parameter-dependent normalizers and posterior densities, positive tilted density, and spatial $C^2$ posterior regularity.
- **A2: classical solution regularity**, main lines 151–154: a $C^1$ parameter path and positive $C^{1,2}$ density paths. The literal time-zero claim for *every* $\mathcal P_2$ initial law is false: a Dirac law cannot have a Lebesgue density. The proved correction uses an admissible regular initial class (R1). The continuous estimates apply to every classical solution in the R1–R4 class; existence of such a classical density solution is not constructed.
- **A3: joint strong log-concavity**, main lines 155–157: each $U_m$ is jointly $\lambda$-strongly convex, with $\lambda>0$.
- **A4: joint gradient Lipschitz continuity**, main lines 200–207 and supplement 753–759: the gradient bound concerns the tilted potential, including the tilt penalty.

## Added regularity, visibly separate from A1–A4

1. **R1, admissible density domain:** positive finite normalizers, actual probability laws, finite KL/energy and posterior membership in the chosen finite-second-moment comparison domain. `RegularModel` derives normalizers and posterior moments from joint strong convexity; `RegularVariational` realizes arbitrary finite-KL trials by their actual Radon–Nikodym densities.
2. **R2, local dominated differentiation:** measurable integrands, pointwise derivatives on a common neighbourhood, finite base energy and an integrable bound for the differentiated integrand. `RegularEvidence` differentiates actual normalizers and derives posterior-score centering at the evidence optimizer. The parameter time chain rule is proved.
3. **R3, classical equations and integrable tails:** the actual parameter ODE and Fokker–Planck PDE, differentiable flux components, and the three absolutely integrable products required by ordinary spatial integration by parts. `RegularFlowCalculus` proves the normalized product-gradient pairing, Fisher integrability and full de Bruijn identity. None is a regularity field.
4. **R4, regular transport domain:** actual pushforward density laws, smooth positive-Jacobian displacement maps, their density/Jacobian conservation equation and integrable logarithms/quadratic costs. Exact transport distance uses minimality against every genuine coupling. The geodesic equivalence uses intermediate optimal maps and endpoint-map uniqueness; its gradient form uses a convex-potential gradient certificate. Entropy displacement convexity, entropy tangents and the normalized first-order inequality are proved from these data.
5. **R5, characteristic metric realization:** square-integrable characteristic curves, their actual velocities, and optimal target anchors. `RegularProductMetricFlow` proves normalized product-distance slopes and identifies kinetic energy with the actual source Fisher information. The corrected slope statement also covers target crossings.
6. **R6, complete regular density domain:** `ProductDensityChart` explicitly identifies its metric with the source normalized parameter/$W_2$ metric of its actual laws. Pointwise continuous densities/potentials and local integrable energy envelopes prove energy continuity and lower semicontinuity. Completeness is required of this chosen domain; it is not attributed to all smooth densities.
7. **R7, stochastic initialization and moments:** actual square-integrable initial clouds, posterior/Gibbs comparison initialization, declared Brownian independence and uniform normalized state/score moments, including a fixed per-copy centered-score variance $V_0$. Count-independent temporal constants also require a uniform normalized force-at-origin bound. The checked Euler restriction is $0<h$, $\lambda h\le1$, $hL^2\le\lambda$. Unique continuous $L^2$ Brownian integral paths are constructed by Picard; Gibbs stationarity, score residuals, local Euler defects and final errors are proved. This is the solution class used by the RMS bounds. Sampling and initialization law conditions are explicit assumptions. Reference existence, stationarity, desired-error recurrences and zero-score identities are conclusions of the final source optimizer theorem.

## Proof correspondence for all 19 source statements

The exact source line ranges and declaration names are maintained in `reference_audit.json`; the following records the mathematical proof chain.

| Source label | Corrected result and proof modules |
| --- | --- |
| `prop:ftildemins` | Literal density-integral minimizers are exactly the evidence optimizers with their posterior laws: `RegularVariational`, `RegularModel`. |
| `thm:exp_convg_informal` | Unique actual evidence optimizer and parameter exponential convergence: `RegularConvergence.existsUnique_optimizer_and_flow_convergence`. |
| `thrm:error-bound` | Actual full-batch Euler parameter RMS bound to the constructed optimizer: `RegularSourceTheorem.full_batch_optimizer_rms_rate`. |
| `app:lemma_1st_var` | Dominated parameter and zero-mass density first variations: `SourceCalculus`; actual continuity-direction score pairing: `RegularFlowCalculus`. |
| `unlabelled-product-gradient` | Actual Riesz pairing for every admissible parameter/continuity velocity under the normalized product metric: `RegularFlowCalculus.normalized_product_gradient_representation`. |
| `prop:de_bruijin` | Derivative of the actual normalized density energy equals minus the actual source Fisher information: `RegularFlowCalculus.normalized_product_deBruijn`, `RegularConvergence.ClassicalFlow.deBruijn`. |
| `lem:geodesic` | Constant-speed actual-law displacement interpolations and the regular normalized product characterization: `RegularTransportGeodesic`. |
| `lem:geodesic_convexity` | Jacobian entropy convexity plus joint potential convexity in the actual normalized transport geometry: `RegularTransport`, `RegularTransportFirstOrder`. |
| `lem:lower_deriv` | Actual probability-law energy right derivative and source law-pairing lower liminf from R2/R3 domination and continuity equations, without A3: `RegularDirectional.lower_directional_liminf_law_pairing`. |
| `thm:sLC_implies_xLSI` | Normalized actual Fisher inequality from proved entropy and potential tangents: `RegularTransportFirstOrder.DatasetRegularity.extendedLSI`, `RegularConvergence.ClassicalFlow.extendedLSI`. |
| `lem:distance_deriv` | Corrected upper-right distance slope and integrated control: `RegularProductMetricFlow`, with actual law couplings and kinetic/Fisher identification. |
| `lem:lower_semi_continuous` | Actual normalized density energy is continuous, hence lower semicontinuous, in its explicitly identified R6 source metric: `RegularDensityDomain`. |
| `lem:cauchy` | A Cauchy *minimizing flow sequence* in the complete R6 domain converges to an admissible actual minimizer: `RegularDensityDomain.ProductDensityChart.cauchy_minimizer`. |
| `thm:xLSI_implies_xTalagrand` | Connected density-flow implication with xLSI as the sole functional inequality and no A3: `RegularFlowTalagrand.CharacteristicRealization.exists_minimizer_talagrand`. Its primitive parameter/Fokker–Planck equations prove dissipation; actual characteristic derivatives and coupling anchors prove metric speed. The same endpoint constructs the minimizing limit; no supplied dissipation or speed inequality remains. |
| `thm:exp_convg_appendix` | Actual normalized full-product and parameter exponential estimates: `RegularConvergence.ClassicalFlow.full_product_exponential_convergence`. |
| `lem:cont-time-convg` | Constructed unique continuous $L^2$ Brownian mean-field solution and actual posterior reference, full cloud contraction, and measurable/integrable per-datum empirical $W_2$ RMS contraction: `RegularSourceTheorem.meanField_actual_empirical_convergence`. |
| `lem:spatial_discretization` | Matched-initialization particle/mean-field error from derived independent centered-score fluctuations: `RegularMeanField.exists_spatial_comparison`. |
| `lem:temporal_discretization` | Actual Brownian integral equation and Euler comparison, with the corrected $O(\sqrt h)$ order: `RegularMeanField.temporal_comparison`. |
| `thrm_app:error-bound` | Appendix restatement of the same actual full-batch optimizer theorem: `RegularSourceTheorem.full_batch_optimizer_rms_rate`. |

The full chain does not assume entropy dissipation, entropy displacement convexity, the desired first-order transport inequality or the desired numerical recurrence. Abstract comparison theorems retain their natural inputs; the source-level wrappers discharge those inputs from the actual model, equations and blue regularity data.

## Precise source corrections

- **A2 at time zero:** main 151–154 and supplement 438–439 include singular initial laws while requiring positive densities at zero. `SourceObstruction` proves the Dirac contradiction; R1 restricts the corrected initial class.
- **Tilted variational normalizer:** main 104–106 integrates over $z_{0:K}$ although the tilted density in main 100–102 is defined on $z_0$. Normalize that actual latent density. Posterior $\mathcal P_2$ membership is explicitly addressed.
- **Zero tilt at one optimizer:** main 107–110 does not imply an original-likelihood optimizer. `Variational` proves a counterexample and a sufficient zero-gap comparison condition at an original optimizer.
- **Density first variation:** supplement 188–199 omits $+1$ from the ordinary derivative of $q\log q$. It vanishes precisely against zero-total-mass density tangents. `SourceCalculus` proves this under dominated differentiation.
- **Normalized law gradient:** supplement 206–221 uses an inverse metric factor $M$, cancelling the objective's $1/M$. The actual transport pairing proves that no extra $1/M$ belongs in the individual density drift or diffusion.
- **Distance derivative:** supplement 623–629 claims an ordinary derivative at every positive time. A smooth path can cross its target and create a distance corner. The corrected upper-right-slope/integrated formulation is proved.
- **Talagrand definition:** supplement 614–620 takes a redundant infimum over the starting state. Keep that state fixed; take the infimum only over minimizers. `RegularFlowTalagrand` proves the intended distance bound from actual density equations and characteristic velocities by flow length, using xLSI without A3.
- **Cauchy/minimizer argument:** supplement 673–685 must use an actual Cauchy flow sequence with minimizing energies. R6 supplies a complete admissible domain and proved energy lower semicontinuity.
- **Empirical coupling:** supplement 781 equates pairwise sample cost and $W_2$ without optimality. Use an actual fixed-time optimal coupling, or the explicitly coupled synchronous integral dynamics. Different data need not have identical posterior laws.
- **Spatial initialization and moments:** supplement 786–837 uses matched initial states and uniform score moments without stating them. R7 exposes them; empirical fluctuations are then derived.
- **Temporal order and noise indices:** supplement 841–852 writes an extra $\sqrt h$ factor, accidentally yielding $O(h)$. The corrected generic order is $O(\sqrt h)$, with Brownian coordinates indexed by both datum and particle and stable steps.
- **Minibatch temperature:** main 232–258 combines inverse-inclusion drift with variance $2hB/M$ noise on every particle. Its temperature differs from the full-batch scheme. `BatchAudit` proves the exact Gaussian second-moment counterexample and two consistent scalar repairs.
- **Concise loss sign:** main 222–228 alternates $\log p_\phi-\mathcal L_D$ and its negative while using descent. Use the loss $\mathcal L_D-\log p_\phi$ consistently.
- **Annealing/adaptive signs:** supplement 266–279 has an inconsistent diffusion-loss sign; supplement 291–328 uses an ascent sign for momentum tracking the positive loss gradient and an incorrect particle index. The printed practical algorithm is a different scheme from the full-batch source theorem.
- **Gaussian formulas:** supplement 63–66 needs conditional variance $\beta_k(1-\bar\alpha_{k-1})/(1-\bar\alpha_k)$. At supplement 85 the reconstruction denominator is $\sqrt{\bar\alpha_k}$. The terminal KL at line 78 is $\frac12[\bar\alpha_K\|z_0\|^2-d_z\bar\alpha_K-d_z\log(1-\bar\alpha_K)]$. The final decoder variances in lines 73 and 79 must agree, and the main reverse variance $\beta_k^2$ and supplemental convention $\beta_k$ must be reconciled.
- **Random diffusion time:** supplement 93–99 needs a factor $K$ on a uniformly selected summand when estimating the declared *sum*. The separate terminal term is not multiplied. `SourceResults` proves the exact finite-uniform-mean correction.

## Separate new theory

Part II retains explicit N1–N7 and theorems for oracle noise, finite-population minibatch variance, tilt-model bias and concrete accuracy allocations. These are additions relative to the supplied manuscript. The practical Adam/preconditioned/momentum algorithm is not silently identified with the proved fixed-step full-batch recursion.

`MainResults.particle_oracle_parameter_bound` bounds the actual lifted Euler parameter error by initialization, finite-cloud fluctuation, drift consistency, Brownian modulus and centered oracle terms. `Accuracy.budget_le_epsilon` gives division-free sufficient particle/step/burn-in choices. The centered oracle hypotheses specify the extension's sampling interface; they are not source assumptions A1–A4 or blue regularity needed to repair the paper results.

## Verification

```text
lake build LatentDiffusion
python3 scripts/verify-latent-diffusion.py --lean --require-source-complete
python3 docs/test_latent_diffusion_landing.py
python3 docs/build_latent_diffusion.py --check
```

The generated statement-check file invokes actual imported Lean proof constants. Exact source hashes, quoted TeX and formal declaration references are checked independently of reader-facing coverage, colours and ordering.
