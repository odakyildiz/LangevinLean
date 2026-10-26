# Latent diffusion: source, assumption and algorithm audit

The audited source is **Training Latent Diffusion Models with Interacting Particle Algorithms**, Tim Y. J. Wang, Juan Kuntz and O. Deniz Akyildiz, in `papers/Latent_diffusion/main_aistats.tex`, including `supp_aistats.tex`. The machine-readable inventory in `reference_audit.json` preserves the exact TeX, line locations and source hashes. There are **19 theorem/proposition/lemma environments**: 3 main statements and 16 supplementary statements. There are no corollary environments. Appendix repetitions of the main convergence and error statements are included in that count.

The paper already states a nonasymptotic error estimate for its **full-batch, exact-gradient Euler–Maruyama** scheme. Its gap is an implicit-constant bound and the absence of guarantees for the practical mini-batch, reweighted, annealed and adaptive scheme. Main-source lines 312–314 explicitly acknowledge this restriction. New results must identify which actual scheme they concern.

This document inventories source claims and explains the correspondence limits. It is not a declaration that every continuum optimal-transport, entropy or SDE result below has been independently reconstructed from the four displayed source assumptions. The statement page and Lean check file identify precisely the proved declarations and any additional hypotheses. A theorem with an explicit analytical interface does not establish that interface from the paper's raw assumptions.

The achieved source correspondence is precise: `Variational.lean` proves the optimizer/minimizer equivalence for the normalized minus-log-evidence plus actual KL formulation on its admissible domain; `Density.lean` now proves identification with the actual raw log-density integral from explicit density normalization and entropy-integrability hypotheses. `Marginal.lean` proves existence and uniqueness of the heterogeneous finite-dimensional marginal optimizer from joint differentiability and strong convexity, using actual marginal integrals. `Flow.lean` and `Marginal.lean` prove the sharp parameter exponential rate conditional on entropy dissipation and first-order transport control. They do not derive those continuum analytic bridges from the source density assumptions or reconstruct the full-state Wasserstein result. The remaining source analytic lemmas are individually marked unverified in `reference_audit.json`. New explicit numerical estimates retain their stationary-reference, moment and oracle-centering hypotheses.

## Setting and four displayed source assumptions

The data are `x¹,…,xᴹ`; `u=(θ,φ)` contains prior and decoder parameters; each datum has a latent law `qᵐ`. The Gaussian decoder is `pφ(x|z)=N(x;gφ(z),σ²I)` and the prior is a Gaussian reverse DDPM. The fixed forward path law is `Q(dz₁:K|z₀)`. The penalty is

\[
R(\theta,z)=\mathrm{KL}(Q(\cdot\mid z)\Vert P_\theta(\cdot\mid z)),\quad
\widetilde p_u(x,z)=p_u(x,z)e^{-R(\theta,z)}.
\]

The averaged tilted free energy is `F̃(u,q)=M⁻¹∑ₘ∫log(qᵐ/p̃u(xᵐ,·))dqᵐ`; the parameter metric is Euclidean and the law metric is `M⁻¹∑ₘ W₂(qᵐ,q′ᵐ)²`. This normalization matters: it prevents an artificial factor `M` in the contraction constant.

1. **A1, model regularity** (`main_aistats.tex:143–150`): for every latent point, the normalized tilted posterior and its normalizing constant are differentiable in parameters; each posterior is twice continuously differentiable in the latent variable; the unnormalized tilted density is everywhere strictly positive. Finiteness and positivity of the normalizing integral are needed to make “normalized posterior” meaningful. The displayed assumption does not explicitly require jointly continuous derivatives, entropy integrability, or continuity of `R` separately.
2. **A2, solution regularity** (`main_aistats.tex:151–154`): from every state in the product space, a classical global flow exists; parameters are `C¹` and law densities are `C^{1,2}([0,∞)×Z)`. Literally this is too broad: arbitrary `P₂` initial laws include Dirac laws, and even restricting to absolutely continuous laws (as the appendix does at `supp_aistats.tex:436`) includes discontinuous uniform densities. They cannot have a continuous density at time zero. The actual Dirac obstruction is checked in `SourceObstruction.lean` by `not_solutionRegularity_of_null_singleton` and `not_solutionRegularity_of_noAtoms`: time-zero density would make a Dirac law absolutely continuous, contradicting a null singleton. A usable version restricts the initial state to the required smoothness class, or requires smoothing only for positive time and continuity in `W₂` at zero. This is an explicit repair, not a consequence of the displayed quantification.
3. **A3, strong log-concavity** (`main_aistats.tex:155–157`): for every datum `x`, the tilted joint density is `λ`-strongly log-concave jointly in `(θ,φ,z)`, with `λ>0`. This is a global hypothesis in parameter coordinates; ordinary neural-network parameterizations with symmetries need not satisfy it. It is an assumption, not an assertion about the trained experimental networks.
4. **A4, Lipschitz gradient** (`main_aistats.tex:200–207`): each tilted joint log-density has a jointly `L`-Lipschitz gradient. The supplementary restatement at `supp_aistats.tex:753–759` omits the tilt in its density notation. The main error theorem additionally requires Lipschitz gradients of `R`; the main displayed A4 already concerns the tilted log-density, so one should not silently replace it with an untilted assumption.

Second moments alone do not imply finite positive entropy, finite Fisher information, differentiation under entropy integrals, or vanishing boundary terms. Continuum proofs must supply the appropriate integrability and approximation arguments. In particular, smoothness alone is not a license for the integration by parts at `supp_aistats.tex:503–524`.

## Complete result inventory

The labels below are stable identifiers; the shared theorem counter is reset at section boundaries.

| Source location | Label / result | Stated dependencies and conclusion | Audit / formal scope |
|---|---|---|---|
| main 104–105 | `prop:ftildemins` | Parameters maximize `ℓ̃` iff they are parameter components of a global `F̃` minimizer. | Gibbs/KL variational identity. Requires positive finite normalizers, admissible normalized tilted posteriors, and the appropriate extended-integral conventions. It does not identify the maximizers of the untilted likelihood. |
| main 158–166 | `thm:exp_convg_informal` | A1–A3 give a unique maximizer and parameter error at most `sqrt(2(F̃₀−F̃*)/λ)e^{−λt}`. | The principal continuous-time claim. Requires the analytic prerequisites used in the appendix, with regularity A2 interpreted consistently. |
| main 208–212 | `thrm:error-bound` | A1–A4 and Lipschitz `∇R` give RMS parameter error `C_{h,N}+Cρᵀ`, with `C_{h,N}=O(√h+N^{-1/2})`. | Only exact-gradient full-batch Euler. `ρ` is permitted to depend on `h`; taking `ρ=e^{−λh}` makes physical time explicit. Constants also depend on initial moments and fixed model parameters. |
| supplement 188–199 | `app:lemma_1st_var` | Computes latent and parameter first variations of the free energy. | The latent variation is defined modulo constants on probability-density tangent directions; omitting `+1` uses `∫r=0`. Parameter differentiation requires a dominating integrable derivative or a justified replacement argument. |
| supplement 223–236 | unlabelled product-gradient proposition | Gives averaged Euclidean gradients and unaveraged Wasserstein gradients under the normalized metric. | The inverse Wasserstein metric contributes `M`, cancelling the objective's `1/M`. It rests on the first-variation and Otto-calculus interpretation, rather than proving that geometry from basic metric-space definitions. |
| supplement 488–493 | `prop:de_bruijin` | A2 gives `dF̃/dt=−I`. | Needs finite entropy/energy, differentiability under the integral, finite score work, and boundary or cutoff justification in addition to classical local smoothness. |
| supplement 531–543 | `lem:geodesic` | Product geodesics are Euclidean segments and Wasserstein displacement interpolations; absolutely continuous first marginals admit Brenier maps. | Standard finite-dimensional optimal transport, with constant-speed parameterization. A claim about arbitrary geodesics must retain endpoint/parameterization conventions. |
| supplement 548–554 | `lem:geodesic_convexity` | A3 implies `λ`-geodesic convexity of `F̃`. | Potential convexity combines with displacement convexity of negative entropy in the normalized product metric. Finite or extended free energies must be defined consistently. |
| supplement 568–575 | `lem:lower_deriv` | Lower bound for the initial geodesic derivative by the gradient pairing. | Requires the entropy subgradient/score domain and integrable pairings; only differentiability a.e. of a density does not make the pairing finite. |
| supplement 579–581 | `thm:sLC_implies_xLSI` | A1,A3 imply `2λ(F̃−F̃*)≤I`. | Uses the preceding transport derivative and a minimizer. An implementation must construct or assume admissible minimizers before choosing one. The Young-inequality step itself is elementary. |
| supplement 623–629 | `lem:distance_deriv` | A2 gives `d d_M(flow_t,state)/dt≤√I_t`. | The natural metric statement is an a.e. metric-speed bound; differentiability at every positive time, including zero-distance times, requires care. |
| supplement 656–658 | `lem:lower_semi_continuous` | `F̃` is lower semicontinuous on the differentiable-density domain. | Its proof separately assumes `R≥0` and joint continuity of `R` (`supplement:665`), which is not an explicit displayed source assumption. The density-only/differentiable-density subspaces are not complete in `W₂`. |
| supplement 673–679 | `lem:cauchy` | Under xLSI, a stated Cauchy sequence yields a flow subsequence converging to a minimizer. | As written, the initial Cauchy sequence is unrelated to the flow subsequence. The proof actually needs a Cauchy **flow** sequence whose free energies tend to `F̃*`. Completeness of all `P₂` does not by itself retain a density in the limit. |
| supplement 688–690 | `thm:xLSI_implies_xTalagrand` | xLSI implies the extended Talagrand inequality. | Section-wide A1,A2 and the prior metric-speed/lower-semicontinuity statements are used. The displayed definition `defn:xTalagrand` at 614–620 contains a redundant infimum over the starting state, making its literal right side zero whenever an optimizer exists; the intended statement is distance from the **given** state to the minimizing set. |
| supplement 714–724 | `thm:exp_convg_appendix` | A1–A3 give uniqueness and full-product distance `≤sqrt(2(F̃_t−F̃*)/λ)≤sqrt(2(F̃₀−F̃*)/λ)e^{−λt}`. | Full version of the main continuous statement. It invokes the variational identity, xLSI, de Bruijn, Talagrand and existence/uniqueness of a minimizer. |
| supplement 767–773 | `lem:cont-time-convg` | A1,A3,A4 give a unique strong mean-field solution and exponential comparison of empirical clouds to target clouds. | The asserted comparison needs a specified optimal or synchronous coupling, not arbitrary independent fixed target samples. The proof's last equality at 781 identifies coupling cost with Wasserstein distance, which requires optimality and is not automatic. “i.i.d.” at 766 only holds across particles for a fixed datum, not across distinct data with different potentials. |
| supplement 786–797 | `lem:spatial_discretization` | A3,A4 give strong finite-particle solutions and uniform RMS error `O(N^{-1/2})`, independent of time and `M`. | Requires matched initial coupling and uniform reference second moments/gradient variance. The proof assumes zero initial coupling error at 837, though the lemma statement does not state it. The displayed constant uses one `Z₀`; heterogeneous initial laws require a uniform or averaged replacement. |
| supplement 841–852 | `lem:temporal_discretization` | A3,A4, `h≤1/(λ+L)` give a uniform-in-step Euler error. | Printed statement says `C(h)=O(√h)` **and** error `≤√h C(h)`, inadvertently asserting `O(h)`. The main theorem and claimed imported argument support `C(h)=O(1)` in this display for an `O(√h)` conclusion. The particle-noise index `W_k^n` omits `m`. |
| supplement 857–861 | `thrm_app:error-bound` | Same full-batch parameter bound as main 208–212. | Triangle combination of the three preceding comparisons. It does not extend to mini-batches or adaptive preconditioning. |

## Algorithm audit and proved scalar correction

### The mini-batch temperature is different from the full-batch temperature

Let `p=B/M` be the inclusion probability of one datum in a uniform fixed-size batch. For its particle, Algorithm 1 (`main_aistats.tex:234–258`) applies the gradient step only on selection, with amplitude `h/p`, but adds noise of variance `2hp` to **every** particle. Consequently the drift is unbiased, while the noise variance is `p` times the intended full-batch variance. The sentence claiming variance matching at main line 232 is incorrect under the displayed pseudocode.

This is already observable for the one-dimensional potential `U(x)=a x²/2`. The exact conditional second moment, integrating a genuine standard Gaussian, is

\[
\mathbb E[X_{k+1}^2\mid X_k=x]
=q_p x^2+2hp,\qquad q_p=1-2ah+a^2h^2/p.
\]

Its affine moment fixed point is

\[
v_p=\frac{p}{a(1-ah/(2p))},\qquad
v_k=v_p+q_p^k(v_0-v_p).
\]

These are proved in `LatentDiffusion/BatchAudit.lean` by `paperConditionalSecondMoment_eq`, `paperStationaryMoment_fixed`, and `paper_moment_all_iterations`. The denominator and step assumptions are explicit. “Fixed point” here means a fixed second moment, not an unproved claim that the full chain is Gaussian or that a nonlinear chain has an invariant law. For `p=1/2,a=1,h=1/4`, the source changes target second moment `1` to `7/8` in one step, and its second-moment fixed point is `2/3`; `paper_half_batch_counterexample` checks both exact values.

Two corrections, also checked by exact Gaussian integration, are:

* Retain inverse-inclusion drift and add full noise `sqrt(2h)W` to every particle. The coefficient stays `q_p`, the forcing is `2h`, and the moment fixed point becomes `1/[a(1-ah/(2p))]`. This retains a batch-dependent finite-step cost, but removes the temperature factor `p`.
* Update selected particles with **uninflated** drift `−h∇U` and selected noise `sqrt(2h)W`, leaving unselected particles fixed. Both drift and diffusion then advance at rate `p`. Its coefficient is `1−2pah+pa²h²` and its second-moment fixed point is `1/[a(1-ah/2)]`, the same as full-batch Euler.

The baseline full-batch Euler variance at temperature `τ` is `τ/[a(1-ah/2)]`; `euler_stationary_variance` proves this identity. Gaussian integration is proved from actual Gaussian moments, rather than supplied as an assumption.

### The practical adaptive algorithm is a further method

Supplement lines 291–303 use `+h_z G M` while `M` tracks the **positive gradient of the loss**, producing ascent for the stated loss unless the momentum sign is changed. The displayed loop at 312 uses `B×[M]` where `B×[N]` is required. Noise in the full algorithm is scaled by `1/M`, and line 303 reports an additional implementation factor `1/B`; neither is justified by the full-batch theorem. A state-dependent preconditioned Langevin sampler also generally requires a divergence correction to retain its claimed target, and momentum introduces an enlarged state and a different invariant-law problem. These features are not covered by an Euler contractivity theorem merely because the formulas use gradients.

### Additional source corrections

* Main lines 107–110 claim that zero tilt penalty at a tilted optimizer makes it an optimizer of the original likelihood. Equality of the two objectives at that one point does not imply this. For two parameter choices, likelihood values `(1,2)` and penalties `(0,log 4)` yield tilted likelihoods `(1,1/2)`: the tilted optimizer has zero penalty and is not a true optimizer. A sufficient condition is an original-likelihood optimizer with zero penalty (or a uniform zero penalty across the entire model).
* Supplement lines 63–66 write the forward conditional variance as `β_k I`; it should be `β_k(1−ᾱ_{k−1})/(1−ᾱ_k) I`. This discrepancy propagates to the displayed Gaussian KL expressions.
* The terminal Gaussian KL at supplement line 78 should be `[ᾱ_K‖z₀‖²−d_z ᾱ_K−d_z log(1−ᾱ_K)]/2`; the source squares the variance and has the wrong logarithm coefficient. Its retained `z₀`-quadratic term is nevertheless `ᾱ_K‖z₀‖²/2`.
* Supplement line 73 declares identity covariance for the final decoder, whereas line 79 uses covariance `(1−ᾱ₁)I`; the two likelihood formulas are inconsistent.
* The random-time estimator at supplement lines 93–99 samples `k` uniformly but omits the factor `K` multiplying the selected summand of the full diffusion-loss sum. It is not an unbiased estimator of the declared summed objective as written. The separately added terminal quadratic must not be inadvertently multiplied by `K`. The reweighted simple loss is an intentional change of objective, not an unbiased estimate of the exact diffusion loss.
* Main lines 222–226 define the concise loss with `Lᵐ=log pφ−L_D` but use a **descent** update. Equation 228 then uses the opposite sign `L_D−log pφ`. The full-batch equations 192–197 have the correct descent signs for the latter convention.
* The annealed Wasserstein-gradient display at supplement 266–273 has an inconsistent sign on `L_D` inside its bracket; the following SDE at 276–279 has the expected drift `∇log pφ−γ_t∇L_D` and noise `sqrt(2γ_t)`.

## Sensible extension scope

Useful rigorous additions distinguish optimization bias, finite-particle fluctuation, discretization error, stochastic-gradient variance, annealing drift and target mismatch. Global joint strong convexity with a Lipschitz gradient is a tractable first setting. Stronger time-uniform estimates can exploit additive noise and extra derivative regularity, while random-scan and preconditioned methods require their actual step maps and actual covariance. The exact mini-batch counterexample above is a substantive necessary correction before claiming target convergence for the practical algorithm.

`Lift.lean` derives the actual `L²` force from the pointwise force, including nonzero force at the origin, by centered Lipschitz composition and addition of a constant. It proves that the result agrees almost everywhere with `F(X)`, retains the same strong monotonicity and Lipschitz constants, and represents every pointwise Euler iterate. Its stochastic numerical consequence therefore does not assume an independently regular abstract force on random variables.

`MiniBatchVariance.lean` proves the heterogeneous orthogonal-family variance `‖K⁻¹∑gᵢ‖²=K⁻²∑‖gᵢ‖²≤V/K`; in `L²` this is the actual expected squared error, and orthogonality is a zero cross-moment condition. It also proves the exact without-replacement mini-batch identity

\[
\mathbb E\|\widehat g_B-\bar g\|^2
=\frac{M-B}{B(M-1)}\frac1M\sum_{i=1}^M\|g_i-\bar g\|^2.
\]

The theorem integrates on an actual finite discrete probability space. Its primitive sampling assumptions are batch cardinality and the first/pair inclusion probabilities `B/M` and `B(B−1)/(M(M−1))`, as occur for uniform fixed-size batches. The combinatorial construction of the uniform-subset distribution is not claimed by that interface. The conclusion is a derived oracle-variance formula, rather than an assumed numerical error or oracle-variance bound. A population dispersion bound `V` yields the explicit `oracleVariance M B V=((M−B)/(B(M−1)))V`.

No assertion of novelty against all published literature is made by the label “new”: it means newly added relative to the supplied latent-diffusion paper. No axiom, `sorry`, or assumed desired recurrence is used in the scalar mini-batch calculation.


## Explicit parameter budget and accuracy choices

`MainResults.particle_oracle_parameter_bound` is a theorem in namespace
`LatentDiffusion`. It bounds the actual parameter RMS error of the constructed
pointwise Euler recursion lifted to L². With K=M N its bound is

```text
E_n ≤ (1-mh/2)^n R0 + (2/m) sqrt(V/K)
      + (L/m)(hG + 4W sqrt(h)/3) + sqrt(h sigma²/m).
```

The reference is required to satisfy an actual integral equation, primitive
moment bounds and a fixed target parameter. Residual zero cross moments derive
the V/K variance. The oracle condition is trajectory-specific orthogonality to
the current Euler displacement; the code does not construct a filtration-based
conditional sampling scheme. No desired numerical error recurrence is assumed.
Constructing the intended frozen posterior reference and proving these moment
and orthogonality properties remain application obligations.

`Accuracy.budget_le_epsilon` allocates epsilon/5 to each term. It suffices that
log(max(1,5R0/epsilon))≤mhn/2, 100V≤m²epsilon²K,
5LhG≤m epsilon, 400L²W²h≤9m²epsilon², and
25h sigma²≤m epsilon², together with nonnegative constants, positive m,K,epsilon
and a nonnegative contraction factor. These division-free criteria cover zero
variance constants. Complexity interpretations additionally require constants
bounded independently of K and h.

`Marginal.tilted_parameter_bias` (also in namespace `LatentDiffusion`) proves
model-bias robustness: original evidence with rho-strongly convex negative,
a uniform one-sided error 0≤ell-tilted≤delta, and epsilon-approximate tilted
optimization give distance to the original maximizer at most
sqrt(2(delta+epsilon)/rho). The objective loss is delta+epsilon, not 2delta+epsilon.


## Actual density normalization bridge

`Density.density_freeEnergy_eq_kl` constructs the posterior probability
π=(ρ/Z)ν and trial probability q=(rρ/Z)ν, proves actual KL(q‖π) finite, and
identifies ∫log((rρ/Z)/ρ)dq with KL(q‖π)−log Z.
`density_weighted_freeEnergy_eq_kl` proves the literal base-density form
∫f log(f/ρ)dν=KL(q‖π)−log Z, including its integrability, for f=rρ/Z.
These are proved identities, not assumptions. Zero values of r are handled on
the trial law's almost-everywhere positive support.

The primitive hypotheses are measurable strictly positive integrable ρ,
Z=∫ρdν>0, measurable nonnegative r with ∫r dπ=1 and integrable r log r.
The source Proposition 1 is therefore linked to a genuine density-integral
identity on this explicit domain. This does not establish every extended-integral
or arbitrary-law version of the original statement, or derive this domain from
raw A1 alone; its full-reconstruction flag remains false.
