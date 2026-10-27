# Assumptions and supporting results for ULA and IPLA

The strongly convex Gaussian ULA theorem and IPLA Theorem 1 follow from their
displayed assumptions on the potential, step size, initialization, and Gaussian
innovations. The proofs establish normalization of the Gibbs measure, the
required moment and concentration bounds, and existence of a stationary
reference process.

The potential assumptions are differentiability, positive strong convexity,
and a globally $L$-Lipschitz gradient of the **same** potential $U$. For IPLA this
is the joint potential $U_y(\theta,x)$, with observations $y$ fixed. There is no separate
convexity or Lipschitz-gradient assumption on $\theta$, $x$, a marginal potential, or
any lifted particle potential. There is no Hessian or $C^2$ assumption on $U$.

## Convergence theorems and their assumptions

`ULA.Hilbert.dalalyan` and `dalalyan_large_step` in `CanonicalULA.lean` prove
both step-size cases of Dalalyan's bound for iteration of the Gaussian transition kernel. The
initial law is a probability measure with finite $W_2$ to Gibbs, and the
Euclidean dimension is finite and nonzero. The admissible step-size inequalities
are displayed in each theorem. Finite target and initial second moments,
finite output $W_2$, and compatibility $m\le L$ are derived.

`ULA.Hilbert.dalalyan_of_gaussian_innovations` and its large-step counterpart
in `GaussianULA.lean` apply to the actual `lpChain` on any probability space.
Their stochastic assumptions are as follows: every scalar noise
coordinate is standard normal, all iteration-coordinate pairs are independent,
and initialization is independent of the complete noise path. Grouping
the coordinates gives independent standard Gaussian vectors, and induction
identifies the distribution of the recursion with iteration of the transition
kernel. The initial random vector belongs to $L^2$, which implies finite initial $W_2$.

`IPLA.theorem1` in `IPLA/Theorem.lean` specializes this shared ULA theorem to
the actual scaled interacting-particle recursion. It uses joint strong
convexity and joint gradient Lipschitz regularity of $U_y(\theta,x)$, the displayed
positive dimensions/particle count and step regime, a marginal maximizer $\theta_\star$,
and `GaussianInnovations`. The fields of that structure are exactly the
Gaussian laws and independence just described. Existence of $\theta_\star$ is proved by
`IPLA.exists_marginalMaximizer`; the maximizer premise specifies which target
point is named in the bound. No reference-family or concentration premise
occurs in the final theorem.

## Supporting results proved from these assumptions

| Mathematical property | Checked result |
| --- | --- |
| $m\le L$ | `ULA.strongConvex_le_lipschitz` in nonzero dimension. |
| Gibbs normalization and second moment | `gibbsPartition_pos`, `gibbsPartition_ne_top`, `isProbabilityMeasure_gibbsMeasure`, and `memLp_id_gibbsMeasure`. |
| Initial second moment or finite initial $W_2$ | `TransportMoments.lean` proves both implications used by the endpoints. |
| Sharp score second moment | `ULA.integral_norm_sq_gradient_gibbs_le_of_strongConvex`. |
| Integrated generator and absolute integrability | `ULA.integral_laplacian_sub_gradient_gibbs_eq_zero` and the companion integrability results. |
| Gibbs Dirichlet form | `ULA.integral_langevinGenerator_dirichlet_gibbs`, including symmetry and dissipativity. |
| Canonical independent Brownian source | `CanonicalBrownian.lean`, from the proved Gaussian Hilbert-series construction. |
| Brownian $L^2$ continuity and exact increment norm | `brownianCoordinatesRealLp_continuous` and `brownianCoordinatesRealLp_increment_scaled_norm`. |
| Integral-solution existence and uniqueness | `exists_lp_langevin_integral_of_brownian` and `lp_langevin_integral_unique`, on every finite horizon. |
| Actual proposal density and Metropolis invariance | `gaussian_proposal_pair_density` and `malaOneStep_gibbs_invariant`. |
| Quantitative vanishing rejection error | `MALAError.lean` and `malaCoupledChain_distance_integral_le`. |
| Euler approximation of the actual integral solution | `lp_langevin_integral_euler_tendsto`. |
| Actual Gibbs stationarity | `ULA.lp_langevin_gibbs_stationary`, with its noise inputs discharged on the constructed product extension. |
| Segment consistency | `ULA.Hilbert.brownianSegments_eq_global`. |
| Complete reference for every initial coupling | `ULA.Hilbert.canonicalProductReference`. |
| Exact initial coupling and cost | `initialExtension_joint`, `initialExtension_independent`, and `initialExtension_lp_cost`. |
| Actual Markov law and independence of realization | `hilbert_lpChain_law_eq_ulaLawStep`, `MarkovLaw.lean`, and `GaussianInnovationVectors.lean`. |
| Exact initial $W_2$ term | The initial-coupling infimum in `ProductReference.lean`, with every reference constructed by `CanonicalULA.lean`. |
| IPLA marginal strong log-concavity | The proved Prékopa–Leindler, tensorization, and `StrongLogConcavity.lean` results. |
| IPLA parameter marginal and maximizer | `gibbsTarget_parameter_marginal` and `exists_marginalMaximizer`. |
| IPLA parameter radius | `IPLA.gibbsTarget_parameter_concentration`, giving $\sqrt{2d/(Nm)}$ from joint strong convexity. |

## Integration by parts and proof of stationarity

For compactly supported $C^2$ tests, `Generator.lean` proves

$$
\int (\Delta\varphi-\langle\nabla U,\nabla\varphi\rangle)\,d\pi=0.
$$

Integration by parts differentiates $e^{-U}$ only once. $U$ need not be $C^2$; the
$C^2$ condition is on the test function. `GeneratorDirichlet.lean` proves

$$
\int\varphi L\psi\,d\pi
 =-\int\langle\nabla\varphi,\nabla\psi\rangle\,d\pi,
$$

with all relevant integrability. `FokkerPlanck.lean` also proves that the
constant Gibbs curve satisfies its explicitly defined weak forward equation.
The final invariance proof does not assume that the constructed process solves
that weak equation or that the equation has unique solutions.

`MALAInvariance.lean` proves detailed balance for the
Gaussian Metropolis proposal. Under a Lipschitz gradient, `MALAError.lean`
proves expected rejected displacement at most $Ch\sqrt h$, with finite $C$ derived
from Gibbs and Gaussian moments. `MALACoupling.lean` compares $n$ ULA steps to
this stationary chain with expected distance at most $nCh\sqrt h$. For $h=T/n$
this tends to zero. `EulerLimit.lean` proves matching-noise Euler convergence
to the continuous Banach-space integral solution. `CouplingLimit.lean`
uses characteristic functions to identify that solution's law with Gibbs.
`GibbsStationarity.lean` applies these results to prove stationarity. The
argument uses the discrete invariant chains and their limit; it requires no
uniqueness assumption for the weak Fokker–Planck equation.

The conditional results for a given reference process or weak equation remain
available as separate lemmas. The final convergence theorems use the process
and stationarity established above.

## Representation and kernel checks

The continuous reference is a continuous $L^2$ curve satisfying a Bochner integral
equation. Its driving process has the Brownian finite-dimensional distributions
and independence properties used in the proof. All required moments follow
from this construction. The convergence theorem uses continuity in $L^2$ and
does not assume continuity of individual sample paths.

The source proof of Gibbs stationarity and the shared ULA convergence theorem
contain no imports from IPLA. IPLA imports and instantiates the shared ULA
results for its scaled joint potential.

```sh
lake build
lake env lean UnadjustedLangevin/Check.lean
lake env lean IPLA/Check.lean
python3 IPLA/build_artifacts.py
python3 IPLA/verify.py
```

The standalone IPLA file imports only Mathlib and contains the included
assumptions and all project proofs needed for its final theorem. The axiom
audits list only `propext`, `Classical.choice`, and `Quot.sound`. An axiom audit
is accompanied by inspection of the theorem's ordinary hypotheses; neither
check substitutes for the other.
