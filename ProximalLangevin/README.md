# Proximal interacting particle Langevin algorithms

Read the [dedicated proof page](exposition/index.html) for the mathematical
results, exact Lean proofs, and a comparison of the proved results and corrections
with the source version for *Proximal Interacting Particle Langevin Algorithms*,
[arXiv:2406.14292v3](https://arxiv.org/pdf/2406.14292v3). The supplied 46-page
v3 PDF is authoritative; the original request linked v1.

**Status: partial paper formalization.** Corrected finite-time MYIPLA, PIPGLA
and MYPGD theorems are proved for the Gaussian algorithms, from the displayed assumptions on the
potentials, step sizes, initialization, and innovations. Their rates or constants differ from the printed statements.
The proof also gives mean-field integral equations with solutions continuous
in L², a smoothing comparison, and convergence from independent particle
initializations. The exact published formulas,
expected path-supremum bounds and PDE claims remain unproved; the page
records the distinction for each result.

## Proved MYIPLA theorem

Let $g_1$ be differentiable and $\mu$-strongly convex with an
$L_1$-Lipschitz gradient, with $\mu>0$. Let $g_2$ be a finite real-valued,
convex, lower-bounded, $K$-Lipschitz function. Define the Moreau envelope
and smoothed potential by

$$
g_2^\lambda(v)=\min_w\left\{g_2(w)+\frac{\|w-v\|^2}{2\lambda}\right\},
\qquad U_\lambda=g_1+g_2^\lambda,\qquad L_\lambda=L_1+\lambda^{-1}.
$$

For $N>0$, $\lambda>0$ and $0<\gamma\le 2/(\mu+L_\lambda)$, the
Gaussian MYIPLA recursion satisfies

$$
\begin{aligned}
\left(\mathbb E\|\theta_k-\bar\theta_\star\|^2\right)^{1/2}
\le{}&\sqrt{\frac{\lambda K^2}{\mu}}
 +\sqrt{\frac{d_\theta}{N\mu}}
 +(1-\mu\gamma)^k W_2(\rho_0,\Pi_{N,\lambda})\\
 &+\frac{33}{20}\frac{L_\lambda}{\mu}
       \sqrt{d_x+\frac{d_\theta}{N}}\sqrt\gamma .
\end{aligned}
$$

Here $\bar\theta_\star$ maximizes the **original latent marginal integral**,
$\Pi_{N,\lambda}$ is the defined lifted smoothed Gibbs target, and $\rho_0$
is the initial law in scaled particle coordinates. Initialization has finite
second moment; the innovations are independent standard Gaussians, independent
of initialization. The source states these distributional premises explicitly.
Output moments, target normalization, stationarity and concentration are
derived. No LSI or entropy-interpolation data are assumed.

The finite smoothing estimate is a proved replacement for the paper's
Taylor-based $O(\lambda)$ distance estimate, with a weaker $O(\sqrt\lambda)$
rate. Its proof derives $0\le U-U_\lambda\le\lambda K^2/2$, transfers this to
the negative log marginal integrals, and uses strong convexity. It does not
disprove the paper's claimed final rate. The discretization constant retains
its explicit dependence on $\lambda$; a uniform constant is not asserted.

## Proved PIPGLA replacement

Under the same potential assumptions, with $0<m\le L_1$,
$0<\gamma\le2/(m+L_1)$ and any positive proximal parameter $\lambda$, the
PIPGLA recursion satisfies

$$
\begin{aligned}
\left(\mathbb E\|\theta_k-\bar\theta_\star\|^2\right)^{1/2}
\le{}&\frac{K|\lambda-\gamma|}{m\gamma}
 +\sqrt{\frac{\gamma K^2}{m}}+\sqrt{\frac{d_\theta}{Nm}}\\
 &+\sqrt{(1-m\gamma)^k W_2(\rho_0,\Pi_{N,\gamma})^2
           +\frac{\gamma}{N}C_N}.
\end{aligned}
$$

Here $C_N$ is an explicit finite constant independent of $\gamma$, defined in
[SplittingEndpoint.lean](SplittingEndpoint.lean). The proof constructs a
stationary Brownian reference, derives orthogonality from independence and
adaptedness, proves the recurrence for the distributions, and takes the coupling infimum.
It assumes neither stationarity nor a convergence bound. The final theorem is
[pipgla_parameter_rms_original](SplittingTheorem.lean).

For the paper's parameter range $\gamma\le\lambda\le\gamma/(1-m\gamma)$ with
$m\gamma<1$, the sensitivity term is at most $K\gamma/(1-m\gamma)$,
including the upper endpoint. The other bias terms are $O(\sqrt\gamma)$ at
fixed dimensions and particle number. This is a complete alternative proof
with conservative constants; the paper's exact heat-flow formula is not
claimed.

## Proved MYPGD replacement

MYPGD sets the parameter noise to zero and retains the latent Gaussian noise.
Coupling it with MYIPLA using the same latent increments gives

$$
W_2(\rho_n^{\mathrm{MYPGD}},\rho_n^{\mathrm{MYIPLA}})^2
\le \frac{2d_\theta}{Nm}.
$$

Consequently, the MYIPLA bound relative to the original marginal maximizer plus
$\sqrt{2d_\theta/(Nm)}$ also bounds the MYPGD parameter root-mean-square error.
The theorem requires $m\le L_\lambda$ and the same smoothing-compatible time
step. Its source is [MYPGDTheorem.lean](MYPGDTheorem.lean).
This is a conservative finite-particle replacement for Theorem B.1, with an
initial term measured by Wasserstein distance to the Gibbs distribution. The paper's mean-field metric and constants are
not reproduced, and no propagation-of-chaos estimate is assumed.

## Other proved components and remaining work

- Proximal minimizer existence, uniqueness, optimality and firm
  nonexpansiveness; Moreau envelope convexity, $C^1$ regularity, gradient and
  $1/\lambda$ smoothness; the sharp $\lambda K^2/2$ value gap.
- Full-envelope strong convexity $\mu/(1+\mu\lambda)$.
- Sharp Gibbs concentration $\mathbb E\|X-x_\star\|^2\le d/\mu$ for
  continuous strongly convex potentials, including nonsmooth potentials.
- Explicit particle algorithm definitions and Gaussian MYIPLA law
  identification, with finiteness of the transport and projected moments.
- The original-potential proximal energy inequality and its averaged
  particle version, replacing the invalid identification of an averaged
  pairwise proximal map with the proximal map of a lifted sum.
- Pathwise PIPGLA stability: two runs with the same innovations contract
  at the smooth forward-step rate. The bound on changes in the proximal parameter
  extends the stochastic equal-step theorem to arbitrary positive parameters.
- Integrability of the averaged mean-field drift and a corrected $W_2$ Lipschitz
  estimate, using $L_1+1/\lambda$ for split smoothing. This is weaker in metric
  than the source's $W_1$ statement.
- Constructed continuous L² mean-field integral equations, with deterministic
  parameter evolution and Brownian noise in the latent coordinates; a finite smoothing comparison
  $\sup_{t\le T}\|Y_t^\eta-Y_t\|_2\le C_T\eta$ under the stated additional
  smoothness assumptions.
- Particle and mean-field processes with independent identically distributed initializations with a derived
  $N$-independent coefficient and tagged error $C_T/\sqrt N$, both in the supremum over time of the L² norms
  and in $W_2$ at each fixed time. Initialization, independent
  Brownian paths, empirical force variance and parameter-noise scale are
  constructed, rather than assumed. The C.2 process norm is different
  from the source's expected path supremum; neither bound generally implies
  the other.
- Exact scalar splitting recurrence, the strict contraction condition and
  the finite-sum formula at the boundary of the contraction range. These are conditional scalar results.
- Algebraic proofs of selected errors in the printed
  proof, with their scope distinguished from counterexamples to final rates.

The paper's exact heat-flow entropy/KL route is not reproduced by the new
PIPGLA proof. The mean-field results do not establish pathwise strong-SDE
versions or the gradient-flow PDE. A separate PIPULA theorem proves a finite-time smoothed-center
bound, but its conservative discretization coefficient diverges as the step
shrinks, so it does not reproduce the source's rate relative to the original marginal maximizer.
A separate consistency theorem shows that global Lipschitzness of the full
potential and a positive proximal-residual strong-monotonicity modulus cannot
both hold in positive dimension. This qualifies one literal reading of the
PIPULA assumptions; it does not refute all readings of Corollary A.6.
The audit also records an iteration-count error in Table 1: the PIPGLA
transient requires an inverse-step factor $1/\gamma$, absent from the listed
essentially logarithmic count. This is a consequence of the printed theorem,
not an algorithmic lower bound or a formalized iteration-count theorem.
Extended-real indicator penalties from some experiments are outside the
finite-valued assumptions used here.

## Module guide

| Files | Purpose |
| --- | --- |
| `Proximal`, `Moreau`, `StrongMoreau` | Proximal minimizers, envelope calculus and sharp constants. |
| `Algorithms`, `MYIPLA`, `Theorem` | Exact MYIPLA identification and original-model theorem. |
| `Perturbation`, `ProjectionCenter`, `SharpConcentration`, `SharpIPLA` | Marginal center shifts, finite moment transfers and sharp concentration. |
| `SplittingLaw`, `SplittingGaussianLaw`, `ProxParameter` | PIPGLA distributions, Gaussian law transfer and parameter sensitivity. |
| `SplittingMoments`, `ParticleSmoothing`, `SplittingOrthogonality` | Smoothing-uniform drift moments and derived Brownian orthogonality. |
| `SplittingCoupling`, `SplittingL2Energy`, `SplittingProcess`, `SplittingCrossEnergy`, `SplittingOneStep` | Proximal energy and integral-equation coupling estimates. |
| `SplittingCanonical`, `SplittingTransport`, `SplittingRate`, `SplittingEndpoint`, `SplittingProjection`, `SplittingTheorem` | Constructed stationary coupling, transport recurrence and final PIPGLA theorem. |
| `MYPGDNoise`, `MYPGDTransport`, `MYPGDAlgorithm`, `MYPGD`, `MYPGDTheorem` | Exact removal of parameter noise, Gaussian distribution comparison and MYPGD bound relative to the original maximizer. |
| `PIPULA`, `PIPULAConsistency` | Full-envelope finite-time bound and qualified assumption-consistency theorem. |
| `MeanFieldDrift`, `MeanFieldProcess`, `MeanFieldSmoothing` | Averaged drift, constructed continuous L² equations and finite smoothing comparison. |
| `MeanFieldVariance`, `MeanFieldCopies`, `MeanFieldParticleDrift`, `MeanFieldForcing`, `MeanFieldParticles` | Exact iid variance, physical particle equations and derived finite-horizon particle limit. |
| `MeanFieldNoise`, `MeanFieldBrownianFamily`, `MeanFieldInitialSource`, `MeanFieldCanonical`, `MeanFieldParticleLaw` | Independent initialization and Brownian inputs; tagged-particle L² bounds and Wasserstein bounds at fixed times. |
| `Recurrence`, `Corrections` | Conditional scalar algebra and algebraic proofs of corrections. |

## Build

```sh
lake build ProximalLangevin +ProximalLangevin.Check
lake env lean ProximalLangevin/Check.lean
python3 ProximalLangevin/exposition/verify_document.py
```

Lean and Mathlib use the repository's existing pinned versions. All downloaded
dependencies and build artifacts stay in the ignored `.lake/` directory.

The [page guide](exposition/README.md) describes regeneration.
