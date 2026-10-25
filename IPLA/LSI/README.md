# IPLA under a lifted log-Sobolev inequality

Read the [proof page](exposition/index.html) for the standalone theorem,
its mathematical proof, and the corresponding Lean declarations. The
[source archive](exposition/proof.html) also retains the reusable interpolation
data interfaces.

Let $N>0$, and write the scaled state as
$z=(\theta,x_1/\sqrt N,\ldots,x_N/\sqrt N)$. Define

$$
V_N(z)=\sum_{i=1}^N U(\theta,\sqrt N z_i),\qquad
D_N=d_\theta+Nd_x,\qquad \Pi_N\propto e^{-V_N}.
$$

Assume $U$ is differentiable with $L$-Lipschitz gradient, the normalized joint particle
target $\Pi_N$ satisfies LSI with constant $\beta>0$, and the initial
probability law has finite joint KL, $H_0=\operatorname{KL}(\mu_0\Vert\Pi_N)<\infty$.
For

$$
0<\gamma\le\frac{\beta}{4NL^2},
$$

the Gaussian IPLA distributions have finite KL at every step and satisfy

$$
H_k\le e^{-\beta\gamma k/N}H_0+
  \frac{8\gamma N D_N L^2}{\beta}.
$$

[`particle_kl_bound_of_finite_kl`](UnconditionalTheorem.lean) proves this
statement from these assumptions. The scaled system is exactly ULA for
$V_N$ with step $\gamma/N$ and smoothness $NL$. The shared ULA development
constructs its Gaussian density, differentiates its entropy, proves the
bound at the initial time and gradient moments, and derives the inequality
between the LSI and smoothness constants. No interpolation data, entropy recurrence, extra
moment, or compatibility premise is required. Zero-dimensional state spaces
are handled separately by equality of their probability laws.

If the joint particle target has LSI constant $\beta=N\alpha$, then
[`particle_kl_bound_linear_lsi_of_finite_kl`](UnconditionalTheorem.lean) gives

$$
\frac{H_k}{N}\le e^{-\alpha\gamma k}\frac{H_0}{N}
 +\frac{8\gamma L^2}{\alpha}
   \left(d_x+\frac{d_\theta}{N}\right),\qquad
0<\gamma\le\frac{\alpha}{4L^2}.
$$

The lifted-target LSI is the functional-inequality assumption. An LSI for one
parameter–latent pair does not by itself establish the $N\alpha$ scaling for
the system with a shared parameter. Parameter projection bounds its KL by
full joint KL; an estimate for $H_k/N$ therefore gives an unnormalized
parameter bound after multiplication by $N$. The parameter-marginal theorem also proves finiteness of its relative
entropy before stating a real-valued bound.

| Module | Content |
| --- | --- |
| [UnconditionalTheorem.lean](UnconditionalTheorem.lean) | Full joint, normalized, linear-LSI, and parameter-marginal bounds from finite initial KL and the joint particle target LSI. |
| [Scaling.lean](Scaling.lean) | Exact step, rate, dimension, forcing, and bias substitutions. |
| [Theorem.lean](Theorem.lean) | Particle distributions and identification of the Gaussian recursion; reusable theorems accepting regular interpolation data. |
| [Marginal.lean](Marginal.lean) | Parameter target, KL data processing, finiteness, and real bound transfer. |
| [Corollaries.lean](Corollaries.lean) | Parameter consequences through the reusable interpolation interface. |
| [Check.lean](Check.lean) | Kernel dependency audit. |

From the repository root, compile and audit locally:

```sh
lake build UnadjustedLangevin IPLA +IPLA.LSI.Check
lake env lean IPLA/LSI/Check.lean
```

The [page build guide](exposition/README.md) describes local regeneration and
source verification. GitHub Actions is not needed.
