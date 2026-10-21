# IPLA under a lifted log-Sobolev inequality

Read the [detailed proof page](exposition/index.html) for the full statement,
the coordinate reduction, the entropy calculation, and the exact Lean proofs.
This is a derivation in this repository from the shared ULA entropy result.

Let $N>0$ be the particle count, with independent parameter dimension $d_\theta$
and latent dimension $d_x$. In scaled coordinates
$z=(\theta,x_1/\sqrt N,\ldots,x_N/\sqrt N)$, define

$$
V_N(z)=\sum_{i=1}^N U(\theta,\sqrt N z_i),\qquad
D_N=d_\theta+Nd_x,\qquad \Pi_N\propto e^{-V_N}.
$$

Assume $U$ is differentiable with $L$-Lipschitz gradient, the **actual lifted
target** $\Pi_N$ satisfies LSI with constant $\beta_N>0$, and
$\beta_N\le NL$. The lifted gradient is $NL$-Lipschitz and IPLA is exactly ULA
for $V_N$ with step $\gamma/N$.

Under the explicit regular interpolation data of the shared ULA theorem, for
$0<\gamma\le\beta_N/(4NL^2)$, the actual Gaussian IPLA laws satisfy

$$
H_{\Pi_N}(\rho_k)
\le e^{-\beta_N\gamma k/N}H_{\Pi_N}(\rho_0)
  +\frac{8\gamma N D_N L^2}{\beta_N}.
$$

The theorem proves finite actual KL before using its real value. Dividing
the full joint entropy by $N$ gives the per-particle version. If the lifted
target has the admissible LSI constant $N\alpha$, with $0<\alpha\le L$, this is

$$
\frac{H_{\Pi_N}(\rho_k)}{N}
\le e^{-\alpha\gamma k}\frac{H_{\Pi_N}(\rho_0)}{N}
 +\frac{8\gamma L^2}{\alpha}
   \left(d_x+\frac{d_\theta}{N}\right),\qquad
0<\gamma\le\frac{\alpha}{4L^2}.
$$

**Status and scope.** The coordinate reduction, scaling, Gaussian law
identification, and KL projection inequalities are proved. The entropy
endpoint remains conditional on the explicit density, weak-equation,
drift-energy and gradient-moment inputs in
[`RegularInterpolationData`](../../UnadjustedLangevin/LSI/InterpolationData.lean).
No entropy recurrence or convergence bound is a field of that structure.
Constructing all these inputs from LSI and smoothness alone remains unfinished
in the shared ULA development.

An LSI for one parameter–latent pair is not the lifted-target hypothesis of
this theorem. The shared parameter prevents a direct product tensorization;
in particular, the development does not infer the scaling $N\alpha$ from a
pair-target LSI. Parameter projection bounds its KL by the **full** joint KL.
Consequently, using a per-particle bound for unscaled parameter KL requires
multiplication by $N$. This result asserts no concentration around an
optimizer or marginal-likelihood maximizer.

| Module | Content |
| --- | --- |
| [Scaling.lean](Scaling.lean) | Step restrictions, rates, biases, dimensions and one-step forcing after the exact IPLA substitutions. |
| [Theorem.lean](Theorem.lean) | Actual particle laws, Gaussian implementation identity, finite KL and conditional entropy bounds. |
| [Marginal.lean](Marginal.lean) | Actual parameter target, extended KL data processing, finiteness and real bound transfer. |
| [Corollaries.lean](Corollaries.lean) | Parameter-marginal consequences of the particle entropy theorem. |
| [Check.lean](Check.lean) | Kernel dependency audit. |

```sh
lake build UnadjustedLangevin IPLA +IPLA.LSI.Check
lake env lean IPLA/LSI/Check.lean
```

The [page build guide](exposition/README.md) describes regeneration and source
verification.
