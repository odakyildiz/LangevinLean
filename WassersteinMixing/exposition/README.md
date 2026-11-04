# Wasserstein mixing proofs and source correspondence

The [standard proof overview](index.html) pairs mathematical statements with exact Lean headers. Supporting pages give every local declaration with its mathematical proof and a separate account of the formal proof. The complete report uses the shared three-chapter format and report identity LL-11; the homepage contribution number is 10.

The supplied manuscript is `papers/Wasserstein_mixing/main.tex`. Its title and authors correspond to [arXiv:2608.02430v1](https://arxiv.org/abs/2608.02430v1). The [reference audit](reference_audit.json) records exact local source hashes, every label and all four numbered statements.

Theorem 1 and both assertions of Corollary 1.1 are proved under the paper's original Assumption 1.1 alone: $V\in C^2(\mathbb R^d)$ with $\alpha I\preccurlyeq\nabla^2V\preccurlyeq\beta I$, $0<\alpha\le\beta$ and $0<h\le1/\beta$. The conclusions concern the actual Gibbs law, the ordinary independent-Gaussian ULA iterates and the constructed ULA invariant law, with the source constants $6$, $12$ and $2$. The stationary Brownian diffusion, its reversible Markov semigroup, the bounded Poisson corrector, the conditional defect mean, the averaged Hessian, the synchronous comparison, the invariant law and the transport triangle inequality are all proved; none is a hypothesis.

The proof differs from the paper's in one respect. The paper builds its corrector by spectral calculus under the temporary Assumption 2.1 and removes that assumption by Gaussian smoothing. Here the corrector is the strong limit of the increasing operator sums $\sum_{n<N}P_{nh}\int_0^h(I-P_s)\,ds$ of the reversible semigroup, which exists directly under $C^2$ regularity. The eigenbasis construction and the smoothing limit are therefore not formalized.

The real-valued endpoints use the real value of an extended Wasserstein distance. The finiteness of each distance involved is proved separately from the second moments of the Gibbs law, the invariant law and the initial law.

The [IPLA application](ipla.html) applies the sharp bias to Project 03's particle recursion. Its main statements, in `WassersteinMixing/IPLATheorem.lean`, use the binders of `IPLA.theorem1` and write the bound out in full:

$$\Bigl(\mathbb E\|\theta_k-\theta_\star\|^2\Bigr)^{1/2}\le\sqrt{\frac{2d_\theta}{Nm}}+(1-m\gamma)^kW_2(\mu_0,\Pi_N)+\frac{6L}{\sqrt m}\sqrt{d_x+\frac{d_\theta}N}\,\gamma,$$

for a $C^2$ joint potential, $\gamma>0$ and $\gamma L\le1$. When $L>0$,
the latter condition is equivalent to $\gamma\le1/L$. In nonzero joint
dimension, strong convexity and gradient Lipschitzness imply $L\ge m>0$.
If both dimensions are zero, the state space is a point and the parameter
error is zero for every admissible positive step, including when $L=0$.
The explicit accuracy step and iteration count are needed only in the
nonzero-dimensional case; the zero-dimensional conclusion holds directly.

Verify locally:

```sh
lake build WassersteinMixing
lake env lean WassersteinMixing/Check.lean
python3 scripts/verify-wasserstein-mixing.py --require-complete
python3 docs/build_site.py --check
python3 docs/verify_site.py
```

Review and verification run locally before a reviewed snapshot is published from
`main` to `gh-pages`. Reference manuscripts are excluded from the website.
