# Wasserstein mixing time of the unadjusted Langevin algorithm

Project 10 studies *Wasserstein mixing time of the unadjusted Langevin algorithm*, by Francesco Pedrotti and Peter A. Whalley. The supplied source is `papers/Wasserstein_mixing/main.tex`; the bibliographic reference is [arXiv:2608.02430v1](https://arxiv.org/abs/2608.02430v1), submitted 3 August 2026. The [proof overview](exposition/index.html) follows the shared mathematics-and-Lean template, with a complete report and a declaration directory.

The checked endpoints prove Theorem 1 and Corollary 1.1 from the paper's original Assumption 1.1: $V\in C^2(\mathbb R^d)$ and $\alpha I\preceq\nabla^2V\preceq\beta I$, with $0<\alpha\le\beta$ and $0<h\le1/\beta$. The [source audit](exposition/reference_audit.json) records the exact source correspondence and checks.

The proof constructs the actual stationary Brownian Langevin diffusion, its reversible strongly continuous contraction semigroup, and a bounded Poisson corrector from increasing operator sums. Whole-path independence and actual Euler limits establish the conditional Markov identity; reversible Gaussian Metropolis approximations establish self-adjointness. Real coordinate embeddings transfer the constructed corrector to the genuine gradient observable. The actual averaged Hessian, score increments, conditional defect mean and synchronous error equation are all derived from the potential.

The shifted-energy argument proves the forcing coefficient $19$ and final bias coefficient $6$. An independent contraction construction gives the actual Gaussian ULA invariant law and its attraction. The proved transport triangle then yields

$$W_2(\pi,\pi_h)\le6h\sqrt{\kappa\beta d},\qquad W_2(K_h^n\mu,\pi)\le(1-\alpha h)^nW_2(\mu,\pi_h)+6h\sqrt{\kappa\beta d},\qquad\kappa=\beta/\alpha.$$

The accuracy endpoint uses the source step $h=\beta^{-1}\min\{1,\varepsilon/(12\sqrt d)\}$ and iteration threshold $\kappa\max\{1,12\sqrt d/\varepsilon\}\log(1+2\sqrt\alpha\,W_2(\mu,\pi_h)/\varepsilon)$ to prove $\sqrt\alpha\,W_2(K_h^n\mu,\pi)\le\varepsilon$. Initial laws require the source finite second moment.

The source labels are Assumption 1.1, Theorem 1, Corollary 1.1 and Assumption 2.1. The paper introduces Assumption 2.1 temporarily for its smooth spectral argument and removes it by approximation. The formal proof works directly under the original twice continuously differentiable Hessian hypothesis through the actual semigroup construction. It needs no additional smoothness, spectral basis or realization assumption.

Verify locally:

```sh
lake build WassersteinMixing
lake env lean WassersteinMixing/Check.lean
python3 scripts/verify-wasserstein-mixing.py
python3 scripts/verify-wasserstein-mixing.py --require-complete
python3 docs/build_site.py --check
python3 docs/verify_site.py
```

The public endpoints are `WassersteinMixing.bias_bound`, `WassersteinMixing.convergence_bound` and `WassersteinMixing.accuracy_bound`. The native declaration notes explain every proof module, with exact source statements read directly from Lean during report generation.

Development and verification run locally. Reviewed snapshots are published from
`main` to `gh-pages` using the repository's publication workflow; reference
manuscripts remain on `main` and are excluded from the website.

## Application to IPLA

The [IPLA application](exposition/ipla.html) applies the sharp bias to the
actual scaled particle recursion of Project 03. Its main theorem,
`ipla_linear_step_bound`, uses the binders of `IPLA.theorem1` and states, for a
$C^2$ joint potential that is $m$-strongly convex with $L$-Lipschitz gradient
and for $\gamma>0$ with $\gamma L\le1$,

$$\Bigl(\mathbb E\|\theta_k-\theta_\star\|^2\Bigr)^{1/2}\le\sqrt{\frac{2d_\theta}{Nm}}+(1-m\gamma)^kW_2(\mu_0,\Pi_N)+\frac{6L}{\sqrt m}\sqrt{d_x+\frac{d_\theta}N}\,\gamma.$$

The first two terms are those of Project 03. Its last term is
$\frac{33}{20}\frac Lm\sqrt{d_x+d_\theta/N}\sqrt\gamma$, and the new term equals
that term times $\frac{40}{11}\sqrt{m\gamma}$. The new bound is therefore no
larger whenever $m\gamma\le121/1600$. The same bound holds with the
initialization distance measured from any stationary law of the recursion with
finite second moment; such a law exists. Explicit particle, step and iteration
choices give $\sqrt m\,(\mathbb E\|\theta_k-\theta_\star\|^2)^{1/2}\le\varepsilon$.

Compared with Project 03, the application additionally assumes $U\in C^2$ and
restricts the step by $\gamma L\le1$ (equivalently $\gamma\le1/L$ when $L>0$);
Project 03 needs only a differentiable
potential with Lipschitz gradient and permits $\gamma\le2/(m+L)$. The ordering
$m\le L$ is derived when $d_\theta+d_x>0$. If $d_\theta=d_x=0$, the state
space is a point and the parameter error is zero, including when $L=0$;
no accuracy-driven step or iteration count is needed. The reciprocal accuracy
step is used in the nonzero-dimensional case, where $L\ge m>0$.
This is an improvement in discretization order under the stated
regularity and smaller-step regime, not a replacement for every case of
Project 03. No comparison, stationarity, spectral-basis or invariant-law
hypothesis is added; those ingredients are constructed by the imported results.
The page distinguishes this new deduction in the repository from any claim of
priority in the literature.

The explicit statements are in [IPLATheorem.lean](IPLATheorem.lean). They rest
on [IPLA.lean](IPLA.lean), with curvature, coordinate transport and rate
arithmetic in [IPLACurvature.lean](IPLACurvature.lean),
[IsometryTransport.lean](IsometryTransport.lean),
[IPLABridge.lean](IPLABridge.lean) and [IPLARates.lean](IPLARates.lean). Compile
the checked endpoints with:

```sh
lake build WassersteinMixing
lake env lean WassersteinMixing/IPLATheorem.lean
lake env lean WassersteinMixing/Check.lean
```
