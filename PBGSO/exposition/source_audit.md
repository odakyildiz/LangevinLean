# PBGSO source and assumption audit

This audit concerns the local TeX source of **Particle-based Generalised Stochastic Optimisation**, Jiechen Jackie Zhang and O. Deniz Akyildiz, at repository revision `400f5532c5611f03f858c23502ca32c52dffd57a`. It inventories every theorem, proposition, corollary, and lemma included by `papers/PBGSO/main.tex`. Numbering below follows the independent counters in `includes.tex` and the appendix counter reset in `main.tex`.

There are **eight numbered mathematical results**: four main-text theorems, two appendix corollaries, one appendix proposition without its own LaTeX label, and one appendix lemma. The theorem-proof appendix adds no separate numbered result. This document is a source audit, not a claim that every stochastic-analytic argument has already been reconstructed in Lean. Machine-readable details and source hashes are in `reference_audit.json`.

## Scope and common mathematical setting

The framework optimises a differentiable objective with

$$
\nabla\ell(\theta)=\int F(\theta,x)\,\pi_\theta(dx).
$$

The optimiser state is $\vartheta\in\Theta\times\mathcal M$, with parameter projection $\Pi_\theta$; the sampler state is $z\in\mathcal X\times\mathcal V$, with observation projection $\Pi_x$. The optimiser map $\Psi_t(\vartheta,g)$, frozen sampler drift $b_\theta(z)$, and diffusion $\sigma_\theta(z)$ are separate inputs. The mean-field equations are

$$
\dot\vartheta_t=\Psi_t(\vartheta_t,G_{\nu_t}(\vartheta_t)),\qquad
dZ_t=b_{\Pi_\theta\vartheta_t}(Z_t)\,dt+
\sigma_{\Pi_\theta\vartheta_t}(Z_t)\,dB_t,
\quad
G_\nu(\vartheta)=\int F(\Pi_\theta\vartheta,\Pi_xz)\,\nu(dz).
$$

The parameter path is deterministic when its initial state is deterministic; the sampler is stochastic. The interacting system replaces $\nu_t$ by $N^{-1}\sum_i\delta_{Z_t^i}$. Consequently this is a general optimiser–sampler framework rather than a theorem only about MMLE, PGD, or IPLA. In particular, the displayed general optimiser equation does **not** include Brownian noise in the optimiser state. Noisy-parameter IPLA requires an extension or a separate interpretation; it should not silently be identified with the exact displayed framework.

The background supposes $F(\theta,\cdot)\in L^1(\pi_\theta)$, and a normalised density $\pi_\theta\propto e^{-E(\theta,\cdot)}$. That integrability statement alone does not define $G_\nu$ for every $\nu\in\mathcal P_2$. An implementation of the general theorems must also supply integrability for all laws actually used. Uniform linear growth in the sampler variable, or global Lipschitz continuity in that variable, is a common sufficient condition.

All positive definite metrics, eigenvalue comparisons, Hilbert–Schmidt diffusion norms, and Wasserstein distances in the theorems are finite dimensional Euclidean constructions. The text mentions manifold samplers as an extension; the numbered Euclidean contraction theorem does not prove the corresponding manifold result.

## Exact assumption inventory

### A1 — `ass:strong_sol_exist_unique` — Well-posedness

Source: `sections/main/main_system.tex:47`.

For **every deterministic** initial optimiser state and every initial sampler random variable independent of the driving Brownian motion with law in $\mathcal P_2$, the mean-field system has a pathwise unique strong solution on every finite interval, and its sampler law stays in $\mathcal P_2$ at every finite time. In addition, either:

1. the diffusion is constant in both parameter and sampler state; or
2. for a uniform constant $K$, $\|b_\theta(z)\|+\|\sigma_\theta(z)\|\le K(1+\|\theta\|+\|z\|)$.

This is an **assumption of existence and uniqueness**, not a proved general existence theorem. It addresses the mean-field system. The finite-particle theorem separately starts by taking a solution of the interacting system; A1 alone does not state existence of every interacting system.

### A2 — `ass:existence_minimizer` — Stationary optimiser–sampler pair

Source: `sections/main/main_system.tex:59`.

There is $\vartheta_\star$, with projected parameter $\theta_\star$, satisfying $\nabla\ell(\theta_\star)=0$ and $\Psi_t(\vartheta_\star,0)=0$ for **every** $t\ge0$. The frozen sampler at $\theta_\star$ has an invariant law $\nu_{\theta_\star}\in\mathcal P_2$, and its $x$-marginal is $\pi_{\theta_\star}$.

The formalized invariant-law meaning is an actual stationary weak frozen SDE on some Brownian probability space, retaining the complete sampler state; a generator-only invariant test identity is insufficient.

Despite the label, this assumes a **stationary point**; it does not assert or prove global minimisation. A main page may call $\theta_\star$ an optimum only with an additional minimisation or suitable convexity hypothesis.

### A3 — `ass:twisted_joint_strong_monotonicity`

Source: `sections/main/analysis.tex:10`.

There are symmetric positive definite matrices $D_\vartheta,D_z$ and $\rho>0$ such that for every nonnegative time, every two optimiser states, every two finite-second-moment sampler laws, and **every coupling** $\Lambda$ of those laws,

$$
\begin{aligned}
&\langle\Delta\vartheta,D_\vartheta\Delta\Psi_t\rangle
+\int\left(\langle\Delta z,D_z\Delta b\rangle
+\tfrac12\|D_z^{1/2}\Delta\sigma\|_{HS}^2\right)d\Lambda\\
&\qquad\le-\rho\left(\|\Delta\vartheta\|_{D_\vartheta}^2+
\int\|\Delta z\|_{D_z}^2d\Lambda\right).
\end{aligned}
$$

The optimiser difference uses its respective law in each term. Sampler differences use the respective projected parameters. This is a strong **joint** hypothesis; separate frozen-sampler stability and exact-gradient optimiser stability do not imply it. It must include, or be used alongside, the integrability needed for the displayed integrals.

**Integral interpretation is explicit.** The low-level Lean joint inequality
is conditional on its stated integrability domain. The separate
`DiracOptimizerGrowth.FiniteCouplingWork` property requires signed sampler work
integrable for every joint probability law with finite quadratic moment, for
every optimizer pair. This is the ordinary finite signed-integral reading of
the source's universal A3 formula used by the constant-diffusion development;
it is not derived from the conditional inequality. An extended-negative-work
reading is broader. `FiniteWorkScopeAudit` proves an actual $\mathcal P_2$/nonintegrable
work witness for the pointwise strongly dissipative drift $-x-x^3$. Apply the
same convention consistently to the universal signed integrals in U5; the
projected inequality criterion alone does not silently imply it.


### A4 — `ass:psi_F_lipschitz` — Lipschitz gradient response

Source: `sections/main/analysis.tex:115`.

For all nonnegative times, all optimiser states, and all gradients $g,\widetilde g\in\mathbb R^{d_\theta}$,
$\|\Psi_t(\vartheta,g)-\Psi_t(\vartheta,\widetilde g)\|\le L_\Psi\|g-\widetilde g\|$, with a uniform finite $L_\Psi\ge0$.

### A5 — `ass:mf_bounded_second_moment` — Uniform gradient fluctuation

Source: `sections/main/analysis.tex:126`.

Along the particular deterministic mean-field optimiser path used for the comparison, the centred observation obeys

$$
\sup_{t\ge0}\mathbb E\|F(\bar\theta_t,\Pi_x\bar Z_t)-
G_{\bar\nu_t}(\bar\vartheta_t)\|^2\le V_F<\infty.
$$

This is a **uniform in time gradient-variance** hypothesis, not merely a position second-moment hypothesis, and it is not automatic from A1. A uniform Lipschitz constant of $F$ in $x$, together with a uniform position second moment, is one sufficient route.

### U1 — `ass:psi_assumptions` — Contractive optimiser response

Source: `sections/appendix/assumptions.tex:122`.

Fix the positive definite metrics. For every time, two states, and finite-second-moment laws, the optimiser response at a **common** law is strongly dissipative in $D_\vartheta$, with rate $\rho_\Psi>0$. At a fixed optimiser state, changing the law changes the response by at most $L_\Psi\|G_\nu-G_{\widetilde\nu}\|$. This second condition is only on attained gradient values; A4 is the stronger global-in-gradient formulation.

### U2 — `ass:lipschitz_F` — Lipschitz gradient observation

Source: `sections/appendix/assumptions.tex:150`.

Uniformly over optimiser states, $\|F(\Pi_\theta\vartheta,\Pi_xz)-F(\Pi_\theta\vartheta,\Pi_x\widetilde z)\|\le L_F\|z-\widetilde z\|$, for a finite $L_F\ge0$.

### U3 — `ass:SDE_assumptions` — Contractive frozen sampler and Lipschitz coupling

Source: `sections/appendix/assumptions.tex:165`.

The frozen drift is dissipative in $D_z$ at a uniform rate $\rho_b>0$. At a common sampler state, its parameter change is bounded by $L_b\|\vartheta-\widetilde\vartheta\|$. The joint diffusion difference obeys

$$
\|\sigma_{\Pi_\theta\vartheta}(z)-\sigma_{\Pi_\theta\widetilde\vartheta}(\widetilde z)\|_{HS}
\le L_\sigma\sqrt{\|\vartheta-\widetilde\vartheta\|^2+\|z-\widetilde z\|^2}.
$$

### U4 — `ass:auxiliary_separation` — Strongly monotone projected field

Source: `sections/appendix/assumptions.tex:373`.

All four component spaces are Euclidean. Write $\vartheta=(\theta,m)$, $z=(x,v)$. The sampler potential force is the score $-\nabla_xE$. The projected field
$\Phi(\theta,x)=(F(\theta,x),\nabla_xE(\theta,x))$ is globally strongly monotone, with constant $\rho_\Phi>0$, in the joint $(\theta,x)$ Euclidean norm. This does not assume the field is conservative. When it is a gradient, strong convexity of its potential is a sufficient condition.

### U5 — `ass:auxiliary_dissipation` — Auxiliary-variable inequalities

Source: `sections/appendix/assumptions.tex:414`.

For every time, states, laws, and coupling, there are fixed $\beta>0$, $A_\theta,A_x\ge0$, and positive definite $D_\vartheta,D_z,D_m,D_v$ such that, with
$R_\Lambda=\|\Delta\theta\|^2+\int\|\Delta x\|^2d\Lambda$,

$$
\langle\Delta\vartheta,D_\vartheta\Delta\Psi_t\rangle
\le-\beta\langle\Delta\theta,\Delta G\rangle
-\|\Delta m\|_{D_m}^2+A_\theta R_\Lambda,
$$

$$
\int\langle\Delta z,D_z\Delta b\rangle d\Lambda
\le-\beta\int\langle\Delta x,\Delta\nabla_xE\rangle d\Lambda
-\int\|\Delta v\|_{D_v}^2d\Lambda+A_xR_\Lambda.
$$

These are substantive inequalities to verify; the name “auxiliary dissipation” should not hide them from a theorem statement or implementation contract.

## Every numbered result

### Theorem 1 — `thm:invariant_measure`

Statement: `sections/main/main_system.tex:72`. Proof: `sections/appendix/theory_proofs.tex:1`, label `app:thm_invariant_measure`.

**Assumptions:** the gradient identity and its integrability; A1; A2; initialise the optimiser deterministically at $\vartheta_\star$, and initialise the sampler with the frozen invariant law independently of the driving Brownian motion.

**Conclusion:** $\mu_\star=\delta_{\vartheta_\star}\otimes\nu_{\theta_\star}$ is stationary: the law stays equal to $\mu_\star$ at every nonnegative time. For a time-dependent $\Psi_t$, this is a stationary solution, not a claim of a time-homogeneous Markov semigroup. The source explicitly distinguishes those cases.

**Audit:** mathematically sound under the displayed assumptions. The proof uses the sampler marginal to identify $G_{\nu_{\theta_\star}}(\vartheta_\star)=\nabla\ell(\theta_\star)=0$, then the optimiser fixed-point condition and uniqueness. It assumes frozen-sampler invariance; it does not derive that invariance from arbitrary coefficients. It establishes stationarity at a critical point, not global optimisation.

### Theorem 2 — `thm:twisted_joint_strong_monotonicity`

Statement: `sections/main/analysis.tex:71`. Proof: `sections/appendix/theory_proofs.tex:31`, label `app:thm_joint_strong_monotonicity`.

**Assumptions:** A1; A3 with fixed positive definite metrics and $\rho>0$; two mean-field solutions with deterministic initial optimiser states and sampler laws in $\mathcal P_2$. For the stationary-target and uniqueness parts, additionally A2. Define
$\kappa=\lambda_{\max}(\operatorname{diag}(D_\vartheta,D_z))/\lambda_{\min}(\operatorname{diag}(D_\vartheta,D_z))$.

**Conclusion:** for $d^2=\|\Delta\vartheta\|^2+W_2^2(\nu,\widetilde\nu)$,

$$
d_t\le\sqrt\kappa e^{-\rho t}d_0.
$$

With A2, $W_2(\mu_t,\mu_\star)\le\sqrt\kappa e^{-\rho t}W_2(\mu_0,\mu_\star)$. The stationary law is unique **among finite-second-moment laws of the form $\delta_\vartheta\otimes\nu$**. Arbitrary random optimiser laws and arbitrary non-product stationary laws are outside that uniqueness statement.

**Audit:** the synchronous-coupling argument and condition-number constant are correct. The proof controls the local martingale under the A1 linear-growth branch by finite-horizon expected supremum second moments and BDG; under constant diffusion, the difference martingale vanishes. The proof writes derivatives of expected energies pointwise. At the stated generality, the safest rigorous formulation is an integrated energy inequality or an almost-everywhere derivative, followed by Gronwall. Merely finite second moments do not independently justify every pointwise differentiation or absolute integrability of a superlinear drift pairing. A formal reconstruction should prove those analytic steps or expose the exact integrated energy hypothesis; it must not quietly assume the final exponential conclusion.

### Theorem 3 — `thm:finite_particle_error` — Finite-particle interaction error

Statement: `sections/main/analysis.tex:151`. Proof: `sections/appendix/theory_proofs.tex:190`, label `app:proof_finite_particle_error`.

**Assumptions:** A1; A3; A4; A5; a positive integer $N$; a deterministic initial optimiser; sampler initial states that are i.i.d. with a common $\mathcal P_2$ law and independent of mutually independent Brownian motions; an interacting-system solution and the independent-copy mean-field system defined on the same probability space; synchronous initial optimiser and paired sampler states; the same Brownian motion for each corresponding interacting/copy pair. A2 is not needed.

**Conclusion:** letting $\bar\nu_t^{[N]}$ be the independent-copy **empirical** measure,

$$
\left\|d((\vartheta_t^N,\nu_t^N),(\bar\vartheta_t,\bar\nu_t^{[N]}))\right\|_{L^2}
\le\frac{L_\Psi}{\rho}\sqrt{\frac{\kappa V_F}{N}}
(1-e^{-\rho t}).
$$

**Audit:** the argument is sound for globally defined coupled solutions with the stated integrability and stochastic-calculus properties. The paper handles the possibly strict local martingale by stopping at energy/quadratic-variation thresholds and applying Fatou; no assumed interacting-system moment bound is needed for that localization. Independent centred copy observations give exactly $V_F/N$, and a square-root Bihari inequality produces the displayed constant.

This is an interaction-error estimate. It does **not** bound $W_2(\nu_t^N,\bar\nu_t)$ by $N^{-1/2}$. That population-distance estimate would also require $W_2(\bar\nu_t^{[N]},\bar\nu_t)$, whose rates depend on dimension and moment assumptions. The interacting particles are exchangeable, not independent; only the mean-field copies are i.i.d. A main page must preserve that distinction.

### Theorem 4 — `thm:parameter_error_full` — Parameter error

Statement: `sections/main/analysis.tex:172`. Proof: `sections/appendix/theory_proofs.tex:591`, label `app:cor_parameter_error_full`.

**Assumptions:** all A1–A5; the same positive-particle-count, deterministic optimiser, i.i.d. sampler, Brownian independence, and coupled-solution conditions needed for Theorem 3. In particular A2 supplies the stationary target and A5 is for the corresponding mean-field comparison path.

**Conclusion:** with $d_0=d((\vartheta_0^N,\nu_0),(\vartheta_\star,\nu_{\theta_\star}))$,

$$
\|\theta_t^N-\theta_\star\|_{L^2}
\le\sqrt\kappa e^{-\rho t}d_0+
\frac{L_\Psi}{\rho}\sqrt{\frac{\kappa V_F}{N}}(1-e^{-\rho t}).
$$

The displayed iterated large-time/large-particle limit is zero. Constants must be uniform over the family of particle counts used in that limit; the intended mean-field comparison and A5 are independent of $N$.

**Audit:** the triangle inequality and Euclidean coordinate projection give this result from Theorems 1–3. The target is the A2 stationary point; a minimiser claim needs an additional assumption. This theorem concerns continuous time. The following unnumbered discretisation paragraph assumes its discretisation error rather than proving it.

### Corollary A.1 — `cor:separate_monotonicity`

Statement and proof: `sections/appendix/assumptions.tex:199`.

**Assumptions:** U1–U3 for fixed positive definite metrics; finite nonnegative Lipschitz constants; positive $\rho_\Psi,\rho_b$. Let $\kappa$ be the joint metric condition number. The symmetric matrix

$$
H=\begin{pmatrix}
\rho_\Psi-\kappa L_\sigma^2/2 &
-\sqrt\kappa(L_\Psi L_F+L_b)/2\\
-\sqrt\kappa(L_\Psi L_F+L_b)/2 &
\rho_b-\kappa L_\sigma^2/2
\end{pmatrix}
$$

must have strictly positive diagonal entries and determinant. Equivalently the source requires

$$
2\rho_\Psi-\kappa L_\sigma^2>0,\quad
2\rho_b-\kappa L_\sigma^2>0,\quad
(2\rho_\Psi-\kappa L_\sigma^2)(2\rho_b-\kappa L_\sigma^2)
>\kappa(L_\Psi L_F+L_b)^2.
$$

**Conclusion:** A3 holds with rate $\lambda_{\min}(H)>0$. A simpler sufficient condition is that each $\rho_\Psi,\rho_b$ exceeds $\kappa L_\sigma^2/2+\sqrt\kappa(L_\Psi L_F+L_b)/2$. Exponential contraction also requires A1.

**Audit:** the law-coupling identity, Cauchy–Schwarz, spectral norm comparisons, and positive-definite $2\times2$ matrix test give the stated coefficients. No error in the factors of two was found. The result is a sufficient condition; it does not follow just from exact-gradient optimiser dissipativity.

### Corollary A.2 — `cor:projected_strong_convexity`

Statement and proof: `sections/appendix/assumptions.tex:501`.

**Assumptions:** U4; U5; diffusion independent of parameter and sampler state; $c=\beta\rho_\Phi-A_\theta-A_x>0$. Define
$K_\vartheta=\operatorname{diag}(cI,D_m)$ and $K_z=\operatorname{diag}(cI,D_v)$.

**Conclusion:** A3 holds with the positive rate

$$
\rho=\min\{\lambda_{\min}(D_\vartheta^{-1/2}K_\vartheta D_\vartheta^{-1/2}),
\lambda_{\min}(D_z^{-1/2}K_zD_z^{-1/2})\}.
$$

Exponential contraction also requires A1.

**Audit:** valid. The two projected force pairings combine, through the coupling marginal identities, into the monotone $\Phi$ pairing. Congruence with the inverse square roots compares the two quadratic forms. The title references strong convexity, but the actual assumption is strong monotonicity and allows a non-conservative field. The auxiliary inequalities are essential; strong monotonicity of $\Phi$ alone does not prove A3 for arbitrary auxiliary dynamics.

### Proposition A.1 — no result label — Hypocoercive verification

Statement and proof: `sections/appendix/assumptions.tex:639`. Stable source locator: subsection label `app:mpgd_result`. There is no `\label` inside the proposition.

**Assumptions:** U4 with rate $\rho_\Phi>0$; in addition the full projected field $\Phi$ is globally $L_\Phi$-Lipschitz; dimensions $d_m=d_\theta$ and $d_v=d_x$; unit-mass heavy-ball optimiser $(m,-G-\gamma m)$; underdamped sampler $(v,-\nabla_xE-\gamma v)$; constant diffusion $(0,\sqrt{2\gamma}I)$; a common friction

$$
\gamma>\frac{\sqrt2 L_\Phi}{\sqrt{\rho_\Phi}}.
$$

**Conclusion:** positive definite $D_\vartheta,D_z$ and a positive rate satisfying A3 exist. It does not directly establish A1, A2, or A5, which must still be supplied to use all main theorems.

**Audit:** the construction is correct. Choose $0<\varepsilon<1$ so $2L_\Phi^2/((1-\varepsilon)\gamma^2)<\rho_\Phi$, any $\beta>0$, and $\delta=2\beta/\gamma$. The $2\times2$ block metric has blocks $\beta\gamma I,\beta I,\delta I$. Its Schur complement is positive. Young's inequality gives $D_m=D_v=\varepsilon\beta I$ and $A_\theta=A_x=\beta L_\Phi^2/((1-\varepsilon)\gamma^2)$; Corollary A.2 applies. The strict friction threshold is sufficient, not claimed necessary or optimal.

This proposition applies to continuous M-MFPO under those assumptions. It is not a proof for all neural-network EBM experiments, and is not a higher-order HOL-MYPGD verification.

### Lemma A.1 — `lemma:vol_preserve_ode` — Volume preservation

Statement and proof: `sections/appendix/momentum_mfpo_appendix.tex:69`.

**Assumptions:** a positive particle count; the frictionless, noise-free $A$/$B$ part of M-MFPO; a globally defined flow; a $C^1$ vector field. For the discrete determinant statement, the kick/drift maps must be differentiable; the proof phrases the one-step map as a $C^1$ diffeomorphism. The stated force regularity ensures the shear maps and their explicit inverses have that property.

**Conclusion:** the continuous flow and the discrete $B$/$A$/$B$ composition have Jacobian determinant exactly one.

**Audit:** correct. Each position drift is independent of its own position coordinate, and each momentum force is independent of its own momentum coordinate, so the continuous divergence is zero. Kicks and drifts are shears with determinant one, and the chain rule proves the discrete result. The full $O$/$L$/$B$/$A$/$B$/$O$/$L$ algorithm includes friction and stochastic updates; the lemma does not assert it is volume preserving. The lemma statement calls the discrete section “$B,A$”, while its proof uses $B,A,B$ and the surrounding text once says “$B_1,A,B_2$”; all listed kick/drift compositions are volume preserving, but the implemented scheme is the displayed $B,A,B$ composition.

## Other claims that must not be mistaken for proved rates

### Frozen-sampler invariant construction

The main-system section gives a sufficient generalised Langevin construction: $H=E+g$, $\int e^{-g(x,v)}dv=C_g$ finite and independent of $x$; diffusion covariance $2D$ with symmetric nonnegative $D$; skew-symmetric $Q$; drift $-(D+Q)\nabla H+\operatorname{div}(D+Q)$. It also requires integrability, enough regularity for the stationary Fokker–Planck equation and commuting mixed derivatives, and appropriate no-flux/decay conditions. The skew term then cancels in the double divergence. This is explanatory source material, not one of the eight numbered results. A stationary PDE identity must be connected to a conservative well-posed diffusion to conclude probabilistic invariance.

### Counterexample to separate stability

Appendix `assumptions.tex:10` constructs an optimiser with exact-gradient dissipation and a contractive frozen Ornstein–Uhlenbeck sampler, while their coupled means are unstable. The numerical eigenvalues printed for $a=1/2,\omega=1$ are consistent with the characteristic polynomial

$$
\lambda^4+2a\lambda^3+(a^2+2a+\omega^2)\lambda^2+
2(a^2+\omega^2)\lambda+a^2+\omega^2.
$$

Its third Hurwitz determinant is $4(a^2+\omega^2)(a^3+(a-1)\omega^2)$, which is negative at those values. Thus the instability is substantive, not just a numerical artefact. This is an unnumbered example, not a source theorem.

### Unproved general discretisation estimate

After Theorem 4, the source explicitly **supposes**
$\|\widehat\theta_k^{N,h}-\theta_{kh}^N\|_{L^2}\le\varepsilon_{\mathrm{disc}}(h,kh,N)$, then applies the triangle inequality. It leaves method-specific rates and infinite-horizon numerical stability to future work. A formal triangle inequality using an assumed $\varepsilon_{\mathrm{disc}}$ is useful composition, but is not itself a new verified method-specific discretisation rate.

### Method 1: HOL-MYPGD

Source: `sections/main/mmle_mfpo_image_debluring.tex:12`; details and coefficients in `sections/appendix/mmle_details.tex:69` onwards.

The optimiser is gradient descent using the original observation $F=\nabla_\theta E$. The sampler has state $(X,U,V)$ and equations

$$
dX=U\,dt,\quad dU=(-\nabla_xE^\lambda+\gamma V)\,dt,\quad
dV=(-\gamma U-\alpha V)\,dt+\sqrt{2\alpha}\,dB.
$$

The paper uses a forward Euler parameter step followed by the displayed Gaussian higher-order sampling update. In its experiments it chooses the **endpoint** force quadrature $\Delta E^\lambda=h\nabla_xE^\lambda(\theta,x)$, rather than the higher-order Lagrange quadrature of the cited sampler work. The name “higher-order Langevin” describes the augmented diffusion and should not be used to infer a convergence order for this implemented coupled method.

For fixed positive smoothing $\lambda$, the sampler targets $\pi_\theta^\lambda\propto e^{-E^\lambda(\theta,\cdot)}$. Its averaged original-gradient force need not equal $\nabla\ell(\theta)$, nor the gradient of the smoothed marginal likelihood. The source acknowledges smoothing bias but gives no quantitative uniform bound for it. A bound to the original target needs an explicit force-bias estimate and stability argument; a bound to a smoothed critical point must identify that target correctly.

No numbered result verifies A3 specifically for this third-order sampler, and no numbered result proves its coupled numerical rate. Such a result is additional work, even if it uses the general framework.

### The printed HOL coefficients are not the full exact linear flow

The discretisation discussion describes an exactly solvable linear evolution. The seven printed coefficients do define a concrete affine implementation, but they are not collectively the matrix exponential of the force-free subsystem $\dot x=u,\ \dot u=\gamma v,\ \dot v=-\gamma u-\alpha v$. For example, an exact fundamental solution would require $\mu_{22}'(h)=\gamma\mu_{32}(h)$. Direct differentiation of the displayed formulas gives, with $s=\alpha h$,

$$
\mu_{22}'(h)-\gamma\mu_{32}(h)
=-\frac{\gamma^4}{\alpha^3}
\left[s(1+e^{-s})-2(1-e^{-s})\right].
$$

For $\alpha,\gamma,h>0$, the bracket is strictly positive: it vanishes at zero and has derivative $1-(s+1)e^{-s}>0$. Thus the required identity fails. Equivalently, the printed $\mu_{22}$ lacks the $\gamma^4h^4/24$ term present in the full linear flow's Taylor expansion. The lower terms agree, so this does not preclude a useful consistent approximation, but an exact-flow claim is incorrect for this full subsystem. Verified numerical results must use the actual printed map and retain its coefficient errors, rather than substitute the exact matrix exponential or assume its covariance identity.

The library now checks a concrete exact counterexample in `PBGSO/HOLCoefficientAudit.lean`: at $\alpha=\gamma=h=1$, the derivative mismatch equals $1-3e^{-1}\ne0$. The general derivative formula above is the source audit's analytic calculation; the Lean counterexample is sufficient to refute the universal exact-flow interpretation.

### The TV prior's normalisation obstruction

The deblurring example writes $p_\theta(x)\propto\exp(-e^\theta\mathrm{TV}(x))$ on $\mathbb R^{d_x}$ and assumes the normalising integral is finite. For the standard discrete image gradient, $\mathrm{TV}(x+c\mathbf1)=\mathrm{TV}(x)$. Decomposing $x=y+c\mathbf1$, with $y\perp\mathbf1$, leaves a strictly positive integrand independent of $c$. Integration over the constant-image direction is infinite. Therefore the asserted proper prior cannot hold on the displayed full Euclidean space.

Possible repaired models anchor the constant mode, work on a mean-zero subspace, add a coercive penalty, or impose a proper bounded-domain prior. Each repair changes the modelling assumptions and possibly the normalising derivative and the $-d_x$ term. In particular, restriction to a subspace changes the scaling exponent to the dimension of that subspace. Posterior normalisability from a likelihood does not, by itself, create a proper original prior or validate a marginal likelihood based on it.

The text also calls $g_1,g_2$ convex and lower bounded in the decomposition $g_1=\|y-Bx\|^2/(2\sigma^2)-d_x\theta$, $g_2=e^\theta\mathrm{TV}(x)$. These properties hold in the required sampler variable for fixed $\theta$, but not as a blanket joint statement in $(\theta,x)$: the linear term is not uniformly lower bounded in $\theta$, and $e^\theta\mathrm{TV}(x)$ need not be jointly convex. The Moreau envelope is taken only in $x$, so a precise formalization can use the correct fixed-parameter convexity assumptions.

### Method 2: M-MFPO and its OBABO-style integrator

Source: `sections/main/momentum_mfpo.tex:20`; full integrator `sections/appendix/momentum_mfpo_appendix.tex:46`.

The method combines a heavy-ball optimiser and underdamped sampler with common friction. The integrator takes exact half Ornstein–Uhlenbeck sampler/friction optimiser steps, half force kicks, full position drifts, half force kicks, and final exact half friction/noise steps. The two Gaussian half-step noises are independent across particles, time, and half steps.

Proposition A.1 supplies a **continuous-time** contractivity route under globally monotone and Lipschitz $\Phi$ and the strict friction threshold. Lemma A.1 proves volume preservation only for the deterministic frictionless kick/drift section. The paper explicitly states that its continuous-time results do not give discretisation guarantees. A quantitative OBABO parameter error or invariant-bias rate is therefore additional to the paper.

The neural EBM experiments are illustrative. Normalisability is assumed, and no argument establishes the global strong monotonicity, global Lipschitz constants, variance bound, or friction threshold for the trained neural models. Reported improvements in Fisher divergence, MSE, SSIM, or speed are empirical comparisons, not a theorem that these methods always accelerate optimisation.

## Requirements for honest formalization and main-page claims

1. State the optimiser, sampler, observation map, projections, law dependence, Brownian independence, and positive particle count explicitly. Preserve separate arbitrary optimiser and sampler choices.
2. Distinguish stochastic existence assumptions from algebraic and differential consequences proved from them. If an integrated energy or local defect estimate is an input, expose it in the theorem's assumption list.
3. Use the actual A2 stationary-point condition; add a minimiser hypothesis when claiming optimisation to a minimiser.
4. Preserve deterministic-optimiser and product-law restrictions in the stationary uniqueness theorem.
5. State uniform variance and joint contractivity as substantive hypotheses; do not describe them as automatic from sampler invariance or frozen contractivity.
6. Keep interaction error, independent empirical sampling error, numerical error, smoothing bias, and force-estimation bias distinct whenever the final bound needs them.
7. For each new method-specific rate, prove or explicitly expose the mechanism producing its contraction and local defect constants. Do not count a theorem assuming the requested final rate as its verification.
8. Do not claim that the unanchored full-space TV prior is proper or that neural EBM examples satisfy the convexity/contractivity assumptions without further evidence.

The eight numbered source statements are consistent under their substantive hypotheses. The most material source limitations are the impossible full-space TV prior normalisation, the hybrid smoothing bias, the mismatch between the printed HOL coefficients and an exact full linear flow, missing method-specific discretisation analysis, and the distinction between a conditional analytic framework and its verification for particular experimental models.

## Verified Lean coverage and explicit source interpretations

The machine-readable `reference_audit.json` is authoritative for per-result
coverage. Its source hashes and exact eight-result/ten-assumption inventory
refer to the unchanged local paper. `additional_method_coverage` separately
records the two new actual implementation bounds. The normal verifier checks
source correspondence; only `--require-complete` checks completion of all
inventoried source results, both method bounds and required bridges. The strict
ledger has no open formal obligation under the stated SDE meaning of A2 and
ordinary finite signed-work interpretation of A3/U5; the broader extended-negative
interpretation is explicitly outside that correspondence.

### General model and actual stochastic processes

`Framework` retains independent optimiser response, gradient observation,
parameter and sampler-position projections, arbitrary auxiliary states,
sampler drift and full state-/parameter-dependent finite-column diffusion.
The mean-field optimiser has no thermal noise. Its original ODE is expressed
in integral form, allowing time-measurable responses. All expected observations
are actual Bochner integrals, and their integrability domains remain explicit.
No conservative potential or matching optimiser/sampler dimensions is assumed.

The Brownian/integral foundations construct actual finite predictable sums,
weighted isometry, martingale representatives, closed predictable-step domains,
density for time-$L^2$ adapted columns, interval cuts, subtraction and source
transport. Actual countable maximal estimates and dyadic Gaussian arguments
construct continuous Brownian modifications and continuous integral versions.
Original raw pre-Brownian paths are not silently declared continuous: actual
computed integrals are proved invariant under their fixed-time AE modifications.

`ProductLpSections.sectionLp_stronglyMeasurable` now works on **arbitrary
sigma-finite spatial measures**. The field determines an actual countably
generated spatial subalgebra; adding measurable finite spanning sets preserves
sigma-finiteness. Its separable $L^2$ section construction pulls back to the exact
original section curve. Thus no ambient `IsSeparable Q` or countable generation
of the original sample space is required by the raw analytic pipeline.

`RawLocalIntegral` derives genuine first-hit stops from the literal progressive
local energy, constructs stopped original diffusion integrals and proves their
continuous-martingale consistency. The resulting `localNoise` has simultaneous
stopped identities on one full-measure event. Common-null-set normalization
handles almost-sure pathwise integrability without mismatching the scalar gauge
and the original diffusion columns. No stopped SDE, matching noise output,
stochastic isometry or energy conclusion is an input.

### Source theorem 1: stationarity from A1 and actual weak frozen invariance

`RawPathSolutionTransfer.stationary_product_law_of_weak_frozen` proves the
original complete-state stationary product law. **A2 has the SDE-semigroup
meaning of invariant law:** an actual stationary weak frozen sampler on some
Brownian source, with original local stochastic equation, continuous adapted
paths, pathwise $L^1$ drift and invariant $\mathcal P_2$ law. A generator-only invariant test
identity is insufficient. The frozen process need not be strong or live on the
original solution's probability space.

The canonical full-system strong solution is the direct A1 existence instance
on independent initial sampler law times the actual Wiener path law. Whole-path
Brownian laws, initialization independence, the probability input map, causal
filtration transport and original local-noise naturality are all derived.
Pulling the canonical solution to each source and applying A1 same-driver
uniqueness identifies both original laws. No common-source frozen strong
realization, global drift moment, linear growth, energy estimate or supplied
output-law equality remains.

The zero mean observation, its integrability, the optimiser fixed point at
all horizon times and stationary initial state/law are visible. The target is
the source critical point; minimization requires an additional assumption.
The older generator-stationarity and arbitrary-integral-operator interfaces
remain intermediate results, not substitutes for this actual local proof.

### Source theorem 2: the two A1 alternatives remain distinguished

For A1(ii), `RawLinearGrowthState` derives original state/coefficient moments
from the original simultaneous local equation, initial $L^2$ and primitive growth
$\|b\|+\|\sigma_{\rm columns}\|\le K(1+P+\|X\|)$. Stopped variation and computed
noise first give local $L^2$. A threshold-independent Volterra estimate and Fatou
give, for every $t\le T$,

$$
\mathbb E\|X_t\|^2\le e^{9K^2(T+1)T}
\bigl(3\mathbb E\|X_0\|^2+1+P^2\bigr)-(1+P^2).
$$

The finite parameter bound $P$ is derived from the original optimiser integral
ODE and continuous parameter projection on the compact horizon. Global spatial
and product-time square integrability, exact local-to-global original noise
identity and the literal predictable Model realization are conclusions.
`RawSamplerGrowthArbitraryLaw.law_distance_decay` combines actual cross-source
law uniqueness with genuine initial coupling infima, giving the exact
$\sqrt\kappa e^{-\rho T}$ factor and true initial optimiser/Wasserstein distance
for the original solutions on distinct probability spaces.

For A1(i), `NaturalFiniteWorkArbitraryLaw.law_distance_decay` proves the exact
contraction across arbitrary original probability spaces under the **ordinary
finite signed-integral reading of universal A3**. Its independent
`FiniteCouplingWork` premise requires absolute integrability of the signed
sampler work for every optimiser pair and every joint probability law with
finite quadratic moment, without an observation-domain restriction. The
conditional inequality alone does not assert this domain.

`DiracSamplerCoercivity` and `RawSamplerCoerciveMoment` derive original uniform
moments from the raw equation and Dirac A3. Universal finite work gives quadratic
work growth, compact-uniform optimiser work and integrable positive sampler
work. Fubini, actual local-noise cancellation, original-law transport and the
Wasserstein infimum are proved. No A4, response continuity, drift-norm growth,
global moments, positive-work estimate or energy conclusion is supplied.

This convention is substantive. `FiniteWorkScopeAudit` constructs an actual
$\mathcal P_2$ law for which the strongly dissipative drift $b(z)=-z-z^3$ has nonintegrable
signed work against zero. An **extended-negative-work** reading of A3 covers
more models and is not claimed by this completion ledger. The audit is not a
counterexample to contraction. `PositiveWorkFubini` and related modules also
provide an optional one-sided-work sufficient criterion; source A4/A5 derive
that criterion for stationary-target comparisons without universal finite work.

The actual product-law Wasserstein identity, law-preserving coupling
realizations and transport infimum are proved; they are not assumed analytic
conclusions. The old weak-generator versions display their quadratic test
domain and synchronous-realization assumptions explicitly.

`RawStationaryUniqueness.stationary_laws_unique_constant` and
`stationary_laws_unique_linearGrowth` assemble the stationary-uniqueness
part for the original raw solution class. Their `Family` contains actual
stationary trajectories on each finite horizon and only direct A1
canonical/path-source existence and same-driver uniqueness instances.
Applying the corresponding original law contraction on every horizon and
transport separation proves equality of both optimiser states and sampler
laws. No quadratic generator domain, synchronous weak realization, energy
identity or contraction estimate is supplied. The same branch qualifications
remain: explicit finite signed work for the constant branch, and primitive
coefficient realization/linear-growth regularity for the other branch.

### Source theorem 3: sharp original raw interaction and physical assembly

`RawParticleInteraction.Data.finite_particle_interaction_bound` proves exactly

$$
\sqrt{\mathbb E\,d_{\rm emp}(P_T,\mathrm{copy}_T)^2}
\le\frac{L_\Psi}{\rho}\sqrt{\frac{\kappa V}{N}}(1-e^{-\rho T}).
$$

The data are original raw continuous adapted particle/copy paths, their
simultaneous equation driven by the **constructed local Brownian integral**,
initial $L^2$, joint raw measurability/pathwise local energy, and the literal
physical drift/diffusion identities. Positive $N,\rho$, source A3/A4/A5,
synchronous initial coordinates, deterministic reference optimiser and the
original reference iid cloud law/observation variance are explicit.

Genuine first-hit localization, exact after-stop damping and random-$L^2$
finite-variation calculus derive all expected energy/work identities. The
sharp $V/N$ forcing comes only from the **original reference** cloud; neither
interacting variables nor artificially damped copies are assigned iid laws.
Fatou removes the threshold. No global drift $L^2$, linear growth, stochastic
isometry, supplied energy inequality or weak-generator test domain enters this
final raw theorem. Actual empirical Wasserstein measurability and transport
are proved.

`RawIndependentCopies` constructs a valid full product Brownian Driver,
coordinate original SDEs, whole-trajectory independence and the exact iid
reference marginal. `RawReferenceCloud` constructs its physical Hilbert
encoding, original diffusion columns, local gauge, $\mathcal P_2$ and joint continuous
representative. Global/local bounded-linear-map and noise-index-injection
identities are proved from finite stochastic sums and completion. The complete
physical packed-cloud equation is proved in `RawReferenceCloudEquation` using
actual state-map/index noise transport. `RawConstructedParticleCopy.build`
constructs the natural physical pair, and
`RawConstructedParticleBounds.original_finite_particle_interaction_bound`
instantiates the sharp bound on the **original native interacting solution**.
Every reference law, physical coefficient and simultaneous noise identity is
proved. The original native $Y$ is on the constructed independent whole-seed
product; arbitrary external interacting-source law transfer is not claimed.

A1 states **mean-field** wellposedness. It does not by itself construct every
arbitrary finite-particle SDE. The general interaction result quantifies over
actual original interacting-particle solutions, as in the paper's instruction
to solve that system. The globally Lipschitz additive implementations construct
their interacting solutions internally.

### Source theorem 4: target work and the genuine initial-law factor

`RawParticleParameter` derives actual original parameter $L^2$ and its RMS triangle
from the sharp raw interaction bound and one-Lipschitz projection. Its family
result proves the joint time/particle-count limit with varying original sample
spaces, uniform primitive constants and no final-error premise.

`ConstantNoiseFluctuation` derives positive target-comparison work from source
A3, source A4 response Lipschitz, source A5 reference observation variance and
stationary-target observation $L^1$. The compact optimiser-gap bound follows from
the original integral ODE. `RawNaturalConstantLawParameter.parameter_bound`
combines natural original raw reference/target equations, actual initial
coupling realizations and the genuine Wasserstein infimum with the sharp
particle floor. It has no extra growth, work, energy, noise, old-process or
weak-coupling conclusion premise. Actual target stationarity remains a
substantive A2 input, supplied by the source1 construction under its stated
interpretation.

`RawConstructedParticleParameter.original_parameter_bound_constant` and
`original_parameter_bound_linearGrowth` instantiate the physical pair internally
and conclude the exact bound on the **original native $Y$**. The constant branch
uses A4/A5 without universal finite work. The state-dependent branch uses only
primitive Borel/progressive/linear-growth realization regularity and direct A1
existence/uniqueness instances, with all global moments derived.
`RawConstructedParticleJointLimit.parameter_joint_limit` takes a family of
actual original equations and primitive A1/A2/initial witnesses, applies the
sharp bounds internally, and proves actual parameter RMS tends to zero jointly
as population and time tend to infinity. Neither Family nor Branch contains
an estimate, work, energy or paired-realization conclusion. Coherent global
trajectories are included by horizon restriction.

### Appendix results

The separated criterion proves the literal source matrix positive definite,
identifies its actual minimum eigenvalue and derives full law monotonicity
from the primitive separate hypotheses. The canonical projected criterion
constructs the source metric actions and SPD block forms from the literal
matrices, derives all coordinate/coercivity identities and proves the exact
minimum generalized eigenvalue rate. The coupling-integrability contract is
visible; no spectral lower bound is assumed as the desired conclusion.
`ProjectedFiniteWork` separately names the ordinary finite domain of the
universal U5 sampler integral. Its wrapper derives both the spectral joint
inequality and `FiniteCouplingWork`; the latter is not inferred from the
conditional criterion alone.

`HypocoerciveCriterion.heavyBall_source_criterion` derives the actual heavy-ball
metric, positive rate, U5 inequalities and law-coupling work from source U4,
primitive complete-field Lipschitz and the exact friction threshold. No common
potential is needed.

`FlowSourceRegularity.phase_flow_fderiv_det_one_source` proves continuous
signed determinant one from an arbitrary $C^1$ joint force and actual globally
defined original ODE trajectories with initial identity. Joint $C^1$ initial-data
dependence, variational equation and determinant evolution are derived. The
original discrete BAB signed determinant result is also proved. No flow
regularity, global force Lipschitz, variational or determinant premise is
supplied.

`ContinuousFlowMeasure.phase_flow_measurePreserving_source` additionally proves
literal continuous Lebesgue measure preservation under the same primitive $C^1$
force, actual all-real ODE and identity-initial-map hypotheses. Actual trajectory
uniqueness derives the flow group identity and negative-time inverse;
Jacobian change of variables then proves MeasurePreserving. Bijectivity,
flow regularity and measure preservation are not premises.


### Both new actual numerical method bounds

`FullyUniformMomentum.explicit_parameter_bound` and
`FullyUniformHigherOrder.explicit_parameter_bound` prove time-uniform
parameter bounds for the actual nonlinear particle algorithms. They combine
the source continuous-time relaxation/particle floor with $D_j\sqrt h$ at every
iteration for $0<h\le h_{\star,j}$, with explicit constants independent of
iteration count, step size and horizon (for fixed $N$). The earlier
`FullyConstructedMomentum.numerical_parameter_bound` and
`FullyConstructedHigherOrder.parameter_bound` remain finite-horizon
`O($\sqrt h$)` supporting results. Physical Brownian
inputs, Gaussian coupling, raw/$L^2$ field and step identities, reference integral
equations, zero initial discretization error and mesh-independent
moment/modulus constants are all constructed. No final discretization error,
reference-law or noise-matching premise remains.

Primitive separate global force Lipschitz, positive particle count, literal
flattened Euclidean encoding, $\mathcal P_2$ initial/target laws, actual frozen invariant
trajectory, zero target mean observation, positive source A3 and uniform
reference variance are explicit. The kinetic friction conditions and HOL
`alpha > 0`, `gamma >= 0` appear in the exact headers. An arbitrary invertible
cloud encoding transforms raw covariance; independent isotropic particle noise
uses the proved Euclidean encoding. The targets are stationary critical points.
No global minimization, uniformity in $N$ or numerical invariant law is asserted.

`FullyConstructedHigherOrder.original_parameter_bound` additionally derives
`L*epsilon/m` from actual coupled original/surrogate target variables within
$\varepsilon$, an original expectation identity, positive original-gradient
monotonicity and spatial observation Lipschitz. The target coupling radius is
a visible assumption, not the bias conclusion.

The formal coefficient audit proves an exact nonzero defect in the printed
HOL full-linear-flow claim. The printed covariance is independently proved to
be the actual Gaussian kernel Gram covariance. The full-space TV prior's
constant-translation impropriety is a source-model validity issue; repairing
that illustrative prior or computing a model-specific coupling radius is not
an additional generic-method completion obligation. Both method bounds are
verified under the assumptions above.
