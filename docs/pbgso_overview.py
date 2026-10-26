"""Statement-only PBGSO landing page; proof details live in technical.html."""
from __future__ import annotations

import html

E = html.escape


def overview_document(sources, parsed, math):
    from build_site import ROOT, anchor, relative, shell
    from build_pbgso import OVERVIEW, CATALOG, proof_page

    page = OVERVIEW

    def proof(path, name, label):
        if path not in parsed or name not in parsed[path]:
            raise ValueError(f'Missing landing-page theorem: {path}: {name}')
        return f'<a href="{relative(proof_page(path), page)}#{anchor(name)}">{E(label)}</a>'

    def article(identifier, title, content, links, source=None, new=None):
        attributes = (f' data-source-result="{source}"' if source else '')
        attributes += (f' data-new-theory="{new}"' if new else '')
        return (f'<article class="theorem-statement" id="{identifier}"{attributes}>'
                f'<h3>{E(title)}</h3>' + math(content) +
                '<p class="theorem-proof-links">' + ' · '.join(proof(*link) for link in links) + '</p></article>')

    body = ('<div class="pbgso-overview"><header class="hero">'
            '<div class="eyebrow">Paper theorems and new numerical bounds</div>'
            '<h1>Particle-based Generalised Stochastic Optimisation</h1>'
            '<p class="subtitle">Four main theorems of the paper, two new discretisation theorems, '
            'and the assumptions used in their formal verification.</p>'
            '<p class="reference-notice"><strong>Source:</strong> Jiechen Jackie Zhang and O. Deniz Akyildiz, '
            '<em>Particle-based Generalised Stochastic Optimisation</em>, local manuscript.</p></header>'
            '<nav class="jump-nav" aria-label="PBGSO contents">'
            '<a href="#paper-theorems">Paper theorems</a><a href="#new-theory">New theory</a>'
            '<a href="#standalone-verification">Standalone verification</a>'
            '<a href="#proof-roadmap">Proof roadmap</a></nav>'
            '<section class="section statement-setting" id="assumptions"><h2>Notation and assumptions</h2>'
            '<div class="assumption-legend" aria-label="Assumption colour key">'
            '<span class="source-assumption-key">Paper assumptions</span>'
            '<span class="added-assumption" data-assumption-kind="added">Added condition</span>'
            '<span class="interpretation-assumption" data-assumption-kind="interpretation">Explicit interpretation</span></div>'
            '<p>Orange marks an additional condition or a restriction in the formal theorem. '
            'Blue states how a paper assumption is interpreted. Each result lists its own additions; '
            'a condition used by one result is not imposed on all the others. '
            'The linked Lean statements retain every quantified hypothesis.</p>')
    body += math(r'''<p>For the paper theorems, optimiser and sampler states are finite-dimensional Euclidean, with dimensions that may differ. The optimiser state is \(s\), its parameter is \(\theta=P_\theta s\), and the sampler state is \(z\), with observation \(x=P_xz\). Independent maps \(\Psi_t,F,b,\sigma\) define</p>
\[\begin{gathered}
G_\nu(s)=\int F(P_\theta s,P_xz)\,\nu(dz),\\
\dot s_t=\Psi_t(s_t,G_{\nu_t}(s_t)),\\
\begin{aligned}
dZ_t&=b_{P_\theta s_t}(Z_t)\,dt\\
&\quad+\sigma_{P_\theta s_t}(Z_t)\,dB_t.
\end{aligned}
\end{gathered}\]
<p>The particle system uses \(\nu_t^N=N^{-1}\sum_{i=1}^N\delta_{Z_t^{i,N}}\). Optimiser and sampler dimensions and their auxiliary variables may differ. The optimiser receives no Brownian noise in this framework.</p>
<p>Write \(\mu_t=\delta_{s_t}\otimes\nu_t\), \(p=(s,\nu)\), \(\widetilde p=(\widetilde s,\widetilde\nu)\), and</p>
\[\begin{gathered}d(p,\widetilde p)^2\\
=\|s-\widetilde s\|^2+W_2(\nu,\widetilde\nu)^2.
\end{gathered}\]
<p>For the positive definite block metric \(D=\operatorname{diag}(D_s,D_z)\), choose certified comparisons \(0&lt;m\le M\) with \(m\|y\|^2\le\|y\|_D^2\le M\|y\|^2\), and put \(\kappa=M/m\). The paper uses the sharp eigenvalue comparisons. The formal statements also allow nonsharp certified comparisons, with the corresponding \(\kappa\).</p>
<dl class="source-assumptions">
<dt>A1 — Well-posedness</dt><dd>For deterministic initial optimiser states and sampler laws in \(\mathcal P_2\), there is a pathwise unique strong mean-field solution on every finite horizon, with sampler laws in \(\mathcal P_2\). Either (i) diffusion is constant or (ii) drift and diffusion satisfy the paper’s uniform linear-growth bound.</dd>
<dt>A2 — Stationary pair</dt><dd>There are \(s_\star\) and \(\nu_\star\in\mathcal P_2\) with \(P_\theta s_\star=\theta_\star\), \(\nabla\ell(\theta_\star)=G_{\nu_\star}(s_\star)=0\), \(\Psi_t(s_\star,0)=0\) for every \(t\ge0\), and frozen invariant law \(\nu_\star\) having the required observation marginal. The gradient identity and its integrability are included. This is a critical point assumption.</dd>
<dt>A3 — Joint twisted monotonicity</dt><dd>For every pair of states, every two \(\mathcal P_2\) sampler laws and every coupling \(\Lambda\), at every nonnegative time,</dd></dl>
\[\begin{aligned}
q_\Lambda&=\langle\Delta s,D_s\Delta\Psi_t\rangle\\
&\quad+\int\langle\Delta z,D_z\Delta b\rangle\,d\Lambda\\
&\quad+\tfrac12\int\|\Delta\sigma\|_{D_z,{\rm HS}}^2\,d\Lambda,\\
E_\Lambda&=\|\Delta s\|_{D_s}^2\\
&\quad+\int\|\Delta z\|_{D_z}^2\,d\Lambda,\\
q_\Lambda&\le-\rho E_\Lambda,\qquad\rho&gt;0.
\end{aligned}\]
<p>The optimiser difference is between its two responses at their respective state and law. Sampler differences use their respective parameters; the diffusion norm is the Hilbert–Schmidt norm weighted by \(D_z\). Every displayed signed integral must have its stated domain.</p>
<dl class="source-assumptions"><dt>A4 — Gradient response</dt><dd>\(\|\Psi_t(s,g)-\Psi_t(s,\widetilde g)\|\le L_\Psi\|g-\widetilde g\|\), uniformly in \(t,s\), with \(L_\Psi\ge0\).</dd>
<dt>A5 — Reference fluctuation</dt><dd>Along the chosen mean-field path,
\(\sup_{t\ge0}\mathbb E\|F(\bar\theta_t,P_x\bar Z_t)-G_{\bar\nu_t}(\bar s_t)\|^2\le V_F&lt;\infty\).
The observation is integrable, so this is a defined variance.</dd></dl>''')
    body += ('<p class="statement-source">Complete source hypotheses, solution domains and exact contracts: '
             '<a href="source_audit.md">source audit</a> · <a href="assumption_inventory.json">assumption inventory</a>.</p></section>'
             '<section class="section" id="paper-theorems"><h2>Main theorems of the paper</h2>')

    body += article('theorem-1', 'Theorem 1 — Invariant measure', r'''
<p><strong>Paper assumptions.</strong> A1 and A2. Initialise \(s_0=s_\star\) deterministically and \(Z_0\sim\nu_\star\), independently of the Brownian driver.</p>
<div class="interpretation-assumption" data-assumption-kind="interpretation"><strong>A2 interpretation.</strong> Frozen invariance means an actual stationary weak frozen SDE on some Brownian probability space, with continuous adapted paths and its original local integral equation. A generator identity alone does not supply A2.</div>
<p class="no-added-assumption"><strong>Added analytic assumptions: none.</strong> The frozen process may be weak and on a different probability space. No global Lipschitz bound or additional drift-growth condition is imposed.</p>
<div class="theorem-conclusion"><p><strong>Statement.</strong> For every \(t\ge0\),</p>
\[\mathcal L(s_t,Z_t)=\mu_\star:=\delta_{s_\star}\otimes\nu_\star.\]
<p>For time-dependent \(\Psi_t\), this asserts a stationary solution. The target is the A2 critical point.</p></div>''', [
        ('PBGSO/RawPathSolutionTransfer.lean', 'stationary_product_law_of_weak_frozen', 'Formal statement and complete proof')], source='thm:invariant_measure')

    body += article('theorem-2', 'Theorem 2 — Contraction under joint twisted monotonicity', r'''
<p><strong>Paper assumptions.</strong> A1 and A3, deterministic initial optimiser states, and initial sampler laws in \(\mathcal P_2\). For the stationary-target and uniqueness conclusions, also A2.</p>
<div class="added-assumption" data-assumption-kind="added"><strong>Added condition — constant diffusion branch.</strong> For every optimiser pair and every joint probability law with finite quadratic moment, the signed sampler work \(\langle\Delta z,D_z\Delta b\rangle\) is absolutely integrable (<code>FiniteCouplingWork</code>). This is the ordinary finite signed-integral reading of universal A3, imposed separately from the conditional inequality. It excludes some superlinear dissipative models admitted by an extended-negative-work reading.</div>
<div class="added-assumption" data-assumption-kind="added"><strong>Explicit measurability — constant diffusion branch.</strong> The projected observation and drift are jointly Borel, the optimiser response is jointly Borel in time, state and gradient, and each frozen drift is Borel.</div>
<div class="added-assumption" data-assumption-kind="added"><strong>Explicit regularity — linear-growth branch.</strong> Each frozen drift and diffusion column is Borel. Along the canonical strong solutions, drift and diffusion are jointly strongly measurable, and the drift is progressively strongly measurable. The parameter projection is continuous, as Euclidean coordinate projections are. Moments, stochastic-integral matching and the energy inequality are proved from these primitives and A1(ii).</div>
<div class="interpretation-assumption" data-assumption-kind="interpretation"><strong>Solution and target interpretation.</strong> Solutions satisfy their original local SDE and optimiser integral equation. Observation integrals are defined for the comparison laws. A2 has the weak-SDE meaning in Theorem 1.</div>
<div class="theorem-conclusion"><p><strong>Statement.</strong> Let \(d_t\) be the distance between the two optimiser–law pairs at time \(t\). For every \(t\ge0\),</p>
\[d_t\le\sqrt\kappa\,e^{-\rho t}d_0.\]
<p>With A2, this gives</p>
\[\begin{gathered}W_2(\mu_t,\mu_\star)\\
\le\sqrt\kappa\,e^{-\rho t}W_2(\mu_0,\mu_\star).
\end{gathered}\]
<p>The stationary law is unique among finite-second-moment laws of the form \(\delta_s\otimes\nu\) satisfying these solution hypotheses.</p></div>''', [
        ('PBGSO/RawSamplerGrowthArbitraryLaw.lean', 'law_distance_decay', 'Linear-growth branch'),
        ('PBGSO/NaturalFiniteWorkArbitraryLaw.lean', 'law_distance_decay', 'Constant diffusion branch'),
        ('PBGSO/RawStationaryUniqueness.lean', 'stationary_laws_unique_constant', 'Stationary uniqueness: constant diffusion'),
        ('PBGSO/RawStationaryUniqueness.lean', 'stationary_laws_unique_linearGrowth', 'Stationary uniqueness: linear growth'),
        ('PBGSO/FiniteWorkScopeAudit.lean', 'exists_p2_nonintegrable_work', 'Why finite signed work is substantive')], source='thm:twisted_joint_strong_monotonicity')

    body += article('theorem-3', 'Theorem 3 — Finite-particle interaction error', r'''
<p><strong>Paper assumptions.</strong> A1, A3, A4 and A5; \(N\ge1\); a deterministic initial optimiser; i.i.d. sampler initial states with a common \(\mathcal P_2\) law, independent of independent Brownian drivers; and an actual interacting-system solution. Start the interacting and mean-field copy systems synchronously and drive each paired sampler with the same Brownian motion.</p>
<div class="interpretation-assumption" data-assumption-kind="interpretation"><strong>Given solution.</strong> The interacting solution obeys the original native empirical SDE on the independent whole-seed product, with the usual adaptedness and local-integrability domains. A1 is a mean-field existence assumption; the paper separately takes an interacting solution. The independent reference paths and their i.i.d. laws are constructed from the independent seeds.</div>
<div class="added-assumption" data-assumption-kind="added"><strong>Explicit measurability.</strong> The projected observation and drift maps are jointly Borel, and the optimiser response is jointly Borel in time, state and gradient. Neither universal finite signed work, an interacting moment estimate nor a global Lipschitz force bound is added.</div>
<div class="theorem-conclusion"><p><strong>Statement.</strong> Let \(\bar\nu_t^{[N]}=N^{-1}\sum_i\delta_{\bar Z_t^i}\) be the independent-copy empirical law. Set \(p_t^N=(s_t^N,\nu_t^N)\) and \(\bar p_t^{[N]}=(\bar s_t,\bar\nu_t^{[N]})\). Then</p>
\[\begin{gathered}
\left(\mathbb E\,d(p_t^N,\bar p_t^{[N]})^2\right)^{1/2}\\
\le c_N(1-e^{-\rho t}),\\
c_N=\frac{L_\Psi}{\rho}\sqrt{\frac{\kappa V_F}{N}}.
\end{gathered}\]
<p>This is an interaction error against an empirical reference cloud. A population-law Wasserstein bound also needs the empirical sampling term.</p></div>''', [
        ('PBGSO/RawConstructedParticleBounds.lean', 'original_finite_particle_interaction_bound', 'Formal statement and complete proof'),
        ('PBGSO/RawEmpiricalDynamics.lean', 'Solution', 'Exact native solution contract')], source='thm:finite_particle_error')

    body += article('theorem-4', 'Theorem 4 — Parameter error bound of particle system', r'''
<p><strong>Paper assumptions.</strong> A1–A5, the coupled initialisation and given interacting solution of Theorem 3, and the stationary target of Theorem 1. The parameter projection is the Euclidean coordinate projection, hence one-Lipschitz. Put \(d_0=d((s_0,\nu_0),(s_\star,\nu_\star))\).</p>
<div class="interpretation-assumption" data-assumption-kind="interpretation"><strong>Target and solution meaning.</strong> A2 is actual weak frozen-SDE invariance. The initial and target laws lie in \(\mathcal P_2\); the observation domains and native solution semantics are as above.</div>
<div class="added-assumption" data-assumption-kind="added"><strong>Explicit regularity.</strong> Use the Borel observation, drift and response maps stated for Theorem 3. In the linear-growth branch also use the canonical coefficient regularity in Theorem 2. The constant-diffusion branch does not require <code>FiniteCouplingWork</code>: A4 and A5 derive the target-comparison work estimate.</div>
<div class="theorem-conclusion"><p><strong>Statement.</strong> For every \(t\ge0\),</p>
\[\begin{aligned}
&\|\theta_t^N-\theta_\star\|_{L^2}\\
&\quad\le\sqrt\kappa\,e^{-\rho t}d_0\\
&\qquad+c_N(1-e^{-\rho t}).
\end{aligned}\]
<p>Here \(c_N\) is defined in Theorem 3. For a family with common constants and initial law, this error tends to zero as time and particle count jointly tend to infinity, and therefore in the paper’s iterated limit. The target is a critical point; a global minimiser claim requires a separate hypothesis.</p></div>''', [
        ('PBGSO/RawConstructedParticleParameter.lean', 'original_parameter_bound_constant', 'Constant diffusion branch'),
        ('PBGSO/RawConstructedParticleParameter.lean', 'original_parameter_bound_linearGrowth', 'Linear-growth branch'),
        ('PBGSO/RawConstructedParticleJointLimit.lean', 'parameter_joint_limit', 'Joint large-time and large-particle limit')], source='thm:parameter_error_full')
    body += '</section><section class="section" id="new-theory"><h2>New theory</h2>'
    body += math(r'''<p>The following are new time-uniform bounds for the actual M-MFPO and HOL-MYPGD particle updates. They are not discretisation theorems stated or proved in the manuscript. In each statement, \(t_n=nh\), \(d_x\) is the position/noise-coordinate dimension, \(d=N d_x\), and \(\widehat\theta_n^{N,h}\) uses the same initial state as the constructed continuous interacting system. Constants may depend on \(N\) and the primitive data, but are independent of \(n,h\) and the time horizon. The augmented sampler phase has dimension \(2d\) for M-MFPO and \(3d\) for HOL.</p>''')

    body += article('theorem-new-a', 'Theorem New A — M-MFPO final discretisation bound', r'''
<p><strong>Inherited assumptions.</strong> For the kinetic model \(ds=(m,-G_\nu(s)-\gamma m)dt\), \(d(x,v)=(v,-G(\theta,x)-\gamma v)dt+(0,\sqrt{2\gamma}\,dB)\), assume A3 with \(\rho&gt;0\), an actual frozen stationary \(\mathcal P_2\) law with zero mean observation at \(s_\star=(\theta_\star,0)\), and the uniform observation variance A5. The initial sampler law is in \(\mathcal P_2\), the initial optimiser is deterministic, and \(N\ge1\). Initial sampler states are i.i.d. with that law and independent of the Brownian drivers.</p>
<div class="added-assumption" data-assumption-kind="added"><strong>Extra assumptions, before the result.</strong> The independent forces \(F,G\) are globally jointly Lipschitz: for \(Q=F,G\), with its own constant \(l_Q\),
\[\begin{gathered}
\|Q(\theta,x)-Q(\theta',x')\|\\
\le l_Q(\|\theta-\theta'\|+\|x-x'\|).
\end{gathered}\]
The optimiser and sampler coordinates are finite-dimensional real Hilbert/Euclidean spaces with their usual Borel structure. Take \(\gamma\ge0\) and \(0&lt;h\le h_{*,M}\), where the explicit positive threshold below depends only on the data. Use the stated OBABO update, standard Euclidean cloud encoding, no optimiser thermal noise, and independent isotropic Gaussian sampler half-step innovations.
<p><strong>Frozen target realization.</strong> Supply an actual norm-continuous L² frozen sampler trajectory on the product of \(\nu_\star\) and the canonical Brownian source. It starts at the initial-coordinate projection, solves the frozen integral equation with the displayed physical Brownian input, and has law \(\nu_\star\) at each time. This <code>FrozenTrajectory</code> premise is more explicit than the weak frozen-invariance assertion used in Theorem 1; this endpoint does not derive it from an abstract invariant law.</p></div>
<p>The contracting particle metric, Brownian coupling, reference moments and local error coefficients are constructed from these primitives. No uniform moment bound, numerical contraction, local-error estimate or error recurrence is an additional assumption.</p>
<div class="theorem-conclusion" data-time-uniform="true"><p><strong>Statement.</strong> There are explicit finite \(D_M\ge0\) and \(h_{*,M}&gt;0\), independent of time. For every \(n\in\mathbb N\) and every \(0&lt;h\le h_{*,M}\),</p>
\[\begin{aligned}
&\|\widehat\theta_n^{N,h}-\theta_\star\|_{L^2}\\
&\quad\le D_M\sqrt h\\
&\qquad+\sqrt\kappa\,e^{-\rho t_n}d_0\\
&+\frac{2+\gamma}{\rho}\sqrt{\frac{\kappa V_F}{N}}(1-e^{-\rho t_n}).
\end{aligned}\]
<p>The discretisation error is \(O(\sqrt h)\) uniformly over all iterations, for fixed \(N\). The constants and allowed step size need not be uniform in particle count.</p></div>
<details class="bound-constants"><summary>Constants in the final bound</summary>
<p>Let \(E\) be the standard cloud encoding and put</p>
\[\begin{aligned}
L_F&=l_F(1+\|E\|),\\
L_G&=\|E^{-1}\|l_G(1+\|E\|),\\
L&=2\max(L_F,L_G),\\
K&=L+\gamma+1,\\
\Xi&=\sqrt d,\qquad\beta=\sqrt\gamma\sqrt{2d}.
\end{aligned}\]
<p>In the actual raw L² implementation coordinates, write \(f\) for the full kinetic drift, \(z_0\) for the initial state and \(g_0\) for the coupled force at zero. Let \((c_0,c_1)\) be exactly <code>momentumUniformDefect</code> evaluated at \((L,\gamma,\|g_0\|,\Xi,\beta)\). These nonnegative coefficients are explicit expressions in the primitive data, defined in the linked proof; the theorem proves the local estimate from the actual OBABO map.</p>
<p>Source A3 constructs a bounded linear metric factor \(C\) and \(m_C&gt;0\) with \(m_C\|z\|\le\|Cz\|\). They are derived, not extra stability assumptions. Let \(P\) be the proved equivalence from raw coordinates to physical particle L² coordinates. With \(\underline d_N=m\min(1,1/N)\) and \(\overline d_N=M\max(1,1/N)\) from the source metric comparisons, take</p>
\[\begin{aligned}
m_C&=\frac{\sqrt{\underline d_N}}{\|P^{-1}\|+1},\\
U_C&=\sqrt{\overline d_N}\,\|P\|,\\
S&=U_Ce^{K+1}(\|f(0)\|+\beta),\\
R&=U_C\|z_0\|\\
&\quad+\frac S{1-e^{-\rho}}+S,\\
a&=U_Cc_0,\\
b&=U_Cc_1/m_C,\\
D_M&=\frac{4(a+bR)}{\rho m_C},\\
h_{*,M}&=\min\{1,\rho^{-1},q^2\},\\
q&=\frac\rho{4(b+1)}.
\end{aligned}\]
<p>The full-state error in the raw product norm (the maximum of the component L² errors) against the continuous interacting particles is also bounded by \(D_M\sqrt h\) for every iteration. The threshold ensures \(\rho h\le1\) and \(b\sqrt h\le\rho/4\). The factor \(2+\gamma\) is the certified response bound used by this endpoint.</p></details>''', [
        ('PBGSO/FullyUniformMomentum.lean', 'numerical_parameter_bound', 'Final formal theorem'),
        ('PBGSO/MomentumUniformDefect.lean', 'momentumUniformDefect', 'Exact local coefficients'),
        ('PBGSO/MomentumUniform.lean', 'momentumUniformErrorConstant', 'Metric uniform estimate'),
        ('PBGSO/UniformStepSize.lean', 'maximumStep', 'Explicit positive step threshold')], new='A')

    body += article('theorem-new-b', 'Theorem New B — HOL-MYPGD final discretisation bound', r'''
<p><strong>Inherited assumptions.</strong> For the original higher-order model \(d\theta=-G_\nu(\theta)dt\), \(dx=u\,dt\), \(du=(-G(\theta,x)+\gamma v)dt\), \(dv=(-\gamma u-\alpha v)dt+\sqrt{2\alpha}\,dB\), assume A3 with \(\rho&gt;0\), a frozen stationary \(\mathcal P_2\) law with zero mean observation at \(\theta_\star\), and A5. Take a deterministic initial parameter, i.i.d. initial sampler states from a \(\mathcal P_2\) law independently of the Brownian drivers, and \(N\ge1\).</p>
<div class="added-assumption" data-assumption-kind="added"><strong>Extra assumptions, before the result.</strong> The independent forces \(F,G\) satisfy the same separate global joint Lipschitz bounds and finite-dimensional Hilbert/Euclidean space conditions as New A. Take \(\alpha&gt;0\), \(\gamma\ge0\), \(0&lt;h\le h_{*,H}\), and standard Euclidean cloud encoding. Use the paper’s parameter-first endpoint-force update and its printed correlated Gaussian innovation law, with independent time and spatial blocks.
<p><strong>Frozen target realization.</strong> Supply an actual norm-continuous L² frozen trajectory on \(\nu_\star\) times the canonical Brownian source, initialized by the first-coordinate projection, satisfying this model’s frozen integral equation with its physical Brownian input, and preserving \(\nu_\star\) at every time. This is the same <code>FrozenTrajectory</code> realization requirement as New A, now for the \((x,u,v)\) sampler.</p></div>
<p>The actual innovations, printed covariance, Brownian coupling, contracting particle metric, uniform reference moments and local error coefficients are constructed. No numerical contraction, moment bound or final error recurrence is assumed.</p>
<div class="theorem-conclusion" data-time-uniform="true"><p><strong>Statement.</strong> There are explicit finite \(D_H\ge0\) and \(h_{*,H}&gt;0\), independent of time. For every \(n\in\mathbb N\) and every \(0&lt;h\le h_{*,H}\),</p>
\[\begin{aligned}
&\|\widehat\theta_n^{N,h}-\theta_\star\|_{L^2}\\
&\quad\le D_H\sqrt h\\
&\qquad+\sqrt\kappa\,e^{-\rho t_n}d_0\\
&\qquad+\frac1\rho\sqrt{\frac{\kappa V_F}{N}}(1-e^{-\rho t_n}).
\end{aligned}\]
<p>The discretisation error is \(O(\sqrt h)\) uniformly over all iterations for fixed \(N\); neither the constant nor the threshold is claimed uniform in \(N\). This conservative strong rate applies to the actual printed coefficients and targets the stationary point of the forces used. Smoothed forces can have a different target from the original unsmoothed problem.</p></div>
<details class="bound-constants"><summary>Constants in the final bound</summary>
<p>Use \(L_F,L_G\) from New A. In the actual raw HOL L² coordinates, let \(f\) be the full drift and \(z_0\) the initial state. Put</p>
\[\begin{aligned}
K&=4(L_F+L_G\\
&\qquad+1+2\gamma+\alpha),\\
\beta&=\sqrt\alpha\sqrt{2d}.
\end{aligned}\]
<p>The exact nonnegative \(c_0,c_1\) are <code>holUniformLocalConstant0</code> and <code>holUniformLocalConstant1</code>, evaluated at the flattened dimension, \(\alpha,\gamma,L_F,L_G\), the lifted force norms at zero, and (for \(c_0\)) \(\|f(0)\|\). Their definitions include the actual printed coefficient and Gaussian remainder constants; the linked sources give their complete expressions.</p>
<p>Source A3 constructs the metric factor \(C\). Use the same physical/raw coordinate equivalence \(P\) and empirical metric comparisons \(\underline d_N,\overline d_N\) as in New A (now for the HOL phase). The data-only constants are</p>
\[\begin{aligned}
m_C&=\frac{\sqrt{\underline d_N}}{\|P^{-1}\|+1},\\
U_C&=\sqrt{\overline d_N}\,\|P\|,\\
S&=U_Ce^{K+1}(\|f(0)\|+\beta),\\
R&=U_C\|z_0\|\\
&\quad+\frac S{1-e^{-\rho}}+S,\\
a&=U_Cc_0,\\
b&=U_Cc_1/m_C,\\
D_H&=\frac{4(a+bR)}{\rho m_C},\\
h_{*,H}&=\min\{1,\rho^{-1},q^2\},\\
q&=\frac\rho{4(b+1)}.
\end{aligned}\]
<p>The full-state error in the raw product norm (the maximum of the component L² errors) against the continuous interacting particles is bounded by \(D_H\sqrt h\) for every iteration. The finite constants are independent of the run length; no higher force derivatives or common potential are required.</p></details>''', [
        ('PBGSO/FullyUniformHigherOrder.lean', 'parameter_bound', 'Final formal theorem'),
        ('PBGSO/HOLRestartLocal.lean', 'holUniformLocalConstant0', 'Exact local constant c₀'),
        ('PBGSO/HOLRestartLocal.lean', 'holUniformLocalConstant1', 'Exact local constant c₁'),
        ('PBGSO/HOLCovariance.lean', 'holCovarianceMatrix_eq_gram', 'Printed innovation covariance')], new='B')
    body += '</section>'
    # Verification commands are authored separately so each file can be checked directly.
    body += ('<section class="section" id="standalone-verification"><h2>Run the standalone verification</h2>'
             '<p>Use the repository’s pinned Lean and Mathlib versions. From the repository root, '
             'compile the development, then run each verification entry file:</p>'
             '<pre class="commands"><code>lake build PBGSO\n'
             'lake env lean standalone/PBGSO/PaperTheorems.lean\n'
             'lake env lean standalone/PBGSO/NewA.lean\n'
             'lake env lean standalone/PBGSO/NewB.lean</code></pre>'
             '<p>These entry files identify the exact formal endpoints and print their logical axioms. '
             'They use the repository’s checked proof modules. For a single-file proof that imports '
             'only Mathlib, generate the transitive local proof closure:</p>'
             '<pre class="commands"><code>python3 scripts/check-pbgso-standalone.py --output /tmp/pbgso-standalone --check\n'
             'lake env lean /tmp/pbgso-standalone/NewA.lean\n'
             'lake env lean /tmp/pbgso-standalone/NewB.lean</code></pre>'
             '<p>Choose a new or empty output directory. The <code>--check</code> run compiles '
             'the exported files in isolation with this project’s compiled proof modules '
             'removed from the search path. The last two commands let you rerun an individual file.</p>'
             '<p>The exported files contain the original proofs and assumptions, rather than an assumed '
             'error estimate. Compilation checks the proofs; the printed axioms should contain only '
             '<code>propext</code>, <code>Classical.choice</code> and <code>Quot.sound</code>. '
             '<a href="../../standalone/PBGSO/PaperTheorems.lean">Paper theorem entry file</a> · '
             '<a href="../../standalone/PBGSO/NewA.lean">New A entry file</a> · '
             '<a href="../../standalone/PBGSO/NewB.lean">New B entry file</a>.</p>'
             '<p>Check the complete axiom audit and the statement-to-source correspondence with:</p>'
             '<pre class="commands"><code>lake env lean PBGSO/Check.lean\n'
             'python3 -B scripts/verify-pbgso.py --require-complete</code></pre></section>')

    from report_citations import citation_panel
    body += citation_panel(None, None, None, page)
    body += '<section class="section proof-roadmap" id="proof-roadmap"><h2>Proof roadmap</h2>'
    body += ('<p>Follow the links from the primitive model through the stochastic constructions to the final theorems. '
             'Every node opens the corresponding complete Lean proof. '
             f'The <a href="{relative(CATALOG,page)}#modules">full module catalog</a> and '
             f'<a href="{relative(CATALOG,page)}#source-inventory">eight-result source ledger</a> '
             'retain the intermediate statements and all four appendix results.</p>')
    lanes = [
        ('01', 'Framework and assumptions', [
            ('PBGSO/Framework.lean','Model','Independent optimiser, observation and sampler maps'),
            ('PBGSO/PaperTheorems.lean','TwistedJointMonotonicity','Joint metric and source A3'),
            ('PBGSO/SmallGainSpectrum.lean','separated_source_criterion','Appendix: separate monotonicity criterion'),
            ('PBGSO/CanonicalProjectedCriterion.lean','canonical_projected_source_criterion','Appendix: projected criterion and its integrability domain'),
            ('PBGSO/HypocoerciveCriterion.lean','heavyBall_source_criterion','Appendix: heavy-ball hypocoercivity'),
        ]),
        ('02', 'Continuous-time paper theorems', [
            ('PBGSO/RawLocalIntegral.lean','RawLocalDiffusion','Actual local Brownian integral'),
            ('PBGSO/RawPathSolutionTransfer.lean','stationary_product_law_of_weak_frozen','Weak frozen invariance → Theorem 1'),
            ('PBGSO/RawSamplerGrowthArbitraryLaw.lean','law_distance_decay','Linear growth → Theorem 2'),
            ('PBGSO/NaturalFiniteWorkArbitraryLaw.lean','law_distance_decay','Constant diffusion and finite work → Theorem 2'),
            ('PBGSO/RawConstructedParticleBounds.lean','original_finite_particle_interaction_bound','Independent references and localisation → Theorem 3'),
            ('PBGSO/RawConstructedParticleParameter.lean','original_parameter_bound_constant','Stationary comparison and interaction → Theorem 4'),
        ]),
        ('03', 'M-MFPO → Theorem New A', [
            ('PBGSO/ParticleMethodLp.lean','meanForce_lipschitz','Empirical forces and actual raw/L² updates'),
            ('PBGSO/ImplementationMetric.lean','momentum_metric','Source A3 → actual contracting particle metric'),
            ('PBGSO/UniformIntegralMoments.lean','uniform_moment','Derived moments uniform over all time'),
            ('PBGSO/MomentumUniformDefect.lean','obabo_affine_local_defect','Actual Gaussian OBABO local error'),
            ('PBGSO/UniformDiscrete.lean','one_step_same_initial_uniform_norm','Small-step absorption of accumulated errors'),
            ('PBGSO/FullyUniformMomentum.lean','numerical_parameter_bound','Time-uniform numerical parameter bound'),
        ]),
        ('04', 'HOL-MYPGD → Theorem New B', [
            ('PBGSO/HigherOrderRates.lean','holCoefficient_bounds','Actual printed coefficients and remainders'),
            ('PBGSO/ImplementationMetric.lean','higherOrder_metric','Source A3 → actual contracting particle metric'),
            ('PBGSO/HOLRestart.lean','higherOrderRestart_contracts','Constructed exact restarts and their contraction'),
            ('PBGSO/HOLRestartLocal.lean','higherOrderRestart_local_error','Printed Gaussian scheme: derived local error'),
            ('PBGSO/HOLUniform.lean','higherOrder_time_uniform_of_integral','All-iteration strong discretisation bound'),
            ('PBGSO/FullyUniformHigherOrder.lean','parameter_bound','Time-uniform numerical parameter bound'),
        ]),
    ]
    body += '<div class="roadmap-grid">'
    for number, title, nodes in lanes:
        body += f'<div class="roadmap-lane"><div class="roadmap-lane-number">{number}</div><h3>{E(title)}</h3><ol>'
        for node in nodes:
            body += '<li>' + proof(*node) + '</li>'
        body += '</ol></div>'
    body += '</div><div class="roadmap-notes">'
    body += '<h3>Appendix and scope checks</h3><ul>'
    for node in [
        ('PBGSO/ContinuousFlowMeasure.lean','phase_flow_measurePreserving_source','Volume lemma: continuous frictionless flow preserves measure'),
        ('PBGSO/FlowSourceRegularity.lean','phase_flow_fderiv_det_one_source','Volume lemma: source C¹ force and global ODE imply determinant one'),
        ('PBGSO/Volume.lean','interwovenBAB_preserves','Volume lemma: discrete frictionless splitting preserves measure'),
        ('PBGSO/DiscreteVolume.lean','interwovenBAB_fderiv_det_one','Volume lemma: discrete splitting has determinant one'),
        ('PBGSO/ProjectedFiniteWork.lean','canonical_projected_source_criterion_finite','Projected criterion: finite sampler-work domain is explicit'),
        ('PBGSO/HOLCoefficientAudit.lean','hol_linear_coefficient_not_exact','HOL scope check: printed coefficients are not the full exact linear flow'),
        ('PBGSO/FiniteWorkScopeAudit.lean','exists_p2_nonintegrable_work','A3 scope check: a P₂ law need not have finite signed work'),
    ]:
        body += '<li>' + proof(*node) + '</li>'
    body += ('</ul><p>Application-specific smoothing bias and the full-space TV prior assumptions are recorded in the '
             f'<a href="{relative(CATALOG,page)}#limitations">model and target audit</a>. '
             'They are separate from the two numerical bounds stated here.</p></div></section></div>')
    document = shell(page, 'PBGSO paper theorems and new discretisation bounds', body, 'PBGSO')
    return document.replace('</head>', '<link rel="stylesheet" href="' +
                            relative('docs/assets/pbgso.css', page) + '"></head>')
