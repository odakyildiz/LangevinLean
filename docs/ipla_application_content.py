"""New IPLA rates obtained from the sharp Wasserstein theorem."""


def section(title, body, *references, statement=False):
    return dict(title=title, body=body, statement=statement,
                references=[dict(file=path, name=name) for path, name in references])


IPLA_APPLICATION_PAGES = {
    'WassersteinMixing/exposition/ipla.html': dict(
        library='WassersteinMixing',
        label='Project 10 application · new IPLA bounds',
        title='Application to IPLA',
        intro=r'''<p>Combining the sharp Wasserstein bias of Project 10 with
        <a href="../../IPLA/exposition/index.html">Project 03</a>'s particle
        geometry and parameter concentration gives an IPLA parameter bound whose
        discretization term is proportional to \(\gamma\), in place of
        Project 03's \(\sqrt\gamma\) term. The concentration and transient terms
        are unchanged. These results are new deductions in this project, not
        numbered statements of either source paper.</p>
        <p><strong>Regularity difference.</strong> The bounds below assume
        \(U_y\in C^2\), \(\gamma&gt;0\) and \(\gamma L\le1\); when
        \(L&gt;0\), the step restriction is \(\gamma\le1/L\). Project 03 requires only a
        differentiable potential with Lipschitz gradient and allows
        \(0&lt;\gamma\le2/(m+L)\). No third derivative or Lipschitz constant of
        the Hessian is assumed.</p>''',
        sections=[
            section('Linear-step parameter error for IPLA', r'''
<p>Fix an observation \(y\) and a joint potential
\(U_y:\mathbb R^{d_\theta}\times\mathbb R^{d_x}\to\mathbb R\) of class
\(C^2\). Assume \(U_y\) is \(m\)-strongly convex with \(m&gt;0\) and has
\(L\)-Lipschitz gradient with \(L\ge0\). Let \(N\ge1\); the independent dimensions
\(d_\theta,d_x\ge0\) may be zero. Define</p>
\[\ell_y(\theta)=\int e^{-U_y(\theta,x)}dx,\quad
\theta_\star\in\operatorname*{argmax}_\theta\ell_y(\theta).\]
<p>In scaled coordinates \(z=(\theta,x^1/\sqrt N,\ldots,x^N/\sqrt N)\), set</p>
\[V_N(z)=\sum_{i=1}^NU_y(\theta,\sqrt N z_i),\qquad
\Pi_N(dz)\propto e^{-V_N(z)}dz.\]
<p>Assume the initial state has a finite second moment. Let all Gaussian
vectors in the following recursion be standard and independent of one another
and of the initial state. For \(\gamma&gt;0\) and \(\gamma L\le1\), define the IPLA iterates
by</p>
\[\begin{aligned}
\theta_{k+1}&=\theta_k-\frac\gamma N\sum_i\nabla_\theta U_y(\theta_k,x_k^i)+\sqrt{2\gamma/N}\,\xi_k^0,\\
x_{k+1}^i&=x_k^i-\gamma\nabla_xU_y(\theta_k,x_k^i)+\sqrt{2\gamma}\,\xi_k^i.
\end{aligned}\]
<p>Writing \(\mu_0\) for the initial scaled-state law, for every
\(k\in\mathbb N\),</p>
\[\begin{aligned}
\bigl(\mathbb E\|\theta_k-\theta_\star\|^2\bigr)^{1/2}
\le{}&\sqrt{\frac{2d_\theta}{Nm}}+(1-m\gamma)^kW_2(\mu_0,\Pi_N)\\
&+\frac{6L}{\sqrt m}\sqrt{d_x+\frac{d_\theta}{N}}\,\gamma.
\end{aligned}\]
<p>Only the last term differs from Project 03, where it is</p>
\[\frac{33}{20}\frac Lm\sqrt{d_x+\frac{d_\theta}{N}}\,\sqrt\gamma.\]
<p>Letting \(k\to\infty\),</p>
\[\limsup_{k\to\infty}\bigl(\mathbb E\|\theta_k-\theta_\star\|^2\bigr)^{1/2}
\le\sqrt{\frac{2d_\theta}{Nm}}+\frac{6L}{\sqrt m}\sqrt{d_x+\frac{d_\theta}{N}}\,\gamma.\]
<p>The ordering \(m\le L\) follows from the assumptions when
\(d_\theta+d_x&gt;0\); it is not an additional hypothesis. As in Project 03,
\(\theta_\star\) exists and is unique, and the Gibbs measure is normalized and
has finite second moments. The stationary Langevin reference process and the
Poisson comparison of Project 10 are constructed in the proof. If
\(d_\theta=d_x=0\), the state space is a single point: the parameter error,
both transport distances and both discretization terms are zero.</p>''',
                    ('WassersteinMixing/IPLATheorem.lean', 'ipla_linear_step_bound'),
                    statement=True),

            section('Comparison with Project 03', r'''
<p>Write \(D_N=d_x+d_\theta/N\). The two discretization terms differ by an
explicit factor:</p>
\[\frac{6L}{\sqrt m}\sqrt{D_N}\,\gamma
=\frac{40}{11}\sqrt{m\gamma}\cdot\frac{33}{20}\frac Lm\sqrt{D_N}\sqrt\gamma.\]
<p>On the common step range, the new bound is no larger than Project 03's whenever</p>
\[m\gamma\le\Bigl(\frac{11}{40}\Bigr)^2=\frac{121}{1600},\]
<p>The displayed multiplicative factor tends to zero as \(\gamma\to0\).
When \(D_N&gt;0\), Project 03's discretization term is strictly smaller for
\(m\gamma&gt;121/1600\), provided the step is admissible for both bounds.
When \(D_N=0\), both terms vanish.</p>
<div class="table-wrap"><table><thead><tr><th></th><th>Project 03</th><th>Linear-step bound</th></tr></thead>
<tbody><tr><th>Discretization term</th>
<td>\(\frac{33}{20}\frac Lm\sqrt{D_N}\sqrt\gamma\)</td>
<td>\(\frac{6L}{\sqrt m}\sqrt{D_N}\,\gamma\)</td></tr>
<tr><th>Order in the step</th><td>\(\gamma^{1/2}\)</td><td>\(\gamma\)</td></tr>
<tr><th>Step range</th><td>\(0&lt;\gamma\le2/(m+L)\)</td><td>\(\gamma&gt;0,\ \gamma L\le1\)</td></tr>
<tr><th>Regularity</th><td>Differentiable, \(L\)-Lipschitz gradient</td>
<td>\(C^2\), \(L\)-Lipschitz gradient</td></tr></tbody></table></div>
<p>The concentration term \(\sqrt{2d_\theta/(Nm)}\) and the transient
\((1-m\gamma)^kW_2(\mu_0,\Pi_N)\) are identical in the two bounds.</p>''',
                    ('IPLA/Theorem.lean', 'theorem1'),
                    ('WassersteinMixing/IPLATheorem.lean', 'ipla_linear_step_term_eq_project03_mul'),
                    ('WassersteinMixing/IPLATheorem.lean', 'ipla_linear_step_term_le_project03'),
                    statement=True),

            section('Initialization from the stationary law', r'''
<p>Under the same assumptions, the IPLA recursion has a stationary law
\(\widehat\Pi_{N,\gamma}\) for the scaled state with finite second moment:
if \(z_0\sim\widehat\Pi_{N,\gamma}\), then \(z_1\sim\widehat\Pi_{N,\gamma}\).
For every such law and every \(k\in\mathbb N\),</p>
\[\begin{aligned}
\bigl(\mathbb E\|\theta_k-\theta_\star\|^2\bigr)^{1/2}
\le{}&\sqrt{\frac{2d_\theta}{Nm}}+(1-m\gamma)^kW_2(\mu_0,\widehat\Pi_{N,\gamma})\\
&+\frac{6L}{\sqrt m}\sqrt{d_x+\frac{d_\theta}{N}}\,\gamma.
\end{aligned}\]
<p>This is the form of Project 10's Corollary 1.1. In nonzero joint dimension,
one step contracts \(W_2\) by \(0\le1-m\gamma&lt;1\), so any two such stationary
laws are at distance zero. In zero joint dimension, every probability law is
the same point mass. Thus the bound does not depend on the choice.</p>''',
                    ('WassersteinMixing/IPLATheorem.lean', 'ipla_stationary_law_exists'),
                    ('WassersteinMixing/IPLATheorem.lean', 'ipla_linear_step_bound_stationary'),
                    statement=True),

            section('Accuracy and iteration complexity', r'''
<p>Under the same assumptions on \(U_y\), the maximizer, the initialization and
the Gaussian innovations, let \(\varepsilon&gt;0\) and choose
\(N\ge1\) with \(N\varepsilon^2\ge18d_\theta\). Put
\(D_N=d_x+d_\theta/N\). If \(D_N=0\), both dimensions are zero and the
normalized parameter error is zero for every iteration and every admissible
positive step; no accuracy-driven step or iteration choice is needed.
Suppose now that \(D_N&gt;0\). Then \(L\ge m&gt;0\), and choose</p>
\[\gamma=\frac1{L\max\bigl(1,18\sqrt{D_N}/\varepsilon\bigr)},\]
<p>that is, \(\gamma=\frac1L\min\bigl(1,\frac{\varepsilon}{18\sqrt{D_N}}\bigr)\)
when \(D_N&gt;0\). Then every \(k\in\mathbb N\) with</p>
\[k\ge\frac Lm\max\Bigl(1,\frac{18\sqrt{D_N}}\varepsilon\Bigr)
\log\Bigl(1+\frac{3\sqrt m\,W_2(\mu_0,\Pi_N)}\varepsilon\Bigr)\]
<p>satisfies</p>
\[\sqrt m\,\bigl(\mathbb E\|\theta_k-\theta_\star\|^2\bigr)^{1/2}\le\varepsilon.\]
<p>The particle condition, the step and the iteration count each bound one of
the three normalized terms by \(\varepsilon/3\). The same choices also work
with \(W_2(\mu_0,\widehat\Pi_{N,\gamma})\) in the logarithm, for any
stationary law \(\widehat\Pi_{N,\gamma}\) with finite second moment.</p>
<p>With \(\kappa=L/m\), the iteration count is
\(\mathcal O\bigl(\kappa\max(1,\sqrt{D_N}/\varepsilon)\bigr)\) up to the
logarithmic initialization factor. Allocating the same thirds in Project 03
requires \(m\gamma\le400\varepsilon^2/(9801\kappa^2D_N)\) when \(D_N&gt;0\),
which gives \(\mathcal O\bigl(\kappa\max(1,\kappa D_N/\varepsilon^2)\bigr)\)
iterations. Each iteration evaluates \(N\) joint gradients. For fixed
\(d_\theta,d_x&gt;0\) and fixed \(m,L\), taking \(N\) proportional to
\(\varepsilon^{-2}\) gives total gradient work of order \(\varepsilon^{-3}\)
instead of \(\varepsilon^{-4}\), up to logarithmic factors and the dependence
of the initialization distance on \(N\).</p>''',
                    ('WassersteinMixing/IPLATheorem.lean', 'ipla_linear_step_accuracy'),
                    ('WassersteinMixing/IPLATheorem.lean', 'ipla_linear_step_accuracy_stationary'),
                    statement=True),

            section('Proof: the particle lift and the sharp bias', r'''
<p>The zero-dimensional case has zero parameter error, as noted above.
For the following argument suppose \(D_N&gt;0\), so \(L\ge m&gt;0\).
The scaled IPLA recursion is the Gaussian ULA recursion for \(V_N\)
with step \(h=\gamma/N\). Since
\(\sum_i\|(\delta\theta,\sqrt N\,\delta z_i)\|^2=N\|\delta z\|^2\),
the potential \(V_N\) is \(C^2\), \(Nm\)-strongly convex and has an
\(NL\)-Lipschitz gradient. Project 10 therefore applies with</p>
\[\alpha=Nm,\qquad\beta=NL,\qquad h=\frac\gamma N,\]
\[d=d_\theta+Nd_x,\qquad\kappa=\frac\beta\alpha=\frac Lm.\]
<p>The condition \(h\beta=\gamma L\le1\) is the step restriction above. The
contraction factor is \(1-\alpha h=1-m\gamma\), and the bias is</p>
\[\begin{aligned}
6h\sqrt{\kappa\beta d}
&=6\frac\gamma N\sqrt{\frac Lm\,NL\,(d_\theta+Nd_x)}\\
&=\frac{6L}{\sqrt m}\sqrt{d_x+\frac{d_\theta}N}\,\gamma.
\end{aligned}\]
<p>The cancellation of \(N\) is exact: more particles reduce the parameter
contribution \(d_\theta/N\), while the latent contribution \(d_x\) remains.
A linear isometry identifies the scaled state with standard Euclidean
coordinates. It preserves the Gibbs law, the Gaussian innovations, the
transition and quadratic transport, so no approximation is introduced.</p>''',
                    ('WassersteinMixing/IPLARates.lean', 'ipla_lifted_bias_eq'),
                    ('WassersteinMixing/IPLATheorem.lean', 'iplaLinearBias_eq_explicit')),

            section('Proof: Gibbs initialization, projection and concentration', r'''
<p>It remains to prove the bounds when \(D_N&gt;0\); the one-point case is
immediate. Let \(T\) be the IPLA transition on scaled-state laws and
\(B=6L\gamma\sqrt{D_N/m}\). Start the chain at \(\Pi_N\) and couple it
synchronously with the stationary Langevin diffusion. Project 10's
shifted-energy estimate holds uniformly in time, so
\(W_2(T^k\Pi_N,\Pi_N)\le B\) for every \(k\). Contraction of the same
transition gives
\(W_2(T^k\mu_0,T^k\Pi_N)\le(1-m\gamma)^kW_2(\mu_0,\Pi_N)\). By the
triangle inequality,</p>
\[W_2(T^k\mu_0,\Pi_N)\le(1-m\gamma)^kW_2(\mu_0,\Pi_N)+B.\]
<p>Project 03 proves the equilibrium concentration</p>
\[\Bigl(\int\|\theta-\theta_\star\|^2\,d\Pi_N\Bigr)^{1/2}
\le\sqrt{\frac{2d_\theta}{Nm}}.\]
<p>The parameter projection has norm at most one, so Minkowski's inequality on
any coupling of \(T^k\mu_0\) and \(\Pi_N\), followed by the infimum over
couplings, gives</p>
\[\bigl(\mathbb E\|\theta_k-\theta_\star\|^2\bigr)^{1/2}
\le W_2(T^k\mu_0,\Pi_N)+\sqrt{\frac{2d_\theta}{Nm}}.\]
<p>Combining the two displays proves the main bound. For the stationary
form, Project 10's Corollary 1.1 gives
\(W_2(T^k\mu_0,\Pi_N)\le(1-m\gamma)^kW_2(\mu_0,\widehat\Pi)+B\) for the
constructed stationary law \(\widehat\Pi\). If \(\Pi'\) is another stationary
law with finite second moment, then
\(W_2(\Pi',\widehat\Pi)=W_2(T\Pi',T\widehat\Pi)\le(1-m\gamma)W_2(\Pi',\widehat\Pi)\),
so \(W_2(\Pi',\widehat\Pi)=0\) and
\(W_2(\mu_0,\widehat\Pi)\le W_2(\mu_0,\Pi')\). All transport distances and
projected moments are finite before they are compared as real numbers.</p>''',
                    ('WassersteinMixing/IPLABridge.lean', 'coordinate_convergence_target_bound_sharp'),
                    ('WassersteinMixing/IPLA.lean', 'ipla_parameter_projection'),
                    ('WassersteinMixing/IPLATheorem.lean', 'IPLASetting.wasserstein2Real_invariantLaw_le')),

            section('Proof: the accuracy budget', r'''
<p>If \(D_N=0\), the parameter error is zero and the accuracy conclusion is
immediate. Suppose \(D_N&gt;0\), so \(L\ge m&gt;0\) and the chosen step is
positive. Multiply the main bound by \(\sqrt m\). The three terms become</p>
\[\sqrt{\frac{2d_\theta}N},\qquad
(1-m\gamma)^k\sqrt m\,W_2(\mu_0,\Pi_N),\qquad
6L\gamma\sqrt{D_N}.\]
<p>The first is at most \(\varepsilon/3\) exactly when
\(N\varepsilon^2\ge18d_\theta\). For the chosen step,
\(6L\gamma\sqrt{D_N}=6\sqrt{D_N}/\max(1,18\sqrt{D_N}/\varepsilon)\le\varepsilon/3\).
The step satisfies \(m\gamma\in(0,1]\) and
\(m\gamma\cdot\frac Lm\max(1,18\sqrt{D_N}/\varepsilon)=1\). With
\(R=\sqrt m\,W_2(\mu_0,\Pi_N)\), the bound
\((1-m\gamma)^k\le e^{-m\gamma k}\) and the iteration count give</p>
\[(1-m\gamma)^kR\le\frac{R}{1+3R/\varepsilon}\le\frac\varepsilon3.\]
<p>Adding the three estimates proves the accuracy statement in the remaining
nonzero-dimensional case.</p>''',
                    ('WassersteinMixing/IPLARates.lean', 'ipla_accuracy_arithmetic')),
        ]),
}
