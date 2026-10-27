"""Average-smoothness sampling proofs and separate source counterexamples."""


def node(identifier, row, col, file, title, detail, parents=(), final=False):
    return dict(id=identifier, row=row, col=col, file=file, title=title,
                detail=detail, parents=parents, final=final)


OBSTRUCTION = r'''<p>The numbered Gaussian design proposition has a
counterexample under the printed hypotheses. Set
\(n=p\), \(\Sigma=I_p\), and choose</p>
\[g_1(t)=t^2-\sin t,\qquad g_i(t)=t^2\quad(i\ge2).\]
<p>Every component is convex and infinitely differentiable, with
\(|g_i''(t)|+|g_i^{(3)}(t)|\le4\). The resulting potential is</p>
\[f(\theta)=\sum_{i=1}^p(X_i^\top\theta)^2-\sin(X_1^\top\theta).\]
<p>The directional derivative of its Hessian at zero along
\(X_1/\|X_1\|\) gives \(M_2\ge\|X_1\|^3\). For a standard Gaussian
\(Z\in\mathbb R^p\), the exact moments are</p>
\[\mathbb E\|Z\|^2=p,\qquad\mathbb E\|Z\|^4=p^2+2p.\]
<p>Thus Chebyshev yields \(\Pr(\|Z\|^2&lt;p/2)\le8/p\).
For every fixed \(C\ge0\), if \(p&gt;16\) and \(p&gt;8C^2\), then</p>
\[\boxed{\Pr(\|Z\|^3\le Cp)&lt;\tfrac12.}\]
<p>The isotropic table requires \(M_2\sqrt p\le Cn\sqrt p\), equivalently
\(M_2\le Cp\) when \(n=p\), with \(C\) depending only on the fixed
\(C_g=4\). Its probability cannot be at least one half uniformly in
dimension. This contradicts the proposition itself. The sampler convergence
theorems are independent of this false Gaussian design estimate.</p>'''

LMC_LOCAL = r'''<p>Let \(f:\mathbb R^p\to\mathbb R\) be differentiable,
\(m\)-strongly convex with \(M_\infty\)-Lipschitz gradient, where
\(m&gt;0\). The coordinate constants are the literal Taylor suprema in the
paper, and \(M_{\rm av}=p^{-1}\sum_j M_j\). For the actual independent
Gaussian step \(X^+=X-h\nabla f(X)+\sqrt{2h}\,Z\), every \(h\ge0\) satisfies</p>
\[W_2^2(\nu^+,\pi)\le
\frac{1-mh}{1+mh}W_2^2(\nu,\pi)+
\frac{(M_{\rm av}+m)h^2p}{1+mh}+
\frac{h^2(hM_\infty-1)}{1+mh}\mathbb E_\nu\|\nabla f\|^2.\]
<p>The energy comparison, Gaussian smoothing, Brownian orthogonality and
transport infimum are proved from these hypotheses. This real-valued local
formula is stated for finite quadratic transport, so every signed energy term
is defined. The nonnegative global estimates below also cover infinite
initial transport.</p>'''

LMC_CONSTANT = r'''<p>For \(0\le h\le1/M_\infty\), the score correction
is nonpositive. Iterating the actual Gaussian transition gives</p>
\[W_2^2(\nu_k,\pi)\le e^{-2mkh}W_2^2(\nu_0,\pi)
+\frac{(M_{\rm av}+m)hp}{2m}.\]
<p>The proof propagates finite moments and discharges the recurrence for each
actual marginal law. An extended-nonnegative version proves the same bound
for every probability initialization, without adding a moment hypothesis.</p>'''

LMC_VARIABLE = r'''<p>Write \(\kappa_\infty=M_\infty/m\),
\(\kappa_{\rm av}=M_{\rm av}/m\), and suppose
\(W_2^2(\nu_0,\pi)\le\varepsilon_0^2p/m\). Set</p>
\[k_0=\left\lceil\frac{\kappa_\infty}{2}
\log_+\frac{2\kappa_\infty\varepsilon_0^2}{\kappa_{\rm av}+1}\right\rceil,
\qquad h_k=\frac1{M_\infty+m(k-k_0)_+}.\]
<p>The actual varying-step chain obeys, for every \(k\ge k_0\),</p>
\[W_2^2(\nu_k,\pi)\le
\frac{\kappa_{\rm av}+1}{\kappa_\infty+k-k_0}\frac p m.\]
<p>The literal schedule, positive-part burn-in and iteration ceiling are
checked, including zero initial error. The source's bounded initial error
itself supplies all moment finiteness used by the proof.</p>'''

SGLD = r'''<p>Let \(f=\sum_{i=1}^n f_i\), each component have a Lipschitz
gradient, and the full potential be \(n\bar m\)-strongly convex. With its
unique minimizer \(\theta_*\), the actual update is</p>
\[X^+=X-hn(\nabla f_I(X)-\nabla f_I(\theta_*))+\sqrt{2h}\,Z,\]
<p>where the uniform index and standard Gaussian are independent of each
other and the initialization. The component seminorms define exactly
\(M_{\rm rms}^2=n^{-1}\sum_i\|\nabla f_i\|_{\rm Lip}^2\), and
\(\bar M_{\rm av}=M_{\rm av}(f)/n\), as in the source. For
\(0\le h\le\bar m/(3nM_{\rm rms}^2)\),</p>
\[W_2^2(\nu_k,\pi)\le(1+n\bar m h)^{-k}W_2^2(\nu_0,\pi)
+\left(\bar M_{\rm av}+2\bar m+
\frac{2M_{\rm rms}^2}{\bar m}\right)\frac{hp}{\bar m}.\]
<p>The estimator is proved unbiased, its variance is computed exactly, and
disintegration constructs the required coupling. No convexity assumption on
the individual components or additional derivative order is used. The
extended version covers every probability initialization.</p>'''

LAPLACIAN = r'''<p>Let \(f\in C^3(\mathbb R^p)\) be \(m\)-strongly
convex with \(M_\infty\)-Lipschitz gradient, \(m&gt;0\), and assume exactly</p>
\[\|\nabla\Delta f(x)\|^2\le M_\Delta^2p\qquad(x\in\mathbb R^p),\quad M_\Delta\ge0.\]
<p>For the actual Gaussian LMC chain and \(0&lt;h&lt;1/M_\infty\),</p>
\[W_2(\nu_k,\pi)\le(1-mh)^kW_2(\nu_0,\pi)
+\frac{(2M_\infty\sqrt{M_{\rm av}}+M_\Delta)h\sqrt p}{m}.\]
<p>The proof derives a weighted Dynkin identity for the constructed stationary
Brownian diffusion from fresh Gaussian Euler steps. Compact C² approximations
of its score preserve precisely the source C³ assumption; the Gibbs score
moment and gradient-generator bound retain the exact average smoothness.
Clipping and the transport infimum give the displayed constant without an
optimal-coupling premise. An extended version covers arbitrary probability
initializations. No Hessian Lipschitz condition or fourth derivative is used.</p>'''

GRADIENT = r'''<p>Let \(H\) be a complete real inner product space, and let
\(f:H\to\mathbb R\) be differentiable and \(m\)-strongly convex. For every
\(h\ge0\) and \(\theta,y\in H\),</p>
\[\|\theta-h\nabla f(\theta)-y\|^2\le
(1-mh)\|\theta-y\|^2+2h(f(y)-f(\theta))+h^2\|\nabla f(\theta)\|^2.\]
<p>This proves the printed gradient-step lemma, including its endpoint
\(h=0\). The proof expands the square and applies the first-order strong
convexity inequality. No stochastic estimate is assumed.</p>'''

RECURRENCE = r'''<p><strong>Conditional scalar result.</strong> Put
\(r_k=mW_2^2(\nu_k,\pi)/p\), \(a=\kappa_{\rm av}+1\), and \(t=mh\).
For any real sequence with \(r_0\ge0\), \(a\ge0\), and \(0\le t\le1\),
if the scalar recurrence</p>
\[r_{k+1}\le\frac{1-t}{1+t}r_k+\frac{at^2}{1+t}\]
<p>is supplied, then</p>
\[r_k\le e^{-2tk}r_0+\frac{at}{2}.\]
<p>The one-step inequality for actual LMC laws is an unproved requirement.
The geometric iteration, the exact ceiling warmup, and the harmonic schedule
arithmetic of Proposition 1 are checked separately. These scalar proofs
establish no new Wasserstein theorem on their own.</p>'''

AVERAGE_CONFIG = {
    'AverageLMC': dict(
        label='Average smoothness · sampling proofs and source audit',
        title='Langevin Monte Carlo with Average Smoothness',
        subtitle='The average-smoothness convergence argument and its supporting probability estimates.',
        top_notice='<a href="mistakes.html"><strong>Mistakes in the supplied manuscript: separate counterexample pages →</strong></a>',
        status='The main sampling theorems and decreasing-step proposition are proved for actual Gaussian laws with the source hypotheses and constants. Verified mistakes have separate counterexample pages; the source audit records broader auxiliary coverage separately.',
        namespace='AverageLMC',
        formal_note='The displayed statements concern actual Gaussian sampling laws. The source inventory distinguishes main theorem coverage, auxiliary scope, and verified false statements.',
        archive='AverageLMC/exposition/reference_audit.json',
        archive_label='Complete source inventory, exact statements, and coverage status (JSON)',
        extra=[('AverageLMC/README.md', 'Scope, counterexample, and build commands'),
               ('AverageLMC/exposition/mistakes.html', 'Mistakes and separate counterexample pages'),
               ('AverageLMC/exposition/README.md', 'Source correspondence and obstruction')],
        results=[
            dict(title='Theorem 1: the actual one-step average-smoothness bound',
                 file='AverageLMC/GaussianLMC.lean', name='lmc_one_step', body=LMC_LOCAL),
            dict(title='Theorem 1: constant-step convergence',
                 file='AverageLMC/Theorem.lean', name='lmc_constant_step', body=LMC_CONSTANT),
            dict(title='Proposition 1: the exact decreasing-step schedule',
                 file='AverageLMC/Theorem.lean', name='lmc_variable_step', body=LMC_VARIABLE),
            dict(title='Theorem 2 (th:3): LMC with the exact Laplacian condition',
                 file='AverageLMC/LaplacianTheorem.lean', name='lmc_laplacian', body=LAPLACIAN),
            dict(title='The SGLD main theorem with exact component RMS smoothness',
                 file='AverageLMC/SGLDTheorem.lean', name='sgld_constant_step_paper', body=SGLD)],
        diagram=[
            node('constants', 0, 0, 'AverageLMC/Assumptions.lean',
                 'Define the exact smoothness constants', 'Coordinate Taylor suprema; actual Laplacian'),
            node('score', 0, 1, 'AverageLMC/ScoreMoment.lean',
                 'Identify the actual Gibbs score moment', r'\(\mathbb E_\pi\|\nabla f\|^2\le pM_{\rm av}\)', ('constants',)),
            node('glm', 0, 2, 'AverageLMC/GLMCounterexample.lean',
                 'Isolate the false GLM proposition', 'Separate counterexample pages and checked certificates'),
            node('gradient', 1, 0, 'AverageLMC/Smoothing.lean',
                 'Prove coordinatewise expected smoothing', 'Independent centered unit-variance coordinates', ('constants',)),
            node('dynkin', 1, 1, 'AverageLMC/LaplacianBrownianDynkin.lean',
                 'Derive the true weighted Dynkin identity', 'Fresh Gaussian steps and a uniform Euler limit', ('score',)),
            node('estimator', 1, 2, 'AverageLMC/SGLDEstimator.lean',
                 'Compute the finite-index estimator variance', 'Exact component RMS seminorm and zero mean', ('constants',)),
            node('recurrence', 2, 0, 'AverageLMC/GaussianLMC.lean',
                 'Prove the actual Gaussian one-step bound', 'Constructed Brownian comparison and energy identity', ('gradient',)),
            node('variable', 3, 0, 'AverageLMC/Theorem.lean',
                 'Prove constant and decreasing-step convergence', 'Actual laws, exact warmup and accuracy count', ('recurrence',)),
            node('laplacian', 2, 1, 'AverageLMC/LaplacianTheorem.lean',
                 'Prove the exact Laplacian LMC bound', 'Gibbs C² cutoffs and dimension-preserving duality', ('dynkin',)),
            node('sgld', 2, 2, 'AverageLMC/SGLDTheorem.lean',
                 'Prove the actual SGLD main theorem', 'Exact estimator variance and RMS constants', ('recurrence', 'estimator')),
            node('audit', 3, 1, 'AverageLMC/Check.lean',
                 'Audit the proved dependencies', 'Main theorem and source-error coverage', ('sgld', 'glm', 'laplacian', 'variable'), True)]),
}


AVERAGE_PAGES = {
    'AverageLMC/exposition/mistakes.html': dict(
        library='AverageLMC', label='Mistakes in the supplied manuscript',
        title='Verified mistakes and counterexamples',
        intro=r'''<p>The following pages record specific false source statements.
An unfinished proof is not a counterexample. The sampling proofs are
independent of these mistakes.</p>''',
        sections=[dict(title='Separate counterexample pages', body=r'''
<ul><li><a href="counterexamples/glm-hessian.html">Proposition 2: the isotropic Hessian Lipschitz bound</a>.</li>
<li><a href="counterexamples/glm-fourth-moment.html">The uniform empirical fourth-moment event in its proof</a>.</li>
<li><a href="counterexamples/sgld-transient.html">The intermediate SGLD transient comparison under only a one-third step restriction</a>.</li></ul>
<p>The SGLD example concerns the stated intermediate implication; it does not refute
the main bound or the later bound with a stricter precision-dependent step choice.
The GLM certificate proves \(M_2\ge\|X_1\|^3\), which is incompatible with
the proposed uniform bound at \(n=p\).</p>''',
            references=[dict(file='AverageLMC/GLMCounterexample.lean', name='no_uniform_glmHessian_bound')])]),
    'AverageLMC/exposition/counterexamples/glm-hessian.html': dict(
        library='AverageLMC', label='Counterexample · Proposition 2',
        title='The isotropic GLM Hessian estimate is false',
        intro='<p><a href="../mistakes.html">All verified mistakes</a>. Source label: <code>prop:glm-constants</code>, isotropic row, Hessian smoothness column.</p>',
        sections=[dict(title='An allowed smooth convex GLM', body=OBSTRUCTION,
            references=[dict(file='AverageLMC/GLMObstruction.lean', name='counterexampleComponent_derivative_bound'),
                        dict(file='AverageLMC/GLMCounterexample.lean', name='no_uniform_glmHessian_bound')])]),
    'AverageLMC/exposition/counterexamples/glm-fourth-moment.html': dict(
        library='AverageLMC', label='Counterexample · Gaussian design proof event',
        title='The claimed uniform fourth-moment event is false',
        intro='<p><a href="../mistakes.html">All verified mistakes</a>. Source label: <code>eq:glm-event-4</code>. This is a separate false assertion in the proof of Proposition 2.</p>',
        sections=[dict(title='A direction chosen from the observed design', body=r'''
<p>Set \(n=p\) and \(\Sigma=I_p\). For a nonzero first row, choose
\(u=X_1/\|X_1\|\). Then</p>
\[\sup_{\|u\|=1}\sum_{i=1}^p(X_i^\top u)^4\ge\|X_1\|^4.\]
<p>The source requires this supremum to be at most \(Cp\) with probability
at least one half for a dimension independent constant C. A Gaussian row has
squared norm of order p, so its fourth power has order \(p^2\).
The checked proof converts any proposed fourth-power bound into a cubic bound
\(\|X_1\|^3\le(C+1)p\). For \(p&gt;16\) and \(p&gt;8(C+1)^2\),
the probability of that event is strictly below one half. This refutes the
printed event under the stated sample-size assumption \(p\le n\).</p>''',
            references=[dict(file='AverageLMC/OtherCounterexamples.lean', name='norm_fourth_le_empirical_direction'),
                        dict(file='AverageLMC/OtherCounterexamples.lean', name='gaussian_empirical_fourth_event_fails')])]),
    'AverageLMC/exposition/counterexamples/sgld-transient.html': dict(
        library='AverageLMC', label='Counterexample · intermediate SGLD comparison',
        title='The stated SGLD transient implication needs a stronger step condition',
        intro='<p><a href="../mistakes.html">All verified mistakes</a>. This concerns the paragraph after the SGLD main theorem, before the precision-dependent step is imposed.</p>',
        sections=[dict(title='A concrete scalar counterexample', body=r'''
<p>Write \(a=n\bar m h\). The source says that \(0\le a\le1/3\) and
\(k\ge a^{-1}\log(2\varepsilon^{-2})\) imply
\((1+a)^{-k}&lt;0.6\varepsilon^2\). Take</p>
\[a=\tfrac13,\qquad \varepsilon=\tfrac1{10},\qquad k=16.\]
<p>The exponential series proves \(\log200\le16/3\), so the stated
iteration threshold holds. But exact rational arithmetic gives</p>
\[\left(\tfrac34\right)^{16}&gt;\tfrac35\left(\tfrac1{10}\right)^2.\]
<p>The proof loses the factor \(0.95^k\) when exponentiating
\(1+a\ge0.95e^a\). This counterexample does not apply to the later,
stricter step choice tied to the target precision, and it does not disprove
the SGLD main theorem.</p>''',
            references=[dict(file='AverageLMC/OtherCounterexamples.lean', name='sgld_transient_comparison_counterexample')])]),
}
