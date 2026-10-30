"""Average-smoothness sampling proofs and source correspondence."""


def node(identifier, row, col, file, title, detail, parents=(), final=False):
    return dict(id=identifier, row=row, col=col, file=file, title=title,
                detail=detail, parents=parents, final=final)


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

LMC_CONSTANT = r'''<p>For finite \(W_2(\nu_0,\pi)\) and \(0\le h\le1/M_\infty\), the score correction
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
checked, including zero initial error. The paired statement bounds the
real-valued distance, so finiteness of \(W_2(\nu_0,\pi)\) is a separate
hypothesis there; a companion version states the initial bound in
\([0,\infty]\) and derives this finiteness from it.</p>'''

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
bound is stated in \([0,\infty]\), so it covers every probability
initialization.</p>'''

LAPLACIAN = r'''<p>Let \(f\in C^3(\mathbb R^p)\) be \(m\)-strongly
convex with \(M_\infty\)-Lipschitz gradient, \(m&gt;0\), and assume exactly</p>
\[\|\nabla\Delta f(x)\|^2\le M_\Delta^2p\qquad(x\in\mathbb R^p),\quad M_\Delta\ge0.\]
<p>For the actual Gaussian LMC chain with finite \(W_2(\nu_0,\pi)\) and
\(0&lt;h&lt;1/M_\infty\),</p>
\[W_2(\nu_k,\pi)\le(1-mh)^kW_2(\nu_0,\pi)
+\frac{(2M_\infty\sqrt{M_{\rm av}}+M_\Delta)h\sqrt p}{m}.\]
<p>The proof derives a weighted Dynkin identity for the constructed stationary
Brownian diffusion from fresh Gaussian Euler steps. Compact \(C^2\) approximations
of its score preserve precisely the source \(C^3\) assumption; the Gibbs score
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


def part(identifier, title, body, references=()):
    return dict(id=identifier, title=title, body=body,
                references=[dict(file=file, name=name) for file, name in references])


AVERAGE_PROOF = [
part('energy', 'Gaussian smoothing and the energy comparison', r'''<p>The
supremum defining \(M_j\) gives
\(f(x+ae_j)\le f(x)+a\,\partial_jf(x)+\tfrac12M_ja^2\) for all \(x\) and
\(a\). Insert the coordinates of a standard Gaussian vector \(\xi\) one at a
time, with \(a=\sqrt{2s}\,\xi_j\). Each \(\xi_j\) is centered and independent
of the coordinates already inserted, so its linear term has mean zero, while
\(\mathbb E a^2=2s\). Summing over \(j\),</p>
\[\mathbb E f(x+\sqrt{2s}\,\xi)-f(x)\le s\sum_{j=1}^pM_j=pM_{\rm av}s
\qquad(s\ge0).\]
<p>Couple \(\vartheta\sim\nu\) with \(Y_0\sim\pi\) at finite cost. Let
\(Y_t=Y_0-\int_0^t\nabla f(Y_s)\,ds+B_t\), \(B_t=\sqrt2W_t\), be the
stationary Langevin diffusion driven by a Brownian motion independent of
\((\vartheta,Y_0)\). Put \(A=\vartheta-h\nabla f(\vartheta)\), so that
\(A+B_h\sim\nu^+\) and \(Y_t\sim\pi\). Write \(w=W_2^2(\nu^+,\pi)\) and use
\(L^2\) norms. The common noise cancels:</p>
\[\|A+B_h-Y_h\|^2=\|A-Y_0\|^2+2\int_0^h\langle A+B_t-Y_t,\nabla f(Y_t)\rangle\,dt.\]
<p>Strong convexity bounds the integrand by
\(2\mathbb E[f(A+B_t)-f(Y_t)]-m\|A+B_t-Y_t\|^2\). Stationarity and smoothing at
the independent centre \(A\) give
\(\mathbb E[f(A+B_t)-f(Y_t)]\le\mathbb E[f(A)-f(Y_0)]+pM_{\rm av}t\). The
future increment \(B_h-B_t\) is orthogonal to \(A+B_t-Y_t\) and has squared
norm \(2(h-t)p\). Since \(w\le\|A+B_h-Y_t\|^2\) for every \(t\), this gives
\(\|A+B_t-Y_t\|^2\ge w-2(h-t)p\). Integrating over \([0,h]\) yields</p>
\[(1+mh)\,w\le\|A-Y_0\|^2+2h\,\mathbb E[f(A)-f(Y_0)]+(M_{\rm av}+m)h^2p.\]''',
     [('AverageLMC/Smoothing.lean', 'integral_stdGaussian_smoothing'),
      ('AverageLMC/GaussianPerturbation.lean', 'gaussian_energy_bound')]),
part('local', 'The one-step Wasserstein bound', r'''<p>With
\(G=\mathbb E\|\nabla f(\vartheta)\|^2\), strong convexity gives the
gradient-step inequality</p>
\[\|A-Y_0\|^2\le(1-mh)\|\vartheta-Y_0\|^2+2h\,\mathbb E[f(Y_0)-f(\vartheta)]+h^2G,\]
<p>and the \(M_\infty\)-Lipschitz gradient gives the descent inequality
\(2\mathbb E[f(A)-f(\vartheta)]\le-h(2-hM_\infty)G\). Adding both to the energy
comparison cancels every potential value:</p>
\[(1+mh)\,W_2^2(\nu^+,\pi)\le(1-mh)\|\vartheta-Y_0\|^2+(M_{\rm av}+m)h^2p
+h^2(hM_\infty-1)G.\]
<p>The output law does not depend on the initial coupling. Taking the
infimum over finite-cost couplings, which is valid also when \(1-mh&lt;0\),
and dividing by \(1+mh\) gives Theorem 1's one-step bound for \(h&gt;0\). At
\(h=0\) the transition is the identity.</p>''',
     [('AverageLMC/ExpectedGradientStep.lean', 'lp_gradient_step'),
      ('AverageLMC/ExpectedGradientStep.lean', 'lp_gradient_descent'),
      ('AverageLMC/GaussianLMC.lean', 'lmc_one_step')]),
part('constant', 'Constant-step convergence', r'''<p>For
\(0\le h\le1/M_\infty\) the score term is nonpositive and is dropped. The
coordinate bounds give \(m\le M_{\rm av}\le M_\infty\), so \(t=mh\in[0,1]\).
Finite second moments propagate from \(\nu_0\), so
\(r_k=W_2^2(\nu_k,\pi)\) satisfies, at every step,</p>
\[r_{k+1}\le q\,r_k+\frac{(M_{\rm av}+m)h^2p}{1+t},\qquad q=\frac{1-t}{1+t}.\]
<p>Since \(1-q=2t/(1+t)\), the fixed point is
\(c=(M_{\rm av}+m)hp/(2m)\), and induction gives
\(r_k\le q^kr_0+(1-q^k)c\le q^kr_0+c\). Finally \(q\le e^{-2t}\) on
\([0,1]\), so</p>
\[W_2^2(\nu_k,\pi)\le e^{-2mkh}W_2^2(\nu_0,\pi)+\frac{(M_{\rm av}+m)hp}{2m}.\]
<p>If \(W_2(\nu_0,\pi)=\infty\), the same bound holds trivially in
\([0,\infty]\).</p>''',
     [('AverageLMC/Recurrence.lean', 'contraction_le_exp'),
      ('AverageLMC/Recurrence.lean', 'constant_step_normalized'),
      ('AverageLMC/Theorem.lean', 'lmc_constant_step')]),
part('decreasing', 'The decreasing-step schedule', r'''<p>Normalize
\(r_k=mW_2^2(\nu_k,\pi)/p\), \(a=\kappa_{\rm av}+1\) and
\(t_k=mh_k=1/(\kappa_\infty+(k-k_0)_+)\). Since \(h_kM_\infty\le1\), the
stable one-step bound reads</p>
\[r_{k+1}\le\frac{1-t_k}{1+t_k}\,r_k+\frac{a\,t_k^2}{1+t_k}.\]
<p>Before \(k_0\) the step is constant, \(t_k=1/\kappa_\infty\le1\), so the
constant-step estimate gives
\(r_{k_0}\le e^{-2k_0/\kappa_\infty}\varepsilon_0^2+a/(2\kappa_\infty)\). The
ceiling defining \(k_0\) makes
\(e^{-2k_0/\kappa_\infty}\varepsilon_0^2\le a/(2\kappa_\infty)\), hence
\(r_{k_0}\le a/\kappa_\infty\). After the warmup, \(r\le a/x\) with \(x\ge1\)
implies</p>
\[\frac{1-1/x}{1+1/x}\,r+\frac{a/x^2}{1+1/x}
\le\frac{x-1}{x+1}\cdot\frac ax+\frac a{x(x+1)}=\frac a{x+1}.\]
<p>Induction with \(x=\kappa_\infty+k-k_0\) gives
\(r_k\le a/(\kappa_\infty+k-k_0)\) for \(k\ge k_0\). Multiplying by \(p/m\)
is Proposition 1. When \(\varepsilon_0=0\), \(k_0=0\) and the induction starts
at once.</p>''',
     [('AverageLMC/Complexity.lean', 'warmup_decay'),
      ('AverageLMC/Recurrence.lean', 'harmonic_step'),
      ('AverageLMC/Theorem.lean', 'lmc_variable_step')]),
part('laplacian', 'The Laplacian refinement', r'''<p>Use the coupling and
stationary diffusion of the first step, with \(L^2\) inner products. Put
\(\Psi=(\vartheta-h\nabla f(\vartheta))-(Y_0-h\nabla f(Y_0))\) and
\(R=\int_0^h(\nabla f(Y_t)-\nabla f(Y_0))\,dt\). The output error is
\(A+B_h-Y_h=\Psi+R\), and for \(hM_\infty\le1\) the gradient step contracts:
\(\|\Psi\|\le(1-mh)\|\vartheta-Y_0\|\).</p>
<p>The diffusion generator maps \(\nabla f\) to
\(\nabla\Delta f-\nabla^2f\,\nabla f\). Because \(\Psi\) is independent of the
Brownian motion, a weighted Dynkin identity, stationarity,
\(\|\nabla\Delta f\|\le M_\Delta\sqrt p\) and the Gibbs score moment
\(\mathbb E_\pi\|\nabla f\|^2\le pM_{\rm av}\) give</p>
\[\langle\Psi,\nabla f(Y_t)-\nabla f(Y_0)\rangle\le t\,\|\Psi\|\,G_\Delta,
\qquad G_\Delta=M_\infty\sqrt{M_{\rm av}p}+M_\Delta\sqrt p.\]
<p>The Dynkin identity is derived for compactly supported \(C^2\) tests from
fresh Gaussian Euler steps. Cutoffs of the score components and radial
clipping of \(\Psi\) extend it to this pairing. The integral equation,
Brownian moments and \(\mathbb E_\pi\|\nabla f\|^2\le pM_\infty\) give
\(\|R\|\le\tfrac32M_\infty h^{3/2}\sqrt p\). Expanding \(\|\Psi+R\|^2\) and
taking the coupling infimum, \(e_k=W_2(\nu_k,\pi)\) and \(q=1-mh\) satisfy</p>
\[e_{k+1}^2\le q^2e_k^2+q\,h^2G_\Delta\,e_k+\bigl(\tfrac32M_\infty h^{3/2}\sqrt p\bigr)^2.\]
<p>A recurrence \(e_{k+1}^2\le q^2e_k^2+2qCe_k+B^2\) with
\(C\le(1-q)a\) and \(B^2\le(1-q^2)b^2\) gives \(e_k\le q^ke_0+a+b\). Take
\(a=hG_\Delta/(2m)\) and \(b=3hM_\infty\sqrt{M_{\rm av}p}/(2m)\); the second
condition uses \(m\le M_{\rm av}\). Then</p>
\[a+b=\frac{(4M_\infty\sqrt{M_{\rm av}}+M_\Delta)h\sqrt p}{2m}
\le\frac{(2M_\infty\sqrt{M_{\rm av}}+M_\Delta)h\sqrt p}{m},\]
<p>which is Theorem 2 for \(0&lt;h&lt;1/M_\infty\).</p>''',
     [('AverageLMC/LaplacianPairing.lean', 'lp_stationary_gradient_pairing_bound'),
      ('AverageLMC/LaplacianOneStep.lean', 'lp_laplacian_one_step_bound'),
      ('AverageLMC/LaplacianLocalError.lean', 'laplacian_recurrence_bound_of_global_defect')]),
part('sgld', 'Control-variate SGLD', r'''<p>Let
\(g_I=n(\nabla f_I(\vartheta)-\nabla f_I(\theta_*))\). Since
\(\nabla f(\theta_*)=0\), its mean over the uniform index is
\(\nabla f(\vartheta)\). The SGLD output is the LMC output plus
\(-h(g_I-\nabla f(\vartheta))\), which has conditional mean zero given
\((\vartheta,\xi)\). Lifting any coupling of the LMC output with \(\pi\) to the
index by disintegration, the cross term vanishes, so</p>
\[W_2^2(\nu^+,\pi)\le W_2^2(\nu^+_{\rm LMC},\pi)
+h^2\bigl(\mathbb E\|g_I\|^2-\mathbb E\|\nabla f(\vartheta)\|^2\bigr).\]
<p>Write \(m=n\bar m\) and let \(M\) be a Lipschitz constant of \(\nabla f\).
The one-step LMC bound turns the score coefficient into
\(h^2(hM-1)/(1+mh)-h^2\le h^2(hM-2)/(1+mh)\), which is Proposition 3's first
claim. The component seminorms give
\(\mathbb E_I\|g_I\|^2\le n^2M_{\rm rms}^2\|\vartheta-\theta_*\|^2\), and the
Gibbs bound \(\mathbb E_\pi\|Y-\theta_*\|^2\le p/m\) gives
\(\mathbb E\|\vartheta-\theta_*\|^2\le2W_2^2(\nu,\pi)+2p/m\). Take
\(M=R=nM_{\rm rms}\). Because \(m\le R\), the step condition
\(3R^2h\le m\) implies \(hR\le1/3\), so the score term is nonpositive and</p>
\[r_{k+1}\le\Bigl(\frac{1-mh}{1+mh}+2R^2h^2\Bigr)r_k
+\Bigl(\frac{M_{\rm av}(f)+m}{1+mh}+\frac{2R^2}m\Bigr)h^2p.\]
<p>The step condition makes the contraction at most \((1+mh)^{-1}\) and the
forcing at most \((M_{\rm av}(f)+2m+2R^2/m)h^2p/(1+mh)\). The fixed point is
\((M_{\rm av}(f)+2m+2R^2/m)hp/m\). Substituting \(m=n\bar m\),
\(R=nM_{\rm rms}\) and \(M_{\rm av}(f)=n\bar M_{\rm av}\) gives the SGLD
bound; an infinite initial distance makes it trivial.</p>''',
     [('AverageLMC/SGLDLaw.lean', 'sgld_variance_addition'),
      ('AverageLMC/SGLDEstimator.lean', 'controlVariateEstimator_second_moment_le'),
      ('AverageLMC/SGLDTheorem.lean', 'sgld_one_step_rms'),
      ('AverageLMC/SGLDRecurrence.lean', 'sgld_recurrence_bound')]),
]


AVERAGE_CONFIG = {
    'AverageLMC': dict(
        label='Average smoothness · sampling proofs and source audit',
        title='Langevin Monte Carlo with Average Smoothness',
        subtitle='The average-smoothness convergence argument and its supporting probability estimates.',
        status='The main sampling theorems and decreasing-step proposition are proved for actual Gaussian laws with the source hypotheses and constants. The source audit records broader auxiliary coverage separately.',
        namespace='AverageLMC',
        formal_note='The displayed statements concern actual Gaussian sampling laws. The source inventory distinguishes main theorem coverage from broader auxiliary scope.',
        archive='AverageLMC/exposition/reference_audit.json',
        archive_label='Complete source inventory, exact statements, and coverage status (JSON)',
        extra=[('AverageLMC/README.md', 'Scope and build commands'),
               ('AverageLMC/exposition/README.md', 'Source correspondence and coverage')],
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
        proof=AVERAGE_PROOF,
        diagram=[
            node('constants', 0, 0, 'AverageLMC/Assumptions.lean',
                 'Define the exact smoothness constants', 'Coordinate Taylor suprema; actual Laplacian'),
            node('score', 0, 1, 'AverageLMC/ScoreMoment.lean',
                 'Identify the actual Gibbs score moment', r'\(\mathbb E_\pi\|\nabla f\|^2\le pM_{\rm av}\)', ('constants',)),
            node('gradient', 1, 0, 'AverageLMC/Smoothing.lean',
                 'Prove coordinatewise expected smoothing', 'Independent centered unit-variance coordinates', ('constants',)),
            node('dynkin', 1, 1, 'AverageLMC/LaplacianBrownianDynkin.lean',
                 'Derive the true weighted Dynkin identity', 'Fresh Gaussian steps and a uniform Euler limit'),
            node('estimator', 1, 2, 'AverageLMC/SGLDEstimator.lean',
                 'Compute the finite-index estimator variance', 'Exact component RMS seminorm and zero mean', ('constants',)),
            node('recurrence', 2, 0, 'AverageLMC/GaussianLMC.lean',
                 'Prove the actual Gaussian one-step bound', 'Constructed Brownian comparison and energy identity', ('gradient',)),
            node('variable', 3, 0, 'AverageLMC/Theorem.lean',
                 'Prove constant and decreasing-step convergence', 'Actual laws, exact warmup and accuracy count', ('recurrence',)),
            node('laplacian', 2, 1, 'AverageLMC/LaplacianTheorem.lean',
                 'Prove the exact Laplacian LMC bound', 'Gibbs \\(C^2\\) cutoffs and dimension-preserving duality', ('score', 'dynkin')),
            node('sgld', 2, 2, 'AverageLMC/SGLDTheorem.lean',
                 'Prove the actual SGLD main theorem', 'Exact estimator variance and RMS constants', ('recurrence', 'estimator')),
            node('audit', 3, 1, 'AverageLMC/Check.lean',
                 'Audit the proved dependencies', 'Main sampling theorem coverage', ('sgld', 'laplacian', 'variable'), True)]),
}


AVERAGE_PAGES = {}

# Sequential correspondence for the mathematical argument.
_AVERAGE_PROOF_CORRESPONDENCE = {
    'energy': r'''
<p><code>integral_stdGaussian_smoothing</code> specializes the independent-coordinate smoothing theorem to the standard Gaussian law. In its finite-coordinate induction, centering removes the linear term and the unit second moment evaluates the quadratic term. <code>gaussian_energy_bound</code> inserts this smoothing inequality into the common-noise stationary comparison; the Brownian orthogonality identity contributes the extra curvature-times-dimension term. All these are integral statements with integrability discharged before linearity is used.</p>
''',
    'local': r'''
<p><code>lp_gradient_step</code> and <code>lp_gradient_descent</code> are the two expected deterministic inequalities whose potential terms cancel. <code>lmc_one_step</code> first separates the zero step. In the positive branch, <code>hsm</code> is the exact coordinate smoothing estimate, <code>houtput</code> proves the output transport finite, and <code>wasserstein2_sq_bound_of_finite_couplings</code> passes the common bound to the infimum even when its input-cost coefficient has either sign. The final field normalization divides by the strictly positive denominator.</p>
''',
    'constant': r'''
<p><code>lmc_one_step_stable</code> first proves that the score correction is nonpositive. <code>lmc_constant_step</code> defines the actual squared-distance sequence as <code>r</code>; <code>lmcLaws_finite</code> allows the one-step theorem to be applied at every index. The block <code>hs</code> is the scalar recurrence after normalization. <code>constant_step_normalized</code> iterates it and uses <code>contraction_le_exp</code>. Finally <code>lmcLaws_const</code> identifies the recursively constructed marginal laws with iteration of the Gaussian transition.</p>
''',
    'decreasing': r'''
<p><code>warmup_decay</code> checks the initial exponential allocation, including the logarithmic ceiling. <code>harmonic_step</code> proves the single rational induction step after warmup. <code>lmc_variable_step</code> verifies admissibility of every actual step in <code>hs</code>, normalizes the initial cost in <code>hi</code>, and derives the normalized recurrence in <code>hrec</code>. <code>variable_step_normalized_all</code> handles zero initial error explicitly before applying the scalar warmup-and-tail estimate.</p>
''',
    'laplacian': r'''
<p><code>lp_stationary_gradient_pairing_bound</code> bounds the cross term with the actual stationary diffusion and the stated gradient-of-Laplacian assumption. <code>lp_laplacian_one_step_bound</code> combines that pairing with the local integral remainder and gradient-step contraction. <code>laplacian_recurrence_bound_of_global_defect</code> iterates the resulting quadratic-plus-linear scalar estimate. The final theorem <code>lmc_laplacian</code> obtains the required finite-distance recurrence for the actual Gaussian laws and simplifies its constant using the exact Gibbs score moment bound.</p>
''',
    'sgld': r'''
<p><code>sgld_variance_addition</code> uses a lifted coupling to remove the centered estimator cross term. <code>controlVariateEstimator_second_moment_le</code> bounds the estimator using the actual component Lipschitz seminorms. <code>sgld_one_step_rms</code> combines this variance bound with the one-step LMC comparison. <code>sgld_recurrence_bound</code> uses the small-step condition to bound the contraction and forcing, then sums the affine recurrence. The extended theorem separates infinite initial transport before converting any distance to a real number.</p>
''',
}
for _part in AVERAGE_PROOF:
    _part["lean"] = _AVERAGE_PROOF_CORRESPONDENCE[_part["id"]]

# Additional sequential derivations for readers of the report.
_AVERAGE_ARGUMENT_DETAILS = {
    'energy': r'''
<p><strong>Objects and hypotheses.</strong> Let \(p\ge1\), \(m&gt;0\), and let \(f:\mathbb R^p\to\mathbb R\) be differentiable, \(m\)-strongly convex and have an \(M_\infty\)-Lipschitz gradient. Thus</p>\[f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle+\frac m2\|y-x\|^2,\qquad\|\nabla f(x)-\nabla f(y)\|\le M_\infty\|x-y\|.\]<p>The Gibbs probability law is \(\pi(dx)=Z^{-1}e^{-f(x)}dx\), where strong convexity makes \(0&lt;Z&lt;\infty\) and gives finite second moments. A coupling of two probability laws is a joint law with those marginals, and \(W_2\) is the infimum of the root-mean-square displacement over couplings. Work first with \(W_2(\nu,\pi)&lt;\infty\). Throughout, a norm of a random vector means \(\|X\|_{L^2}=(\mathbb E\|X\|_2^2)^{1/2}\); its inner product is \(\mathbb E\langle X,Y\rangle\). The gradient bound \(\|\nabla f(x)\|\le\|\nabla f(0)\|+M_\infty\|x\|\) makes all score second moments finite for the states considered. The two Taylor bounds give \(|f(x)|\le|f(0)|+\|\nabla f(0)\|\|x\|+M_\infty\|x\|^2/2\), justifying the expected potential differences.</p>
''',
    'local': r'''
<p><strong>The cancellation explicitly.</strong> Strong convexity at \(\vartheta\), with comparison point \(Y_0\), gives</p>\[-2h\mathbb E\langle\nabla f(\vartheta),\vartheta-Y_0\rangle\le2h\mathbb E[f(Y_0)-f(\vartheta)]-mh\|\vartheta-Y_0\|_{L^2}^2.\]<p>Expanding \(\|\vartheta-h\nabla f(\vartheta)-Y_0\|_{L^2}^2\) produces the gradient-step bound. For the descent bound apply the upper Taylor model at \(\vartheta\) with displacement \(-h\nabla f(\vartheta)\): its linear term is \(-h\|\nabla f(\vartheta)\|^2\) and its quadratic term is \(M_\infty h^2\|\nabla f(\vartheta)\|^2/2\). Adding the two inequalities to the energy comparison cancels \(f(Y_0)\), \(f(\vartheta)\) and \(f(A)\) exactly. The remaining score coefficient is \(h^2-2h^2+h^3M_\infty=h^2(hM_\infty-1)\). Every denominator is positive because \(m&gt;0\) and \(h\ge0\).</p>
''',
    'constant': r'''
<p><strong>Induction explicitly.</strong> If \(h=0\), the chain is constant and the assertion follows by equality. If \(h&gt;0\), write \(F=(M_{\rm av}+m)h^2p/(1+mh)\). Since \(0\le q&lt;1\), the identity \(F=(1-q)c\) holds with \(c=(M_{\rm av}+m)hp/(2m)\). At \(k=0\) the proposed sharper bound \(r_k\le q^kr_0+(1-q^k)c\) is equality. If it holds at \(k\), multiply it by \(q\ge0\), add \((1-q)c\), and obtain \(q^{k+1}r_0+(1-q^{k+1})c\). This proves the induction. For \(0\le t&lt;1\), differentiation gives</p>\[\frac{d}{dt}\left(\log\frac{1-t}{1+t}+2t\right)=-\frac2{1-t^2}+2=-\frac{2t^2}{1-t^2}\le0.\]<p>The expression vanishes at zero, so \(q\le e^{-2t}\). At \(t=1\), \(q=0\) and the same inequality is immediate. Raising this nonnegative comparison to the natural power \(k\) yields the displayed exponential rate.</p>
''',
    'decreasing': r'''
<p><strong>The warmup ceiling.</strong> For \(\varepsilon_0\ne0\), set \(R=2\kappa_\infty\varepsilon_0^2/a\) and \(\log_+R=\max(\log R,0)\). If \(R\le1\), the initial error already satisfies \(\varepsilon_0^2\le a/(2\kappa_\infty)\), and the warmup may be zero. If \(R&gt;1\), the ceiling ensures \(2k_0/\kappa_\infty\ge\log R\); exponentiating its negative gives \(e^{-2k_0/\kappa_\infty}\varepsilon_0^2\le a/(2\kappa_\infty)\). In both cases the constant-step bias contributes the other half of \(a/\kappa_\infty\). After warmup \(x=\kappa_\infty+k-k_0\ge1\), so the factor \((x-1)/(x+1)\) multiplying the induction hypothesis is nonnegative. The rational calculation above therefore preserves the inequality. Positive dimension and positive \(m\) justify the final multiplication by \(p/m\). When \(\varepsilon_0=0\), the logarithmic warmup is defined to be zero and \(r_0=0\le a/\kappa_\infty\), giving the same induction directly.</p>
''',
    'laplacian': r'''
<p><strong>Bounds used by the recurrence.</strong> Here the additional assumptions are \(f\in C^3\), \(M_\Delta\ge0\) and \(\|\nabla\Delta f(x)\|^2\le M_\Delta^2p\) for every \(x\), with \(0&lt;hM_\infty&lt;1\). The derivative of the gradient has operator norm at most \(M_\infty\). Thus Cauchy–Schwarz and the score moment bound give</p>\[\|\nabla\Delta f(Y_t)-\nabla^2f(Y_t)\nabla f(Y_t)\|_{L^2}\le(M_\Delta+M_\infty\sqrt{M_{\rm av}})\sqrt p=G_\Delta.\]<p>Integrating the pairing bound over time gives \(2\langle\Psi,R\rangle\le h^2G_\Delta\|\Psi\|_{L^2}\). For the total defect, the integral equation, Minkowski and the stationary score moment give \(\|Y_t-Y_0\|_{L^2}\le t\sqrt{M_\infty p}+\sqrt{2pt}\). Hence</p>\[\begin{aligned}\|R\|_{L^2}&\le M_\infty\int_0^h\left(t\sqrt{M_\infty p}+\sqrt{2pt}\right)dt\\&=M_\infty\left(\frac{h^2}2\sqrt{M_\infty p}+\frac{2\sqrt2}3h^{3/2}\sqrt p\right)\\&\le\left(\frac12+\frac{2\sqrt2}3\right)M_\infty h^{3/2}\sqrt p\le\frac32M_\infty h^{3/2}\sqrt p.\end{aligned}\]<p>The penultimate inequality uses \(hM_\infty\le1\); the last uses \(\sqrt2\le3/2\). For the stated recurrence floor, \(C=h^2G_\Delta/2=(1-q)a\). Also \(B^2\le mh\,b^2\) follows from \(m\le M_{\rm av}\), and \(mh\le1-q^2=mh(2-mh)\). These verify both scalar recurrence hypotheses. The final enlargement of the nonnegative \(M_\Delta\) term gives precisely the printed coefficient.</p>
''',
    'sgld': r'''
<p><strong>Why the variance adds.</strong> Conditional on \((\vartheta,\xi)\), the index \(I\) is uniform and its centered error \(\eta=g_I-\nabla f(\vartheta)\) has mean zero. Expanding a lifted coupled square gives \(\mathbb E\|D-h\eta\|^2=\mathbb E\|D\|^2+h^2\mathbb E\|\eta\|^2\), because the conditional expectation of \(\langle D,\eta\rangle\) is zero. Also \(\mathbb E_I\|\eta\|^2=\mathbb E_I\|g_I\|^2-\|\nabla f(\vartheta)\|^2\). If \(L_i\) is the actual Lipschitz seminorm of \(\nabla f_i\), then</p>\[\mathbb E_I\|g_I\|^2=n\sum_i\|\nabla f_i(\vartheta)-\nabla f_i(\theta_*)\|^2\le n\sum_iL_i^2\|\vartheta-\theta_*\|^2=n^2M_{\rm rms}^2\|\vartheta-\theta_*\|^2.\]<p>For any coupling with Gibbs, \(\|\vartheta-\theta_*\|^2\le2\|\vartheta-Y\|^2+2\|Y-\theta_*\|^2\). Integrate, use the Gibbs second moment, and pass costs to their infimum to obtain the displayed second-moment bound. With \(R=nM_{\rm rms}\), the small-step condition \(3R^2h\le m\) and \(m\le R\) imply \(mh\le1/3\). The forcing comparison uses \(2R^2h\le m\): after multiplication by \(1+mh\), its extra term is at most \(mh\) in the required coefficient. The recurrence fixed point is the forcing divided by \(1-(1+mh)^{-1}=mh/(1+mh)\). At \(h=0\) the transition is the identity and this division is unnecessary.</p>
''',
}
for _part in AVERAGE_PROOF:
    if _part["id"] == "energy":
        _part["body"] = _AVERAGE_ARGUMENT_DETAILS["energy"] + _part["body"]
    else:
        _part["body"] += _AVERAGE_ARGUMENT_DETAILS[_part["id"]]
