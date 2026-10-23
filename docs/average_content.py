"""Checked components and the obstruction to exact Average LMC coverage."""


def node(identifier, row, col, file, title, detail, parents=(), final=False):
    return dict(id=identifier, row=row, col=col, file=file, title=title,
                detail=detail, parents=parents, final=final)


OBSTRUCTION = r'''<p><strong>The full paper is not formalized.</strong> Its numbered Gaussian
design proposition has a counterexample under the printed hypotheses. Set
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
dimension. This contradicts the proposition itself. It does not disprove the
paper's three sampler convergence theorems, which remain unproved here.</p>'''

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
        label='Average smoothness · source audit and partial proofs',
        title='Langevin Monte Carlo with Average Smoothness',
        subtitle='Exact deterministic lemmas, conditional rates, and a counterexample to the Gaussian design proposition.',
        status='Incomplete. The supplied Gaussian design proposition is false with its printed dimension independent constants. Its exact full-paper formalization is impossible. The actual-law convergence theorems remain unproved; checked components are identified below.',
        namespace='AverageLMC',
        formal_note='Only the displayed Lean statements are proved. The source audit records all unproved stochastic endpoints and the false GLM claim separately.',
        archive='AverageLMC/exposition/reference_audit.json',
        archive_label='Complete source inventory, exact statements, and coverage status (JSON)',
        extra=[('AverageLMC/README.md', 'Scope, counterexample, and build commands'),
               ('AverageLMC/exposition/README.md', 'Source correspondence and obstruction')],
        results=[
            dict(title='Gaussian probability obstruction to Proposition 2',
                 file='AverageLMC/GLMCounterexample.lean',
                 name='no_uniform_glmHessian_bound', body=OBSTRUCTION),
            dict(title='The exact deterministic gradient-step lemma',
                 file='AverageLMC/GradientStep.lean', name='gradient_step',
                 context='variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]',
                 body=GRADIENT),
            dict(title='The constant-step recurrence, conditional on its stochastic input',
                 file='AverageLMC/Recurrence.lean', name='constant_step_normalized',
                 body=RECURRENCE)],
        diagram=[
            node('constants', 0, 0, 'AverageLMC/Assumptions.lean',
                 'Define the exact smoothness constants', 'Coordinate Taylor suprema; actual Laplacian'),
            node('gradient', 1, 0, 'AverageLMC/GradientStep.lean',
                 'Prove deterministic gradient estimates', 'Strong convexity and smooth descent', ('constants',)),
            node('recurrence', 2, 0, 'AverageLMC/Recurrence.lean',
                 'Iterate a supplied scalar recurrence', 'Conditional on the unproved stochastic input', ('gradient',)),
            node('variable', 3, 0, 'AverageLMC/Complexity.lean',
                 'Check the variable schedule arithmetic', 'Exact ceiling warmup and accuracy count', ('recurrence',)),
            node('glm', 0, 1, 'AverageLMC/GLMObstruction.lean',
                 'Exhibit the allowed GLM obstruction', 'A quadratic potential plus a sine perturbation'),
            node('fourth', 0, 2, 'KineticLangevin/GaussianFourth.lean',
                 'Reuse exact Gaussian fourth moments', r'\(p^2+2p\), with every dimension retained'),
            node('variance', 1, 2, 'AverageLMC/GaussianObstruction.lean',
                 'Calculate the squared-norm variance', r'\(\operatorname{Var}\|Z\|^2=2p\)', ('fourth',)),
            node('probability', 2, 2, 'AverageLMC/GaussianObstruction.lean',
                 'Disprove the uniform cubic bound', r'Probability below \(1/2\) for all large \(p\)', ('variance',)),
            node('audit', 3, 1, 'AverageLMC/Check.lean',
                 'Audit the proved dependencies', 'Incomplete full-paper status remains explicit', ('glm', 'probability', 'variable'), True)]),
}
