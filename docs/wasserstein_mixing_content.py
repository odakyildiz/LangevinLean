"""Project 10: the direct proof under the original Hessian assumptions."""


def node(identifier, row, col, file, title, detail, parents=(), final=False):
    return dict(id=identifier, row=row, col=col, file=file, title=title,
                detail=detail, parents=parents, final=final)


def part(identifier, title, body, lean, references=()):
    return dict(id=identifier, title=title, body=body, lean=lean,
                references=[dict(file=file, name=name) for file, name in references])


BIAS = r'''<p>Let \(V\in C^2(\mathbb R^d)\), \(0&lt;\alpha\le\beta\), and
\(\alpha I_d\preccurlyeq\nabla^2V\preccurlyeq\beta I_d\).
For \(0&lt;h\le1/\beta\), set \(\kappa=\beta/\alpha\).
The Gibbs target is \(\pi(dx)=Z^{-1}e^{-V(x)}dx\), and
\(\widehat\pi\) is the constructed invariant law of the actual independent-Gaussian ULA transition. Then</p>
\[W_2(\pi,\widehat\pi)\le6h\sqrt{\kappa\beta d}.\]
<p>The invariant law, stationary Langevin process, reversible Markov semigroup,
Poisson corrector and synchronous comparison are all constructed from these
source assumptions. No spectral, Markov, invariant-law or comparison estimate
is an additional hypothesis of this endpoint.</p>'''

CONVERGENCE = r'''<p>Under the same source Hessian assumptions and step restriction,
let \(\mu\in\mathcal P_2(\mathbb R^d)\), and let \(\mu_k\) be the law after
\(k\) actual independent-Gaussian ULA updates. For every \(k\ge0\),</p>
\[W_2(\mu_k,\pi)\le(1-\alpha h)^kW_2(\mu,\widehat\pi)
+6h\sqrt{\kappa\beta d}.\]
<p>The measure \(\widehat\pi\) is the constructed invariant law. The exact
contraction factor and the transport triangle inequality are proved for the
same Gaussian ULA laws appearing in this statement.</p>'''

ACCURACY = r'''<p>Under the source Hessian assumptions, let
\(\mu\in\mathcal P_2(\mathbb R^d)\), \(d&gt;0\) and \(\varepsilon&gt;0\).
Choose</p>
\[h=\frac1\beta\min\!\left(1,\frac{\varepsilon}{12\sqrt d}\right).\]
<p>Every natural number \(k\) satisfying</p>
\[k\ge\kappa\max\!\left(1,\frac{12\sqrt d}{\varepsilon}\right)
\log\!\left(1+\frac{2\sqrt\alpha\,W_2(\mu,\widehat\pi)}{\varepsilon}\right)\]
<p>gives \(\sqrt\alpha\,W_2(\mu_k,\pi)\le\varepsilon\).
The step, logarithmic count and constants are the literal formulas in
Corollary 1.1. The paired statement uses the actual Gaussian laws and the
constructed invariant measure.</p>'''

WASSERSTEIN_PROOF = [
    part('source', 'Deriving the potential contract from the source Hessian bounds',
    r'''<p>The source assumes precisely \(V\in C^2\) and
    \(\alpha I_d\preccurlyeq\nabla^2V\preccurlyeq\beta I_d\).
    Symmetry and the quadratic-form bounds give
    \(\|\nabla^2V(x)\|\le\beta\). The mean-value theorem makes
    \(\nabla V\) globally \(\beta\)-Lipschitz. Integrating the lower Hessian
    inequality along line segments gives the strong supporting-plane
    inequality, hence \(\alpha\)-strong convexity.</p>
    <p>Thus the first-order contract used by the existing Langevin library is
    a consequence of the paper's original assumptions. The final proof works
    directly under \(C^2\); it does not require the source proof's temporary
    smoothness and polynomial-growth assumption or a smoothing limit.</p>''',
    r'''<p><code>HessianAssumptions</code> records the quadratic forms of the
    genuine derivative of the gradient. Its
    <code>toPotentialAssumptions</code> theorem derives every field of the
    internal potential contract.</p>''',
    [('WassersteinMixing/CurvatureAssumptions.lean', 'HessianAssumptions.toPotentialAssumptions')]),

    part('process', 'Constructing the actual stationary Brownian comparison',
    r'''<p>Start the diffusion at an actual Gibbs-distributed random vector
    independent of a canonical Brownian path. Picard iteration in the
    complete \(L^2\) space constructs the global solution of</p>
    \[X_t-X_0=-\int_0^t\nabla V(X_s)\,ds+\sqrt2\,B_t.\]
    <p>Uniqueness identifies its successive segments with the reference
    process used by the synchronous Gaussian ULA chain. The Gibbs law is
    stationary. The independent Gaussian increments have the exact laws
    required by the original ULA recursion; their pushforward chain laws are
    the actual iterates of that transition.</p>''',
    r'''<p><code>CanonicalSemigroup.state</code> is the constructed global
    solution. <code>state_integral</code>, <code>state_law</code> and
    <code>state_grid</code> identify its equation, law and grid states.
    <code>actualChain_law</code> identifies the comparison chain with the
    original Gaussian ULA laws.</p>''',
    [('WassersteinMixing/SemigroupGlobal.lean', 'state_integral'),
     ('WassersteinMixing/SemigroupGlobal.lean', 'state_law'),
     ('WassersteinMixing/ActualComparison.lean', 'actualChain_law')]),

    part('semigroup', 'Proving the actual reversible Markov semigroup',
    r'''<p>Evaluating an observable at \(X_t\) is an isometry from
    \(L^2(\pi)\) into the common probability space. Compress evaluation at
    \(t\) against evaluation at zero to define \(P_t\).
    Future Brownian increments are independent of the complete
    initial/Brownian past. Finite shifted Euler maps and their genuine
    \(L^2\) limits prove</p>
    \[\mathbb E[f(X_{a+t})\mid\mathcal F_a]=P_tf(X_a),
    \qquad P_{s+t}=P_sP_t.\]
    <p>For reversibility, realize MALA with the same Brownian Gaussian
    proposals and independent uniform accept/reject variables. Its anchored
    finite-step laws are exactly reversible. The proved rejection-distance
    estimate and Euler convergence give convergence in probability to the
    actual diffusion; stationarity and density upgrade every observable to
    strong \(L^2\) convergence. Self-adjointness passes to \(P_t\).
    Its contraction and strong continuity follow from actual evaluation
    isometries and state continuity.</p>''',
    r'''<p><code>actualEvaluation_markov_pastAt</code> proves the conditional
    identity. <code>op_isSelfAdjoint</code> uses actual reversible MALA
    approximants. <code>CanonicalSemigroup.semigroup</code> assembles all
    proved fields; no abstract Markov or spectral realization is supplied.</p>''',
    [('WassersteinMixing/ActualMarkov.lean', 'actualEvaluation_markov_pastAt'),
     ('WassersteinMixing/SemigroupReversible.lean', 'op_isSelfAdjoint'),
     ('WassersteinMixing/SemigroupInstance.lean', 'semigroup')]),

    part('corrector', 'Constructing the bounded Poisson corrector without an eigenbasis',
    r'''<p>On complex Gibbs observables define
    \(A_hf=\int_0^h(f-P_sf)\,ds\) and
    \(G_N=\sum_{n&lt;N}P_{nh}A_h\).
    Self-adjointness and \(P_t=P_{t/2}^2\) imply
    \(0\preccurlyeq P_t\preccurlyeq P_s\preccurlyeq I\) for
    \(0\le s\le t\). Integration and telescoping give</p>
    \[0\preccurlyeq G_N\preccurlyeq h(I-P_{Nh})\preccurlyeq hI.\]
    <p>The increasing bounded operators converge strongly to a genuine
    bounded operator \(G\). Passing the finite telescoping identity to the
    limit gives \((I-P_h)G=A_h\), while
    \(\|G\|\le h\). Commutation and positivity of
    \((h^2I-G^2)(I-P_h)\) give the energy domination</p>
    \[\langle Gf,(I-P_h)Gf\rangle
      \le h^2\langle f,(I-P_h)f\rangle.\]
    <p>Pointwise real-to-complex embedding commutes with actual evaluation
    and adjunction. Thus the constructed corrector preserves real
    observables. The extracted real semigroup operator is the actual real
    transition. Set \(g=G\nabla V\).</p>''',
    r'''<p><code>corrector_norm_le</code>,
    <code>corrector_poisson</code> and <code>corrector_energy_le</code>
    prove the required conclusions from the constructed semigroup.
    <code>actualPoissonProcess</code> transfers them to the actual adapted
    grid evaluations.</p>''',
    [('WassersteinMixing/SemigroupPoisson.lean', 'corrector_poisson'),
     ('WassersteinMixing/SemigroupPoisson.lean', 'corrector_energy_le'),
     ('WassersteinMixing/ActualPoisson.lean', 'actualPoissonProcess')]),

    part('local', 'Deriving the actual score increment and defect bounds',
    r'''<p>Gibbs integration gives
    \(\|\nabla V\|_{L^2(\pi)}^2\le\beta d\).
    The actual integral equation and Brownian second moment imply</p>
    \[\|X_{kh+s}-X_{kh}\|_{L^2}^2
      \le d(2s^2\beta+4s).\]
    <p>Gradient Lipschitzness and \(s\beta\le1\) then give</p>
    \[\|\nabla V(X_{kh+s})-\nabla V(X_{kh})\|_{L^2}^2
      \le6s\beta^2d.\]
    <p>The true local defect is
    \(D_k=\int_0^h(\nabla V(X_{kh})-\nabla V(X_{kh+s}))\,ds\).
    Integral Cauchy–Schwarz gives
    \(\|D_k\|_{L^2}^2\le3h^3\beta^2d\).
    The corrector bound yields
    \(\|g(X_{kh})\|_{L^2}^2\le h^2\beta d\), and its energy bound
    gives a corrector-increment budget \(6h^3\beta^2d\).</p>''',
    r'''<p><code>actualObservableScore_energy</code>,
    <code>actualScoreIncrement_energy</code> and
    <code>actualDefect_energy</code> derive these constants for the genuine
    diffusion. They are not inputs to the final theorem.</p>''',
    [('WassersteinMixing/ActualScoreObservable.lean', 'actualObservableScore_energy'),
     ('WassersteinMixing/ActualLocalError.lean', 'actualScoreIncrement_energy'),
     ('WassersteinMixing/ActualLocalError.lean', 'actualDefect_energy')]),

    part('martingale', 'Identifying and centering the actual martingale residual',
    r'''<p>The proved conditional Markov identity and commutation with
    the Bochner time integral identify the actual defect mean:</p>
    \[\mathbb E[D_k\mid\mathcal F_{kh}]
      =\int_0^h(I-P_s)\nabla V(X_{kh})\,ds
      =(I-P_h)g(X_{kh}).\]
    <p>Hence
    \(M_{k+1}=D_k-[g(X_{kh})-g(X_{(k+1)h})]\) is conditionally
    centered. The separate budgets \(3h^3\beta^2d\) and
    \(6h^3\beta^2d\), together with
    \(\|u-v\|^2\le2\|u\|^2+2\|v\|^2\), give</p>
    \[\|M_{k+1}\|_{L^2}^2\le18h^3\beta^2d.\]
    <p>The predictable shifted drift belongs to the actual Brownian past,
    so conditional orthogonality removes its cross term with \(M_{k+1}\).</p>''',
    r'''<p><code>actualDefect_conditionalMean</code> identifies the true
    integral defect. The Poisson process derives martingale centering and
    its energy bound; the synchronous comparison then derives the shifted
    energy recurrence.</p>''',
    [('WassersteinMixing/ActualDefectMean.lean', 'actualDefect_conditionalMean'),
     ('WassersteinMixing/PoissonProcess.lean', 'martingaleAt_energy_le'),
     ('WassersteinMixing/PoissonComparison.lean', 'shifted_energy_step')]),

    part('energy', 'Using the genuine averaged Hessian and shifted energy',
    r'''<p>The literal segment average of the Hessian between the actual
    diffusion and ULA states is symmetric, lies between \(\alpha I\) and
    \(\beta I\), and maps their difference to the true gradient difference.
    Writing \(Z_k=X_{kh}-\widehat X_k\) and \(U_k=Z_k+g(X_{kh})\),
    the exact synchronous updates give</p>
    \[U_{k+1}=(I-hA_k)U_k+hA_kg(X_{kh})+M_{k+1}.\]
    <p>The positive contraction inequality yields</p>
    \[\|(I-hA_k)u+hA_kv\|^2
      \le(1-\alpha h)\|u\|^2+h\beta\|v\|^2.\]
    <p>After conditional orthogonality, the forcing constant is
    \(1+18=19\):</p>
    \[\|U_{k+1}\|_{L^2}^2
      \le(1-\alpha h)\|U_k\|_{L^2}^2+19h^3\beta^2d.\]
    <p>Starting the two processes together gives the uniform floor
    \(19h^2\kappa\beta d\). The triangle inequality, with
    \(\sqrt{19}\le5\), gives
    \(\|Z_k\|_{L^2}\le6h\sqrt{\kappa\beta d}\).</p>''',
    r'''<p><code>actual_curvature_error_step</code> uses the genuine
    averaged-Hessian secant identity.
    <code>curvature_weighted_interpolation</code> proves the deterministic
    inequality. <code>shifted_energy_uniform</code> and
    <code>shifted_norm_le_bias</code> derive the floor and literal
    coefficient six.</p>''',
    [('WassersteinMixing/ActualCurvature.lean', 'actual_curvature_error_step'),
     ('WassersteinMixing/ShiftedEnergy.lean', 'curvature_weighted_interpolation'),
     ('WassersteinMixing/Recurrence.lean', 'shifted_norm_le_bias')]),

    part('invariant', 'Constructing the actual Gaussian ULA invariant law',
    r'''<p>Let \(F(x)=x-h\nabla V(x)\), whose Lipschitz factor is
    \(q=1-\alpha h&lt;1\). On an iid Gaussian past
    \(\omega=(\omega_0,\omega_1,\ldots)\), let \(\tau\) drop its first entry.
    The tail preserves the product law and is independent of \(\omega_0\).
    On the complete \(L^2\) space define</p>
    \[\Phi(X)(\omega)=F(X(\tau\omega))+\sqrt{2h}\,\omega_0.\]
    <p>This is a contraction with factor \(q\), so Banach's theorem
    constructs a square-integrable fixed point. Its law \(\widehat\pi\)
    is a probability measure with finite second moment. The actual
    recursion and head/tail independence prove invariance under the
    original independent-Gaussian ULA transition. The proved two-law
    contraction gives
    \(W_2(T^k\mu,\widehat\pi)\le q^kW_2(\mu,\widehat\pi)\to0\).</p>''',
    r'''<p><code>invariantLaw</code> specializes the genuine random
    fixed-point construction. <code>invariantLaw_invariant</code> and
    <code>invariantLaw_attraction</code> prove the exact stationary and
    limiting properties needed in Theorem 1.</p>''',
    [('WassersteinMixing/Invariant.lean', 'invariantLaw_invariant'),
     ('WassersteinMixing/Invariant.lean', 'invariantLaw_attraction')]),

    part('transport', 'Passing the actual stationary comparison to transport',
    r'''<p>The synchronous trajectories give actual couplings of
    \(\pi\) and each stationary-start Gaussian ULA law. Their uniform
    \(L^2\) bound therefore bounds the actual quadratic transport
    infimum. To prove its triangle inequality, disintegrate two couplings
    with the same middle marginal and construct a genuine triple law.
    Minkowski bounds its endpoint cost; taking both coupling infima gives</p>
    \[W_2(\mu,\xi)\le W_2(\mu,\nu)+W_2(\nu,\xi).\]
    <p>Apply this with the stationary-start ULA law between \(\pi\) and
    \(\widehat\pi\), then use the proved attraction to the constructed
    invariant law. Theorem 1 follows. Combining it with actual ULA
    contraction gives the finite-time inequality of Corollary 1.1.
    Second moments prove finiteness before distances are converted to
    real numbers.</p>''',
    r'''<p><code>stationary_transport_bound</code> uses the actual
    synchronous coupling. <code>glueCouplings</code> constructs the
    triple law and <code>wasserstein2Real_triangle</code> proves the
    finite-distance triangle inequality. The final theorem instantiates
    the comparison from the source Hessian assumptions.</p>''',
    [('WassersteinMixing/PoissonComparison.lean', 'stationary_transport_bound'),
     ('WassersteinMixing/TransportGeometry.lean', 'wasserstein2Real_triangle'),
     ('WassersteinMixing/Transport.lean', 'ula_iterate_wasserstein2Real_le')]),

    part('complexity', 'Recovering the exact scale-invariant iteration count',
    r'''<p>For \(d&gt;0\) and \(\varepsilon&gt;0\), write</p>
    \[m=\max\left(1,\frac{12\sqrt d}{\varepsilon}\right),\qquad
    h=\frac1{\beta m},\qquad K=\frac\beta\alpha m.\]
    <p>This is the source minimum formula and gives \(\alpha hK=1\).
    Since
    \(\sqrt\alpha\sqrt{(\beta/\alpha)\beta d}=\beta\sqrt d\),
    the scaled bias is at most \(\varepsilon/2\).
    For \(t=\alpha h\in(0,1]\), use \((1-t)^k\le e^{-tk}\).
    The displayed source iteration restriction makes the scaled transient
    at most \(\varepsilon/2\). Adding the two budgets proves the
    literal accuracy conclusion, including zero initial error.</p>''',
    r'''<p><code>paperStep_eq_inv</code> identifies the two step
    formulas. <code>paper_complexity_bound</code> proves their exact
    scalar consequence. <code>accuracy_bound</code> applies it to the
    actual Gaussian chain and constructed invariant law.</p>''',
    [('WassersteinMixing/Complexity.lean', 'paperStep_eq_inv'),
     ('WassersteinMixing/Complexity.lean', 'paper_complexity_bound'),
     ('WassersteinMixing/Theorem.lean', 'accuracy_bound')]),
]


WASSERSTEIN_CONFIG = {
    'WassersteinMixing': dict(
        include_report_assumptions=True,
        label=r'Project 10 · direct \(C^2\) Wasserstein mixing proof',
        title='Wasserstein Mixing Time of the Unadjusted Langevin Algorithm',
        subtitle='Actual Brownian dynamics, reversible Poisson correctors and sharp Gaussian ULA bounds.',
        status=r'The exact source bias, finite-time and accuracy bounds are proved under the original \(C^2\) Hessian assumptions.',
        top_notice='Theorem 1 and Corollary 1.1 are proved for the actual Gibbs target, independent-Gaussian ULA laws and constructed invariant measure, without additional realization assumptions.',
        namespace='WassersteinMixing',
        formal_note='The exact endpoint header uses only the source Hessian assumptions, the stated step/count restrictions and a finite-second-moment initialization where required.',
        proof_difference=r'''<p><strong>Theorem 1 and Corollary 1.1 are proved under
        the paper's original hypotheses, with the same conclusions and constants,
        using a modified proof.</strong> This is not a step-by-step formalization
        of the original proof.</p>
        <p>The paper constructs its Poisson corrector using spectral calculus for
        the Langevin generator, first imposing extra smoothness and then removing
        that temporary assumption by Gaussian smoothing. Here, a suitable
        corrector is constructed directly from the reversible Markov semigroup
        under \(C^2\) regularity.</p>
        <p>Both arguments use the Poisson decomposition, martingale cancellation
        and shifted-energy estimate. <strong>The paper's generator/eigenbasis
        construction and Gaussian-smoothing passage are not formalized here.</strong></p>''',
        archive='WassersteinMixing/exposition/reference_audit.json',
        archive_label=r'Exact source statements and direct \(C^2\) proof correspondence (JSON)',
        extra=[('WassersteinMixing/README.md', 'Proof scope and local verification'),
               ('WassersteinMixing/exposition/ipla.html', 'Application to IPLA: new parameter rates'),
               ('WassersteinMixing/exposition/README.md', 'Source correspondence and proof architecture')],
        results=[
            dict(title='The invariant bias bound', file='WassersteinMixing/Theorem.lean', name='bias_bound', body=BIAS),
            dict(title='Finite-time Gaussian ULA convergence', file='WassersteinMixing/Theorem.lean', name='convergence_bound', body=CONVERGENCE),
            dict(title='The exact iteration complexity', file='WassersteinMixing/Theorem.lean', name='accuracy_bound', body=ACCURACY),
        ],
        proof=WASSERSTEIN_PROOF,
        diagram=[
            node('source', 0, 0, 'WassersteinMixing/CurvatureAssumptions.lean', r'Use the original \(C^2\) Hessian bounds', r'\(\alpha I\preccurlyeq\nabla^2V\preccurlyeq\beta I\)'),
            node('process', 1, 0, 'WassersteinMixing/SemigroupGlobal.lean', 'Construct the actual stationary diffusion', 'Canonical Brownian input and Picard solution', ('source',)),
            node('semigroup', 2, 0, 'WassersteinMixing/SemigroupInstance.lean', 'Prove the reversible Markov semigroup', 'Fresh-noise Markov identity and actual MALA limits', ('process',)),
            node('corrector', 3, 0, 'WassersteinMixing/ActualPoisson.lean', 'Construct the actual Poisson corrector', r'\(\|G\|\le h\), Poisson identity and energy domination', ('semigroup',)),
            node('local', 2, 1, 'WassersteinMixing/ActualLocalError.lean', 'Bound actual score increments and defects', r'The derived constants are \(6\) and \(3\)', ('process',)),
            node('curvature', 3, 1, 'WassersteinMixing/ActualCurvature.lean', 'Use the true averaged Hessian', 'Exact synchronous error and past measurability', ('source', 'process')),
            node('comparison', 4, 0, 'WassersteinMixing/RealizedComparison.lean', 'Assemble the genuine comparison', r'Centered residual \(18\), shifted forcing \(19\)', ('corrector', 'local', 'curvature')),
            node('recurrence', 5, 0, 'WassersteinMixing/Recurrence.lean', 'Sum the shifted-energy recurrence', r'The literal bias coefficient is \(6\)', ('comparison',)),
            node('transport', 1, 2, 'WassersteinMixing/Transport.lean', 'Prove actual Gaussian ULA contraction', r'Exact factor \(1-\alpha h\)', ('source',)),
            node('invariant', 2, 2, 'WassersteinMixing/Invariant.lean', 'Construct the actual invariant law', 'Banach fixed point on an iid Gaussian past', ('transport',)),
            node('geometry', 4, 2, 'WassersteinMixing/TransportGeometry.lean', 'Glue actual transport couplings', 'Symmetry, triangle inequality and finite distances'),
            node('complexity', 5, 2, 'WassersteinMixing/Complexity.lean', 'Prove the exact accuracy arithmetic', r'The source step and logarithmic count', ('transport',)),
            node('theorem', 6, 0, 'WassersteinMixing/Theorem.lean', 'Recover the source main conclusions', 'Original Hessian assumptions; actual laws', ('recurrence', 'invariant', 'geometry', 'complexity'), True),
            node('audit', 6, 1, 'WassersteinMixing/Check.lean', 'Audit native theorem dependencies', 'Only Lean’s standard logical axioms', ('theorem',), True),
        ]),
}
