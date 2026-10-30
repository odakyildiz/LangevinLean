"""PBGSO assumptions and proved statements beside their exact Lean contracts."""
from __future__ import annotations

import html
import re
from pathlib import Path
from math_notation import render_prose_math

E = html.escape


def overview_document(sources, parsed, math, record=None):
    """The PBGSO landing page; ``record`` collects each statement for the PDF report."""
    from build_site import anchor, relative, shell, code, commands, proof_diagram, lean_logic
    from build_pbgso import OVERVIEW, CATALOG, proof_page, exact_header, context_text, load_notes, step_anchor, statement_code
    from references import reference_notice
    from separate_reports import argument

    page = OVERVIEW

    def proof(path, name, label):
        if path not in parsed or name not in parsed[path]:
            raise ValueError(f'Missing landing-page declaration: {path}: {name}')
        return f'<a href="{relative(proof_page(path), page)}#{anchor(name)}">{E(label)}</a>'

    def eq(desktop, mobile=None, *, tablet=False):
        """Whole mathematical lines on desktop; optional mobile-only line breaks."""
        if mobile is None:
            return r'<div class="statement-equation">\[' + desktop + r'\]</div>'
        cls = 'responsive-equation equation-tablet-break' if tablet else 'responsive-equation'
        return ('<div class="' + cls + r'"><div class="equation-desktop" data-equation-layout="desktop">\['
                + desktop + r'\]</div><div class="equation-mobile" data-equation-layout="mobile">\['
                + mobile + r'\]</div></div>')

    def formal(identifier, refs):
        chunks = []
        for ref in refs:
            path, name, label, *binder = ref
            chunks.append('<div class="formal-item"><h4>' + proof(path, name, label) + '</h4>')
            if binder:
                rows = sources[path].splitlines()
                declaration = parsed[path][name]
                selected = range(declaration['start']-1, declaration['marker']) if binder[0] != '*' else range(len(rows))
                token = binder[-1]
                start = next((i for i in selected if re.search(r'\(' + re.escape(token) + r'\s*:', rows[i])), None)
                if start is None:
                    raise ValueError(f'Missing premise {token}: {path}: {name}')
                depth, end = 0, start
                for end in range(start, len(rows)):
                    depth += rows[end].count('(')-rows[end].count(')')
                    if depth == 0:
                        break
                chunks.append(code(path, start+1, end+1, sources, page, 'premise',
                                   identifier + '.' + token))
                shared = context_text(sources[path], parsed[path])
                chunks.append('<details class="statement-context"><summary>Exact shared Lean context</summary>' +
                              commands(shared, identifier + '-context-' + token, 'Copy context') + '</details>')
            else:
                declaration = parsed[path][name]
                if declaration['kind'] in ('def', 'abbrev'):
                    shared = context_text(sources[path], parsed[path])
                    chunks.append('<details class="statement-context"><summary>Exact shared Lean context</summary>' +
                                  commands(shared, identifier + '-context-' + Path(path).stem + '.' + name, 'Copy context') + '</details>')
                    rendered = code(path, declaration['start'], declaration['end'], sources,
                                    page, 'contract', name)
                    chunks.append(rendered.replace(' id="'+anchor(name), ' id="'+anchor(Path(path).stem+'.'+name)))
                else:
                    chunks.append(exact_header(path, name, sources, parsed, page))
            chunks.append('</div>')
        return '<aside class="statement-lean" aria-label="Lean formalization"><div class="pane-label">Lean formalization</div>' + ''.join(chunks) + '</aside>'

    def row(identifier, title, content, refs, *, source=None, new=None, assumption=None, added=False, interpretation=False):
        if record is not None:
            record.append(dict(id=identifier, title=title, content=content,
                               refs=[(ref[0], ref[1]) for ref in refs],
                               kind='assumption' if assumption else 'theorem' if (source or new) else 'setting'))
        attrs = (f' data-source-result="{source}"' if source else '')
        attrs += (f' data-new-theory="{new}"' if new else '')
        attrs += (f' data-assumption-id="{assumption}"' if assumption else '')
        kind = 'added' if added else 'interpretation' if interpretation else None
        if kind:
            attrs += f' data-assumption-kind="{kind}"'
        classes = 'theorem-statement paired-statement'
        if assumption:
            classes += ' assumption-statement'
        if kind:
            classes += ' added-assumption' if added else ' interpretation-assumption'
        return (f'<article class="{classes}" id="{identifier}"{attrs}><h3>{E(title)}</h3>'
                '<div class="statement-pair"><div class="statement-math"><div class="pane-label">Mathematical statement</div>'
                + math(content) + '</div>' + formal(identifier, refs) + '</div></article>')

    def badge(text, kind='added'):
        cls = 'added-assumption' if kind == 'added' else 'interpretation-assumption'
        return f'<span class="assumption-badge {cls}" data-assumption-kind="{kind}">{text}</span>'

    def declarations(path, *names):
        return [(path, name, name) for name in names]

    body = ('<div class="pbgso-overview"><header class="hero"><div class="eyebrow">Assumptions · proved theorems · exact Lean statements</div>'
            '<h1>Particle-based Generalised Stochastic Optimisation</h1>'
            '<p class="subtitle">The paper’s notation and assumptions, four main proved theorems, '
            'and two new time-uniform discretisation bounds, each beside its Lean formalization.</p>'
            + reference_notice('PBGSO') + '</header>'
            '<p class="proof-download"><a href="' + relative('docs/pdf/PBGSO/FullProof.pdf', page) + '" download>Download full proof (PDF)</a> · '
            '<a href="' + relative('docs/latex/PBGSO/FullProof.tex', page) + '" download>Download full proof (LaTeX)</a></p>'
            '<nav class="jump-nav" aria-label="PBGSO contents"><a href="#assumptions">Assumptions</a>'
            '<a href="#paper-theorems">Paper theorems</a><a href="#new-theory">New bounds</a>'
            '<a href="#verification">Check the proofs</a><a href="#proof-roadmap">Proof roadmap</a>'
            + ('<a href="#mathematical-proof">Mathematical argument</a>' if argument('PBGSO')['parts'] else '')
            + '<a href="#modules">Supporting proofs</a></nav>'
            '<section class="section" id="assumptions"><h2>Framework and explicit assumptions</h2>'
            '<div class="assumption-legend"><span class="source-assumption-key">Paper assumption</span>'
            '<span class="added-assumption" data-assumption-kind="added">Added assumption</span>'
            '<span class="interpretation-assumption" data-assumption-kind="interpretation">Explicit solution interpretation</span></div>'
            '<p>Orange identifies a strengthening or additional regularity condition. Blue explains the '
            'solution meaning used in the formalization. Each theorem specifies which conditions it uses. '
            'The right column contains exact Lean source, with its shared variables available to expand; '
            'proofs open through the linked declaration names. Raw-SDE endpoints may use an arbitrary finite horizon \\(T\\); choosing \\(T\\) equal to the displayed time gives the all-time statement.</p>')

    body += row('framework-setting', 'The paper’s state spaces and notation', '\n<p>The paper’s objective has the integrable gradient representation</p>'
        + eq(r'\nabla_\theta\ell(\theta)=\int_{\mathsf X}F(\theta,x)\,\pi_\theta(\mathrm dx),\qquad F(\theta,\cdot)\in\mathrm L^1(\pi_\theta).',
             r'\begin{gathered}\nabla_\theta\ell(\theta)=\int F(\theta,x)\,\pi_\theta(\mathrm dx),\\F(\theta,\cdot)\in\mathrm L^1(\pi_\theta).\end{gathered}')
        + r'''<p>The optimiser state is \(\vartheta\in\Theta\times\mathsf M\), with \(\theta=\Pi_\theta(\vartheta)\). The sampler state is \(Z\in\mathsf X\times\mathsf V\), with \(X=\Pi_x(Z)\). These finite-dimensional Euclidean spaces can have different dimensions. The Brownian motion takes values in \(\mathsf B\).</p>'''
        + eq(r'G_\nu(\vartheta)=\int_{\mathsf X\times\mathsf V} F(\Pi_\theta\vartheta,\Pi_xz)\,\nu(\mathrm dz),\qquad \nu_t=\operatorname{Law}(Z_t).',
             r'\begin{gathered}G_\nu(\vartheta)=\int F(\Pi_\theta\vartheta,\Pi_xz)\,\nu(\mathrm dz),\\\nu_t=\operatorname{Law}(Z_t).\end{gathered}')
        + eq(r'\begin{aligned}\mathrm d\vartheta_t&=\Psi_t(\vartheta_t,G_{\nu_t}(\vartheta_t))\,\mathrm dt,\\\mathrm dZ_t&=b_{\Pi_\theta\vartheta_t}(Z_t)\,\mathrm dt+\sigma_{\Pi_\theta\vartheta_t}(Z_t)\,\mathrm dB_t.\end{aligned}',
             r'\begin{gathered}\mathrm d\vartheta_t=\Psi_t(\vartheta_t,G_{\nu_t}(\vartheta_t))\,\mathrm dt,\\\begin{aligned}\mathrm dZ_t&=b_{\Pi_\theta\vartheta_t}(Z_t)\,\mathrm dt\\&\quad+\sigma_{\Pi_\theta\vartheta_t}(Z_t)\,\mathrm dB_t.\end{aligned}\end{gathered}')
        + '<p>The particle system replaces \\(G_{\\nu_t}\\) by \\(N^{-1}\\sum_i F(\\Pi_\\theta\\vartheta_t^N,\\Pi_xZ_t^i)\\), with \\(\\nu_t^N=N^{-1}\\sum_i\\delta_{Z_t^i}\\) and independent Brownian drivers \\(B^i\\). The independent maps \\(F,\\Psi,b,\\sigma\\) need not come from a common potential.</p>\n<p><strong>Lean notation.</strong> <code>S</code> represents \\(\\Theta\\times\\mathsf M\\), <code>Z</code> represents \\(\\mathsf X\\times\\mathsf V\\), <code>M.parameter</code> and <code>M.position</code> are \\(\\Pi_\\theta,\\Pi_x\\), and <code>M.meanGradient ν s</code> is \\(G_\\nu(\\vartheta)\\). Internal source variable <code>s</code> denotes the paper’s \\(\\vartheta\\).</p>', declarations('PBGSO/Framework.lean', 'Model', 'meanGradient', 'meanGradient_of_marginal', 'particleGradient'))

    body += row('metric-setting', 'Distance and twisted metric',
        eq(r'\mathbf d((\vartheta,\nu),(\tilde\vartheta,\tilde\nu))=\sqrt{\|\vartheta-\tilde\vartheta\|^2+W_2^2(\nu,\tilde\nu)}.',
           r'\begin{gathered}\mathbf d((\vartheta,\nu),(\tilde\vartheta,\tilde\nu))\\=\sqrt{\|\vartheta-\tilde\vartheta\|^2+W_2^2(\nu,\tilde\nu)}.\end{gathered}')
        + eq(r'D=\operatorname{diag}(D_\vartheta,D_z),\qquad \kappa=\frac{\lambda_{\max}(D)}{\lambda_{\min}(D)}.',
             r'\begin{gathered}D=\operatorname{diag}(D_\vartheta,D_z),\\\kappa=\frac{\lambda_{\max}(D)}{\lambda_{\min}(D)}.\end{gathered}')
        + '<p>The paper uses symmetric positive definite weights and sharp spectral comparisons. Lean stores certified bounds \\(0&lt;\\underline\\lambda\\le\\overline\\lambda\\), satisfying \\(\\underline\\lambda\\|y\\|^2\\le\\langle y,Dy\\rangle\\le\\overline\\lambda\\|y\\|^2\\). Taking \\(\\underline\\lambda=\\lambda_{\\min}(D)\\), \\(\\overline\\lambda=\\lambda_{\\max}(D)\\) gives the paper’s \\(\\kappa\\). Any nonsharp certified bounds give the same statements with the corresponding larger ratio \\(\\overline\\lambda/\\underline\\lambda\\).</p>', declarations('PBGSO/PaperTheorems.lean', 'TwistedGeometry', 'conditionNumber'))

    body += row('assumption-a1', 'A1 — Well-posedness', r'''
<p>For every deterministic \(\vartheta_0\) and every \(Z_0\), independent of \(B\), with law \(\nu_0\in\mathcal P_2(\mathsf X\times\mathsf V)\), the original mean-field SDE has a pathwise unique strong solution on every finite time interval, and \(\nu_t\in\mathcal P_2\) for all finite \(t\ge0\). In addition, either (i) \(\sigma_\theta(z)\) is constant, or (ii) for one \(K\ge0\),</p>'''
        + eq(r'\|b_{\Pi_\theta\vartheta}(z)\|+\|\sigma_{\Pi_\theta\vartheta}(z)\|\le K(1+\|\Pi_\theta\vartheta\|+\|z\|).',
             r'\begin{gathered}\|b_{\Pi_\theta\vartheta}(z)\|+\|\sigma_{\Pi_\theta\vartheta}(z)\|\\\le K(1+\|\Pi_\theta\vartheta\|+\|z\|).\end{gathered}')
        + '<p>The formal endpoints use the required A1 instances on their original and canonical Brownian spaces. These are solution existence and uniqueness premises, rather than a supplied law-comparison conclusion.</p>',
        [('PBGSO/RawLocalStationarity.lean','Data','Original integral-equation solution'),
         ('PBGSO/RawLocalStationarity.lean','PathwiseUniqueness','Same-driver pathwise uniqueness'),
         ('PBGSO/NaturalFiniteWorkArbitraryLaw.lean','CanonicalSolution','Canonical strong existence instance')], assumption='A1')

    body += row('assumption-a2', 'A2 — Stationary optimiser–sampler pair', r'''
<p>There are \(\vartheta_\star\), \(\theta_\star=\Pi_\theta\vartheta_\star\), and a frozen invariant law \(\nu_{\theta_\star}\in\mathcal P_2\), with</p>'''
        + eq(r'\nabla_\theta\ell(\theta_\star)=0,\qquad \Psi_t(\vartheta_\star,0)=0\ (t\ge0),\qquad (\Pi_x)_\#\nu_{\theta_\star}=\pi_{\theta_\star}.',
             r'\begin{gathered}\nabla_\theta\ell(\theta_\star)=0,\\\Psi_t(\vartheta_\star,0)=0\quad(t\ge0),\\(\Pi_x)_\#\nu_{\theta_\star}=\pi_{\theta_\star}.\end{gathered}')
        + eq(r'G_{\nu_{\theta_\star}}(\vartheta_\star)=\int F(\theta_\star,x)\,\pi_{\theta_\star}(\mathrm dx)=\nabla_\theta\ell(\theta_\star)=0.',
             r'\begin{gathered}G_{\nu_{\theta_\star}}(\vartheta_\star)=\int F(\theta_\star,x)\,\pi_{\theta_\star}(\mathrm dx)\\=\nabla_\theta\ell(\theta_\star)=0.\end{gathered}')
        + '<p>The second line uses the paper’s integrable gradient identity. The target is a critical point.</p>',
        [('PBGSO/RawLocalStationarity.lean','FrozenSamplerData','Actual frozen invariant sampler'),
         ('PBGSO/RawPathSolutionTransfer.lean','stationary_product_law_of_weak_frozen','Zero mean observation premise','hg'),
         ('PBGSO/RawPathSolutionTransfer.lean','stationary_product_law_of_weak_frozen','Optimiser fixed point premise','hfix')], assumption='A2')
    body += row('assumption-a2-meaning', 'A2 — Actual SDE interpretation', r'''
<p>Frozen invariance means an actual stationary weak frozen SDE on some filtered Brownian probability space. Its paths are continuous and adapted, and satisfy</p>'''
        + eq(r'Z_t=Z_0+\int_0^t b_{\theta_\star}(Z_r)\,\mathrm dr+\int_0^t\sigma_{\theta_\star}(Z_r)\,\mathrm dB_r,\qquad\operatorname{Law}(Z_t)=\nu_{\theta_\star}.',
             r'\begin{gathered}Z_t=Z_0+\int_0^t b_{\theta_\star}(Z_r)\,\mathrm dr\\\quad+\int_0^t\sigma_{\theta_\star}(Z_r)\,\mathrm dB_r,\\\operatorname{Law}(Z_t)=\nu_{\theta_\star}.\end{gathered}')
        + '<p>This may be a different probability space from the coupled strong solution. A generator identity alone does not supply this solution premise.</p>',
        declarations('PBGSO/RawLocalStationarity.lean','SamplerData'), assumption='A2-SDE', interpretation=True)

    body += row('assumption-a3', 'A3 — Twisted joint strong monotonicity', r'''
<p>There are symmetric positive definite \(D_\vartheta,D_z\) and \(\rho&gt;0\). For every \(t\ge0\), \(\vartheta,\tilde\vartheta\), \(\nu,\tilde\nu\in\mathcal P_2\), and \(\Lambda\in\Gamma(\nu,\tilde\nu)\), put \(\delta\vartheta=\vartheta-\tilde\vartheta\), \(\delta z=z-\tilde z\), \(\theta=\Pi_\theta\vartheta\), \(\tilde\theta=\Pi_\theta\tilde\vartheta\). Then</p>'''
        + eq(r'\begin{aligned}&\left\langle\delta\vartheta,D_\vartheta[\Psi_t(\vartheta,G_\nu(\vartheta))-\Psi_t(\tilde\vartheta,G_{\tilde\nu}(\tilde\vartheta))]\right\rangle\\&+\int\left[\langle\delta z,D_z[b_\theta(z)-b_{\tilde\theta}(\tilde z)]\rangle+\tfrac12\|D_z^{1/2}[\sigma_\theta(z)-\sigma_{\tilde\theta}(\tilde z)]\|_{\rm HS}^2\right]\,\mathrm d\Lambda\\&\le-\rho\left(\|\delta\vartheta\|_{D_\vartheta}^2+\int\|\delta z\|_{D_z}^2\,\mathrm d\Lambda\right).\end{aligned}',
             r'\begin{aligned}\Delta\Psi_t&=\Psi_t(\vartheta,G_\nu(\vartheta))\\&\quad-\Psi_t(\tilde\vartheta,G_{\tilde\nu}(\tilde\vartheta)),\\\Delta b&=b_\theta(z)-b_{\tilde\theta}(\tilde z),\\\Delta\sigma&=\sigma_\theta(z)-\sigma_{\tilde\theta}(\tilde z),\\q_\Lambda&=\langle\delta\vartheta,D_\vartheta\Delta\Psi_t\rangle\\&\quad+\int\langle\delta z,D_z\Delta b\rangle\,\mathrm d\Lambda\\&\quad+\tfrac12\int\|D_z^{1/2}\Delta\sigma\|_{\rm HS}^2\,\mathrm d\Lambda,\\E_\Lambda&=\|\delta\vartheta\|_{D_\vartheta}^2\\&\quad+\int\|\delta z\|_{D_z}^2\,\mathrm d\Lambda,\\q_\Lambda&\le-\rho E_\Lambda.\end{aligned}')
        + '<p>All expectations are taken on their stated integrability domains. The ordinary finite signed-work domain needed by the constant-diffusion contraction branch is the separate orange condition R2 below.</p>', declarations('PBGSO/PaperTheorems.lean','TwistedJointMonotonicity'), assumption='A3')

    source3 = 'PBGSO/RawConstructedParticleBounds.lean'
    source3name = 'original_finite_particle_interaction_bound'
    body += row('assumption-a4', 'A4 — Lipschitz gradient response',
        r'<p>For every \(t\ge0\), \(\vartheta\) and \(g,\tilde g\in\Theta\), with \(L_\Psi\ge0\),</p>'
        + eq(r'\|\Psi_t(\vartheta,g)-\Psi_t(\vartheta,\tilde g)\|\le L_\Psi\|g-\tilde g\|.',
             r'\begin{gathered}\|\Psi_t(\vartheta,g)-\Psi_t(\vartheta,\tilde g)\|\\\le L_\Psi\|g-\tilde g\|.\end{gathered}'),
        [(source3,source3name,'Exact gradient-response hypothesis','hΨ')], assumption='A4')
    body += row('assumption-a5', 'A5 — Uniform gradient fluctuation',
        '<p>Along the independent-copy mean-field path, the observation is square-integrable and, for a finite nonnegative constant,</p>'
        + eq(r'\sup_{t\ge0}\mathbb E\left\|F(\Pi_\theta\bar\vartheta_t,\Pi_x\bar Z_t)-G_{\bar\nu_t}(\bar\vartheta_t)\right\|^2\le V_F<\infty.',
             r'\begin{gathered}\sup_{t\ge0}\mathbb E\bigl\|F(\Pi_\theta\bar\vartheta_t,\Pi_x\bar Z_t)\\-G_{\bar\nu_t}(\bar\vartheta_t)\bigr\|^2\le V_F<\infty.\end{gathered}'),
        [(source3,source3name,'Observation domain','hF'),(source3,source3name,'Exact variance hypothesis (\\(V=V_F\\))','hVar')], assumption='A5')

    body += row('regularity-r1', 'R1 — Explicit Borel regularity', r'''
<p>The following maps are jointly Borel:</p>'''
        + eq(r'(\vartheta,z)\mapsto F(\Pi_\theta\vartheta,\Pi_xz),\qquad (\vartheta,z)\mapsto b_{\Pi_\theta\vartheta}(z),\qquad(t,\vartheta,g)\mapsto\Psi_t(\vartheta,g).',
             '\\begin{gathered}(\\vartheta,z)\\mapsto F(\\Pi_\\theta\\vartheta,\\Pi_xz),\\\\(\\vartheta,z)\\mapsto b_{\\Pi_\\theta\\vartheta}(z),\\\\(t,\\vartheta,g)\\mapsto\\Psi_t(\\vartheta,g).\\end{gathered}')
        + '<p>Use R1 for Theorems 3 and 4 and for the constant-diffusion branch of Theorem 2. The constant-diffusion branches of Theorems 2 and 4 also assume each frozen drift is Borel, as shown in their complete Lean statements.</p>',
        [(source3,source3name,'Observation measurability','hBorelF'),(source3,source3name,'Drift measurability','hBorelb'),(source3,source3name,'Response measurability','hBorelΨ')], assumption='R1', added=True)
    body += row('regularity-r2', 'R2 — Finite signed work for constant-diffusion contraction', r'''
<p>For every optimiser pair and every joint probability law with finite quadratic moment, require the ordinary finite signed-integral domain:</p>'''
        + eq(r'\int\left|\langle z-\tilde z,D_z[b_{\Pi_\theta\vartheta}(z)-b_{\Pi_\theta\tilde\vartheta}(\tilde z)]\rangle\right|\,\Lambda(\mathrm dz,\mathrm d\tilde z)<\infty.',
             r'\begin{gathered}\Delta b=b_{\Pi_\theta\vartheta}(z)-b_{\Pi_\theta\tilde\vartheta}(\tilde z),\\\int|\langle z-\tilde z,D_z\Delta b\rangle|\,\mathrm d\Lambda<\infty.\end{gathered}')
        + '<p>The Lean integrand also contains the weighted Hilbert–Schmidt diffusion term of A3; it vanishes under constant diffusion, the only branch that uses R2. This <code>FiniteCouplingWork</code> condition is used for the constant-diffusion branch of Theorem 2 and its stationary uniqueness corollary. It strengthens an extended-negative-work reading of A3; it is not imposed separately on Theorems 3 or 4.</p>',
        declarations('PBGSO/DiracOptimizerGrowth.lean','FiniteCouplingWork'), assumption='R2', added=True)
    body += row('regularity-r3', 'R3 — Explicit realization regularity in the linear-growth branch', r'''
<p>Each frozen drift and diffusion column is Borel, and \(\Pi_\theta\) is continuous. Along the canonical strong solutions, the functions</p>'''
        + eq(r'(r,\omega)\mapsto b_{\Pi_\theta\vartheta_r}(Z_r(\omega)),\qquad(r,\omega)\mapsto\sigma_{\Pi_\theta\vartheta_r}(Z_r(\omega))e_i',
             '\\begin{gathered}(r,\\omega)\\mapsto b_{\\Pi_\\theta\\vartheta_r}(Z_r(\\omega)),\\\\(r,\\omega)\\mapsto\\sigma_{\\Pi_\\theta\\vartheta_r}(Z_r(\\omega))e_i\\end{gathered}')
        + '<p>are jointly strongly measurable, and the drift is progressively strongly measurable with respect to the driver filtration. The linear-growth inequality is exactly A1(ii). These are coefficient regularity assumptions; the proof derives the moment and energy estimates.</p>',
        declarations('PBGSO/RawSamplerGrowth.lean','Regularity'), assumption='R3', added=True)
    body += '</section><section class="section" id="paper-theorems"><h2>Main theorems of the paper — proved</h2>'

    body += row('theorem-1','Theorem 1 — Invariant measure',
        '<p><strong>Assumptions:</strong> A1, A2, with the actual weak-SDE meaning stated above. Initialise the optimiser at the target and the sampler independently of Brownian motion with its frozen invariant law.</p>'
        + '<p class="no-added-assumption"><strong>Added analytic assumptions: none.</strong></p>'
        + r'<div class="theorem-conclusion"><p>For every \(t\ge0\),</p>'
        + eq(r'\operatorname{Law}(\vartheta_t,Z_t)=\mu_\star:=\delta_{\vartheta_\star}\otimes\nu_{\theta_\star}.',
             r'\begin{gathered}\operatorname{Law}(\vartheta_t,Z_t)=\mu_\star,\\\mu_\star:=\delta_{\vartheta_\star}\otimes\nu_{\theta_\star}.\end{gathered}')
        + '</div><p>For time-dependent optimiser response this asserts a stationary solution; for autonomous response it is also ordinary invariant-measure preservation.</p>',
        [('PBGSO/RawPathSolutionTransfer.lean','stationary_product_law_of_weak_frozen','Complete proved stationary-law theorem')], source='thm:invariant_measure')
    body += row('theorem-2','Theorem 2 — Contraction under joint twisted monotonicity',
        '<p><strong>Assumptions:</strong> A1, A3, deterministic optimiser initial states and initial sampler laws in the stated second-moment domain.</p>'
        + badge('Constant diffusion: R1 + R2 (FiniteCouplingWork); linear growth: R3.')
        + r'<div class="theorem-conclusion"><p>For every \(t\ge0\),</p>'
        + eq(r'\mathbf d((\vartheta_t,\nu_t),(\tilde\vartheta_t,\tilde\nu_t))\le\sqrt\kappa\,e^{-\rho t}\mathbf d((\vartheta_0,\nu_0),(\tilde\vartheta_0,\tilde\nu_0)).',
             r'\begin{gathered}\mathbf d((\vartheta_t,\nu_t),(\tilde\vartheta_t,\tilde\nu_t))\\\le\sqrt\kappa\,e^{-\rho t}\mathbf d((\vartheta_0,\nu_0),(\tilde\vartheta_0,\tilde\nu_0)).\end{gathered}')
        + '<p>With A2, the target is stationary and</p>'
        + eq(r'W_2(\mu_t,\mu_\star)\le\sqrt\kappa\,e^{-\rho t}W_2(\mu_0,\mu_\star),\qquad\mu_t=\delta_{\vartheta_t}\otimes\nu_t.',
             r'\begin{gathered}W_2(\mu_t,\mu_\star)\le\sqrt\kappa\,e^{-\rho t}W_2(\mu_0,\mu_\star),\\\mu_t=\delta_{\vartheta_t}\otimes\nu_t.\end{gathered}')
        + '</div><p>The second bound follows from the first, with the stationary target of Theorem 1 as comparison solution, and the product identity \\(W_2(\\delta_\\vartheta\\otimes\\nu,\\delta_{\\tilde\\vartheta}\\otimes\\tilde\\nu)=\\mathbf d((\\vartheta,\\nu),(\\tilde\\vartheta,\\tilde\\nu))\\) for \\(\\nu,\\tilde\\nu\\in\\mathcal P_2\\). The stationary law is unique among finite-second-moment laws of the form prescribed by the paper, with a deterministic optimiser and the stated solution hypotheses.</p>',
        [('PBGSO/NaturalFiniteWorkArbitraryLaw.lean','law_distance_decay','Constant-diffusion contraction'),
         ('PBGSO/RawSamplerGrowthArbitraryLaw.lean','law_distance_decay','Linear-growth contraction'),
         ('PBGSO/ProductTransport.lean','wasserstein_product_eq','Product-law Wasserstein identity'),
         ('PBGSO/RawStationaryUniqueness.lean','stationary_laws_unique_constant','Stationary uniqueness: constant diffusion'),
         ('PBGSO/RawStationaryUniqueness.lean','stationary_laws_unique_linearGrowth','Stationary uniqueness: linear growth')], source='thm:twisted_joint_strong_monotonicity')
    body += row('theorem-3','Theorem 3 — Finite-particle interaction error',
        '<p><strong>Assumptions:</strong> A1, A3–A5; positive population; deterministic optimiser initialisation; i.i.d. initial samplers from a common second-moment law, independent of the independent Brownian drivers; and an actual interacting solution of the original native SDE.</p>'
        + badge('Added regularity: R1.')
        + r'<p>Couple the particle and independent-copy systems synchronously: \(\vartheta_0^N=\bar\vartheta_0\), \(Z_0^i=\bar Z_0^i\), with the same driver for each pair. Put \(\bar\nu_t^{[N]}=N^{-1}\sum_i\delta_{\bar Z_t^i}\).</p><div class="theorem-conclusion"><p>For every \(t\ge0\),</p>'
        + eq(r'\left\|\mathbf d((\vartheta_t^N,\nu_t^N),(\bar\vartheta_t,\bar\nu_t^{[N]}))\right\|_{\mathrm L^2}\le\frac{L_\Psi}{\rho}\sqrt{\frac{\kappa V_F}{N}}(1-e^{-\rho t}).',
             r'\begin{gathered}\left\|\mathbf d((\vartheta_t^N,\nu_t^N),(\bar\vartheta_t,\bar\nu_t^{[N]}))\right\|_{\mathrm L^2}\\\le\frac{L_\Psi}{\rho}\sqrt{\frac{\kappa V_F}{N}}(1-e^{-\rho t}).\end{gathered}')
        + '</div><p>The comparison is with the independent-copy empirical law. A population-law Wasserstein estimate also needs empirical sampling error.</p>',
        [(source3,source3name,'Complete proved native particle theorem')], source='thm:finite_particle_error')
    body += row('theorem-4','Theorem 4 — Parameter error bound of particle system',
        '<p><strong>Assumptions:</strong> A1–A5 and the coupled initialisation/native interacting solution of Theorem 3. The parameter map is the Euclidean coordinate projection.</p>'
        + badge('R1; also R3 in the linear-growth branch.')
        + eq(r'\mathbf d_0=\mathbf d((\vartheta_0^N,\nu_0),(\vartheta_\star,\nu_{\theta_\star})).',
             '\\begin{gathered}\\mathbf d_0=\\mathbf d((\\vartheta_0^N,\\nu_0),\\\\(\\vartheta_\\star,\\nu_{\\theta_\\star})).\\end{gathered}')
        + r'<div class="theorem-conclusion"><p>For every \(t\ge0\),</p>'
        + eq(r'\|\theta_t^N-\theta_\star\|_{\mathrm L^2}\le\sqrt\kappa\,e^{-\rho t}\mathbf d_0+\frac{L_\Psi}{\rho}\sqrt{\frac{\kappa V_F}{N}}(1-e^{-\rho t}).',
             r'\begin{gathered}\|\theta_t^N-\theta_\star\|_{\mathrm L^2}\\\le\sqrt\kappa\,e^{-\rho t}\mathbf d_0\\+\frac{L_\Psi}{\rho}\sqrt{\frac{\kappa V_F}{N}}(1-e^{-\rho t}).\end{gathered}')
        + eq(r'\lim_{N\to\infty}\limsup_{t\to\infty}\|\theta_t^N-\theta_\star\|_{\mathrm L^2}=0.')
        + '</div><p>The limit is for a family with common constants and initial law. The verified family theorem also gives a joint time/population limit. The critical-point target is the one in A2. In Lean, A2 enters as a canonical target solution whose optimiser stays at \\(\\vartheta_\\star\\) and whose sampler law stays \\(\\nu_{\\theta_\\star}\\) (premises <code>hopt</code>, <code>hlaw</code>); Theorem 1 proves this stationarity from A1 and A2.</p>',
        [('PBGSO/RawConstructedParticleParameter.lean','original_parameter_bound_constant','Constant-diffusion parameter theorem'),
         ('PBGSO/RawConstructedParticleParameter.lean','original_parameter_bound_linearGrowth','Linear-growth parameter theorem'),
         ('PBGSO/RawConstructedParticleJointLimit.lean','parameter_joint_limit','Joint limit consequence')], source='thm:parameter_error_full')
    body += '</section><section class="section" id="new-theory"><h2>Numerics — explicit assumptions and time-uniform bounds</h2>'
    body += math('<p>Theorem New A and Theorem New B are new results for the paper’s actual numerical updates. We keep the paper’s \\(\\hat\\theta_n\\), \\(\\hat X_n^i\\), \\(\\hat U_n^i\\), \\(\\hat V_n^i\\) and \\(t_n=nh\\). All constants below are defined mathematically; no coefficient is specified only by a Lean function name.</p>')

    body += row('numerical-n1','N1 — Added global force regularity', '\n<p>Let \\(F_x(\\theta,x)\\) denote the sampler force: in the paper it is \\(\\nabla_xE(\\theta,x)\\) for M-MFPO and \\(\\nabla_xE^\\lambda(\\theta,x)\\) for HOL-MYPGD. This additional notation avoids reusing the paper’s \\(G_\\nu\\), which denotes the population gradient. The verified theorem also permits independent, nonconservative forces \\(F,F_x\\).</p>\n<p>On the paper’s finite-dimensional optimiser and Euclidean sampler spaces, take \\(\\ell_F,\\ell_x\\ge0\\), with</p>'
        + eq(r'\|F(\theta,x)-F(\tilde\theta,\tilde x)\|\le\ell_F(\|\theta-\tilde\theta\|+\|x-\tilde x\|),',
             r'\begin{gathered}\|F(\theta,x)-F(\tilde\theta,\tilde x)\|\\\le\ell_F(\|\theta-\tilde\theta\|+\|x-\tilde x\|),\end{gathered}')
        + eq(r'\|F_x(\theta,x)-F_x(\tilde\theta,\tilde x)\|\le\ell_x(\|\theta-\tilde\theta\|+\|x-\tilde x\|).',
             r'\begin{gathered}\|F_x(\theta,x)-F_x(\tilde\theta,\tilde x)\|\\\le\ell_x(\|\theta-\tilde\theta\|+\|x-\tilde x\|).\end{gathered}')
        + '<p>Force values may grow linearly. No second derivative, Hessian bound or common potential is required. In Lean, <code>D.F</code> is the observation and <code>D.G</code> is the sampler force.</p>',
        declarations('PBGSO/ParticleMethodLp.lean','ParticleForceData'), assumption='N1', added=True)
    body += row('numerical-n2','N2 — Initial laws, contraction and reference variance', '\n<p>Take \\(N\\ge1\\), deterministic initial optimiser state, and i.i.d. initial sampler states with common law \\(\\nu_0\\in\\mathcal P_2\\), independently of the independent Brownian drivers. Assume A3 with \\(\\rho&gt;0\\), A5 with \\(V_F\\ge0\\), and target zero mean observation \\(G_{\\nu_{\\theta_\\star}}(\\vartheta_\\star)=0\\) for the chosen complete-state model.</p>\n<p>Use the physical noise from the paper: \\(\\sqrt{2\\gamma}\\,\\mathrm dB^i\\) for M-MFPO, and \\(\\sqrt{2\\alpha}\\,\\mathrm dB^i\\) in the final HOL auxiliary coordinate. The optimiser receives no thermal noise.</p>',
        [('PBGSO/FullyUniformMomentum.lean','explicit_parameter_bound','Source A3 premise','hmono'),
         ('PBGSO/FullyUniformMomentum.lean','explicit_parameter_bound','Zero mean target premise','hg'),
         ('PBGSO/FullyUniformMomentum.lean','explicit_parameter_bound','Initial second moment','*','hμ'),
         ('PBGSO/FullyUniformMomentum.lean','explicit_parameter_bound','A5 on the canonical mean-field path','*','hVariance')], assumption='N2')
    body += row('numerical-n3','N3 — Added canonical frozen-target realization', r'''
<p>For the target pair, require \(\nu_{\theta_\star}\in\mathcal P_2\). On \(\nu_{\theta_\star}\) times the canonical Brownian probability, supply a norm-continuous \(\mathrm L^2\) frozen sampler trajectory, initialized by the initial-coordinate projection, which satisfies</p>'''
        + eq(r'Z_t^\star-Z_0^\star=\int_0^t b_{\theta_\star}(Z_r^\star)\,\mathrm dr+\sigma_\star B_t,\qquad\operatorname{Law}(Z_t^\star)=\nu_{\theta_\star}\quad(t\ge0).',
             r'\begin{gathered}Z_t^\star-Z_0^\star=\int_0^t b_{\theta_\star}(Z_r^\star)\,\mathrm dr+\sigma_\star B_t,\\\operatorname{Law}(Z_t^\star)=\nu_{\theta_\star}\quad(t\ge0).\end{gathered}')
        + '<p>The constant physical diffusion is the one in N2. This explicit <code>FrozenTrajectory</code> input is stronger than the weak frozen-SDE realization used in Theorem 1. The numerical endpoint retains it as a visible assumption.</p>',
        declarations('PBGSO/AdditiveStationaryTarget.lean','FrozenTrajectory'), assumption='N3', added=True)

    # Every coefficient used in New A/B is expanded in the following paired rows.
    body += numerical_constants(row, eq, declarations)

    body += row('theorem-new-a','Theorem New A — M-MFPO final discretisation bound',
        '<p><strong>Assumptions:</strong> N1–N3 and the standard Euclidean cloud encoding defined above. Use the paper’s OBABO update and independent Gaussian sampler half-step innovations, with zero optimiser innovations.</p>'
        + badge(r'Added regularity N1 and frozen realization N3; \(\gamma\ge0\), \(0&lt;h\le h_{\star,M}\).')
        + r'<p>The stationary optimiser state is \(\vartheta_\star=(\theta_\star,0)\). Initialise the numerical and continuous interacting systems identically.</p>'
        + r'<div class="theorem-conclusion" data-time-uniform="true"><p>For every iteration \(n\in\mathbb N\), with all constants independent of time and step size,</p>'
        + eq(r'\|\hat\theta_n-\theta_\star\|_{\mathrm L^2}\le D_M\sqrt h+\sqrt\kappa\,e^{-\rho nh}\mathbf d_0+\frac{2+\gamma}{\rho}\sqrt{\frac{\kappa V_F}{N}}(1-e^{-\rho nh}).',
             r'\begin{gathered}\|\hat\theta_n-\theta_\star\|_{\mathrm L^2}\le D_M\sqrt h\\+\sqrt\kappa\,e^{-\rho nh}\mathbf d_0\\+\frac{2+\gamma}{\rho}\sqrt{\frac{\kappa V_F}{N}}(1-e^{-\rho nh}).\end{gathered}')
        + '</div><p>The full-state raw maximum-component \\(L^2\\) error is also at most the same discretisation term. The factor in the particle floor is the certified response constant used by this endpoint. Constants can depend on fixed population and initial law; they do not grow with iteration count.</p>',
        [('PBGSO/FullyUniformMomentum.lean','explicit_parameter_bound','Explicit proved parameter bound'),
         ('PBGSO/FullyUniformMomentum.lean','explicit_discretization_bound','Explicit full-state discretisation bound')], new='A')
    body += row('theorem-new-b','Theorem New B — HOL-MYPGD final discretisation bound',
        '<p><strong>Assumptions:</strong> N1–N3 and the same cloud encoding. Use the paper’s parameter-first endpoint-force update, its printed coefficients, and the correlated Gaussian innovation triple, with independent time/spatial blocks.</p>'
        + badge(r'Added regularity N1 and frozen realization N3; \(\alpha&gt;0\), \(\gamma\ge0\), \(0&lt;h\le h_{\star,H}\).')
        + '<p>Initialise the numerical and continuous interacting systems identically.</p>'
        + r'<div class="theorem-conclusion" data-time-uniform="true"><p>For every iteration \(n\in\mathbb N\), with all constants independent of time and step size,</p>'
        + eq(r'\|\hat\theta_n-\theta_\star\|_{\mathrm L^2}\le D_H\sqrt h+\sqrt\kappa\,e^{-\rho nh}\mathbf d_0+\frac1\rho\sqrt{\frac{\kappa V_F}{N}}(1-e^{-\rho nh}).',
             r'\begin{gathered}\|\hat\theta_n-\theta_\star\|_{\mathrm L^2}\le D_H\sqrt h\\+\sqrt\kappa\,e^{-\rho nh}\mathbf d_0\\+\frac1\rho\sqrt{\frac{\kappa V_F}{N}}(1-e^{-\rho nh}).\end{gathered}')
        + '</div><p>The full-state raw maximum-component \\(L^2\\) error has the same uniform discretisation coefficient. This is the stationary zero-observation target of the forces actually implemented; a smoothed sampler may have a different target from the original unsmoothed objective. No uniformity in particle count is claimed.</p>',
        [('PBGSO/FullyUniformHigherOrder.lean','explicit_parameter_bound','Explicit proved parameter bound'),
         ('PBGSO/FullyUniformHigherOrder.lean','explicit_discretization_bound','Explicit full-state discretisation bound')], new='B')
    body += '</section>'
    # Verification commands are authored separately so each file can be checked directly.
    body += ('<section class="section" id="verification"><h2>Check the proofs</h2>'
             '<p>Use the repository’s pinned Lean and Mathlib versions. From the repository root, '
             'fetch the Mathlib cache, compile the development and print the axioms of every main theorem:</p>'
             '<pre class="commands"><code>lake exe cache get\n'
             'lake build PBGSO\n'
             'lake env lean PBGSO/Check.lean</code></pre>'
             '<p><code>lake build PBGSO</code> checks every proof; the printed axioms should contain only '
             '<code>propext</code>, <code>Classical.choice</code> and <code>Quot.sound</code>. '
             'Readable entry files state each main result with its complete assumptions and conclusion, '
             'and their short checked proofs apply the library theorems:</p>'
             '<div id="standalone-verification"><pre class="commands"><code>'
             'lake env lean standalone/PBGSO/PaperTheorems.lean\n'
             'lake env lean standalone/PBGSO/NewA.lean\n'
             'lake env lean standalone/PBGSO/NewB.lean</code></pre>'
             '<p>For a single-file proof that imports only Mathlib, generate the transitive local proof closure:</p>'
             '<pre class="commands"><code>python3 scripts/check-pbgso-standalone.py --output /tmp/pbgso-standalone --check\n'
             'lake env lean /tmp/pbgso-standalone/NewA.lean\n'
             'lake env lean /tmp/pbgso-standalone/NewB.lean</code></pre>'
             '<p>Choose a new or empty output directory. The <code>--check</code> run compiles '
             'the exported files in isolation with this project’s compiled proof modules '
             'removed from the search path. The exported files contain the original proofs and assumptions, '
             'rather than an assumed error estimate. '
             '<a href="../../standalone/PBGSO/PaperTheorems.lean">Paper theorem entry file</a> · '
             '<a href="../../standalone/PBGSO/NewA.lean">New A entry file</a> · '
             '<a href="../../standalone/PBGSO/NewB.lean">New B entry file</a>.</p></div>'
             '<p>Check the statement-to-source correspondence with '
             '<code>python3 -B scripts/verify-pbgso.py --require-complete</code>.</p></section>')
    notes = load_notes('PBGSO')

    def placed(nodes):
        result = []
        for node in nodes:
            node = dict(node)
            node['href'] = proof_page(node['file']) + '#' + step_anchor(node['file'], node['declaration'], notes)
            result.append(node)
        return result

    body += ('<section class="section proof-roadmap" id="proof-roadmap"><h2>Proof roadmap</h2>'
             '<p class="section-intro">The roadmap reads from the primitive model at the top to the four paper theorems '
             'and the two new discretisation bounds at the bottom. The left columns follow the continuous-time argument: '
             'the joint metric of assumption A3 and the local Brownian integral give the stationary product law '
             '(Theorem 1), its exponential contraction (Theorem 2), the particle interaction bound (Theorem 3) and the '
             'parameter bound (Theorem 4). The right columns follow the numerical argument: the Lipschitz empirical force, '
             'the contracting particle metrics built from A3, moments uniform in time and the local errors of the '
             'two Gaussian schemes combine into the time-uniform bounds New A and New B. Each box opens the '
             'mathematical statement and proof of that step beside its complete Lean code.</p>'
             + proof_diagram(placed(ROADMAP), page, math, 'PBGSO proof roadmap')
             + '<h3 class="roadmap-appendix">Appendix criteria, volume lemmas and scope checks</h3>'
             '<p class="section-intro">The appendix results give sufficient conditions for assumption A3 and the '
             'volume preservation used by the frictionless splittings; the two scope checks show that the finite '
             'signed-work convention and the corrected HOL coefficients are needed.</p>'
             + proof_diagram(placed(APPENDIX_ROADMAP), page, math, 'PBGSO appendix roadmap')
             + f'<p class="small">The <a href="{relative(CATALOG,page)}#modules">full module catalog</a> and '
             f'<a href="{relative(CATALOG,page)}#source-inventory">eight-result source ledger</a> retain every '
             'intermediate statement. Application-specific smoothing bias and the full-space TV prior assumptions are '
             f'recorded in the <a href="{relative(CATALOG,page)}#limitations">model and target audit</a>.</p></section>')
    parts = argument('PBGSO')['parts']
    if parts:
        body += ('<section class="section" id="mathematical-proof"><h2>The mathematical argument</h2>'
                 '<p class="section-intro">The argument below proves the theorems in order. The adjacent panels give the '
                 'exact Lean statements it rests on and explain how the formal proof assembles them.</p>')
        for i, part in enumerate(parts, 1):
            body += (f'<article class="proof-step" id="argument-{part["id"]}"><h3><span class="step-number">{i:02}</span>'
                     f'{E(part["title"])} <a class="permalink" href="#argument-{part["id"]}">§</a></h3><div class="pair">'
                     '<div class="math-pane">' + math(part['body']) + '</div><div class="lean-pane">')
            if part.get('lean'):
                body += ('<div class="lean-logic"><div class="pane-label">How the Lean proof follows this argument</div>'
                         + math(part['lean']) + '</div>')
            for j, reference in enumerate(part.get('references', []), 1):
                path, name = reference['file'], reference['name']
                body += statement_code(path, name, sources, parsed, page, f'argument-{i}-{j}')
                body += (f'<p class="small"><a href="{relative(proof_page(path), page)}#{step_anchor(path, name, notes)}">'
                         f'Detailed proof in {E(Path(path).name)} →</a></p>')
            body += '</div></div></article>'
        body += '</section>'
    body += ('<section class="section" id="modules"><h2>Supporting proofs</h2>'
             '<p class="section-intro">Each roadmap module has a page pairing its mathematical statements and proofs with '
             'the complete Lean declarations. The technical catalog lists every module of the development.</p>'
             '<div class="dependencies">'
             + ''.join(f'<a href="{relative(proof_page(path), page)}">{E(notes[path]["title"])}</a>'
                       for path in dict.fromkeys(node['file'] for node in ROADMAP + APPENDIX_ROADMAP) if path in notes)
             + f'<a href="{relative(CATALOG,page)}#modules">Complete module catalog</a>'
             f'<a href="{relative("PBGSO/exposition/source_audit.md",page)}">Source audit and formal scope</a></div></section>')
    from report_citations import citation_panel
    from separate_reports import report_revision
    body += citation_panel('PBGSO', 'Particle-based Generalised Stochastic Optimisation', report_revision('PBGSO'), page)
    body += '</div>'
    document = shell(page, 'PBGSO paper theorems and new discretisation bounds', render_prose_math(body, math))
    document = document.replace('<body data-theme-family="modern">', '<body data-theme-family="modern" class="pbgso-page">')
    return document.replace('</head>', '<link rel="stylesheet" href="' +
                            relative('docs/assets/pbgso.css', page) + '"></head>')


def node(identifier, row, col, file, declaration, title, detail, parents=(), final=False):
    return dict(id=identifier, row=row, col=col, file='PBGSO/' + file + '.lean', declaration=declaration,
                title=title, detail=detail, parents=parents, final=final)


# Edges follow the imports between the modules; every box opens its proof page.
ROADMAP = [
    node('model', 0, 0, 'Framework', 'Model', 'Optimiser, observation and sampler maps',
         r'Independent \(F,\Psi,b,\sigma\) and the mean gradient \(G_\nu\)'),
    node('metric', 0, 1, 'PaperTheorems', 'TwistedJointMonotonicity', 'Joint metric and assumption A3',
         'Twisted joint strong monotonicity', ('model',)),
    node('hol-coefficients', 0, 2, 'HigherOrderRates', 'holCoefficient_bounds', 'Coefficients of the higher-order scheme',
         'Printed coefficients and their remainders'),
    node('integral', 1, 0, 'RawLocalIntegral', 'RawLocalDiffusion', 'The local Brownian integral',
         'Stochastic integral of the sampler diffusion', ('metric',)),
    node('heavy-ball', 1, 1, 'HypocoerciveCriterion', 'heavyBall_source_criterion', 'Heavy-ball hypocoercivity',
         'A sufficient condition for A3 with momentum', ('metric',)),
    node('force', 1, 2, 'ParticleMethodLp', 'meanForce_lipschitz', 'Lipschitz empirical mean force',
         'Global Lipschitz bound from N1', ('hol-coefficients',)),
    node('theorem-1', 2, 0, 'RawPathSolutionTransfer', 'stationary_product_law_of_weak_frozen',
         'Theorem 1: stationary product law', 'Weak frozen invariance of the sampler', ('integral',)),
    node('absorption', 2, 1, 'UniformDiscrete', 'one_step_same_initial_uniform_norm', 'Absorption of accumulated errors',
         r'Contraction beats local error for \(h\le h_\star\)', ('metric',)),
    node('moments', 2, 2, 'UniformIntegralMoments', 'uniform_moment', 'Moments uniform in time',
         'Derived from the contraction, not assumed', ('force',)),
    node('theorem-2-growth', 3, 0, 'RawSamplerGrowthArbitraryLaw', 'law_distance_decay', 'Theorem 2 under linear growth',
         'Exponential decay of the law distance', ('theorem-1',)),
    node('theorem-2-work', 3, 1, 'NaturalFiniteWorkArbitraryLaw', 'law_distance_decay', 'Theorem 2 for constant diffusion',
         'Exponential decay with finite signed work', ('theorem-1',)),
    node('theorem-3', 3, 2, 'RawConstructedParticleBounds', 'original_finite_particle_interaction_bound',
         'Theorem 3: particle interaction bound', 'Independent reference clouds and localisation', ('integral', 'force')),
    node('theorem-4', 4, 0, 'RawConstructedParticleParameter', 'original_parameter_bound_constant',
         'Theorem 4: parameter bound', 'Stationary comparison plus particle interaction', ('theorem-2-growth', 'theorem-3'), True),
    node('metric-m', 4, 1, 'ImplementationMetric', 'momentum_metric', 'Contracting metric for M-MFPO',
         'Built from assumption A3', ('heavy-ball', 'force', 'integral')),
    node('metric-h', 4, 2, 'ImplementationMetric', 'higherOrder_metric', 'Contracting metric for HOL-MYPGD',
         'Built from assumption A3', ('heavy-ball', 'force')),
    node('obabo', 5, 0, 'MomentumUniformDefect', 'obabo_affine_local_defect', 'Local error of the OBABO scheme',
         'Gaussian splitting with explicit coefficients', ('moments',)),
    node('restart', 5, 2, 'HOLRestart', 'higherOrderRestart_contracts', 'Exact restarts and their contraction',
         'Restarted flows of the higher-order dynamics', ('force',)),
    node('new-a', 6, 0, 'FullyUniformMomentum', 'explicit_parameter_bound', 'Theorem New A',
         r'M-MFPO error \(D\sqrt h\) at every iteration', ('metric-m', 'obabo', 'absorption'), True),
    node('hol-local', 6, 2, 'HOLRestartLocal', 'higherOrderRestart_local_error', 'Local error of the higher-order scheme',
         'Gaussian scheme against the exact restart', ('restart', 'moments')),
    node('hol-uniform', 7, 1, 'HOLUniform', 'higherOrder_time_uniform_of_integral', 'Error bound for all iterations',
         'Strong discretisation error of the higher-order scheme', ('hol-local', 'absorption')),
    node('new-b', 8, 1, 'FullyUniformHigherOrder', 'explicit_parameter_bound', 'Theorem New B',
         r'HOL-MYPGD error \(D\sqrt h\) at every iteration', ('hol-uniform', 'metric-h'), True),
]

APPENDIX_ROADMAP = [
    node('separated', 0, 0, 'SmallGainSpectrum', 'separated_source_criterion', 'Separate monotonicity criterion',
         'Small-gain condition implying A3'),
    node('projected', 0, 1, 'CanonicalProjectedCriterion', 'canonical_projected_source_criterion', 'Projected criterion',
         'A3 for projected samplers'),
    node('volume', 0, 2, 'Volume', 'interwovenBAB_preserves', 'Discrete splitting preserves volume',
         'Frictionless splitting step'),
    node('finite-domain', 1, 0, 'ProjectedFiniteWork', 'canonical_projected_source_criterion_finite',
         'Finite sampler work', 'The integrability domain of the projected criterion', ('projected',)),
    node('flow-determinant', 1, 1, 'FlowSourceRegularity', 'phase_flow_fderiv_det_one_source', 'Jacobian determinant one',
         r'\(C^1\) force and global solutions', ('volume',)),
    node('discrete-determinant', 1, 2, 'DiscreteVolume', 'interwovenBAB_fderiv_det_one', 'Determinant of the splitting step',
         'Each substep has determinant one', ('volume',)),
    node('flow-volume', 2, 0, 'ContinuousFlowMeasure', 'phase_flow_measurePreserving_source',
         'Continuous flow preserves volume', 'Change of variables with determinant one', ('flow-determinant',)),
    node('work-scope', 2, 1, 'FiniteWorkScopeAudit', 'exists_p2_nonintegrable_work', 'Signed work can be infinite',
         r'A law in \(\mathcal P_2\) with non-integrable work'),
    node('hol-scope', 2, 2, 'HOLCoefficientAudit', 'hol_linear_coefficient_not_exact', 'Printed coefficients are not exact',
         'The linear flow differs from the printed scheme'),
]


def numerical_constants(row, eq, declarations):
    """Closed mathematical definitions, paired with their checked source values."""
    expanded = 'PBGSO/UniformConstantExpansions.lean'
    mfile = 'PBGSO/FullyUniformMomentum.lean'
    hfile = 'PBGSO/FullyUniformHigherOrder.lean'
    result = row('numerical-models', 'The two method models and their raw coordinates', '\n<p>As in the paper’s algorithm section, suppress the population superscript in the method coordinates. For M-MFPO:</p>'
        + eq(r'\begin{aligned}\dot\theta_t&=m_t,\qquad\dot m_t=-N^{-1}\sum_i F(\theta_t,X_t^i)-\gamma m_t,\\\mathrm dX_t^i&=V_t^i\,\mathrm dt,\\\mathrm dV_t^i&=(-F_x(\theta_t,X_t^i)-\gamma V_t^i)\,\mathrm dt+\sqrt{2\gamma}\,\mathrm dB_t^i.\end{aligned}',
             r'\begin{aligned}\dot\theta_t&=m_t,\\\dot m_t&=-N^{-1}\sum_i F(\theta_t,X_t^i)-\gamma m_t,\\\mathrm dX_t^i&=V_t^i\,\mathrm dt,\\\mathrm dV_t^i&=(-F_x(\theta_t,X_t^i)-\gamma V_t^i)\,\mathrm dt\\&\quad+\sqrt{2\gamma}\,\mathrm dB_t^i.\end{aligned}')
        + '<p>For HOL-MYPGD:</p>'
        + eq(r'\begin{aligned}\dot\theta_t&=-N^{-1}\sum_iF(\theta_t,X_t^i),\qquad\mathrm dX_t^i=U_t^i\,\mathrm dt,\\\mathrm dU_t^i&=(-F_x(\theta_t,X_t^i)+\gamma V_t^i)\,\mathrm dt,\\\mathrm dV_t^i&=(-\gamma U_t^i-\alpha V_t^i)\,\mathrm dt+\sqrt{2\alpha}\,\mathrm dB_t^i.\end{aligned}',
             r'\begin{aligned}\dot\theta_t&=-N^{-1}\sum_iF(\theta_t,X_t^i),\\\mathrm dX_t^i&=U_t^i\,\mathrm dt,\\\mathrm dU_t^i&=(-F_x(\theta_t,X_t^i)+\gamma V_t^i)\,\mathrm dt,\\\mathrm dV_t^i&=(-\gamma U_t^i-\alpha V_t^i)\,\mathrm dt\\&\quad+\sqrt{2\alpha}\,\mathrm dB_t^i.\end{aligned}')
        + '<p>Write \\(y\\) for the implementation phase, an additional symbol distinct from the paper’s sampler \\(Z\\). Its four coordinates are \\(((m,V^{[N]}),(\\theta,X^{[N]}))\\) for M-MFPO and \\((\\theta,X^{[N]},U^{[N]},V^{[N]})\\) for HOL. The exact raw norm is \\(\\|y\\|_{\\max,2}=\\max_{1\\le k\\le4}\\|y_k\\|_{\\mathrm L^2}\\). The numerical and continuous initial phases coincide.</p>',
        [('PBGSO/HypocoerciveCriterion.lean','heavyBallModel','Actual kinetic model'),
         ('PBGSO/ImplementationDynamics.lean','higherOrderModel','Actual higher-order model')])
    result += row('numerical-force-constants', 'Explicit force and cloud constants', r'''
<p>Let \(d=Nd_x\), and let the standard cloud map be the concrete reindexing \(\mathcal E_N:\mathbb R^{Nd_x}\to(\mathbb R^{d_x})^N\), \((\mathcal E_Nx)_i=(x_{i,j})_{j=1}^{d_x}\). Its domain has the Euclidean norm and its target the maximum of particle Euclidean norms. Define the actual finite-cloud maps</p>'''
        + eq(r'\bar F_N(\theta,x)=\frac1N\sum_{i=1}^NF(\theta,(\mathcal E_Nx)_i),\qquad\mathcal F_{x,N}(\theta,x)=\mathcal E_N^{-1}\bigl((F_x(\theta,(\mathcal E_Nx)_i))_{i=1}^N\bigr).',
             r'\begin{gathered}\bar F_N(\theta,x)=N^{-1}\sum_iF(\theta,(\mathcal E_Nx)_i),\\\mathcal F_{x,N}(\theta,x)\\=\mathcal E_N^{-1}\bigl((F_x(\theta,(\mathcal E_Nx)_i))_i\bigr).\end{gathered}')
        + '<p>For the paper’s positive position dimension \\(d_x\\ge1\\), the exact norm identities \\(\\|\\mathcal E_N\\|=1\\), \\(\\|\\mathcal E_N^{-1}\\|=\\sqrt N\\) give the explicit certified force constants</p>'
        + eq(r'L_F=2\ell_F,\qquad L_x=2\sqrt N\,\ell_x.')
        + r'<p>The formal development also permits \(d_x=0\); then use \(L_F=\ell_F\), \(L_x=0\). Both cases are proved in Lean, so no positive-dimension assumption is hidden.</p>'
        + eq(r'f_0=\|F(0,0)\|,\qquad g_0=\sqrt N\,\|F_x(0,0)\|,\qquad b_\circ=\max\{f_0,g_0\}.',
             r'\begin{gathered}f_0=\|F(0,0)\|,\\g_0=\sqrt N\,\|F_x(0,0)\|,\\b_\circ=\max\{f_0,g_0\}.\end{gathered}')
        + '<p>The origin identities on the right prove that these are exactly the \\(L^2\\) norms of the lifted mean and sampler forces. In either raw phase, the full drift at zero has norm \\(b_\\circ\\). These formulas specify the coordinate norms, the force values and every input used below; \\(G_\\nu\\) retains its meaning from the paper.</p>',
        [('PBGSO/ParticleMethodLp.lean','euclideanParticleEncoding','Standard cloud coordinates'),
         ('PBGSO/CloudEncodingConstants.lean','meanLip_euclidean','Exact positive-dimension empirical constant'),
         ('PBGSO/CloudEncodingConstants.lean','samplerForceLip_euclidean','Exact positive-dimension sampler constant'),
         ('PBGSO/CloudEncodingConstants.lean','meanLip_euclidean_zero','Zero-dimensional empirical constant'),
         ('PBGSO/CloudEncodingConstants.lean','samplerForceLip_euclidean_zero','Zero-dimensional sampler constant'),
         ('PBGSO/UniformOriginConstants.lean','meanForceLp_zero_norm','Primitive mean-force value at zero'),
         ('PBGSO/UniformOriginConstants.lean','samplerForceLp_zero_norm','Primitive sampler-force value at zero'),
         ('PBGSO/UniformOriginConstants.lean','coupledForce_zero_norm','Full kinetic force at zero'),
         ('PBGSO/UniformOriginConstants.lean','holDrift_zero_norm','Full HOL drift at zero')])
    result += row('numerical-m-constants', 'New A — Fully expanded local coefficients',
        eq(r'L_M=2\max\{L_F,L_x\},\qquad K_M=L_M+\gamma+1,\qquad\Xi_M=\sqrt d,\qquad\beta_M=\sqrt\gamma\sqrt{2d}.',
           r'\begin{gathered}L_M=2\max\{L_F,L_x\},\\K_M=L_M+\gamma+1,\\\Xi_M=\sqrt d,\quad\beta_M=\sqrt\gamma\sqrt{2d}.\end{gathered}')
        + eq(r'T_M=b_\circ+K_Me^{K_M+1}(b_\circ+\beta_M)+\beta_M.',
             r'\begin{aligned}T_M&=b_\circ+\beta_M\\&\quad+K_Me^{K_M+1}(b_\circ+\beta_M).\end{aligned}')
        + eq(r'c_{0,M}=\left(\frac{\gamma+1}{2}+\frac{L_M}{4}\right)b_\circ+\left(\frac{L_M}{2}+\sqrt\gamma+\frac32\gamma\sqrt\gamma\right)\sqrt d+\frac23K_MT_M.',
             r'\begin{aligned}c_{0,M}&=\left(\frac{\gamma+1}{2}+\frac{L_M}{4}\right)b_\circ\\&\quad+\left(\frac{L_M}{2}+\sqrt\gamma\right)\sqrt d\\&\quad+\frac32\gamma\sqrt\gamma\sqrt d+\frac23K_MT_M.\end{aligned}')
        + eq(r'c_{1,M}=\frac{\gamma^2+\gamma+L_M}{2}+\left(\frac{\gamma+1}{2}+\frac{L_M}{4}\right)L_M+\frac23K_M^2e^{K_M+1}.',
             r'\begin{aligned}c_{1,M}&=\frac{\gamma^2+\gamma+L_M}{2}\\&\quad+\left(\frac{\gamma+1}{2}+\frac{L_M}{4}\right)L_M\\&\quad+\frac23K_M^2e^{K_M+1}.\end{aligned}')
        + '<p>These are nonnegative coefficients of the proved local error, with its dependence on the numerical input norm explicit. The Lean equality on the right verifies the arithmetic expansion.</p>',
        declarations(expanded,'momentumExpandedConstant0','momentumExpandedConstant1','momentumUniformDefect_expanded'))
    result += row('numerical-h-constants', 'New B — Fully expanded local coefficients',
        eq(r'K_H=4(L_F+L_x+1+2\gamma+\alpha),\qquad\beta_H=\sqrt\alpha\sqrt{2d}.',
           r'\begin{gathered}K_H=4(L_F+L_x+1+2\gamma+\alpha),\\\beta_H=\sqrt\alpha\sqrt{2d}.\end{gathered}')
        + '<p>The coefficient-remainder constants below are distinct from the paper’s step-dependent \\(\\mu_{ij}\\):</p>'
        + eq(r'r_{12}=\frac{\gamma^2}{2\alpha},\quad r_{13}=\frac\gamma2,\quad r_{22}=\frac{\gamma^2}{2},\quad r_{23}=\frac{\gamma\alpha}{2},\quad r_{31}=\frac\gamma2,',
             r'\begin{gathered}r_{12}=\frac{\gamma^2}{2\alpha},\quad r_{13}=\frac\gamma2,\\r_{22}=\frac{\gamma^2}{2},\quad r_{23}=\frac{\gamma\alpha}{2},\quad r_{31}=\frac\gamma2,\end{gathered}')
        + eq(r'r_{32}=\frac{2\gamma^3}{\alpha}+\frac{\gamma^3}{2}+\frac{\gamma\alpha}{2},\qquad r_{33}=\frac{3\gamma^2}{2}+\frac{\alpha^2}{2}+\frac{\alpha\gamma^2}{2}.',
             r'\begin{gathered}r_{32}=\frac{2\gamma^3}{\alpha}+\frac{\gamma^3}{2}+\frac{\gamma\alpha}{2},\\r_{33}=\frac{3\gamma^2}{2}+\frac{\alpha^2}{2}+\frac{\alpha\gamma^2}{2}.\end{gathered}')
        + eq(r'A_H=\frac{1+\gamma}{2}\bigl[g_0+2L_x+L_x(f_0+2L_F)\bigr]+(r_{12}+r_{22}+r_{32})+(r_{13}+r_{23}+r_{33})+L_x(f_0+2L_F),',
             r'\begin{aligned}A_H&=\frac{1+\gamma}{2}\bigl[g_0+2L_x\\&\qquad+L_x(f_0+2L_F)\bigr]\\&\quad+(r_{12}+r_{22}+r_{32})\\&\quad+(r_{13}+r_{23}+r_{33})\\&\quad+L_x(f_0+2L_F),\end{aligned}', tablet=True)
        + eq(r'N_H=\sqrt{2\alpha}\left(\frac{3\gamma}{2}+\alpha+r_{33}\right),\qquad T_H=b_\circ+K_He^{K_H+1}(b_\circ+\beta_H)+\beta_H,',
             r'\begin{gathered}N_H=\sqrt{2\alpha}\left(\frac{3\gamma}{2}+\alpha+r_{33}\right),\\\begin{aligned}T_H&=b_\circ+\beta_H\\&\quad+K_He^{K_H+1}(b_\circ+\beta_H),\end{aligned}\end{gathered}')
        + eq(r'c_{0,H}=A_H+\sqrt d\,N_H+\frac83K_HT_H,\qquad c_{1,H}=A_H+\frac83K_H^2e^{K_H+1}.',
             r'\begin{gathered}c_{0,H}=A_H+\sqrt d\,N_H+\frac83K_HT_H,\\c_{1,H}=A_H+\frac83K_H^2e^{K_H+1}.\end{gathered}')
        + r'<p>Every intermediate coefficient is defined here. The dimension factor \(\sqrt d\) occurs once in the Gaussian term. The identities on the right certify these expansions for \(\alpha&gt;0\), \(\gamma\ge0\).</p>',
        declarations(expanded,'holExpandedRemainder32','holExpandedRemainder33','holExpandedGrowthConstant','holExpandedNoiseConstant','holExpandedConstant0','holExpandedConstant1','holUniformLocalConstant0_expanded','holUniformLocalConstant1_expanded'))
    result += row('numerical-metric-constants', 'Both methods — Explicit metric comparisons', r'''
<p>For either chosen method, use its source A3 weights and certified \(\underline\lambda,\overline\lambda\). Define</p>'''
        + eq(r'\underline d_N=\underline\lambda\min\{1,N^{-1}\},\qquad\overline d_N=\overline\lambda\max\{1,N^{-1}\},\qquad m_N=\frac{\sqrt{\underline d_N}}2,\qquad U_N=2\sqrt{\overline d_N}.',
             r'\begin{gathered}\underline d_N=\underline\lambda\min\{1,N^{-1}\},\\\overline d_N=\overline\lambda\max\{1,N^{-1}\},\\m_N=\frac{\sqrt{\underline d_N}}2,\quad U_N=2\sqrt{\overline d_N}.\end{gathered}')
        + r'<p>Since \(N\ge1\), these are \(m_N=\tfrac12\sqrt{\underline\lambda/N}\) and \(U_N=2\sqrt{\overline\lambda}\). The coordinate comparisons and source A3 construct a linear metric factor \(C\) with \(m_N\|y\|_{\max,2}\le\|Cy\|\le U_N\|y\|_{\max,2}\), together with exact-flow contraction at rate \(\rho\). No unknown coordinate-map norm enters these metric constants.</p>',
        declarations(mfile,'metricCoercivity','metricUpper') + declarations('PBGSO/MethodMetricComparisons.lean','momentum_metric_explicit','higherOrder_metric_explicit'))
    result += row('numerical-final-constants', 'Both methods — Explicit uniform constants and allowed steps', r'''
<p>For \(j=M,H\), use the corresponding \(K_j,\beta_j,c_{0,j},c_{1,j}\) above and the same initial raw phase \(y_0\). All remaining constants are</p>'''
        + eq(r'S_j=U_Ne^{K_j+1}(b_\circ+\beta_j),\qquad R_j=U_N\|y_0\|_{\max,2}+\frac{S_j}{1-e^{-\rho}}+S_j,',
             r'\begin{gathered}S_j=U_Ne^{K_j+1}(b_\circ+\beta_j),\\\begin{aligned}R_j&=U_N\|y_0\|_{\max,2}\\&\quad+\frac{S_j}{1-e^{-\rho}}+S_j,\end{aligned}\end{gathered}')
        + eq(r'a_j=U_Nc_{0,j},\qquad b_j=\frac{U_Nc_{1,j}}{m_N},\qquad D_j=\frac{4(a_j+b_jR_j)}{\rho m_N},',
             r'\begin{gathered}a_j=U_Nc_{0,j},\quad b_j=\frac{U_Nc_{1,j}}{m_N},\\D_j=\frac{4(a_j+b_jR_j)}{\rho m_N},\end{gathered}')
        + eq(r'h_{\star,j}=\min\left\{1,\frac1\rho,\left(\frac{\rho}{4(b_j+1)}\right)^2\right\}>0.',
             r'\begin{gathered}q_j=\frac{\rho}{4(b_j+1)},\\h_{\star,j}=\min\{1,\rho^{-1},q_j^2\}>0.\end{gathered}')
        + r'<p>Thus \(D_j\) and \(h_{\star,j}\) depend on the fixed population, initial second moments, force values and Lipschitz constants, friction parameters and A3 metric/rate. They are independent of \(h,n\) and time horizon. The proof derives the reference radius and absorbs the local errors; they are not additional moment or numerical-stability assumptions.</p>',
        declarations(mfile,'zeroStartMoment','referenceRadius','radiusGrowth','discretizationConstant','maximumStep') +
        declarations(hfile,'zeroStartMoment','referenceRadius','radiusGrowth','discretizationConstant','maximumStep'))
    return result
