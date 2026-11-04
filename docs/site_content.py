"""Authored standalone theorem statements and logical proof roadmaps."""
from pathlib import Path
from references import reference_notice, DEVELOPMENTS, PAPERS
from build_site import (E, LIBRARIES, relative, module_page, anchor, shell,
                        toolbar, commands, proof_diagram, declaration_header, code)


def node(identifier, row, col, file, title, detail, parents=(), final=False):
    return dict(id=identifier,row=row,col=col,file=file,title=title,detail=detail,parents=parents,final=final)


ULA_SETUP = r'''<p>Let \(d\ge1\), and let \(U:\mathbb R^d\to\mathbb R\) be differentiable and \(m\)-strongly convex, with \(m>0\) and \(L\)-Lipschitz gradient. These assumptions imply \(m\le L\). Define</p>
\[\pi(dx)=Z^{-1}e^{-U(x)}dx,\qquad Z=\int e^{-U(x)}dx\in(0,\infty).\]
<p>Let \(\mu_0\) be a probability measure with \(W_2(\mu_0,\pi)&lt;\infty\). This condition holds if \(\mu_0\) has a finite second moment, because the assumptions on \(U\) imply that \(\pi\) has a finite second moment. Let \(X_0\) have distribution \(\mu_0\), and let \((\xi_k)\) be independent standard Gaussian vectors, independent of \(X_0\). For \(h>0\), define</p>
\[X_{k+1}=X_k-h\nabla U(X_k)+\sqrt{2h}\,\xi_k,\qquad\mu_k=\operatorname{Law}(X_k).\]
<p>The conditional distribution of \(X_{k+1}\) given \(X_k=x\) is \(P_h(x,\cdot)=\mathcal N(x-h\nabla U(x),2hI_d)\). Consequently \(\mu_{k+1}=\mu_kP_h\). This follows from the independence of \(\xi_k\) from the preceding variables. The convergence estimate below is therefore an estimate for the distribution of the stated recursion.</p>
<p class="formal-note">In the Lean statement, \(\mathbb R^d\) is <code>EuclideanSpace ℝ ι</code> with a finite nonempty index type, and \(d=|\iota|\). <code>ulaLawStep</code> is the exact Gaussian transition on probability laws.</p>'''

IPLA_STATEMENT = r'''<p>Fix an observation \(y\) and a differentiable joint potential \(U_y:\mathbb R^{d_\theta}\times\mathbb R^{d_x}\to\mathbb R\). Assume \(U_y\) is \(m\)-strongly convex with \(m>0\) and has \(L\)-Lipschitz gradient. Let \(N\ge1\); the independent dimensions \(d_\theta,d_x\ge0\) may be zero. Define</p>
\[\ell_y(\theta)=\int e^{-U_y(\theta,x)}dx,\quad
\theta_\star\in\operatorname*{argmax}_\theta\ell_y(\theta).\]
<p>In scaled coordinates \(z=(\theta,x^1/\sqrt N,\ldots,x^N/\sqrt N)\), set</p>
\[V_N(z)=\sum_{i=1}^NU_y(\theta,\sqrt N z_i),\qquad
\Pi_N(dz)\propto e^{-V_N(z)}dz.\]
<p>Assume the initial state has a finite second moment. Let all Gaussian vectors in the following recursion be standard and independent of one another and of the initial state. For \(0&lt;\gamma\le2/(m+L)\), define the IPLA iterates by</p>
\[\begin{aligned}
\theta_{k+1}&=\theta_k-\frac\gamma N\sum_i\nabla_\theta U_y(\theta_k,x_k^i)+\sqrt{2\gamma/N}\,\xi_k^0,\\
x_{k+1}^i&=x_k^i-\gamma\nabla_xU_y(\theta_k,x_k^i)+\sqrt{2\gamma}\,\xi_k^i.
\end{aligned}\]
<p>Writing \(\mu_0\) for the initial scaled-state law, for every \(k\in\mathbb N\),</p>
\[\begin{aligned}
\bigl(\mathbb E\|\theta_k-\theta_\star\|^2\bigr)^{1/2}
\le{}&\sqrt{\frac{2d_\theta}{Nm}}+(1-m\gamma)^kW_2(\mu_0,\Pi_N)\\
&+\frac{33}{20}\frac Lm\sqrt{d_x+\frac{d_\theta}{N}}\sqrt\gamma.
\end{aligned}\]
<p>The assumptions imply that the Gibbs measures are normalized by finite positive constants and have finite second moments. The proof also establishes strong convexity of the negative log marginal. Existence and uniqueness of its minimizer are proved separately from the same assumptions, so \(\theta_\star\) exists and is the unique maximizer of the integrated joint density \(\ell_y\). If the potential includes the negative log of a prior density, the same definition maximizes that prior-weighted marginal. The proof compares the particle distribution with its Gibbs measure and then bounds the parameter's second moment about \(\theta_\star\).</p>'''

PROX_SETUP = r'''<p>Write \(U=g_1+g_2\) on \(\mathbb R^{d_\theta+d_x}\). Assume \(g_1\) is differentiable, \(m\)-strongly convex for \(m>0\), and has \(L_1\)-Lipschitz gradient. Assume \(g_2\) is finite-valued, convex, bounded below, and \(K\)-Lipschitz. Define its proximal map and Moreau envelope by</p>
\[P_\eta(x)=\operatorname*{argmin}_p\left\{g_2(p)+\frac{\|p-x\|^2}{2\eta}\right\},\quad
g_2^\eta(x)=g_2(P_\eta(x))+\frac{\|P_\eta(x)-x\|^2}{2\eta},\]
\[V_\eta=g_1+g_2^\eta,\qquad L_\eta=L_1+\eta^{-1},\qquad\eta>0.\]
<p>Let \(N\ge1\), \(d_\theta,d_x\ge0\), and assume the initial particle state in scaled coordinates has a finite second moment. The Gaussian vectors are standard, independent over coordinates and time, and are independent of the initial state. Denote the initial distribution in these coordinates by \(\rho_0\), and denote the Gibbs measure associated with the sum of the \(N\) copies of \(V_\eta\) by \(\Pi_{N,\eta}\). Let \(\theta_U\) and \(\theta_\eta\) maximize the parameter marginals corresponding to \(g_1+g_2\) and \(V_\eta\). The proof establishes the existence of both maximizers under these assumptions.</p>'''

PROX_SETUP += r'''<p>Precisely, the scaled state, lifted potential, and normalized target are</p>
\[z=(\theta,x^1/\sqrt N,\ldots,x^N/\sqrt N),\qquad
W_{N,\eta}(z)=\sum_{i=1}^N V_\eta(\theta,\sqrt N z_i),\]
\[\Pi_{N,\eta}(dz)=Z_{N,\eta}^{-1}e^{-W_{N,\eta}(z)}dz.\]
<p>A marginal maximizer of a pair potential \(V\) maximizes \(\theta\mapsto\int e^{-V(\theta,x)}dx\).</p>'''

MYIPLA = PROX_SETUP + r'''<p>MYIPLA is the Gaussian IPLA recursion for \(V_\eta\), using the proved identity \(\nabla g_2^\eta=(I-P_\eta)/\eta\):</p>
\[z_{n+1}=z_n-\frac\gamma N\nabla W_{N,\eta}(z_n)+\sqrt{2\gamma/N}\,\xi_n.\]
<p>For \(0&lt;\gamma\le2/(m+L_\eta)\) and every \(n\in\mathbb N\), the parameter iterate satisfies</p>
\[\begin{aligned}
\bigl(\mathbb E\|\theta_n-\theta_U\|^2\bigr)^{1/2}
\le{}&\sqrt{\frac{\eta K^2}{m}}+\sqrt{\frac{d_\theta}{Nm}}
+(1-m\gamma)^nW_2(\rho_0,\Pi_{N,\eta})\\
&+\frac{33}{20}\frac{L_\eta}{m}\sqrt{d_x+\frac{d_\theta}{N}}\sqrt\gamma.
\end{aligned}\]
<p>The first term bounds \(\|\theta_U-\theta_\eta\|\). The second bounds the root mean square distance from a parameter drawn from \(\Pi_{N,\eta}\) to \(\theta_\eta\). The remaining two terms bound the distance between the numerical distribution and \(\Pi_{N,\eta}\). The smoothing estimate is \(O(\sqrt\eta)\), and the discretization term depends on \(\eta\) through \(L_\eta\). These are the bounds proved here; the paper's linear-in-\(\eta\) smoothing expression is not a conclusion of this argument.</p>'''

PIPGLA = PROX_SETUP + r'''<p>For PIPGLA assume also \(m\le L_1\), take any proximal parameter \(\lambda>0\), and \(0&lt;\gamma\le2/(m+L_1)\). First apply the smooth-gradient step with its averaged parameter drift and Gaussian innovation:</p>
\[\begin{aligned}
\widetilde\theta_n&=\theta_n-\frac\gamma N\sum_i\nabla_\theta g_1(\theta_n,x_n^i)+\sqrt{2\gamma/N}\,\xi_n^0,\\
\widetilde x_n^i&=x_n^i-\gamma\nabla_x g_1(\theta_n,x_n^i)+\sqrt{2\gamma}\,\xi_n^i.
\end{aligned}\]
<p>Then set \((a_i,b_i)=P_\lambda(\widetilde\theta_n,\widetilde x_n^i)\), \(\theta_{n+1}=N^{-1}\sum_i a_i\), and \(x_{n+1}^i=b_i\). Let \(\theta_\gamma\) maximize the marginal for \(V_\gamma\). The actual iterates satisfy</p>
\[\begin{aligned}
\bigl(\mathbb E\|\theta_n-\theta_U\|^2\bigr)^{1/2}
\le{}&\frac{K|\lambda-\gamma|}{m\gamma}+\sqrt{\frac{\gamma K^2}{m}}+\sqrt{\frac{d_\theta}{Nm}}\\
&+\sqrt{(1-m\gamma)^n W_2(\rho_0,\Pi_{N,\gamma})^2+\frac\gamma N C_N}.
\end{aligned}\]
<p>All constants are explicit. Put \(D=d_\theta+Nd_x\), \(a=Nm\), \(b=NL_1\), \(c=NK\),</p>
\[G=\sqrt{2b^2D/a+2c^2}+c,\qquad\sigma=\sqrt{2D},\]
\[C_N=\frac{4b^2}{a^2}\left(\frac{G^2}{a}+\sigma^2\right)+\frac2a(Gc+c^2).\]
<p>The first term bounds the difference caused by using \(P_\lambda\) in place of \(P_\gamma\). The next two terms bound smoothing of the parameter maximizer and the second moment of the smoothed Gibbs parameter marginal. The square-root term follows from a coupling of the splitting recursion with a stationary comparison process, followed by a recurrence for their squared distance. The constants in this estimate differ from those printed in the paper.</p>'''

MYPGD = PROX_SETUP + r'''<p>MYPGD has the MYIPLA drift, with zero Gaussian noise in the parameter coordinates and unchanged Gaussian noise in the latent coordinates:</p>
\[z_{n+1}=z_n-\frac\gamma N\nabla W_{N,\eta}(z_n)+\sqrt{2\gamma/N}\,M\xi_n,\]
<p>where \(M\) is the orthogonal projection onto latent coordinates. Assume \(m\le L_\eta\) explicitly and \(0&lt;\gamma\le2/(m+L_\eta)\). For every \(n\in\mathbb N\), the actual finite-particle recursion satisfies</p>
\[\begin{aligned}
\bigl(\mathbb E\|\theta_n^{\rm PGD}-\theta_U\|^2\bigr)^{1/2}
\le{}&\sqrt{\frac{2d_\theta}{Nm}}+\sqrt{\frac{\eta K^2}{m}}+\sqrt{\frac{d_\theta}{Nm}}\\
&+(1-m\gamma)^nW_2(\rho_0,\Pi_{N,\eta})\\
&+\frac{33}{20}\frac{L_\eta}{m}\sqrt{d_x+\frac{d_\theta}{N}}\sqrt\gamma.
\end{aligned}\]
<p>The additional \(\sqrt{2d_\theta/(Nm)}\) bounds the distance caused by setting the parameter noise to zero. It is obtained by comparing the two recursions with the same latent Gaussian variables. The displayed estimate concerns the finite-particle algorithm; it does not establish the paper's stronger estimate for the mean-field distance or its constants.</p>'''

CONFIG = {
    'UnadjustedLangevin':dict(label='Wasserstein convergence',title='Unadjusted Langevin under Strong Convexity',subtitle='A Wasserstein convergence bound for a strongly convex potential.',
        status='The proof establishes Gibbs stationarity and compares ULA with a stationary Langevin process. It assumes differentiability, strong convexity and a Lipschitz gradient. The separate LSI report proves an entropy estimate from smoothness, LSI and finite initial relative entropy.',
        archive='UnadjustedLangevin/exposition/dist/index.html',archive_label='Extended teaching document and Lean notes',
        extra=[('UnadjustedLangevin/LSI/exposition/index.html','Entropy under LSI · full proof and reference audit')],
        results=[dict(title='The small-step convergence bound',file='UnadjustedLangevin/CanonicalULA.lean',name='dalalyan',body=ULA_SETUP+r'''<p>If \(0&lt;h\le2/(m+L)\), then for every \(k\in\mathbb N\),</p>\[W_2(\mu_k,\pi)\le(1-mh)^kW_2(\mu_0,\pi)+\frac{33}{20}\frac Lm\sqrt{hd}.\]<p>The rational coefficient \(33/20\) is exactly \(1.65\). The initial distance is the infimum of root mean square costs over all couplings of the two initial measures.</p>'''),
                 dict(title='The larger-step convergence bound',file='UnadjustedLangevin/CanonicalULA.lean',name='dalalyan_large_step',body=ULA_SETUP+r'''<p>If \(2/(m+L)\le h\) and \(Lh&lt;2\), then for every \(k\in\mathbb N\),</p>\[W_2(\mu_k,\pi)\le(Lh-1)^kW_2(\mu_0,\pi)+\frac{33}{20}\frac{Lh}{2-Lh}\sqrt{hd}.\]<p>The assumption \(Lh&lt;2\) makes the denominator positive. The two estimates follow from the same error recurrence with the contraction factor appropriate to each step interval.</p>''')],
        diagram=[node('geometry',0,0,'UnadjustedLangevin/SharpContraction.lean','Contraction of the gradient step',r'\(q=1-mh\) or \(Lh-1\)'),
                 node('gibbs',0,1,'UnadjustedLangevin/Gibbs.lean','Normalization of the Gibbs measure',r'Positive normalization and \(L^2\) moments'),
                 node('brownian',0,2,'UnadjustedLangevin/CanonicalBrownian.lean','Gaussian construction of Brownian motion','Independent Gaussian coordinates'),
                 node('local',1,0,'UnadjustedLangevin/LocalError.lean','The local discretization error','Integrate the Lipschitz drift error'),
                 node('stationary',1,1,'UnadjustedLangevin/GibbsStationarity.lean','Stationarity of the Gibbs measure','Metropolis invariance and Euler limit',('gibbs','brownian')),
                 node('integral',1,2,'UnadjustedLangevin/LangevinIntegral.lean','Existence of the integral solution',r'\(L^2\) Picard construction',('brownian',)),
                 node('recurrence',2,0,'UnadjustedLangevin/Recurrence.lean','The scalar error recurrence',r'\(a_{k+1}\le q a_k+b\)',('geometry','local')),
                 node('coupling',2,1,'UnadjustedLangevin/HilbertDalalyan.lean','Coupling with the same Brownian motion','Cancellation of the common increment',('local','stationary','integral')),
                 node('law',2,2,'UnadjustedLangevin/ChainLaw.lean','Distributions of the Gaussian recursion','Independence determines each transition',('brownian',)),
                 node('final',3,1,'UnadjustedLangevin/CanonicalULA.lean','The ULA convergence theorem','Both stable step-size regimes',('recurrence','coupling','law'),True)]),
    'IPLA':dict(label='Particle convergence',title='Interacting Particle Langevin under Strong Convexity',subtitle='A root mean square parameter estimate for the particle recursion.',
        status='The bound follows from strong convexity and gradient Lipschitzness of the joint potential. Parameter and latent dimensions need not agree. Normalization, moments and concentration of the Gibbs measure are proved under these assumptions. The separate entropy result assumes LSI for the joint particle target and finite initial joint relative entropy.',
        archive='IPLA/exposition/proof.html',archive_label='Extended statement correspondence and assumption audit',
        extra=[('IPLA/LSI/exposition/index.html','Particle entropy under a lifted-target LSI · full proof'),('docs/modules/IPLA/Standalone.html','Standalone Mathlib-only theorem · full dependency proofs')],
        results=[dict(title='Parameter error for IPLA',file='IPLA/Theorem.lean',name='theorem1',body=IPLA_STATEMENT)],
        diagram=[node('geometry',0,0,'IPLA/Geometry.lean','The scaled particle coordinates',r'Dimension \(d_\theta+Nd_x\); curvature \(Nm\)'),
                 node('gibbs',0,1,'IPLA/Foundations.lean','Normalization of the particle target','Positive normalizing constant and finite moments'),
                 node('marginal',0,2,'IPLA/MarginalConcentration.lean','The parameter marginal density',r'Density proportional to \(\ell_y(\theta)^N\)'),
                 node('algorithm',1,0,'IPLA/ULAAdapter.lean','IPLA as a ULA recursion',r'The same distribution; step \(\gamma/N\)',('geometry',)),
                 node('ula',1,1,'UnadjustedLangevin/GaussianULA.lean','The ULA convergence estimate',r'Gaussian innovations and \(L^2\) initialization',('geometry','gibbs')),
                 node('convex',1,2,'IPLA/StrongLogConcavity.lean','Strong convexity of the negative log marginal','Prékopa–Leindler and tensorization',('marginal',)),
                 node('scaling',2,0,'IPLA/Scaling.lean','Substitution of the scaled constants',r'Exact \(N\), step, and dimension factors',('algorithm',)),
                 node('projection',2,1,'UnadjustedLangevin/Projection.lean','Projection to the parameter coordinates',r'RMS \(\le W_2+r\) for \(\|P_\theta\|\le1\)',('ula',)),
                 node('concentration',2,2,'IPLA/Concentration.lean','The equilibrium parameter second moment',r'RMS \(\le\sqrt{2d_\theta/(Nm)}\)',('convex','marginal')),
                 node('theorem',3,1,'IPLA/Theorem.lean','The IPLA parameter bound','Possibly unequal parameter and latent dimensions',('scaling','projection','concentration'),True)]),
    'ProximalLangevin':dict(label='Proximal',title='Proximal particle Langevin',subtitle='Proximal maps, parameter error estimates and mean-field limits.',
        status='The results bound MYIPLA, PIPGLA and MYPGD parameter errors relative to the maximizer of the original marginal. Their constants differ from arXiv:2406.14292v3. The proofs cover part of that paper; the reference table identifies the remaining claims and the differences in the estimates.',
        archive='ProximalLangevin/exposition/proof.html',archive_label='Detailed proofs and version-specific paper audit',
        extra=[('docs/modules/ProximalLangevin/MeanFieldParticleLaw.html','Independent mean-field particles and their marginal distributions'),('docs/modules/ProximalLangevin/PIPULA.html','PIPULA for the full potential and its assumptions')],
        results=[dict(title='MYIPLA: parameter error',file='ProximalLangevin/Theorem.lean',name='moreau_myipla_parameter_rms_original',body=MYIPLA),
                 dict(title='PIPGLA: parameter error',file='ProximalLangevin/SplittingTheorem.lean',name='pipgla_parameter_rms_original',body=PIPGLA),
                 dict(title='MYPGD: parameter error without parameter noise',file='ProximalLangevin/MYPGDTheorem.lean',name='moreau_mypgd_parameter_rms_original',body=MYPGD)],
        diagram=[node('prox',0,0,'ProximalLangevin/Proximal.lean','Existence of the proximal map','Existence, optimality, nonexpansiveness'),
                 node('moreau',0,1,'ProximalLangevin/Moreau.lean','Differentiability of the Moreau envelope','Gradient, Lipschitz constant and approximation error',('prox',)),
                 node('bias',0,2,'ProximalLangevin/Perturbation.lean','Difference of the marginal maximizers','Pointwise potential bounds and strong convexity'),
                 node('myipla',1,0,'ProximalLangevin/MYIPLA.lean','IPLA for the smoothed potential',r'Reuse ULA with \(L_\eta=L_1+\eta^{-1}\)',('prox','moreau')),
                 node('splitting',1,1,'ProximalLangevin/SplittingOneStep.lean','A one-step coupling estimate for splitting','Expansion of the squared coupling error',('prox','moreau')),
                 node('meanfield',1,2,'ProximalLangevin/MeanFieldProcess.lean','Existence of the mean-field solution',r'\(L^2\) integral equation by Picard iteration',('moreau',)),
                 node('mytheorem',2,0,'ProximalLangevin/Theorem.lean','MYIPLA error relative to the original maximizer','Smoothing + concentration + ULA',('myipla','bias'),True),
                 node('endpoint',2,1,'ProximalLangevin/SplittingEndpoint.lean','The recurrence for the splitting distributions','Coupling comparison and Wasserstein infimum',('splitting',)),
                 node('particles',2,2,'ProximalLangevin/MeanFieldParticles.lean','Comparison with independent mean-field particles',r'Uniform \(L^2\) error \(O(N^{-1/2})\)',('meanfield',)),
                 node('mypgd',3,0,'ProximalLangevin/MYPGDTheorem.lean','MYPGD error relative to the original maximizer','Bound for omitted parameter noise',('mytheorem',),True),
                 node('pitheorem',3,1,'ProximalLangevin/SplittingTheorem.lean','PIPGLA error relative to the original maximizer','Arbitrary positive proximal parameter',('endpoint','bias'),True),
                 node('particlelaw',3,2,'ProximalLangevin/MeanFieldParticleLaw.lean','Convergence of a tagged particle distribution','Wasserstein estimate at each fixed time',('particles',),True)])
}



SEPARATE_TITLES = {'PBGSO': 'Particle-based Generalised Stochastic Optimisation',
                   'LatentDiffusion': 'Training Latent Diffusion Models with Interacting Particle Algorithms'}


def development_title(key):
    """Titles of the CONFIG overviews and of the two separately generated ones."""
    return CONFIG[key]['title'] if key in CONFIG else SEPARATE_TITLES[key]


def home_document(lib, config, notes, sources, parsed, math, catalog=None):
    from math_notation import render_prose_math
    page = lib + '/exposition/index.html'
    if catalog:
        typeset = math
        math = lambda value: catalog.resolve_html(typeset(value), page)
    parent_library=lib.split('/')[0]
    entropy='/LSI' in lib
    footref='<sup><a id="entropy-note-ref" href="#entropy-note" aria-label="Entropy analogue">1</a></sup>' if lib=='IPLA' else ''
    body=(f'<div id="legacy-destination" hidden data-url="{relative(config["archive"],page)}"></div>'
          f'<header class="hero"><div class="eyebrow">{config["label"]}</div>'
          f'<h1>{config["title"]}</h1><p class="subtitle">{config["subtitle"]}{footref}</p>'
          + reference_notice(lib)
          + (f'<p class="status">{config["top_notice"]}</p>' if config.get('top_notice') else '')
          + f'<p class="status">{config["status"]}</p></header>')
    proof_library=lib
    body+=('<p class="proof-download"><a href="'+relative('docs/pdf/'+proof_library+'/FullProof.pdf',page)+'" download>Download full proof (PDF)</a> · '
           '<a href="'+relative('docs/latex/'+proof_library+'/FullProof.tex',page)+'" download>Download full proof (LaTeX)</a></p>')
    body+=('<nav class="jump-nav" aria-label="On this page"><a href="#paper-correspondence">Paper correspondence</a>'
           '<a href="#paper-assumptions">Paper assumptions</a><a href="#extra-assumptions">Extra assumptions</a>'
           '<a href="#main-results">Paper results</a>')
    if config.get('proof_difference'):
        body+='<a href="#proof-difference">Proof differences</a>'
    body+='<a href="#verification">Check the proofs</a><a href="#proof-map">Proof roadmap</a>'
    if config.get('proof'):body+='<a href="#mathematical-proof">Mathematical argument</a>'
    body+='<a href="#additional-results">Additional results</a><a href="#modules">Supporting proofs</a></nav>'+toolbar()
    from paper_sources import (assumption_sections, correspondence_section, result_metadata,
                               result_notice, proof_status)
    body += correspondence_section(lib, config['results'], math) + assumption_sections(lib, math)
    numbered = list(enumerate(config['results'], 1))
    paper_results = [(i, result) for i, result in numbered
                     if result_metadata(lib, result['name'])['status'] in {'proved', 'corrected', 'conditional'}]
    additional_results = [(i, result) for i, result in numbered
                          if result_metadata(lib, result['name'])['status'] in {'new', 'auxiliary'}]
    for section_id, heading, entries in [('main-results', 'Paper results', paper_results),
                                         ('additional-results', 'Additional results — not statements of the paper', additional_results)]:
        body += '<section class="section" id="' + section_id + '"><h2>' + heading + '</h2>'
        if section_id == 'additional-results':
            body += '<details' + (' open' if not paper_results else '') + '><summary>Show additional results and supporting statements</summary>'
        if not entries:
            body += ('<p>No numbered paper result is claimed by this extension.</p>'
                     if section_id == 'main-results' else '<p>No additional results are presented on this page.</p>')
        for i,result in entries:
            correspondence = result_metadata(lib, result['name'])
            label = correspondence.get('label') if correspondence['status'] in {'proved', 'corrected', 'conditional'} else proof_status(correspondence) + ' — ' + result['title']
            source_attribute = (' data-source-label="' + E(label) + '"' if correspondence['status'] in {'proved', 'corrected', 'conditional'}
                                else ' data-result-kind="' + correspondence['status'] + '"')
            target=module_page(result['file'])
            namespace=result.get('namespace',config.get('namespace','ULA.Hilbert' if lib=='UnadjustedLangevin' else lib))
            context='import '+result['file'].removesuffix('.lean').replace('/','.')+'\nopen MeasureTheory Set\nopen scoped NNReal ENNReal\nnamespace '+namespace
            if lib=='UnadjustedLangevin':context+='\nvariable {ι : Type*} [Fintype ι]'
            if lib=='UnadjustedLangevin/LSI':
                context+='\nvariable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]\n  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]'
            if lib=='KineticLangevin':
                context+='\nvariable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]\n  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]\nlocal instance (T : ℝ) : MeasurableSpace (VelocityForcing (E := E) T) := borel _\nlocal instance (T : ℝ) : BorelSpace (VelocityForcing (E := E) T) := ⟨rfl⟩'
            if result.get('context'):context+='\n'+result['context']
            body+=(f'<article id="result-{i}"{source_attribute}><h3>{E(label)}</h3>'
                   + f'<p class="result-description">{E(result["title"])}</p>'
                   + result_notice(lib, result, math) + '<div class="pair">'
                   '<div class="math-pane"><div class="pane-label">Mathematical statement</div>'+math(result['body'])
                   +'</div><div class="lean-pane"><div class="pane-label">Lean statement</div>'
                   +('<p class="correspondence-note">'+config['formal_note']+'</p>' if config.get('formal_note') else '')
                   +'<details class="statement-context"><summary>Imports and notation</summary>'+commands(context,f'statement-context-{i}','Copy Lean')+'</details>'
                   +declaration_header(result['file'],result['name'],sources,parsed,page)
                   +f'<p class="small"><a href="{relative(target,page)}#{anchor(result["name"])}">Full Lean proof and mathematical commentary →</a></p></div></div></article>')
        if section_id == 'additional-results':
            body += '</details>'
        body += '</section>'
        if section_id == 'main-results' and config.get('proof_difference'):
            body += ('<section class="section" id="proof-difference">'
                     '<h2>Same results, modified proof</h2>'
                     + math(config['proof_difference']) + '</section>')
    body+=verification_section(lib,page)
    body+='<section class="section" id="proof-map"><h2>Proof roadmap</h2><p class="section-intro">Each box opens a supporting proof, with its mathematical argument and Lean implementation. Follow the arrows to see how the conclusions are assembled.</p>'
    body+=proof_diagram(config['diagram'],page,math,config['title']+' proof roadmap')+'</section>'
    if config.get('proof'):
        body+='<section class="section" id="mathematical-proof"><h2>The mathematical argument</h2><p class="section-intro">The argument below gives the estimates in order, including their constants and analytic justification. The adjacent panels identify the corresponding checked Lean statements and explain their role in the proof.</p>'
        for i,part in enumerate(config['proof'],1):
            body+=(f'<article class="proof-step" id="argument-{part["id"]}"><h3><span class="step-number">{i:02}</span>{E(part["title"])} <a class="permalink" href="#argument-{part["id"]}">§</a></h3><div class="pair"><div class="math-pane">'+math(part['body'])+'</div><div class="lean-pane">')
            if part.get('lean'):
                body+='<div class="lean-logic"><div class="pane-label">How the Lean proof follows this argument</div>'+math(part['lean'])+'</div>'
            elif part.get('note'):body+='<p class="correspondence-note">'+part['note']+'</p>'
            for j,reference in enumerate(part.get('references',[]),1):
                path,name=reference['file'],reference['name'];decl=parsed[path][name]
                body+=code(path,decl['start'],decl['end'],sources,page,'proof-fragment',name,f'argument-{i}-{j}')
                body+=f'<p class="small"><a href="{relative(module_page(path),page)}#{anchor(name)}">Detailed explanation in {E(Path(path).name)} →</a></p>'
            body+='</div></div></article>'
        body+='</section>'
    body+='<section class="section" id="modules"><h2>Supporting proofs</h2><p class="section-intro">Browse the definitions and lemmas used in this development. Each page pairs the mathematical statement and proof with the corresponding Lean declarations. The report gives the supporting proofs for this development and cites earlier reports by precise section number.</p>'
    body+='<div class="toolbar"><div><label for="module-search">Find a proof </label><input class="search" id="module-search" type="search" placeholder="Name, topic, or source file" aria-controls="module-directory"></div><span class="small" id="module-count" aria-live="polite"></span></div><div id="module-directory">'
    groups={}
    for path,note in sorted(notes.items()):
        if not (path.startswith(lib+'/') or path==lib+'.lean'):continue
        if not entropy and '/LSI/' in path:continue
        group='Analysis foundations' if '/Analysis/' in path else 'Proof library'
        groups.setdefault(group,[]).append((path,note))
    for group,entries in groups.items():
        body+=f'<div class="module-group"><h3 class="category">{group}</h3><div class="module-grid">'
        for path,note in entries:
            body+=(f'<article class="module-card"><a href="{relative(module_page(path),page)}">{E(note["title"])}</a>'
                   f'<code>{E(path)}</code></article>')
        body+='</div></div>'
    body+='</div></section>'
    if lib=='IPLA':
        body+='<aside class="footnote" id="entropy-note"><p><sup>1</sup> The entropy analogue is developed separately in <a href="'+relative('IPLA/LSI/exposition/index.html',page)+'">Interacting Particle Langevin under LSI</a>. It uses an LSI for the actual lifted target, tracks per-particle normalization, and proves the parameter-marginal consequence. <a href="#entropy-note-ref" aria-label="Back to reference">↩</a></p></aside>'
    body+='<section class="section" id="further-reading"><h2>References and further reading</h2><div class="dependencies">'
    body+=f'<a href="{relative(config["archive"],page)}">{config["archive_label"]}</a>'
    body+=''.join(f'<a href="{relative(p,page)}">{E(label)}</a>' for p,label in config['extra'])+'</div></section>'
    if catalog:
        from report_citations import citation_panel
        plan = catalog.plans[lib]
        body += citation_panel(lib, plan['title'], plan['revision'], page)
    return shell(page,config['title'],render_prose_math(body,math))


def verification_section(lib, page, extra='', note=''):
    """How to check the proofs; the same section appears on every overview."""
    parent_library = lib.split('/')[0]
    command = ('git clone https://github.com/odakyildiz/LangevinLean.git\ncd LangevinLean\n'
               f'lake exe cache get\nlake build {parent_library}\nlake env lean {lib}/Check.lean\n'
               + extra + 'bash scripts/check-local.sh')
    return ('<section class="section" id="verification"><h2>Check the proofs</h2><div class="workflow"><div>'
            + commands(command, 'verification-commands') + '</div><div><h3>What the commands check</h3>'
            '<p>Install Git and elan, Lean’s toolchain manager, before cloning. The repository pins the Lean and '
            'Mathlib versions; the first cache download requires an internet connection.</p>'
            f'<p><code>lake build {parent_library}</code> checks every proof in the library: when it succeeds, each '
            'theorem on this page is proved from the hypotheses displayed in its Lean statement. '
            f'<code>lake env lean {lib}/Check.lean</code> prints the axioms on which the main theorems depend; only '
            '<code>propext</code>, <code>Classical.choice</code> and <code>Quot.sound</code> appear. '
            + note + 'The local check script also verifies that every displayed Lean excerpt matches the source and '
            'that these pages and the PDF regenerate exactly; regenerating them requires Python 3 and Node.js.</p>'
            f'<p><a href="{relative("README.md",page)}">Complete installation and update instructions</a> · '
            f'<a href="{relative("docs/README.md",page)}">Regenerate the exposition</a></p></div></div></section>')


def project_document(notes, catalog=None):
    page='index.html'
    body=('<header class="hero project-hero">'
          '<h1>Langevin algorithms in Lean</h1>'
          '<p class="subtitle">Formalization of Langevin-based stochastic algorithms and their convergence bounds for sampling and particle methods, with mathematical proofs alongside Lean. '
          'These pages are prepared by <a href="https://odakyildiz.com/">Omer Deniz Akyildiz</a> with AI assistance as part of an ongoing effort to formalize Langevin algorithms comprehensively. '
          'This is draft work, and the pages may contain mistakes.</p></header>'
          '<section class="cards" id="developments" aria-label="Formalized developments">')
    # One record per development; every entry is rendered with the same fields.
    cards=[('UnadjustedLangevin','Wasserstein distance',
            'Wasserstein error bounds for Gaussian ULA in both stable step-size regimes.',
            'Published bounds; Gibbs stationarity proved.',
            'Dalalyan and Karagulyan (2019)'),
           ('UnadjustedLangevin/LSI','Relative entropy',
            'Relative-entropy convergence of Gaussian ULA from a log-Sobolev inequality and finite initial entropy.',
            'Includes finite relative entropy at every iterate.',
            'Vempala and Wibisono (2019)'),
           ('IPLA','Interacting particles',
            'Finite-time parameter error from lifted ULA convergence and marginal concentration.',
            'The extension to unequal parameter and latent dimensions and the entropy analogue are unpublished.',
            'Glyn-Davies et al. (2025)'),
           ('ProximalLangevin','Nonsmooth models',
            'Corrected MYIPLA, PIPGLA and MYPGD bounds, with proximal-map calculus and mean-field limits.',
            'Partial paper coverage; corrected bounds and proofs are unpublished.',
            'Cordero Encinar et al. (2025)'),
           ('KineticLangevin','Kinetic sampling',
            'Wasserstein convergence for the kinetic diffusion and KLMC/KLMC2 samplers, with Gibbs stationarity and accuracy guarantees.',
            'Includes unpublished corrections to the source proofs.',
            'Dalalyan and Riou-Durand (2020)'),
           ('KIPLMC','Kinetic interacting particles',
            'Parameter error for the kinetic particle diffusion, KIPLMC1 and KIPLMC2, with sharp marginal concentration.',
            'Includes Gaussian sampler bounds and explicit accuracy guarantees.',
            'Valsecchi Oliva and Akyildiz (2026)'),
           ('PBGSO','General stochastic optimisation',
            'General optimiser and sampler models, contraction and particle bounds, and time-uniform discretisation bounds for two new methods.',
            'Four main theorems under explicit assumptions; the two discretisation bounds are new and unpublished.',
            'Zhang and Akyildiz (2026)'),
           ('LatentDiffusion','Latent diffusion and inference',
            'Variational identities, marginal optimizers, interacting-particle error bounds and explicit accuracy choices.',
            '19 corrected statements proved under extra assumptions; the literal printed statements are not certified as stated.',
            'Wang, Kuntz and Akyildiz (2026)'),
           ('AverageLMC','Average-smoothness sampling',
            'LMC, decreasing-step, Laplacian LMC and control-variate SGLD bounds with exact smoothness constants.',
            'Main sampling theorems with the source hypotheses and constants.',
            'Dalalyan and Karagulyan (2026)'),
           ('WassersteinMixing','Wasserstein mixing time',
            'Constructed Langevin dynamics, Poisson correctors and exact ULA bias and accuracy bounds.',
            'The source results are proved under the original Hessian assumptions.',
            'Pedrotti and Whalley (2026)')]
    extra_assumptions = {
        'IPLA': 'Entropy extension: lifted-target LSI and finite initial joint entropy; the specialization assumes linear scaling of the LSI constant.',
        'KineticLangevin': 'A dimension restriction for the simplified KLMC2 bound, and a curvature condition for the printed tail-free iteration bound.',
        'PBGSO': 'Extra A1–Extra A3 for the stated theorem branches; Extra A4–Extra A5 for the additional numerical bounds.',
        'LatentDiffusion': 'Extra A1–Extra A7, as specified for each corrected paper result.',
    }
    for number,(key,label,description,scope,source_label) in enumerate(cards,1):
        paper=PAPERS[DEVELOPMENTS[key]['papers'][0]]
        extra_notice = ('<p class="card-extra-assumptions added-assumption" data-assumption-kind="added"><strong>Extra assumptions:</strong> '
                        + extra_assumptions[key] + '</p>') if key in extra_assumptions else ''
        body+=(f'<article class="landing-card"><span class="entry-index" aria-hidden="true">{number:02}</span>'
               f'<div class="entry-main"><div class="eyebrow">{E(label)}</div>'
               f'<h2><a href="{key}/exposition/index.html">{E(development_title(key))}</a></h2>'
               f'<p>{E(description)}</p></div><div class="entry-meta">'
               f'<p class="entry-source">Source: <a href="{E(paper["url"])}">{E(source_label)}</a>.</p>'
               f'<p class="card-scope">{E(scope)}</p>'
               + extra_notice +
               f'<p><a href="docs/pdf/{key}/FullProof.pdf">Full proof (PDF)</a></p>'
               + ('<p><a href="WassersteinMixing/exposition/ipla.html">Application to IPLA</a></p>'
                  if key == 'WassersteinMixing' else '') +
               '</div></article>')
    body+=('</section><section class="section reading-guide" aria-label="Reading and verification">'
           '<div class="reading-note"><h2>Read the proofs</h2><p>Each development has one PDF with its theorem statements, the mathematical argument and the supporting proofs. After every step, the PDF gives the exact Lean statement and explains how the Lean proof follows the mathematics. On the web pages, each step of the proof roadmap opens the same mathematics beside the complete Lean code.</p></div>'
           '<div class="verification-summary"><h2>Verify locally</h2><p>After installation and cloning:</p>')
    body+=commands('lake exe cache get\nbash scripts/check-local.sh','project-commands')
    body+='<p class="small"><a href="README.md">Installation and verification instructions</a></p></div></section>'
    if catalog:
        from report_citations import citation_panel
        body += citation_panel(None, None, None, page)
    return shell(page,'Langevin algorithms in Lean',body)


from classical_proofs import ULA_PROOF, IPLA_PROOF, PROXIMAL_PROOF
CONFIG['UnadjustedLangevin']['proof'] = ULA_PROOF
CONFIG['IPLA']['proof'] = IPLA_PROOF
CONFIG['ProximalLangevin']['proof'] = PROXIMAL_PROOF

from entropy_content import ENTROPY_CONFIG
CONFIG.update(ENTROPY_CONFIG)

from kinetic_overviews import KINETIC_CONFIG
CONFIG.update(KINETIC_CONFIG)

from average_content import AVERAGE_CONFIG
CONFIG.update(AVERAGE_CONFIG)

from wasserstein_mixing_content import WASSERSTEIN_CONFIG
CONFIG.update(WASSERSTEIN_CONFIG)
