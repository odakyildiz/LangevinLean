"""Authored standalone theorem statements and logical proof roadmaps."""
from pathlib import Path
from build_site import (E, LIBRARIES, relative, module_page, anchor, shell,
                        toolbar, commands, proof_diagram, declaration_header)


def node(identifier, row, col, file, title, detail, parents=(), final=False):
    return dict(id=identifier,row=row,col=col,file=file,title=title,detail=detail,parents=parents,final=final)


ULA_SETUP = r'''<p>Let \(d\ge1\), and let \(U:\mathbb R^d\to\mathbb R\) be differentiable and \(m\)-strongly convex, with \(m>0\) and \(L\)-Lipschitz gradient. These assumptions imply \(m\le L\). Define</p>
\[\pi(dx)=Z^{-1}e^{-U(x)}dx,\qquad Z=\int e^{-U(x)}dx\in(0,\infty).\]
<p>Let \(\mu_0\) be a probability law with \(W_2(\mu_0,\pi)&lt;\infty\). A finite second moment suffices. For \(h>0\), take independent standard Gaussian vectors \(\xi_k\), independent of initialization, and set</p>
\[X_{k+1}=X_k-h\nabla U(X_k)+\sqrt{2h}\,\xi_k,\qquad\mu_k=\operatorname{Law}(X_k).\]
<p>In the Lean statement, \(\mathbb R^d\) is <code>EuclideanSpace ℝ ι</code> with a finite nonempty index type, and \(d=|\iota|\). <code>ulaLawStep</code> is the exact Gaussian transition on probability laws; its identification with this recursion is proved.</p>'''

IPLA_STATEMENT = r'''<p>Fix an observation \(y\) and a differentiable joint potential \(U_y:\mathbb R^{d_\theta}\times\mathbb R^{d_x}\to\mathbb R\). Assume \(U_y\) is \(m\)-strongly convex with \(m>0\) and has \(L\)-Lipschitz gradient. Let \(N\ge1\); the independent dimensions \(d_\theta,d_x\ge0\) may be zero. Define</p>
\[\ell_y(\theta)=\int e^{-U_y(\theta,x)}dx,\quad
\theta_\star\in\operatorname*{argmax}_\theta\ell_y(\theta).\]
<p>In scaled coordinates \(z=(\theta,x^1/\sqrt N,\ldots,x^N/\sqrt N)\), set</p>
\[V_N(z)=\sum_{i=1}^NU_y(\theta,\sqrt N z_i),\qquad
\Pi_N(dz)\propto e^{-V_N(z)}dz.\]
<p>Use a square-integrable initial state and standard Gaussian innovations independent in every coordinate and time and independent of initialization. For \(0&lt;\gamma\le2/(m+L)\), the actual IPLA updates are</p>
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
<p>The target normalization, finite transport moments, stationary reference, marginal strong convexity, and equilibrium radius are derived. The selected center is a maximizer of the integrated joint density; including a prior in \(U_y\) gives the prior-inclusive interpretation.</p>'''

PROX_SETUP = r'''<p>Write \(U=g_1+g_2\) on \(\mathbb R^{d_\theta+d_x}\). Assume \(g_1\) is differentiable, \(m\)-strongly convex for \(m>0\), and has \(L_1\)-Lipschitz gradient. Assume \(g_2\) is finite-valued, convex, bounded below, and \(K\)-Lipschitz. Define the actual proximal minimizer and Moreau envelope by</p>
\[P_\eta(x)=\operatorname*{argmin}_p\left\{g_2(p)+\frac{\|p-x\|^2}{2\eta}\right\},\quad
g_2^\eta(x)=g_2(P_\eta(x))+\frac{\|P_\eta(x)-x\|^2}{2\eta},\]
\[V_\eta=g_1+g_2^\eta,\qquad L_\eta=L_1+\eta^{-1},\qquad\eta>0.\]
<p>Take \(N\ge1\), \(d_\theta,d_x\ge0\), an L² initial scaled particle state, and independent standard Gaussian innovations at all coordinates and times, independent of initialization. Write \(\rho_0\) for the initial scaled law, \(\Pi_{N,\eta}\) for the Gibbs target of the lifted \(V_\eta\), and choose marginal maximizers \(\theta_U\) for \(g_1+g_2\) and \(\theta_\eta\) for \(V_\eta\). Their existence is established in the supporting modules.</p>'''

PROX_SETUP += r'''<p>Precisely, the scaled state, lifted potential, and normalized target are</p>
\[z=(\theta,x^1/\sqrt N,\ldots,x^N/\sqrt N),\qquad
W_{N,\eta}(z)=\sum_{i=1}^N V_\eta(\theta,\sqrt N z_i),\]
\[\Pi_{N,\eta}(dz)=Z_{N,\eta}^{-1}e^{-W_{N,\eta}(z)}dz.\]
<p>A marginal maximizer of a pair potential \(V\) maximizes \(\theta\mapsto\int e^{-V(\theta,x)}dx\).</p>'''

MYIPLA = PROX_SETUP + r'''<p>MYIPLA is the Gaussian IPLA recursion for \(V_\eta\), using the proved identity \(\nabla g_2^\eta=(I-P_\eta)/\eta\):</p>
\[z_{n+1}=z_n-\frac\gamma N\nabla W_{N,\eta}(z_n)+\sqrt{2\gamma/N}\,\xi_n.\]
<p>For \(0&lt;\gamma\le2/(m+L_\eta)\) and every \(n\in\mathbb N\), its actual parameter iterate satisfies</p>
\[\begin{aligned}
\bigl(\mathbb E\|\theta_n-\theta_U\|^2\bigr)^{1/2}
\le{}&\sqrt{\frac{\eta K^2}{m}}+\sqrt{\frac{d_\theta}{Nm}}
+(1-m\gamma)^nW_2(\rho_0,\Pi_{N,\eta})\\
&+\frac{33}{20}\frac{L_\eta}{m}\sqrt{d_x+\frac{d_\theta}{N}}\sqrt\gamma.
\end{aligned}\]
<p>The terms are the finite smoothing displacement, sharp equilibrium radius, decaying initial transport error, and discretization bias. The smoothing rate is \(O(\sqrt\eta)\), and the discretization coefficient depends on \(\eta\). This is the proved corrected theorem; the paper’s Taylor-based linear smoothing expression is not asserted.</p>'''

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
<p>The first term is a proved proximal-parameter comparison. The remaining transport estimate comes from a constructed synchronous coupling and actual-law recurrence. The constants differ from the paper’s printed bound.</p>'''

MYPGD = PROX_SETUP + r'''<p>MYPGD uses the MYIPLA drift and erases its parameter Gaussian noise, retaining latent Gaussian noise:</p>
\[z_{n+1}=z_n-\frac\gamma N\nabla W_{N,\eta}(z_n)+\sqrt{2\gamma/N}\,M\xi_n,\]
<p>where \(M\) is the orthogonal projection onto latent coordinates. Assume \(m\le L_\eta\) explicitly and \(0&lt;\gamma\le2/(m+L_\eta)\). For every \(n\in\mathbb N\), the actual finite-particle recursion satisfies</p>
\[\begin{aligned}
\bigl(\mathbb E\|\theta_n^{\rm PGD}-\theta_U\|^2\bigr)^{1/2}
\le{}&\sqrt{\frac{2d_\theta}{Nm}}+\sqrt{\frac{\eta K^2}{m}}+\sqrt{\frac{d_\theta}{Nm}}\\
&+(1-m\gamma)^nW_2(\rho_0,\Pi_{N,\eta})\\
&+\frac{33}{20}\frac{L_\eta}{m}\sqrt{d_x+\frac{d_\theta}{N}}\sqrt\gamma.
\end{aligned}\]
<p>The additional \(\sqrt{2d_\theta/(Nm)}\) is a proved conservative cost of removing parameter noise. This finite-particle replacement does not assert the paper’s stronger mean-field metric or constants.</p>'''

CONFIG = {
    'UnadjustedLangevin':dict(label='ULA',title='Unadjusted Langevin',subtitle='From strongly convex geometry to the law of the Gaussian algorithm.',
        status='The strongly convex convergence theorems construct their Brownian reference and prove Gibbs stationarity. The separate LSI extension retains explicit analytic interpolation hypotheses.',
        archive='UnadjustedLangevin/exposition/dist/index.html',archive_label='Extended teaching document and Lean notes',
        extra=[('UnadjustedLangevin/LSI/exposition/index.html','Entropy under LSI · conditional proof and reference audit')],
        results=[dict(title='Small-step Gaussian ULA',file='UnadjustedLangevin/CanonicalULA.lean',name='dalalyan',body=ULA_SETUP+r'''<p>If \(0&lt;h\le2/(m+L)\), then for every \(k\in\mathbb N\),</p>\[W_2(\mu_k,\pi)\le(1-mh)^kW_2(\mu_0,\pi)+\frac{33}{20}\frac Lm\sqrt{hd}.\]<p>The rational coefficient \(33/20\) is exactly \(1.65\). The initial term uses the true Wasserstein infimum over couplings.</p>'''),
                 dict(title='The other stable step-size regime',file='UnadjustedLangevin/CanonicalULA.lean',name='dalalyan_large_step',body=ULA_SETUP+r'''<p>If \(2/(m+L)\le h\) and \(Lh&lt;2\), then for every \(k\in\mathbb N\),</p>\[W_2(\mu_k,\pi)\le(Lh-1)^kW_2(\mu_0,\pi)+\frac{33}{20}\frac{Lh}{2-Lh}\sqrt{hd}.\]<p>The strict upper endpoint ensures the denominator is positive. Both regimes follow from the same scalar recurrence, using their respective contraction factors.</p>''')],
        diagram=[node('geometry',0,0,'UnadjustedLangevin/SharpContraction.lean','Contract the gradient step','q = 1 − mh or Lh − 1'),
                 node('gibbs',0,1,'UnadjustedLangevin/Gibbs.lean','Construct the Gibbs target','Positive normalization and L² moments'),
                 node('brownian',0,2,'UnadjustedLangevin/CanonicalBrownian.lean','Construct Brownian noise','Independent Gaussian coordinates'),
                 node('local',1,0,'UnadjustedLangevin/LocalError.lean','Bound the local Euler defect','Integrate the Lipschitz drift error',('geometry',)),
                 node('stationary',1,1,'UnadjustedLangevin/GibbsStationarity.lean','Prove Gibbs stationarity','Metropolis invariance and Euler limit',('gibbs','brownian')),
                 node('integral',1,2,'UnadjustedLangevin/LangevinIntegral.lean','Solve the integral equation','L² Picard construction',('brownian',)),
                 node('recurrence',2,0,'UnadjustedLangevin/Recurrence.lean','Solve the scalar recurrence','a[k+1] ≤ q a[k] + b',('local',)),
                 node('coupling',2,1,'UnadjustedLangevin/HilbertDalalyan.lean','Compare synchronous paths','Noise cancellation and initial infimum',('local','stationary','integral')),
                 node('law',2,2,'UnadjustedLangevin/ChainLaw.lean','Identify the Gaussian laws','Independent transitions give the chain',('brownian',)),
                 node('final',3,1,'UnadjustedLangevin/CanonicalULA.lean','Canonical ULA theorem','Both stable step-size regimes',('recurrence','coupling','law'),True)]),
    'IPLA':dict(label='IPLA',title='Interacting particle Langevin',subtitle='Lift the particle system, reuse ULA, and project to the parameter.',
        status='The final strongly convex theorem derives its stationary reference, target moments, and equilibrium concentration from the joint-potential assumptions. Parameter and latent dimensions are independent. The entropy extension is conditional.',
        archive='IPLA/exposition/proof.html',archive_label='Extended statement correspondence and assumption audit',
        extra=[('IPLA/LSI/exposition/index.html','Particle entropy under a lifted-target LSI · conditional proof'),('docs/modules/IPLA/Standalone.html','Standalone Mathlib-only theorem · full dependency proofs')],
        results=[dict(title='Parameter error for the actual IPLA recursion',file='IPLA/Theorem.lean',name='theorem1',body=IPLA_STATEMENT)],
        diagram=[node('geometry',0,0,'IPLA/Geometry.lean','Lift and rescale particles','Dimension dθ + N dx; curvature Nm'),
                 node('gibbs',0,1,'IPLA/Foundations.lean','Normalize the lifted target','Derived probability and finite moments'),
                 node('marginal',0,2,'IPLA/MarginalConcentration.lean','Compute the parameter marginal','Density proportional to ℓ(θ)ᴺ'),
                 node('algorithm',1,0,'IPLA/ULAAdapter.lean','Identify IPLA with ULA','Exact algorithm law; step γ/N',('geometry',)),
                 node('ula',1,1,'UnadjustedLangevin/GaussianULA.lean','Apply the shared ULA theorem','Stationarity and Gaussian law proved',('geometry','gibbs')),
                 node('convex',1,2,'IPLA/StrongLogConcavity.lean','Prove marginal strong convexity','Prékopa–Leindler and tensorization',('marginal',)),
                 node('scaling',2,0,'IPLA/Scaling.lean','Simplify particle constants','Exact N, step, and dimension factors',('algorithm',)),
                 node('projection',2,1,'IPLA/Transport.lean','Project the transport estimate','Parameter projection has norm ≤ 1',('ula',)),
                 node('concentration',2,2,'IPLA/Concentration.lean','Derive the equilibrium radius','Parameter RMS ≤ √(2dθ/(Nm))',('convex','marginal')),
                 node('theorem',3,1,'IPLA/Theorem.lean','Final IPLA parameter bound','General independent dimensions',('scaling','projection','concentration'),True)]),
    'ProximalLangevin':dict(label='Proximal',title='Proximal particle Langevin',subtitle='Actual proximal minimizers, finite-time algorithm bounds, and mean-field limits.',
        status='Corrected MYIPLA, PIPGLA, and MYPGD original-center bounds are proved. This is a partial formalization of arXiv:2406.14292v3: exact published constants and several appendix claims remain outside the proved results. The reference audit records the differences.',
        archive='ProximalLangevin/exposition/proof.html',archive_label='Detailed proofs and version-specific paper audit',
        extra=[('docs/modules/ProximalLangevin/MeanFieldParticleLaw.html','Constructed iid mean-field limit and tagged laws'),('docs/modules/ProximalLangevin/PIPULA.html','Full-potential PIPULA reduction and its assumptions')],
        results=[dict(title='MYIPLA: a finite original-model guarantee',file='ProximalLangevin/Theorem.lean',name='moreau_myipla_parameter_rms_original',body=MYIPLA),
                 dict(title='PIPGLA: an actual-law splitting bound',file='ProximalLangevin/SplittingTheorem.lean',name='pipgla_parameter_rms_original',body=PIPGLA),
                 dict(title='MYPGD: finite-particle noise removal',file='ProximalLangevin/MYPGDTheorem.lean',name='moreau_mypgd_parameter_rms_original',body=MYPGD)],
        diagram=[node('prox',0,0,'ProximalLangevin/Proximal.lean','Construct actual proximal maps','Existence, optimality, nonexpansiveness'),
                 node('moreau',0,1,'ProximalLangevin/Moreau.lean','Prove Moreau calculus','Gradient, smoothness, and value gap',('prox',)),
                 node('bias',0,2,'ProximalLangevin/Perturbation.lean','Control the marginal center shift','Finite value sandwich, then convexity'),
                 node('myipla',1,0,'ProximalLangevin/MYIPLA.lean','Identify the smoothed IPLA law','Reuse ULA with Lη = L₁ + 1/η',('prox','moreau')),
                 node('splitting',1,1,'ProximalLangevin/SplittingOneStep.lean','Prove the splitting coupling step','Energy cancellation and Brownian terms',('prox','moreau')),
                 node('meanfield',1,2,'ProximalLangevin/MeanFieldProcess.lean','Construct mean-field dynamics','L² integral equation and uniqueness',('moreau',)),
                 node('mytheorem',2,0,'ProximalLangevin/Theorem.lean','MYIPLA original-center theorem','Smoothing + concentration + ULA',('myipla','bias'),True),
                 node('endpoint',2,1,'ProximalLangevin/SplittingEndpoint.lean','Derive the actual-law recurrence','Construct references, then take infima',('splitting',)),
                 node('particles',2,2,'ProximalLangevin/MeanFieldParticles.lean','Couple iid particles to the limit','Uniform timewise L² error O(N⁻¹ᐟ²)',('meanfield',)),
                 node('mypgd',3,0,'ProximalLangevin/MYPGDTheorem.lean','MYPGD original-center theorem','Proved Gaussian noise-removal cost',('mytheorem',),True),
                 node('pitheorem',3,1,'ProximalLangevin/SplittingTheorem.lean','PIPGLA original-center theorem','Arbitrary positive proximal parameter',('endpoint','bias'),True),
                 node('particlelaw',3,2,'ProximalLangevin/MeanFieldParticleLaw.lean','Actual tagged-law limit','Constructed one-time Wasserstein bound',('particles',),True)])
}


def home_document(lib, config, notes, sources, parsed, math):
    page = lib + '/exposition/index.html'
    body = (f'<div id="legacy-destination" hidden data-url="{relative(config["archive"],page)}"></div>'
            f'<header class="hero"><div class="eyebrow">Sampling algorithms · {config["label"]} proof library</div>'
            f'<h1>{config["title"]}</h1><p class="subtitle">{config["subtitle"]}</p>'
            f'<p class="status">{config["status"]}</p></header>'
            '<nav class="jump-nav" aria-label="Page sections"><a href="#main-results">Main results</a>'
            '<a href="#verification">Verification workflow</a><a href="#proof-map">Proof diagram</a>'
            '<a href="#modules">All module proofs</a><a href="#further-reading">Further reading</a></nav>')
    body += toolbar() + '<section class="section" id="main-results"><h2>Main results</h2>'
    for i,result in enumerate(config['results'],1):
        target = module_page(result['file'])
        namespace = 'ULA.Hilbert' if lib=='UnadjustedLangevin' else lib
        context = 'import ' + result['file'].removesuffix('.lean').replace('/','.') + '\nopen MeasureTheory Set\nopen scoped NNReal ENNReal\nnamespace ' + namespace
        if lib=='UnadjustedLangevin': context += '\nvariable {ι : Type*} [Fintype ι]'
        body += (f'<article id="result-{i}"><h3>{result["title"]}</h3><div class="pair">'
                 '<div class="math-pane"><div class="pane-label">Mathematical statement · all assumptions</div>'
                 + math(result['body']) + '</div><div class="lean-pane"><div class="pane-label">Exact Lean statement</div>'
                 + '<p class="small">Context for the names and ambient variables in this statement:</p><pre class="commands">' + E(context) + '</pre>'
                 + declaration_header(result['file'],result['name'],sources,parsed,page)
                 + f'<p class="small"><a href="{relative(target,page)}#{anchor(result["name"])}">Read the complete proof alongside its mathematics →</a></p>'
                 + '<p class="small">The statement is extracted from the current Lean source. The linked module page includes the full proof body and explains every local declaration.</p></div></div></article>')
    body += '</section><section class="section" id="verification"><h2>Verification workflow</h2><div class="workflow"><div>'
    command = f'lake exe cache get\nlake build {lib}\nlake env lean {lib}/Check.lean\npython3 docs/build_site.py\npython3 docs/verify_site.py'
    if lib=='IPLA': command += '\npython3 IPLA/verify.py'
    body += commands(command,'verification-commands')
    body += '</div><div><h3>Run from the repository root</h3><p>Install Git and elan first. The committed <code>lean-toolchain</code> and <code>lake-manifest.json</code> pin Lean and Mathlib. The initial cache download needs internet access.</p><p><code>lake build</code> checks the formal proofs. <code>Check.lean</code> prints axiom dependencies. The Python commands regenerate the pages and check exact source excerpts, declaration coverage, LaTeX exports, and local links. Regeneration also needs Node.js; KaTeX and fonts are bundled.</p>'
    body += f'<p><a href="{relative("README.md",page)}">Full clone and build instructions</a> · <a href="{relative(lib+"/exposition/README.md",page)}">Method guide</a></p></div></div></section>'
    body += '<section class="section" id="proof-map"><h2>Proof diagram</h2><p class="section-intro">Follow the arrows from the assumptions to the result. Every box opens an HTML page with a mathematical statement and proof beside the complete Lean declarations. The directory below includes all supporting subfiles.</p>'
    body += proof_diagram(config['diagram'],page,config['title']+' proof diagram') + '</section>'
    body += '<section class="section" id="modules"><h2>All module proofs</h2><p class="section-intro">Each source file has its own proof page and downloadable LaTeX exposition. Import-only and audit modules explain their role; the generated IPLA standalone bundle links to every included proof.</p>'
    body += '<div class="toolbar"><div><label for="module-search">Find a module </label><input class="search" id="module-search" type="search" placeholder="Name, path, or topic" aria-controls="module-directory"></div><span class="small" id="module-count" aria-live="polite"></span></div><div id="module-directory">'
    groups = {}
    for path,note in sorted(notes.items()):
        if path.startswith(lib+'/') or path==lib+'.lean':
            group = 'Entropy extension · LSI' if '/LSI/' in path else 'Analysis foundations' if '/Analysis/' in path else 'Main library'
            groups.setdefault(group,[]).append((path,note))
    for group, entries in groups.items():
        body += f'<div class="module-group"><h3 class="category">{group}</h3><div class="module-grid">'
        for path,note in entries:
            count = len(parsed.get(path,{}))
            body += (f'<article class="module-card"><a href="{relative(module_page(path),page)}">{E(note["title"])}</a>'
                     f'<code>{E(path)}</code><p class="small">{len(note["steps"])} proof steps · '
                     + (f'{count} declarations' if path!='IPLA/Standalone.lean' else 'Generated dependency bundle') + '</p></article>')
        body += '</div></div>'
    body += '</div></section><section class="section" id="further-reading"><h2>Further reading</h2><div class="dependencies">'
    body += f'<a href="{relative(config["archive"],page)}">{config["archive_label"]}</a>'
    body += ''.join(f'<a href="{relative(p,page)}">{E(label)}</a>' for p,label in config['extra'])
    body += '</div></section>'
    return shell(page,config['title'],body,lib)


def project_document(notes):
    page='index.html'
    body='<header class="hero"><div class="eyebrow">Sampling algorithms · Lean + Mathlib</div><h1>LangevinLean</h1><p class="subtitle">Mathematical proofs and machine-checked Lean, read side by side.</p><p>Three connected developments share the same reading and verification workflow. Start with a standalone result, follow its proof diagram, then open any supporting module for the full parallel proof.</p></header><section class="cards" aria-label="Algorithm proof libraries">'
    descriptions=['Strongly convex ULA: sharp gradient contraction, local error, constructed Brownian references, Gibbs stationarity, and both stable step-size regimes.',
                  'The actual interacting particle algorithm, its identification with ULA, lifted geometry, marginal concentration, and independent parameter and latent dimensions.',
                  'Actual proximal minimizers, Moreau calculus, corrected MYIPLA/PIPGLA/MYPGD guarantees, and constructed mean-field particle limits.']
    for (lib,config),description in zip(CONFIG.items(),descriptions):
        count=sum(p.startswith(lib+'/') or p==lib+'.lean' for p in notes)
        body+=f'<article class="landing-card"><div class="eyebrow">{count} module proof pages</div><h2>{config["title"]}</h2><p>{description}</p><a href="{lib}/exposition/index.html">Read the theorem and proof →</a></article>'
    body+='</section><section class="section workflow"><div><h2>Verify the proofs</h2>'
    body+=commands('lake exe cache get\nlake build\nlake env lean UnadjustedLangevin/Check.lean\nlake env lean IPLA/Check.lean\nlake env lean ProximalLangevin/Check.lean\npython3 docs/build_site.py\npython3 docs/verify_site.py','project-commands')
    body+='</div><div><h2>Read anywhere</h2><p>Open this page directly after cloning, or serve the repository root:</p><pre class="commands">python3 -m http.server 8000 --bind 127.0.0.1</pre><p>Mathematics is rendered at build time. Fonts and scripts are local, so the proof pages work offline without a documentation account. Every module also offers its mathematical exposition as a LaTeX source file.</p><p><a href="README.md">Clone, update, and regeneration instructions</a> · <a href="docs/README.md">Documentation architecture and coverage</a></p></div></section>'
    return shell(page,'Proofs and exposition',body)
