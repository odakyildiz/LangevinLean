"""Checked endpoints and proof roadmaps for the two kinetic developments."""
from kinetic_content import KINETIC_PROOF, KIPLMC_PROOF


def node(identifier, row, col, file, title, detail, parents=(), final=False):
    return dict(id=identifier, row=row, col=col, file=file, title=title,
                detail=detail, parents=parents, final=final)


KINETIC_CHECKED = r'''<p>Let \(E\) be a complete real inner product space with its Borel
structure and a countable topological base. Suppose \(f:E\to\mathbb R\) is
differentiable and \(m\)-strongly convex with \(M\)-Lipschitz gradient,
\(m\le M\). Fix \(\gamma\ge0\), \(a&lt;\gamma/2\), and \(0\le t\le T\).
Let \(\mu,\nu\) be probability laws of the initial position with
\(W_2(\mu,\nu)&lt;\infty\). Let \(Q\) be any probability law of the initial
velocity and continuous velocity forcing on \([0,T]\), independent of the
initial position in each process.</p>
<p>The selected flow solves the actual integral equation, with normalized
forcing \(b_t-b_0\),</p>
\[Y_t-Y_0=-\int_0^t(\gamma V_s+\nabla f(X_s),-V_s)ds+(b_t-b_0,0).\]
<p>Denote its position law by \(P_t^Q\mu\). Then</p>
\[\boxed{W_2(P_t^Q\mu,P_t^Q\nu)\le A_a e^{k_at}W_2(\mu,\nu),}\]
\[A_a=\frac{\sqrt{2((\gamma-a)^2+a^2)}}{\gamma-2a},\]
\[k_a=\frac{\max\{a^2-m,M-(\gamma-a)^2\}}{\gamma-2a}.\]
<p>This is the explicit prefactor and exponent of the manuscript's equation
(exp2), proved for the actual independent-product laws and the infimum over
initial couplings. No continuous Hessian assumption is needed. Choosing
\(a=0\) and \(\gamma^2\ge m+M\) gives
\(\sqrt2e^{-mt/\gamma}W_2(\mu,\nu)\).</p>
<p>The proof first cancels the common forcing in two integral solutions.
Strong-smooth gradient interpolation controls the transformed energy
\(\|V-V'+(\gamma-a)(X-X')\|^2+\|-(V-V')-a(X-X')\|^2\).
Gronwall gives the path estimate. Each initial coupling is then extended by
an independent copy of \(Q\); both output marginals and its cost are proved
before taking the Wasserstein infimum. The canonical Brownian source and
its Gibbs-stationary solution are also constructed in the supporting modules;
the separate KLMC theorem below combines them with the numerical analysis.'''

KINETIC_KLMC = r'''<p>Let \(f:\mathbb R^p\to\mathbb R\) be differentiable,
\(m\)-strongly convex and have \(M\)-Lipschitz gradient, where
\(0&lt;m\le M\). Write \(\pi(dx)\propto e^{-f(x)}dx\).
Choose \(\gamma&gt;0\) and \(h&gt;0\) with</p>
\[\gamma^2\ge m+M,\qquad 4\gamma Mh\le m.\]
<p>Initialize velocity as a standard Gaussian independent of the initial
position law \(\nu_0\), with \(W_2(\nu_0,\pi)&lt;\infty\).
At every step use the constructed centered Gaussian velocity–position
innovation pair with covariance given by the shared exponential Gram kernels;
pairs are independent across time and spatial coordinates. Let \(\nu_n\)
be the position law of this actual KLMC recursion. Then</p>
\[\boxed{W_2(\nu_n,\pi)\le
\sqrt2\left(1-\frac{3mh}{4\gamma}\right)^nW_2(\nu_0,\pi)
+\frac{Mh\sqrt{2p}}m.}\]
<p>The first term contracts the initial error; the second is the persistent
error caused by freezing the force over a step. The proof constructs the
exact and numerical processes together on every initial coupling extended
by an independent Gaussian velocity and canonical Brownian source. Their
common forcing cancels in the contraction estimate. The local freezing error
is quadratic in \(h\), while geometric accumulation divides by a quantity
of order \(h\), producing the linear bias above.</p>
<p>The stationary reference is derived from the actual kinetic equation by a
Verlet–OU splitting limit. Exact chain-law identities show that changing the
initial coupling does not change the numerical output law. Taking the true
Wasserstein infimum gives the initial \(W_2\) term; an optimal coupling is
not assumed. All these constructions and law identities are internal to the
Lean proof of this theorem.</p>'''

KIPLMC_CONCENTRATION = r'''<p>Let \(N\ge1\) and let the joint potential
\(U:\mathbb R^{d_\theta+d_x}\to\mathbb R\) be differentiable and
\(m\)-strongly convex, with \(m&gt;0\). The dimensions \(d_\theta,d_x\)
may differ and may be zero. Define</p>
\[\ell(\theta)=\int e^{-U(\theta,x)}dx,\]
\[\pi_\Theta(d\theta)\propto\ell(\theta)^N d\theta.\]
<p>The normalization is positive and finite. There is a unique maximizer
\(\theta_\star\) of \(\ell\), and its powered marginal satisfies</p>
\[\boxed{\int\|\theta-\theta_\star\|^2d\pi_\Theta(\theta)
\le\frac{d_\theta}{Nm}.}\]
<p>This gives the sharp concentration contribution
\(\sqrt{d_\theta/(Nm)}\) in both particle bounds. The exact powered Gibbs target, its kinetic invariance, and both complete numerical error bounds are proved in the supporting modules.</p>'''

KIPLMC_UPDATE = r'''<p>Write \(z=(\theta,x^1/\sqrt N,\ldots,x^N/\sqrt N)\),
and scale velocities the same way. Put
\(V_N(z)=\sum_iU(\theta,\sqrt N z_i)\) and
\(F_N=\nabla V_N/N\). KIPLMC1 is exactly the shared exponential update
with force \(F_N\) and phase noise amplitude \(\sqrt{2\gamma/N}\):</p>
\[\begin{aligned}
v^+&=\psi_0(h)v-\psi_1(h)F_N(z)+\sqrt{2\gamma/N}\,\varepsilon,\\
z^+&=z+\psi_1(h)v-\psi_2(h)F_N(z)+\sqrt{2\gamma/N}\,\varepsilon'.
\end{aligned}\]
<p>After multiplying a latent coordinate by \(\sqrt N\), its velocity update
is precisely</p>
\[V^{x_i,+}=\psi_0(h)V^{x_i}-\psi_1(h)\nabla_xU(\theta,x^i)
+\sqrt{2\gamma}\,\varepsilon^i.\]
<p>The checked coordinate theorem proves this identity from the lifted gradient;
it does not introduce a second exponential-integrator implementation.</p>'''

KIPLMC_SPLITTING = r'''<p>Set \(\delta=e^{-\gamma h/2}\),
\(\sigma=\sqrt{(1-\delta^2)/N}\), and take separate noise vectors
\(\xi,\xi'\) for the thermostat half-steps. KIPLMC2 is exactly</p>
\[v_{1/2}=\delta v+\sigma\xi-\tfrac h2F_N(z),\qquad
z^+=z+hv_{1/2},\qquad
v^+=\delta\bigl(v_{1/2}-\tfrac h2F_N(z^+)\bigr)+\sigma\xi'.\]
<p>The new position is used when recomputing the second force. The Lean
implementation is the shared O-B-A-B-O subflow composition; its expanded form,
parameter averages, latent unscaling, and independent-Gaussian transition laws
are proved.</p>'''


KINETIC_CONFIG = {
    'KineticLangevin': dict(
        label='Kinetic sampling', title='Kinetic Langevin Monte Carlo',
        subtitle='The exponential integrator, transformed-energy contraction, and the Dalalyan–Riou-Durand manuscript.',
        status='The actual Brownian kinetic mixing theorem, both Gaussian sampler bounds, Gibbs stationarity, and accuracy guarantees are checked, with explicit source corrections.',
        namespace='KineticLangevin',
        formal_note='The displayed statements are checked Lean theorems. The source audit separately records the remaining requirements for the entire manuscript.',
        archive='KineticLangevin/exposition/reference_audit.json',
        archive_label='Complete manuscript result and equation audit (JSON)',
        extra=[('KineticLangevin/exposition/README.md', 'Source version, conventions, and remaining proof obligations')],
        results=[dict(title='Kinetic position laws: the complete shifted contraction estimate',
                      file='KineticLangevin/FlowLaw.lean',
                      name='kineticPositionLaw_wasserstein2Real_general', body=KINETIC_CHECKED),
                 dict(title='The actual KLMC sampler: the complete first-order bound',
                      file='KineticLangevin/CanonicalKLMC.lean',name='klmc_wasserstein_bound',
                      namespace='KineticLangevin.CanonicalCoupling',
                      context='variable {d : ℕ} {μ : Measure (H d)} [IsProbabilityMeasure μ]',
                      body=KINETIC_KLMC)],
        proof=KINETIC_PROOF,
        diagram=[
            node('coefficients',0,0,'KineticLangevin/Coefficients.lean','Integrate the exponential response',r'\(\psi_{k+1}=\int_0^t\psi_k\)'),
            node('geometry',0,1,'KineticLangevin/Geometry.lean','Change phase coordinates',r'\(\|v+(\gamma-a)x\|^2+\|-v-ax\|^2\)'),
            node('dynamics',0,2,'KineticLangevin/Dynamics.lean','Construct the integral equation','A Lipschitz phase drift and Picard iteration'),
            node('integrator',1,0,'KineticLangevin/Integrator.lean','Define both exponential updates','One force evaluation; Hessian correction for KLMC2',('coefficients',)),
            node('spectral',1,1,'KineticLangevin/Contraction.lean','Cancel mixed Hessian terms','A symmetric Hessian gives scalar dissipation',('geometry',)),
            node('force',1,2,'KineticLangevin/PotentialContraction.lean','Use the original potential assumptions','Strong-smooth interpolation gives the sector bound',('geometry',)),
            node('covariance',2,0,'KineticLangevin/Coefficients.lean','Prove covariance positivity','A Gram quadratic form is an integral of a square',('coefficients',)),
            node('decay',2,1,'KineticLangevin/SynchronousFlow.lean','Contract actual integral flows',r'\(\sqrt2e^{-mt/\gamma}\)',('force','spectral','dynamics'),True),
            node('obabo',2,2,'KineticLangevin/OBABO.lean','Build the OBABO subflows','Shared by the second particle algorithm')]),
    'KIPLMC': dict(
        label='Kinetic interacting particles', title='Kinetic Interacting Particle Langevin Monte Carlo',
        subtitle='KIPLMC1 from the shared exponential integrator; KIPLMC2 from OBABO.',
        status='The actual Brownian KIPLD and both Gaussian-chain parameter-error theorems are proved, with exact particle geometry, target concentration, and accuracy guarantees.',
        namespace='KIPLMC',
        formal_note='The checked target, algorithm, and pathwise results are distinguished from the full numerical bounds discussed in the paper exposition.',
        archive='KIPLMC/exposition/reference_audit.json',
        archive_label='Complete manuscript result and algorithm audit (JSON)',
        extra=[('KIPLMC/exposition/README.md', 'Source version, scaling conventions, and remaining proof obligations'),
               ('KineticLangevin/exposition/index.html','The shared kinetic Langevin development')],
        results=[dict(title='Sharp concentration of the powered parameter marginal',
                      file='KIPLMC/Target.lean',name='parameter_secondMoment_le',body=KIPLMC_CONCENTRATION),
                 dict(title='KIPLMC1 reuses exponential integration exactly',
                      file='KIPLMC/Exponential.lean',name='kiplmc1Step_particle_velocity',body=KIPLMC_UPDATE),
                 dict(title='KIPLMC2 is the exact OBABO composition',
                      file='KIPLMC/Splitting.lean',name='kiplmc2Step_velocity',body=KIPLMC_SPLITTING)],
        proof=KIPLMC_PROOF,
        diagram=[
            node('lift',0,0,'IPLA/Geometry.lean','Reuse particle geometry',r'\(d_\theta+Nd_x\) scaled coordinates'),
            node('shared',0,1,'KineticLangevin/Integrator.lean','Reuse the kinetic integrator','The same exponential update'),
            node('subflows',0,2,'KineticLangevin/OBABO.lean','Reuse the OBABO composition','Separate thermostat innovations'),
            node('geometry',1,0,'KIPLMC/Geometry.lean','Average the lifted potential',r'\(F_N=\nabla V_N/N\)',('lift',)),
            node('first',1,1,'KIPLMC/Exponential.lean','Recover KIPLMC1 coordinates','Mean parameter force; ordinary latent force',('geometry','shared')),
            node('second',1,2,'KIPLMC/Splitting.lean','Recover KIPLMC2 coordinates','Recompute force at the new position',('geometry','subflows')),
            node('target',2,0,'KIPLMC/Target.lean','Normalize and project the target',r'\(\pi_\Theta\propto\ell(\theta)^N\)',('lift',)),
            node('laws',2,1,'KIPLMC/Laws.lean','Identify the actual chain laws','Independent noise gives Markov iteration',('first','second')),
            node('dynamics',2,2,'KIPLMC/Dynamics.lean','Transfer the pathwise kinetic theorem',r'Particle-independent \(m/\gamma\) rate',('geometry',)),
            node('concentration',3,0,'KIPLMC/Target.lean','Obtain sharp parameter concentration',r'\(d_\theta/(Nm)\) second moment',('target',),True)]),
}

KINETIC_BROWNIAN = r'''<p>The source is an actual constructed Brownian probability space. With standard Gaussian initial velocity independent of the initial position, the selected continuous L² solution solves the kinetic integral equation. Its Gibbs stationarity is proved by an exact Hamiltonian–thermostat splitting limit.</p>
<p>For any finite-second-moment initial law \(\nu\), any \(a&lt;\gamma/2\), and \(t\ge0\), its actual position law \(\nu_t\) satisfies</p>
\[W_2(\nu_t,\pi)\le \frac{\sqrt{2((\gamma-a)^2+a^2)}}{\gamma-2a}\,e^{k_at}W_2(\nu,\pi),\]
\[k_a=\frac{\max\{a^2-m,M-(\gamma-a)^2\}}{\gamma-2a}.\]
<p>The theorem takes no stationarity or reference-process premise. The proof constructs the noise, shows that every coupling produces the same output marginals, proves the energy inequality in L², and takes the infimum over all initial couplings. At \(a=0\) and \(\gamma^2\ge m+M\), the prefactor becomes \(\sqrt2\) and the exponent is \(-mt/\gamma\).</p>'''

KIPLMC_FLOW = r'''<p>Let \(N\ge1\), and suppose the joint potential \(U(\theta,x)\) is differentiable, \(m\)-strongly convex, and has \(L\)-Lipschitz gradient, with \(0&lt;m\le L\). Initialize the scaled position \(Z_0\sim\nu\) with finite second moment. Independently initialize scaled velocity as \(\mathcal N(0,N^{-1}I)\), and use the actual independent Brownian source. If \(\gamma^2\ge m+L\), the constructed physical KIPLD parameter law satisfies</p>
\[\boxed{W_2(\mathcal L(\Theta_t),\pi_\Theta)\le\sqrt2e^{-mt/\gamma}\bigl(\mathbb E\|Z_0-\bar Z_*\|^2\bigr)^{1/2}.}\]
<p>Here \(\bar Z_*\sim\pi_Z\) is independent of \(Z_0\), and \(\pi_Z(dz)\propto e^{-V_N(z)}dz\). The target parameter marginal is exactly \(\pi_\Theta(d\theta)\propto\ell(\theta)^N d\theta\). This is the supplied manuscript’s continuous convergence proposition.</p>
<p>The proof uses \(c=\sqrt N\), unit-temperature friction \(c\gamma\), and time \(t/c\). The sum potential has curvature \(Nm\), so its mixing exponent becomes \((Nm)/(c\gamma)\,(t/c)=mt/\gamma\). The actual flow is rescaled in velocity only; its position endpoint is unchanged. A separate theorem verifies its full physical integral equation and its independent thermal initial law. Brownian scaling proves that the transformed forcing has amplitude \(\sqrt{2\gamma/N}\). Projection to the parameter cannot increase a coupling’s cost, and the independent initial coupling gives the displayed constant.</p>'''

KIPLMC_FIRST_BOUND = r'''<p>Use the same assumptions and thermal initialization as above. Let \(\theta_*\) be the unique marginal-likelihood maximizer. KIPLMC1 calls the shared Dalalyan–Riou-Durand exponential step with the actual correlated Gaussian velocity–position innovations. If</p>
\[\gamma^2\ge m+L,\qquad 0&lt;h,\qquad4\gamma Lh\le m,\]
<p>then its actual parameter iterates obey</p>
\[\boxed{\bigl(\mathbb E\|\Theta_n-\theta_*\|^2\bigr)^{1/2}\le C_1q^n+hC_2+\sqrt{\frac{d_\theta}{Nm}},}\]
\[q=1-\frac{3mh}{4\gamma},\qquad C_1=\sqrt2\bigl(\mathbb E\|Z_0-\bar Z_*\|^2\bigr)^{1/2},\]
\[C_2=\frac{\sqrt2L}{m}\sqrt{\frac{d_\theta+Nd_x}{N}}.\]
<p>The three terms have different meanings. The first remembers initialization and vanishes geometrically. The second is the numerical bias and decreases with the step. The third is the statistical concentration radius and decreases with particle count. Increasing the number of iterations cannot remove either persistent floor.</p>
<p>The proof transfers the exact Gaussian Markov law through the clock and velocity conjugacy, applies the shared first-order KLMC theorem, and checks every power of \(N\). The factor \(NL\) from smoothness, the transformed step \(h/\sqrt N\), and curvature \(Nm\) leave precisely \(h(L/m)\sqrt{2(d_\theta+Nd_x)/N}\). Parameter projection and the L² triangle inequality add the sharp equilibrium radius. The independent initial coupling bounds the true initial Wasserstein distance. Gaussian laws, their independence, target invariance, and finite transport moments are proved internally.</p>'''

KIPLMC_SECOND_BOUND = r'''<p>KIPLMC2 uses the actual shared O-B-A-B-O composition with independent Gaussian thermostat vectors. Under the same joint potential assumptions, suppose</p>
\[\gamma&gt;0,\qquad \gamma^2\ge4L,\qquad0&lt;h,\qquad33\gamma^3h\le m.\]
<p>Put \(d_z=d_\theta+Nd_x\) and \(D_0=W_2(\nu,\pi_Z)\). The supplied manuscript’s bound holds with the following explicit constant, independent of \(N,n,h,d_\theta,d_x\):</p>
\[C=\sqrt2+\frac{6\sqrt2\gamma}{m}\left(4\sqrt L+\frac{Lm}{66\gamma^3}\right)+\frac1{\sqrt m}.\]
\[\boxed{\begin{aligned}(\mathbb E\|\Theta_n-\theta_*\|^2)^{1/2}\le C\bigl[&(\sqrt N D_0+hN\sqrt{d_z})e^{-mhn/(6\gamma)}\\&+h\sqrt{Nd_z}+\sqrt{d_\theta/N}\bigr].\end{aligned}}\]
<p>The proof first obtains a stronger direct bound. In the weighted phase metric, the actual two-force OBABO step contracts by \(r=\sqrt{1-mh/(3\gamma)}\). Compare one such step with an exact O–Hamiltonian–O step, which preserves the proved Gibbs target. The common-noise local defect is quadratic in \(h\); summing the contractive perturbations gives the persistent position bias</p>
\[\frac{6\sqrt2\gamma}{m}\,h\sqrt{\frac{d_z}{N}}\left(4\sqrt L+\frac{Lh}{2}\right).\]
<p>This argument proves sampling from the actual Gaussian chain directly. It requires no assumed discrete invariant law or external OBABO error estimate. Exact clock scaling and \(r^n\le e^{-mhn/(6\gamma)}\) turn that stronger result into the supplied coarse rate, retaining both of its transient terms. The final concentration term is the same sharp statistical contribution as for KIPLMC1. The checked accuracy corollaries expose positive step choices, natural particle counts, and rounded logarithmic iteration counts.</p>'''

KINETIC_CONFIG['KineticLangevin']['results'].insert(1,dict(
    title='The actual Brownian diffusion mixes to its proved Gibbs target',
    file='KineticLangevin/ContinuousGibbs.lean',name='wasserstein2_gibbs_general',
    namespace='KineticLangevin.CanonicalContinuous',
    context='variable (ι : Type*) [Fintype ι] [DecidableEq ι]',body=KINETIC_BROWNIAN))
KINETIC_CONFIG['KIPLMC']['status'] = 'The actual Brownian KIPLD convergence proposition and both Gaussian algorithm parameter-error theorems are proved. KIPLMC1 reuses the shared exponential integrator; KIPLMC2 has an internal OBABO contraction and Gibbs sampling proof. The source audit records the exact correspondence and source corrections.'
KINETIC_CONFIG['KIPLMC']['formal_note'] = 'The statements below concern the constructed Brownian diffusion and actual Gaussian Markov chains. All displayed convergence and concentration conclusions are checked Lean theorems.'
KINETIC_CONFIG['KIPLMC']['results'] = [
    dict(title='The actual Brownian KIPLD parameter convergence proposition',file='KIPLMC/Continuous.lean',name='kipld_parameter_sampling_bound',body=KIPLMC_FLOW),
    dict(title='KIPLMC1: the complete parameter RMS theorem',file='KIPLMC/CanonicalExponential.lean',name='kiplmc1_parameter_bound_independent',body=KIPLMC_FIRST_BOUND),
    dict(title='KIPLMC2: the supplied rate with an explicit uniform constant',file='KIPLMC/OBABOPaperRate.lean',name='kiplmc2_parameter_paper_bound',body=KIPLMC_SECOND_BOUND),
    *KINETIC_CONFIG['KIPLMC']['results']]

# The proof diagrams finish at the actual stochastic endpoints.
KINETIC_CONFIG['KineticLangevin']['diagram'] += [
    node('brownian',3,0,'KineticLangevin/BrownianConvolution.lean','Construct the actual Brownian source','Exact Gaussian convolution laws and independent intervals',('covariance',)),
    node('stationary',3,1,'KineticLangevin/ContinuousGibbs.lean','Prove actual Gibbs stationarity','Exact Hamiltonian invariance and a splitting limit',('dynamics','brownian')),
    node('klmc-final',4,0,'KineticLangevin/CanonicalKLMC.lean','Bound the actual first-order sampler','True transport infimum and exact Gaussian chain law',('integrator','stationary','brownian'),True),
    node('continuous-final',4,1,'KineticLangevin/ContinuousGibbs.lean','Mix actual Brownian laws to Gibbs','Full arbitrary-shift prefactor and exponent',('stationary','decay'),True),
    node('accuracy-final',4,2,'KineticLangevin/Accuracy.lean','Choose an explicit accuracy budget','Positive minimum step and integer logarithmic count',('klmc-final',),True)]
KINETIC_CONFIG['KIPLMC']['diagram'] += [
    node('kipld-final',4,0,'KIPLMC/Continuous.lean','Mix the actual Brownian KIPLD','Exact physical clock and proved target stationarity',('dynamics','target'),True),
    node('kiplmc1-final',4,1,'KIPLMC/CanonicalExponential.lean','Prove the actual KIPLMC1 RMS bound','Shared KLMC theorem plus sharp concentration',('first','laws','concentration'),True),
    node('kiplmc2-final',4,2,'KIPLMC/OBABOPaperRate.lean','Prove the supplied KIPLMC2 rate','Internal OBABO sampling proof and explicit uniform C',('second','laws','concentration'),True),
    node('particle-accuracy',5,1,'KIPLMC/Accuracy.lean','Choose particles, steps and iterations','Integer statistical budget and rounded accuracy counts',('kiplmc1-final','kiplmc2-final'),True)]

KINETIC_SECOND_BOUND = r'''<p>Assume the same strongly convex, smooth potential, and let its actual Hessian be \(M_2\)-Lipschitz in operator norm, with \(M_2&gt;0\). Let the initial position have law \(\nu_0\) with \(W_2(\nu_0,\pi)&lt;\infty\). KLMC2 uses the four correlated Brownian response kernels \(\psi_0,\psi_1,\varphi_2,\varphi_3\), with the Hessian applied to both the deterministic velocity and the corresponding noise corrections. Initialize velocity with the standard Gaussian law \(\mathcal N(0,I_p)\), independently of the initial position and the fresh innovations. Suppose</p>
\[\gamma&gt;0,\qquad\gamma^2\ge m+M,\qquad0&lt;h,\qquad5\gamma Mh\le m,\qquad4\sqrt{5p}M_2h\le m.\]
<p>Define \(q=1-mh/(4\gamma)\), \(\alpha=(m/(4M_2h))^2\), and</p>
\[C_p=M_2\sqrt{p^2+2p}+M\sqrt{Mp}.\]
<p>The actual Gaussian-chain position law satisfies, in every finite dimension,</p>
\[\boxed{\begin{aligned}W_2(\nu_n,\pi)\le{}&\sqrt2q^nW_2(\nu_0,\pi)+\frac{\sqrt2h^2C_p}{m}\\&+\frac{8(M-m)}m h e^{-(\alpha-p)/8}.\end{aligned}}\]
<p>The tail is bounded by both \(e^{-p/2}\) and \(e^{-m^2/(160M_2^2h^2)}\). For \(p\ge2\), simplifying the exact fourth moment yields the supplied manuscript’s displayed bound:</p>
\[\begin{aligned}W_2(\nu_n,\pi)\le{}&\sqrt2q^nW_2(\nu_0,\pi)+\frac{2M_2ph^2}{m}\\&+\frac{Mh^2\sqrt{2Mp}}m+\frac{8M}m h e^{-p/2}.\end{aligned}\]
<p>The dimension restriction belongs to this final simplification: \(p^2+2p\le2p^2\) requires \(p\ge2\). The preceding exact-moment bound provides the valid dimension-one conclusion. The source audit preserves the supplied statement and identifies this correction explicitly.</p>
<p>The proof combines a cubic local Taylor–memory error with a contractive comparison of two actual Hessian-corrected updates. The supplied subtraction omits stochastic Hessian-difference terms. The formal proof retains them and combines the initial Gaussian velocity with the fresh Brownian interval into one stationary free Ornstein–Uhlenbeck process. Its Gaussian cutoff estimate does not assume independence from the random Hessian. The choice of \(\alpha\) absorbs the Hessian contribution into the contraction gap. Exact canonical chain and reference laws then permit the true Wasserstein infimum. No local-error, stationarity, independence, or convergence conclusion is left as a theorem premise.</p>
<p>An explicit accuracy corollary bounds the entire persistent floor by \(B_ph^2\), chooses a positive minimum step satisfying both source restrictions and \(B_ph^2\le0.94\varepsilon\), and rounds the logarithmic transient count to a natural number. It gives a checked error at most \(\varepsilon\) for the actual sampler.</p>'''

KINETIC_CONFIG['KineticLangevin']['status'] = 'The actual Brownian kinetic mixing theorem, first-order KLMC sampler theorem, Hessian-corrected KLMC2 theorem, Gibbs stationarity, exact Gaussian and Cholesky constructions, and explicit accuracy corollaries are checked. The source audit records the supplied manuscript corrections and the continuous-L² Brownian model.'
KINETIC_CONFIG['KineticLangevin']['formal_note'] = 'The statements below concern the constructed Brownian integral solution and actual Gaussian chains. The source audit preserves the printed statements and distinguishes the corrected prefactor, stochastic Hessian comparison, kernel index range, and final dimension simplification.'
KINETIC_CONFIG['KineticLangevin']['results'] += [
    dict(title='The actual KLMC2 sampler: the exact-moment bound in every dimension',
         file='KineticLangevin/CanonicalKLMC2.lean',name='klmc2_wasserstein_bound_exact',
         namespace='KineticLangevin.SecondOrderSource',context='variable (ι : Type*) [Fintype ι] [DecidableEq ι]',body=KINETIC_SECOND_BOUND),
    dict(title='The supplied simplified KLMC2 bound, with its valid dimension range',
         file='KineticLangevin/CanonicalKLMC2.lean',name='klmc2_wasserstein_bound',
         namespace='KineticLangevin.SecondOrderSource',context='variable (ι : Type*) [Fintype ι] [DecidableEq ι]',
         body=r'<p>For \(p\ge2\), the exact-moment result above implies the supplied formula with terms \(2M_2ph^2/m\), \(Mh^2\sqrt{2Mp}/m\), and \((8M/m)he^{-p/2}\). The Lean statement makes the dimension restriction explicit. The stronger inverse-step-square tail is available in <code>klmc2_wasserstein_bound_sharp_tail</code> in the same module.</p>')]
KINETIC_CONFIG['KineticLangevin']['diagram'] += [
    node('hessian-local',5,0,'KineticLangevin/SecondOrderLpLocal.lean','Bound the true Hessian local defect','Actual fourth moments and cubic Taylor–memory error',('integrator','stationary')),
    node('hessian-compare',5,1,'KineticLangevin/SecondOrderComparison.lean','Repair the stochastic Hessian comparison','Free OU bundling retains all four noise kernels',('brownian','stationary')),
    node('klmc2-final',6,0,'KineticLangevin/CanonicalKLMC2.lean','Bound the actual second-order sampler','Exact-moment theorem and source dimension correction',('hessian-local','hessian-compare'),True),
    node('klmc2-accuracy',6,1,'KineticLangevin/SecondOrderAccuracy.lean','Choose the second-order accuracy step','A positive minimum and integer iteration count',('klmc2-final',),True)]


KINETIC_CONFIG['KineticLangevin']['results'] += [
    dict(title='The refined complexity correction: an explicit bound for the natural count',
         file='KineticLangevin/SecondOrderComplexity.lean',name='secondOrderTailFree_iterationCount_conditionNumber',
         namespace='KineticLangevin',
         body=r'<p>The source refinement explicitly omits its exponential tail. For \(m&gt;0\), \(M\ge m\), \(M_2&gt;0\), \(p\ge1\), and \(\varepsilon&gt;0\), set \(\gamma=\sqrt{m+M}\). Let \(h_0\) be the minimum of the two source stability limits and \(\sqrt{\varepsilon\sqrt m/(4M_2p+2M\sqrt{2Mp})}\). Put \(\kappa=M/m\), \(\rho=(M_2^{2/3}+Mp^{-1/3})/m\), and \(R=\max\{\kappa,\rho\}\). Take a positive finite initial distance \(D\), and select \(n=\lceil\max\{0,(4\gamma/(mh_0))\log(24D\sqrt m/\varepsilon)\}\rceil\). This natural count obeys</p>\[n&lt;1+64\left[\sqrt p R^2+\sqrt{p/\varepsilon}R^{5/4}\right]\max\left\{0,\log\frac{24D\sqrt m}{\varepsilon}\right\}.\]<p>The exact reciprocal-step identity proves the connection to the physical source parameters. The printed form is recovered under the explicit regime \(M(1-p^{-1/3})\le M_2^{2/3}\). A separate Lean theorem proves that no uniform constant repairs the printed expression without that regime or a correction. This is a statement about the source step prescription; the actual sampler accuracy theorem above retains its full tail.</p>')]
KINETIC_CONFIG['KineticLangevin']['diagram'] += [
    node('refined-budget',7,0,'KineticLangevin/SecondOrderComplexity.lean','Audit the exact refined step and count','A corrected condition number and explicit constant 64',('klmc2-accuracy',),True),
    node('refined-correction',7,1,'KineticLangevin/ConditionNumber.lean','Prove the source complexity correction','Natural dimensions disprove the unqualified budget',('klmc2-final',),True)]
