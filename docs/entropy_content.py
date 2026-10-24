"""Standalone mathematical exposition of the ULA and IPLA entropy arguments.

The classical theorem and the scope of the currently checked Lean endpoint
are deliberately stated separately. References point only to actual sources.
"""


def ref(file,name):
    return dict(file=file,name=name)


def part(identifier,title,body,references=(),note=''):
    return dict(id=identifier,title=title,body=body,references=list(references),note=note)


def node(identifier,row,col,file,title,detail,parents=(),final=False):
    return dict(id=identifier,row=row,col=col,file=file,title=title,detail=detail,parents=parents,final=final)


ULA_STATEMENT=r'''<p>Let \(d\ge1\) and \(\nu(dx)=Z^{-1}e^{-U(x)}dx\) be a probability measure on \(\mathbb R^d\). Assume \(U\) is differentiable with globally \(L\)-Lipschitz gradient, \(L>0\), and \(\nu\) satisfies a log-Sobolev inequality with constant \(\alpha>0\):</p>
\[2\alpha H_\nu(\rho)\le I_\nu(\rho),\qquad
H_\nu(\rho)=\int\log\frac{d\rho}{d\nu}\,d\rho,\quad
I_\nu(\rho)=\int\left\|\nabla\log\frac{d\rho}{d\nu}\right\|^2d\rho.\]
<p>Take an initial probability law \(\rho_0\) with finite relative entropy. Let \(Z_k\) be independent standard Gaussian vectors, independent of initialization. For</p>
\[X_{k+1}=X_k-h\nabla U(X_k)+\sqrt{2h}\,Z_k,
\qquad 0&lt;h\le\frac{\alpha}{4L^2},\]
<p>the laws \(\rho_k=\operatorname{Law}(X_k)\) satisfy, for every \(k\ge0\),</p>
\[\boxed{H_\nu(\rho_k)\le e^{-\alpha hk}H_\nu(\rho_0)+\frac{8hdL^2}{\alpha}.}\]
<p>This is the KL estimate of <a href="https://www.cs.yale.edu/homes/wibisono/VW19.pdf">Vempala–Wibisono (2019), Theorem 2</a>. The first term is the initial entropy contracted at an exponential rate. The second is the discretization floor. Convexity of \(U\) is not assumed. The proof uses the compatible inequality \(\alpha\le L\), derived below in positive dimension. If the initial entropy is infinite the extended-valued inequality is immediate; the finite case is the substantive assertion.</p>'''


ULA_PROOF=[
part('entropy','The Gibbs law, the actual update, and the LSI test class',r'''<p>Write \(\nu(dy)=J(y)dy\), where \(J=Z^{-1}e^{-U}>0\). A positive C¹ relative density \(r\), normalized by \(\int r\,d\nu=1\), defines the law \(r\nu\). The functional inequality is</p>
\[2\alpha\,\mathrm{KL}(r\nu\mid\nu)\le\int\|\nabla\log r\|^2r\,d\nu.\]
<p>Both quantities initially take values in the extended nonnegative reals. Their finiteness is established before ordinary real integral manipulations are used. It applies this same LSI definition to the actual Gaussian mixture, whose strict positivity and C¹ regularity are proved below.</p>
<p>For one step, take \(X\sim\mu\) independently of \(Z_0\sim\mathcal N(0,I_d)\), and set</p>
\[Y_t=X-t\nabla U(X)+\sqrt{2t}\,Z_0,\quad\rho_t=\operatorname{Law}(Y_t).\]
<p>The independent product measure makes independence explicit. At zero the law is \(\mu\), and at \(h\) it is its actual ULA update. The discrete laws are repeated applications of this transition.</p><p>The relative density is distinct from a Lebesgue density. If \(p_t\) is the density of \(\rho_t\) with respect to volume, then \(r_t=p_t/J\); consequently \(\log r_t=\log p_t+U+\log Z\) and the relative score is \(S_t=\nabla\log p_t+\nabla U\). For the exact Gibbs density, these two score contributions cancel and Fisher information is zero. This explains why the functional inequality controls distance from Gibbs rather than merely spatial variation of \(p_t\).</p><p>The interpolation is local to a numerical step: its initial random variable remains fixed in the frozen drift. It is therefore not the exact Langevin diffusion during that step. The proof will quantify the discrepancy between \(\nabla U(X)\) and \(\nabla U(Y_t)\), while retaining the exact law equality at both endpoints. Those endpoint equalities are what allow a continuous entropy estimate to become a recurrence for the actual algorithm.</p>''',[
ref('UnadjustedLangevin/LSI/FunctionalInequality.lean','IsLogSobolev'),
ref('UnadjustedLangevin/LSI/ULALaw.lean','interpolationLaw_endpoint')],
'The positive C¹ test class is sufficient because the actual relative density is proved to belong to it at every positive time.'),

part('compatibility','Derive α ≤ L with bounded tests',r'''<p>We first derive compatibility, rather than assume it. For bounded C¹ \(f\) with \(\|\nabla f\|\le D\), let \(\Lambda(s)=\log\int e^{sf}d\nu\). The normalized density \(e^{sf-\Lambda(s)}\) is an admissible LSI test, and its log-gradient is \(s\nabla f\). Its entropy is \(s\Lambda'(s)-\Lambda(s)\). Consequently</p>
\[2\alpha\bigl(s\Lambda'(s)-\Lambda(s)\bigr)\le s^2D^2.\]
<p>Boundedness permits differentiating the moment generating function near zero. Divide by \(s^2\) and let \(s\downarrow0\): the quotient \((s\Lambda'(s)-\Lambda(s))/s^2\) tends to \(\Lambda''(0)/2=\operatorname{Var}_\nu(f)/2\), so the entire left side tends to \(\alpha\operatorname{Var}_\nu(f)\). Thus \(\alpha\operatorname{Var}_\nu(f)\le D^2\).</p>
<p>Choose a unit vector \(v\). Translation invariance of the partition function and the smooth upper model <cite data-report-ref="UnadjustedLangevin/Analysis/Smooth.lean" data-report-declaration="smooth_upper_bound"></cite> give a centered sub-Gaussian directional score \(g_v=\langle\nabla U,v\rangle\) <cite data-report-ref="UnadjustedLangevin/GibbsScore.lean" data-report-declaration="gibbs_score_subgaussian"></cite>, with \(\int g_v^2d\nu\le L\) by the directional second-moment estimate <cite data-report-ref="UnadjustedLangevin/GibbsScore.lean" data-report-declaration="integral_sq_le_of_subgaussian"></cite>. Integration by parts for bounded C¹ tests gives</p>
\[\int f g_v\,d\nu=\int\langle\nabla f,v\rangle d\nu.\]
<p>Use \(f_t(x)=\sin(t\langle v,x\rangle)\). Its gradient norm is at most \(t\), and the identity reads \(\int(f_t-\nu f_t)g_vd\nu=t\int\cos(t\langle v,x\rangle)d\nu\). Cauchy–Schwarz and the bounded-test variance bound yield</p>
\[\alpha\left(\int\cos(t\langle v,x\rangle)d\nu\right)^2\le L.\]
<p>The cosine is bounded by one and converges pointwise to one. Dominated convergence gives \(\alpha\le L\). This uses no position second moment, Hessian, or coordinate approximation. If the state space is a singleton, all probability measures coincide and KL is zero; that case is handled separately.</p><p>To see the cancellation of the small parameter explicitly, write \(D=t\) for the sine test. The variance bound gives \(\operatorname{Var}(f_t)\le t^2/\alpha\), while the score has mean zero and second moment at most \(L\). Thus</p>\[t^2\left(\int\cos(t\langle v,x\rangle)d\nu\right)^2
=\left(\int(f_t-\nu f_t)g_vd\nu\right)^2
\le\frac{Lt^2}{\alpha}.\]<p>For \(t>0\), divide by \(t^2\) and multiply by \(\alpha\). The limiting cosine integral is one without any assumption on \(\langle v,X\rangle\), because its integrand is bounded. Positive dimension enters only through the existence of a unit direction; all scalar integrations remain bounded-test calculations.</p>''',[
ref('UnadjustedLangevin/LSI/Compatibility.lean','IsLogSobolev.exponential_test'),
ref('UnadjustedLangevin/LSI/Compatibility.lean','logSobolev_constant_le_smoothness')],
'The original LSI definition implies the compatibility inequality; it is not an extra premise of the final bound.'),

part('moment','Obtain the initial gradient moment directly from entropy',r'''<p>The directional score estimate <cite data-report-ref="UnadjustedLangevin/GibbsScore.lean" data-report-declaration="gibbs_score_lmgf_le"></cite> also gives, for every vector \(v\),</p>
\[\int e^{\langle\nabla U(x),v\rangle}d\nu(x)\le e^{L\|v\|^2/2}.\]
<p>Average this inequality over an auxiliary centered Gaussian vector. Completing the square in its density gives an exponential square moment. Tonelli applies because every integrand is nonnegative. With the Gaussian variance chosen to match \(4L\),</p>
\[\int\exp\!\left(\frac{\|\nabla U\|^2}{4L}\right)d\nu
\le 2^{d/2}\le e^{d/2}.\]
<p>For any finite-KL probability law \(\mu\), the entropy variational inequality then gives</p>
\[G_0:=\int\|\nabla U\|^2d\mu\le4L\,H_\nu(\mu)+2dL
\le\frac{4L^2}{\alpha}H_\nu(\mu)+2dL.\]
<p>The last inequality uses \(\alpha\le L\) and nonnegative KL. Integrability is part of the conclusion. Its integrability is derived before using the real integral: for the Radon–Nikodym density \(a=d\mu/d\nu\), the pointwise inequality \(ab\le a\log a-a+e^b\) controls the nonnegative weighted integrand. Subtracting the certified log-moment bound inside the Fenchel inequality gives the sharper variational bound. Thus finite KL alone supplies the score moment required by the Gaussian calculations.</p><p>The entropy variational inequality can be read directly as a density calculation. If \(a=d\mu/d\nu\) and \(F\) has a finite exponential moment, normalize \(e^F\nu\) by \(M=\int e^Fd\nu\). Nonnegativity of relative entropy with respect to this tilted probability gives</p>\[0\le\operatorname{KL}\left(\mu\,\middle\Vert\,M^{-1}e^F\nu\right)
=H_\nu(\mu)-\int Fd\mu+\log M.\]<p>The pointwise convex-duality estimate first supplies the absolute integrability required to write this identity. For the nonnegative score-square observable, monotone truncations also justify passage from bounded tests to the full \(F\). Taking \(F=\|\nabla U\|^2/(4L)\) and \(\log M\le d/2\) yields the stated coefficient after multiplication by \(4L\).</p>''',[
ref('UnadjustedLangevin/LSI/EntropyMoment.lean','gibbs_score_exponential_moment'),
ref('UnadjustedLangevin/LSI/EntropyMoment.lean','gibbs_gradient_moment_bound_of_finite_kl_of_alpha_le')],
'The checked proof uses this direct score-exponential argument, so no entropy-cost coupling or LSI-to-transport theorem is required.'),

part('gaussian-law','Compute displacement and drift-error energies',r'''<p>On the same independent product probability space,</p>
\[Y_t-X=-t\nabla U(X)+\sqrt{2t}\,Z_0.\]
<p>Expand its squared norm. The cross term integrates to zero because the Gaussian mean is zero and the two factors are independent. The Gaussian second moment is \(\mathbb E\|Z_0\|^2=d\), hence</p>
\[\mathbb E\|Y_t-X\|^2=t^2G_0+2td.\]
<p>The Lipschitz gradient now gives the exact error estimate used in production:</p>
\[\mathbb E\|\nabla U(Y_t)-\nabla U(X)\|^2
\le L^2(t^2G_0+2td).\]
<p>All terms are integrable by the score moment just proved and the Gaussian second moment. The joint law of \((X,Y_t)\) is also identified as \(K_t(x,y)\mu(dx)dy\), where \(K_t\) is the Gaussian transition density. This transfers the same sharp bound to the kernel-weighted pair integral used in the weak equation.</p><p>In more detail, independence and Cauchy–Schwarz justify</p>\[\mathbb E\langle\nabla U(X),Z_0\rangle
=\left\langle\mathbb E\nabla U(X),\mathbb EZ_0\right\rangle=0.\]<p>The initial gradient is integrable because it is square-integrable under a probability law. Hence this is an ordinary expectation of an integrable mixed term, rather than a formal cancellation. No term involving \(\mathbb E\|X\|^2\) appears: the position cancels before any square is expanded. Multiplying the displacement energy by \(L^2\) preserves its two distinct orders, \(t^2G_0\) from the frozen drift and \(2td\) from Gaussian diffusion. These orders determine the separate initial-entropy and dimensional forcing terms later.</p>''',[
ref('UnadjustedLangevin/LSI/GaussianDrift.lean','frozen_displacement_second_moment'),
ref('UnadjustedLangevin/LSI/GaussianEnergyIntegrability.lean','frozenGaussianKernel_gradient_error_energy')],
'The error is calculated for the actual Gaussian transition, with finiteness and the pair-law change of variables established explicitly.'),

part('density-and-flux','Prove density regularity, Fisher finiteness, and the weak equation',r'''<p>For \(t>0\), write</p>
\[K_t(x,y)=(4\pi t)^{-d/2}e^{-\|y-x+t\nabla U(x)\|^2/(4t)},\quad
p_t(y)=\int K_t(x,y)d\mu(x),\quad r_t=p_t/J.\]
<p>Gaussian polynomials times their decaying exponential are bounded. They dominate the first spatial derivative independently of the center, so differentiation under the probability integral proves that \(p_t\), and therefore \(r_t\), are positive C¹ functions. The posterior probability on \(x\), proportional to \(K_t(x,y)\mu(dx)\), gives</p>
\[\nabla\log p_t(y)=-\frac1{2t}\mathbb E[y-X+t\nabla U(X)\mid Y_t=y].\]
<p>Jensen and the Gaussian displacement moment imply \(\int\|\nabla\log p_t\|^2d\rho_t\le d/(2t)\). Since \(S_t:=\nabla\log r_t=\nabla\log p_t+\nabla U\),</p>
\[I_t:=\int\|S_t\|^2d\rho_t\le d/t+2\int\|\nabla U\|^2d\rho_t&lt;\infty.\]
<p>Lipschitzness and the displacement identity bound the last integral by \(2(1+L^2t^2)G_0+4tdL^2\). Applying the original extended-valued LSI now proves finite actual KL for every \(t>0\), as well as \(2\alpha H(t)\le I_t\).</p>
<p>Directly differentiating the kernel in time gives</p>
\[\dot K_t=K_t\left[-\frac d{2t}+\frac{\|y-x\|^2}{4t^2}-\frac{\|\nabla U(x)\|^2}{4}\right].\]
<p>Its absolute integral is controlled on each positive compact time interval by \(G_0\) and Gaussian moments. Set \(F_t(x,y)=\nabla_y K_t(x,y)+K_t(x,y)\nabla U(x)\). Its spatial divergence equals \(\dot K_t\). Coordinate integration by parts, with integrable derivatives and flux, proves for every bounded C¹ test \(\psi\) with \(\nabla\psi\in L^2(\rho_t)\),</p>
\[\int\dot p_t\psi\,dy=-\iint\langle F_t(x,y),\nabla\psi(y)\rangle d\mu(x)dy.\]
<p>This is the actual weak equation; no weak-equation hypothesis is passed to the final theorem. The jointly measurable score field equals \(S_t\) at positive times, so its spacetime integrals are well-defined.</p><p>The smoothing Fisher bound follows by integrating posterior Jensen with its denominator canceled:</p>\[\begin{aligned}
\int p_t(y)\|\nabla\log p_t(y)\|^2dy
&\le\iint\frac{\|y-x+t\nabla U(x)\|^2}{4t^2}
K_t(x,y)d\mu(x)dy\\
&=\frac{2td}{4t^2}=\frac d{2t}.
\end{aligned}\]<p>The inner Gaussian moment is the same for every initial point, so no location moment of \(\mu\) is introduced. The bound diverges as \(t\downarrow0\), which is why the entropy identity is first proved on intervals bounded away from zero. For the weak equation, a bounded test makes the flux-test product integrable, finite gradient energy makes the flux-gradient product integrable, and the explicit quadratic Gaussian envelope makes the flux derivative integrable. These are the precise global integration-by-parts conditions replacing an unproved boundary-decay assertion.</p>''',[
ref('UnadjustedLangevin/LSI/GaussianEntropy.lean','interpolationLebesgue_fisher_bound'),
ref('UnadjustedLangevin/LSI/GaussianTimeDerivative.lean','hasDerivAt_interpolationLebesgueDensity_time'),
ref('UnadjustedLangevin/LSI/GaussianWeakEquation.lean','interpolationLebesgueDensity_weak_identity')],
'The kernel differentiation, weak equation, and all required integrability are derived from the stated potential assumptions and the entropy-derived score moment.'),

part('production','Pass bounded log tests to the entropy identity',r'''<p>An unbounded logarithm cannot be inserted into the weak equation without justification. For \(m\ge0\), put</p>
\[\begin{aligned}
\chi_m(z)&=(m+1)\arctan\frac z{m+1},\\
w_m(z)&=\chi_m'(z)=\frac1{1+(z/(m+1))^2},\\
\Phi_m(r)&=\int_1^r\chi_m(\log u)du.
\end{aligned}\]
<p>These functions satisfy \(0\le w_m\le1\), \(w_m\to1\), and \(0\le\Phi_m(r)\le r\log r-r+1\), with pointwise convergence to the upper bound. The test \(\psi_{m,t}=\chi_m(\log r_t)\) is bounded C¹, with \(\nabla\psi_{m,t}=w_m(\log r_t)S_t\). Its gradient is square-integrable because \(I_t&lt;\infty\).</p>
<p>The time chain rule is first applied pointwise to \(J\Phi_m(r_t)\): its derivative is \(\chi_m(\log r_t)\dot p_t\). Boundedness of \(\chi_m\) and the spacetime L¹ estimate for \(\dot p_t\) justify Fubini and the fundamental theorem of calculus on \([a,b]\subset(0,\infty)\). The weak equation identifies this bounded-entropy flux with a weighted Gaussian pair integral.</p>
<p>The Fisher bound and the Gaussian velocity energy are integrable uniformly on every such interval. Cauchy–Schwarz dominates the absolute cross term by half the sum of these energies. Therefore dominated convergence sends \(m\to\infty\) in both the entropy endpoints and the time-integrated flux. The result is local absolute continuity of actual KL and an entropy derivative almost everywhere. Averaging the Gaussian component score gives the mixture score, so the identity becomes</p>
\[H'(t)=-I_t+\mathbb E\langle\nabla U(Y_t)-\nabla U(X),S_t(Y_t)\rangle.\]
<p>The averaging is an integrable Fubini identity for the actual kernel; it does not require choosing a conditional drift jointly in time. Apply \(\langle a,b\rangle\le\|a\|^2+\|b\|^2/4\) and the sharp error energy:</p>
\[\boxed{H'(t)\le-\tfrac34I_t+t^2L^2G_0+2tdL^2}\quad\text{for almost every }t>0.\]
<p>This is sufficient for scalar integration. No pointwise entropy derivative at every time is assumed.</p><p>It is useful to keep the two limiting measures distinct. At a fixed endpoint time, the dominating function is the nonnegative entropy integrand \(r_t\log r_t-r_t+1\), integrated against Gibbs. For the time flux, the domination is instead a spacetime energy bound on one independent state-noise probability. Passing both limits in the integrated bounded-entropy identity yields</p>\[H(b)-H(a)=\int_a^b\left[-I_t+
\mathbb E\langle\nabla U(Y_t)-\nabla U(X),S_t(Y_t)\rangle\right]dt.\]<p>The integrand is integrable on every positive compact interval. This identity itself proves local absolute continuity and gives the derivative almost everywhere by the fundamental theorem of calculus. Applying Young's inequality spends exactly one quarter of \(I_t\); the remaining three quarters can still be converted into a strictly dissipative entropy term through LSI.</p>''',[
ref('UnadjustedLangevin/LSI/BoundedLog.lean','boundedEntropy_tendsto'),
ref('UnadjustedLangevin/LSI/GaussianEntropyIdentity.lean','interpolationEntropy_local_chain_rule'),
ref('UnadjustedLangevin/LSI/GaussianEntropyProduction.lean','interpolationEntropy_derivative_bound_ae')],
'The bounded tests, endpoint and flux limits, and positive-time entropy calculus are proved for the actual Gaussian density.'),

part('analytic-endpoints','Control the initial endpoint for every finite-entropy law',r'''<p>A one-sided entropy bound suffices to send \(a\downarrow0\); we can construct it directly without assuming an initial smooth density. Data processing for the same independent Gaussian transition gives</p>
\[\mathrm{KL}(\mu P_t\mid\nu P_t)\le\mathrm{KL}(\mu\mid\nu).\]
<p>For \(\delta=1-4tL>0\), set \(s=t/\delta\). The first-order smoothness estimate <cite data-report-ref="UnadjustedLangevin/Analysis/Smooth.lean" data-report-declaration="smooth_upper_bound"></cite> and gradient Lipschitzness yield the pointwise square-completion bound</p>
\[U(y)-U(x)-\frac{\|y-x+t\nabla U(x)\|^2}{4t}
\le-\frac{\|x-y+s\nabla U(y)\|^2}{4s}
+\frac s4\|\nabla U(y)\|^2.\]
<p>Integrate in \(x\). The ratio of Gaussian normalizers is \((s/t)^{d/2}=\delta^{-d/2}\), hence</p>
\[\frac{d(\nu P_t)}{d\nu}(y)\le\delta^{-d/2}
\exp\!\left(\frac t{4\delta}\|\nabla U(y)\|^2\right).\]
<p>The chain rule for log likelihood ratios, followed by the propagated gradient bound, proves</p>
\[H(t)\le M(t):=H(0)-\frac d2\log\delta
+\frac t{4\delta}\bigl[2(1+L^2t^2)G_0+4tdL^2\bigr].\]
<p>The proof establishes the needed likelihood-ratio integrability, including the negative part, before adding the entropies. The explicit majorant satisfies \(M(0)=H(0)\) and is continuous at zero. Consequently integrating any affine entropy differential inequality on \([a,h]\) and then sending \(a\downarrow0\) is valid. Finite initial KL is the only initial-law regularity assumption. The proof works directly for differentiable potentials with Lipschitz gradient, so no potential-smoothing limit is needed either.</p><p>To apply this endpoint control, suppose the positive-time comparison reads \(H'\le-aH+B\) with \(a>0\). Integration on \([s,h]\), where \(s>0\), gives</p>\[H(h)\le e^{-a(h-s)}H(s)+\frac Ba\bigl(1-e^{-a(h-s)}\bigr).\]<p>Insert \(H(s)\le M(s)\) and let \(s\downarrow0\). Continuity of \(M\) gives precisely the same formula with \(H(0)\) on the right. This argument requires an upper endpoint envelope rather than two-sided entropy continuity. It therefore accommodates every finite-entropy initial law covered by the theorem, while the density differentiations remain confined to strictly positive elapsed time.</p>''',[
ref('UnadjustedLangevin/LSI/GibbsInterpolationBound.lean','gibbs_frozen_exponent_le'),
ref('UnadjustedLangevin/LSI/InitialEntropy.lean','interpolationLaw_entropy_eventually_le_majorant'),
ref('UnadjustedLangevin/LSI/IntegratedEntropy.lean','affine_decay_of_local_ae_deriv_le')],
'The initial endpoint is a proved upper-envelope limit for the actual law, rather than a regularity field or an assumed approximation theorem.'),

part('one-step','Absorb the forcing and obtain the coefficient six',r'''<p>Combine LSI, the score moment, and production:</p>
\[H'\le-\tfrac32\alpha H+t^2L^2\left(\frac{4L^2}{\alpha}H(0)+2dL\right)+2tdL^2.\]
<p>From \(h\le\alpha/(4L^2)\) and \(\alpha\le L\), we have \(hL\le1/4\) and \(\alpha h\le1/4\). In particular,</p>
\[h^2L^2\frac{4L^2}{\alpha}\le\frac\alpha4,\qquad
h^2L^2(2dL)\le\tfrac12hdL^2.\]
<p>Thus the forcing for \(0&lt;t&lt;h\) is at most \(B=\alpha H(0)/4+(5/2)hdL^2\). Local absolute continuity permits multiplication by the integrating factor and integration from \(a>0\). The continuous initial majorant just proved permits \(a\downarrow0\), giving</p>
\[H(h)\le e^{-3\alpha h/2}H(0)+\frac B{3\alpha/2}(1-e^{-3\alpha h/2})
\le e^{-3\alpha h/2}H(0)+Bh.\]
<p>For \(0\le x\le1/4\), \(e^{-x}\ge e^{-3x/2}+x/4\). Apply this with \(x=\alpha h\), multiply by nonnegative \(H(0)\), and absorb its forcing contribution. The remaining \((5/2)h^2dL^2\) is at most \(6h^2dL^2\). Therefore</p>
\[\boxed{H_\nu(\mu P_h)\le e^{-\alpha h}H_\nu(\mu)+6h^2dL^2.}\]
<p>The scalar comparison needs derivatives only almost everywhere and no density extension through zero.</p><p>The signs used in absorption are part of the comparison. Nonnegative KL allows multiplication of the exponential-gap estimate by \(H(0)\), and nonnegative \(B\) allows the forcing kernel to be bounded by its interval length. Explicitly,</p>\[\int_0^he^{-(3\alpha/2)(h-t)}Bdt\le Bh
=\frac{\alpha h}{4}H(0)+\frac52h^2dL^2.\]<p>The first term is paid for by replacing \(e^{-3\alpha h/2}\) with the slower factor \(e^{-\alpha h}\). The second is a genuine discretization error, retained as the additive forcing in the discrete recurrence. The coefficient six is a convenient enlargement of \(5/2\); the proof makes no claim that this intermediate coefficient is optimal.</p>''',[
ref('UnadjustedLangevin/LSI/IntegratedEntropy.lean','one_step_entropy_of_ae_interpolation')],
'Every analytic premise of this scalar lemma is supplied by the actual-law results above in the final theorem.'),

part('iteration','Prove finite KL at every iterate and sum the recurrence',r'''<p>Finite KL at each iterate is proved first by induction: finite current KL gives a square-integrable gradient, the Gaussian Fisher estimate gives finite relative Fisher after a positive step, and LSI then gives finite next KL. Thus the real-valued sequence \(H_k\) faithfully represents the actual divergences.</p>
<p>Write \(q=e^{-\alpha h}\), \(c=6h^2dL^2\). The actual one-step estimate and the finite-horizon affine recurrence <cite data-report-ref="UnadjustedLangevin/Recurrence.lean" data-report-declaration="affine_recurrence_exact"></cite> imply</p>
\[H_k\le q^kH_0+c\frac{1-q^k}{1-q}.\]
<p>For \(0\le x\le1/4\), the exponential tangent bound gives</p>
\[1-e^{-x}\ge\frac{x}{1+x}\ge\tfrac34x.\]
<p>Use \(x=\alpha h\), discard \(1-q^k\le1\), and simplify:</p>
\[\frac{6h^2dL^2}{1-e^{-\alpha h}}\le\frac{8hdL^2}{\alpha}.\]
<p>This proves the displayed convergence bound with the original potential, actual independent-Gaussian ULA laws, and every finite-KL initial probability law. The final theorem assumes smoothness, LSI, the step restriction, and finite initial KL. All density, moment, weak-equation, entropy-regularity, compatibility, and recurrence facts have been proved within its dependency chain.</p><p>The induction can be written in its exact finite-horizon form. Starting from \(H_0\), each insertion of \(c\) is damped once for every remaining transition. The geometric-sum form <cite data-report-ref="UnadjustedLangevin/Recurrence.lean" data-report-declaration="affine_recurrence_sum"></cite> is</p>\[H_k\le e^{-\alpha hk}H_0+
6h^2dL^2\sum_{j=0}^{k-1}e^{-\alpha hj}.\]<p>The geometric denominator is strictly positive because both \(\alpha\) and \(h\) are positive. Its lower bound is proportional to \(h\), turning the local \(h^2\) error into a global \(h\) floor. At fixed step, increasing \(k\) removes only the initial-entropy contribution. Reducing the asymptotic floor requires a smaller step; the separate dependences on dimension, smoothness, and LSI constant remain explicit.</p>''',[
ref('UnadjustedLangevin/LSI/UnconditionalTheorem.lean','ula_kl_finite'),
ref('UnadjustedLangevin/LSI/DiscreteEntropy.lean','discrete_entropy_recurrence_bound')],
'The final axiom audit checks the complete dependency chain against Lean’s standard logical axioms.')
]


IPLA_STATEMENT=r'''<p>Let \(N\ge1\), \(D=d_\theta+Nd_x\), assume \(D\ge1\), and let the joint potential \(U(\theta,x)\) have an \(L\)-Lipschitz gradient with \(L>0\). In scaled coordinates set</p>
\[z=(\theta,x^1/\sqrt N,\ldots,x^N/\sqrt N),\qquad
V_N(z)=\sum_{i=1}^NU(\theta,\sqrt N z_i),\quad
\Pi_N(dz)\propto e^{-V_N(z)}dz.\]
<p>The target is the Gibbs law of the lifted potential under the established target identity <cite data-report-ref="IPLA/Foundations.lean" data-report-declaration="gibbsTarget_eq_gibbsMeasure"></cite>. Assume an LSI with constant \(\beta_N>0\) for this actual lifted target. The positive-dimensional compatibility result <cite data-report-ref="UnadjustedLangevin/LSI/Compatibility.lean" data-report-declaration="logSobolev_constant_le_smoothness"></cite> gives \(\beta_N\le NL\); the final theorem derives this compatibility from its stated assumptions. For finite initial joint entropy and</p>
\[0&lt;\gamma\le\frac{\beta_N}{4NL^2},\]
<p>the IPLA laws \(\mu_k\), equivalently ULA for \(V_N\) at step \(\gamma/N\) by the established algorithm-law identity <cite data-report-ref="IPLA/ULAAdapter.lean" data-report-declaration="laws_eq_ulaLawStep"></cite>, satisfy</p>
\[\frac{H_{\Pi_N}(\mu_k)}N\le
e^{-\beta_N\gamma k/N}\frac{H_{\Pi_N}(\mu_0)}N
+\frac{8\gamma DL^2}{\beta_N}.\]
<p>In particular, if the lifted target has the admissible constant \(\beta_N=N\alpha\), then</p>
\[\boxed{\frac{H_{\Pi_N}(\mu_k)}N\le
e^{-\alpha\gamma k}\frac{H_{\Pi_N}(\mu_0)}N
+\frac{8\gamma L^2}{\alpha}\left(d_x+\frac{d_\theta}N\right).}\]
<p>The condition is now \(0&lt;\gamma\le\alpha/(4L^2)\). An LSI for the original pair target is not substituted for the lifted-target hypothesis. The result derives all interpolation estimates from the shared ULA entropy theorem <cite data-report-ref="UnadjustedLangevin/LSI/UnconditionalTheorem.lean" data-report-declaration="ula_kl_bound"></cite> and finite initial joint KL. If \(D=0\), both laws are the unique point mass and their entropy is zero.</p>'''


IPLA_PROOF=[
part('lift','The geometry fixes the dimension, gradient constant, and step',r'''<p>Each physical pair \((\theta,x^i)\) is extracted from the scaled state by \((\theta,\sqrt N z_i)\). The two gradient-block formulas <cite data-report-ref="IPLA/Geometry.lean" data-report-declaration="gradient_potential_parameter"></cite> show that differentiating the lifted sum gives the averaged parameter drift and ordinary latent drifts at step \(\gamma/N\). The corresponding Euclidean state has</p>
\[D=d_\theta+Nd_x,\qquad L_N=NL,\qquad h_N=\gamma/N.\]
<p>The dimension identity is the coordinate-space dimension formula <cite data-report-ref="IPLA/Geometry.lean" data-report-declaration="finrank_state"></cite>. The parameter block of the lifted gradient is a sum over particles; each latent block contributes a factor \(\sqrt N\). Squaring and summing the blocks, then applying Cauchy–Schwarz to the common-parameter sum, proves the gradient Lipschitz constant \(NL\) <cite data-report-ref="IPLA/Geometry.lean" data-report-declaration="potential_gradient_lipschitz"></cite>. The coordinate Gaussian laws and independence identify the actual noise-driven IPLA law with this ULA transition <cite data-report-ref="IPLA/ULAAdapter.lean" data-report-declaration="laws_eq_ulaLawStep"></cite>. No equality between \(d_\theta\) and \(d_x\) is needed.</p><p>The scaling can also be verified directly in physical coordinates. The parameter component of a step is the previously established physical parameter update <cite data-report-ref="IPLA/Geometry.lean" data-report-declaration="scaledUpdate_parameter"></cite>:</p>\[\theta_{k+1}=\theta_k-\frac\gamma N\sum_i\nabla_\theta U(\theta_k,x_k^i)
+\sqrt{\frac{2\gamma}{N}}Z_k^\theta.\]<p>For the latent block, multiply the scaled update by \(\sqrt N\); the physical latent update <cite data-report-ref="IPLA/Geometry.lean" data-report-declaration="scaledUpdate_particle"></cite> is</p>\[x_{k+1}^i=x_k^i-\gamma\nabla_xU(\theta_k,x_k^i)+\sqrt{2\gamma}Z_k^i.\]<p>Thus the lifted Gaussian transition is exactly the intended particle algorithm, with the same joint innovation law. The dimension \(D\) counts all coordinates of that joint state, and the full joint entropy is the natural input to the shared ULA entropy theorem <cite data-report-ref="UnadjustedLangevin/LSI/UnconditionalTheorem.lean" data-report-declaration="ula_kl_bound"></cite>.</p>''',[
ref('IPLA/LSI/Theorem.lean','particleLaws_eq_laws')],
'The lifted geometry and identification with the actual Gaussian particle algorithm are checked.'),
part('step','Apply the ULA one-step estimate with the lifted target',r'''<p>Apply the ULA one-step entropy theorem <cite data-report-ref="UnadjustedLangevin/LSI/UnconditionalTheorem.lean" data-report-declaration="ula_kl_one_step"></cite> to \((V_N,\Pi_N)\), with constant \(\beta_N\), dimension \(D\), smoothness \(NL\), and step \(\gamma/N\). Its step restriction becomes</p>
\[\frac\gamma N\le\frac{\beta_N}{4(NL)^2}
\quad\Longleftrightarrow\quad
\gamma\le\frac{\beta_N}{4NL^2}.\]
<p>The one-step forcing simplifies without losing a particle factor:</p>
\[6h_N^2D L_N^2=6(\gamma/N)^2D(NL)^2=6\gamma^2DL^2.\]
<p>Consequently the unnormalized joint entropy obeys</p>
\[H_{k+1}\le e^{-\beta_N\gamma/N}H_k+6\gamma^2DL^2.\]
<p>The lifted LSI assumption includes probability normalization of the Gibbs target <cite data-report-ref="UnadjustedLangevin/LSI/FunctionalInequality.lean" data-report-declaration="IsLogSobolev"></cite>. The shared finiteness theorem <cite data-report-ref="UnadjustedLangevin/LSI/UnconditionalTheorem.lean" data-report-declaration="ula_kl_finite"></cite> supplies finite KL before the one-step theorem is applied and its rescaled constants are simplified. Every analytic input is supplied by the actual Gaussian ULA construction.</p><p>The product \(\beta_Nh_N\) equals \(\beta_N\gamma/N\), which fixes the rate in the one-step exponential. The numerical step condition also yields \(\beta_N\gamma/N\le1/4\) through the lifted compatibility inequality <cite data-report-ref="UnadjustedLangevin/LSI/Compatibility.lean" data-report-declaration="logSobolev_constant_le_smoothness"></cite>. Hence the geometric-denominator estimate <cite data-report-ref="UnadjustedLangevin/LSI/DiscreteEntropy.lean" data-report-declaration="three_quarters_mul_le_one_sub_exp_neg"></cite> used in the ULA proof is available with the rescaled constants, without losing a particle factor.</p><p>The recurrence is for the unnormalized joint divergence. The additive term has no remaining factor \(N^{-1}\) because the squared step contributes \(N^{-2}\) and the squared lifted smoothness contributes \(N^2\). Normalization by \(N\) is postponed until the complete joint inequality has been derived.</p>''',[
ref('UnadjustedLangevin/LSI/UnconditionalTheorem.lean','ula_kl_one_step')],
'The particle substitution and scalar algebra use the shared ULA proof from smoothness, LSI, and finite initial KL.'),
part('normalization','Normalize by the particle number only after deriving the joint bound',r'''<p>The shared full ULA entropy theorem <cite data-report-ref="UnadjustedLangevin/LSI/UnconditionalTheorem.lean" data-report-declaration="ula_kl_bound"></cite> gives the unnormalized floor after the lifted substitution:</p>
\[\frac{8h_NDL_N^2}{\beta_N}
=\frac{8\gamma NDL^2}{\beta_N}.\]
<p>Divide the entire inequality by positive \(N\), including the initial entropy and the floor. This proves</p>
\[\frac{H_k}N\le e^{-\beta_N\gamma k/N}\frac{H_0}N
+\frac{8\gamma DL^2}{\beta_N}.\]
<p>Now, and only under the separate lifted-target assumption \(\beta_N=N\alpha\), use \(D/N=d_x+d_\theta/N\). The rate is \(e^{-\alpha\gamma k}\), and the per-particle floor is \((8\gamma L^2/\alpha)(d_x+d_\theta/N)\). Shared parameter coordinates prevent a direct tensorization argument from a pair LSI; the target for which LSI is assumed remains \(\Pi_N\).</p><p>The normalization is a scalar division of an already established inequality, not a change of reference measure. Under \(\beta_N=N\alpha\), substitute \(D=d_\theta+Nd_x\) only after the division:</p>\[\frac{8\gamma DL^2}{N\alpha}
=\frac{8\gamma L^2}{\alpha}\left(\frac{d_\theta}{N}+d_x\right).\]<p>This exposes two distinct dimension contributions. The shared parameter dimension is amortized over particles, while the latent dimension contributes once per particle and survives in the normalized floor. The assumption \(\beta_N=N\alpha\) concerns the interacting lifted target; shared coordinates mean it cannot be inferred by independent tensorization of unrelated pair laws.</p>''',[
ref('IPLA/LSI/UnconditionalTheorem.lean','particle_kl_bound_normalized_of_finite_kl'),
ref('IPLA/LSI/UnconditionalTheorem.lean','particle_kl_bound_linear_lsi_of_finite_kl')],
'The general lifted-constant bound, division by N, and linear-LSI specialization are checked with their assumptions visible.'),
part('parameter','Project to the parameter marginal using data processing',r'''<p>Let \(P_\theta\) be the continuous linear parameter projection <cite data-report-ref="IPLA/Geometry.lean" data-report-declaration="parameterCLM"></cite>, \(\mu_k^\theta=P_{\theta\#}\mu_k\), and \(\Pi_N^\theta=P_{\theta\#}\Pi_N\). Relative entropy decreases under a measurable map:</p>
\[H_{\Pi_N^\theta}(\mu_k^\theta)\le H_{\Pi_N}(\mu_k).\]
<p>This controls the unnormalized parameter KL. In particular, under \(\beta_N=N\alpha\),</p>
\[H_{\Pi_N^\theta}(\mu_k^\theta)
\le e^{-\alpha\gamma k}H_{\Pi_N}(\mu_0)
+\frac{8\gamma NL^2}{\alpha}\left(d_x+\frac{d_\theta}N\right).\]
<p>The initial entropy remains the full joint entropy. Data processing does not allow it to be replaced by the smaller initial parameter entropy on the right. Likewise, a normalized joint bound must be multiplied by \(N\) before it bounds the unscaled parameter KL. The proof establishes finite joint KL, transfers finiteness to the marginal, and then compares their ordinary finite values.</p><p>For a density-based view of data processing, let \(R=d\mu_k/d\Pi_N\). The density of the parameter marginal is the conditional mean \(\mathbb E_{\Pi_N}[R\mid\theta]\). Convexity of \(u\log u\) and conditional Jensen therefore give</p>\[\int\mathbb E[R\mid\theta]\log\mathbb E[R\mid\theta]d\Pi_N
\le\int R\log R\,d\Pi_N.\]<p>This proves the marginal inequality with the original, unnormalized joint entropy on the right. There is no factor \(N^{-1}\) in data processing itself. A bound for entropy per particle must consequently be multiplied by \(N\) before being used as a bound on the ordinary parameter marginal KL.</p>''',[
ref('IPLA/LSI/UnconditionalTheorem.lean','parameter_kl_bound_of_finite_kl')],
'The parameter data-processing argument and all normalization factors are checked. This conclusion concerns a probability marginal, not distance to a likelihood maximizer.'),
]


ENTROPY_CONFIG={
 'UnadjustedLangevin/LSI':dict(label='Entropy convergence · Log-Sobolev inequality',
  title='Unadjusted Langevin under LSI',namespace='ULA.LSI',
  subtitle='An entropy-contraction theorem from smoothness, LSI, and finite initial relative entropy.',
  status='The actual Gaussian ULA theorem derives its density regularity, entropy identity, score moments, initial endpoint, and compatibility of constants from the stated assumptions. Finite KL at every iterate is part of the checked conclusion.',
  formal_note='The adjacent statement is the complete actual-law theorem. Its finite-KL conclusion guards every real-valued entropy in the estimate. No interpolation data or moment bound is assumed.',
  archive='UnadjustedLangevin/LSI/exposition/proof.html',archive_label='Detailed source-by-source proof and reference audit',
  extra=[('UnadjustedLangevin/exposition/index.html','ULA under Strong Convexity'),('IPLA/LSI/exposition/index.html','Interacting Particle Langevin under LSI')],
  results=[dict(title='KL convergence of the Gaussian ULA algorithm',file='UnadjustedLangevin/LSI/UnconditionalTheorem.lean',name='ula_kl_bound',body=ULA_STATEMENT)],
  proof=ULA_PROOF,
  diagram=[node('compatibility',0,0,'UnadjustedLangevin/LSI/Compatibility.lean','Derive compatibility from LSI',r'Bounded sinusoidal tests give \(\alpha\le L\)'),
           node('moment',0,1,'UnadjustedLangevin/LSI/EntropyMoment.lean','Derive the gradient moment','Finite KL and the Gibbs score MGF'),
           node('density',0,2,'UnadjustedLangevin/LSI/GaussianEntropy.lean','Construct density and finite Fisher',r'Positive \(C^1\) Gaussian mixture'),
           node('initial',1,0,'UnadjustedLangevin/LSI/InitialEntropy.lean','Prove the initial entropy endpoint','Data processing and a continuous majorant',('moment',)),
           node('weak',1,1,'UnadjustedLangevin/LSI/GaussianWeakEquation.lean','Prove the actual weak equation','Gaussian kernel derivatives and integrable flux',('density',)),
           node('energy',1,2,'UnadjustedLangevin/LSI/GaussianEnergyIntegrability.lean','Control spacetime energies','Finite Fisher and sharp drift-error bounds',('moment','density')),
           node('identity',2,0,'UnadjustedLangevin/LSI/GaussianEntropyIdentity.lean','Derive the full entropy identity','Bounded logarithmic tests and dominated limits',('weak','energy')),
           node('production',2,1,'UnadjustedLangevin/LSI/GaussianEntropyProduction.lean','Prove entropy production',r'Average scores; retain \(3/4\) of Fisher',('identity','energy')),
           node('scalar',3,0,'UnadjustedLangevin/LSI/IntegratedEntropy.lean','Obtain the one-step estimate','Local absolute continuity; coefficient 6',('initial','production','compatibility')),
           node('iteration',3,1,'UnadjustedLangevin/LSI/DiscreteEntropy.lean','Iterate and bound the error floor','Geometric sum; coefficient 8',('scalar',)),
           node('endpoint',4,1,'UnadjustedLangevin/LSI/UnconditionalTheorem.lean','Full actual Gaussian ULA bound','Smoothness, LSI, finite initial KL',('iteration','density'),True)]),
 'IPLA/LSI':dict(label='Particle entropy · Lifted-target LSI',
  title='Interacting Particle Langevin under LSI',namespace='IPLA.LSI',
  subtitle='Joint entropy, per-particle scaling, and the parameter marginal.',
  status='The lifted-target entropy bound follows from the full actual Gaussian ULA proof and finite initial joint KL. The LSI hypothesis concerns the actual lifted target; all interpolation and moment estimates are derived.',
  formal_note='The adjacent theorem assumes the lifted-target LSI and finite initial joint KL. No regular interpolation data or compatibility premise is supplied. Parameter and latent dimensions are independent.',
  archive='IPLA/LSI/exposition/proof.html',archive_label='Detailed particle-entropy proof and normalization audit',
  extra=[('IPLA/exposition/index.html','IPLA under Strong Convexity'),('UnadjustedLangevin/LSI/exposition/index.html','Shared ULA entropy argument')],
  results=[dict(title='Joint KL bound and the linear lifted-LSI specialization',file='IPLA/LSI/UnconditionalTheorem.lean',name='particle_kl_bound_linear_lsi_of_finite_kl',body=IPLA_STATEMENT)],
  proof=IPLA_PROOF,
  diagram=[node('geometry',0,0,'IPLA/Geometry.lean','Rescale the particle geometry',r'\(D=d_\theta+Nd_x\); smoothness \(NL\)'),
           node('laws',0,1,'IPLA/LSI/Theorem.lean','Identify the actual particle laws',r'ULA step \(\gamma/N\)'),
           node('shared',0,2,'UnadjustedLangevin/LSI/UnconditionalTheorem.lean','Use the full ULA entropy proof','Smoothness, lifted-target LSI, finite KL'),
           node('scaling',1,0,'IPLA/LSI/Scaling.lean','Track step and rate factors',r'Rate \(\beta_N\gamma/N\); forcing \(6\gamma^2DL^2\)',('geometry',)),
           node('joint',1,1,'IPLA/LSI/UnconditionalTheorem.lean','Derive full joint entropy bound','Unnormalized and per-particle forms',('laws','shared','scaling')),
           node('marginal',1,2,'IPLA/LSI/Marginal.lean','Apply KL data processing','Measurable parameter projection'),
           node('linear',2,0,'IPLA/LSI/Scaling.lean','Specialize the LSI scaling',r'\(\beta_N=N\alpha\); bias uses \(d_x+d_\theta/N\)',('scaling',)),
           node('final',2,1,'IPLA/LSI/UnconditionalTheorem.lean','Parameter-marginal consequence','Retain full initial joint entropy',('joint','marginal','linear'),True)])
}
