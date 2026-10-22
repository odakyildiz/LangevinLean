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
\qquad 0<h\le\frac{\alpha}{4L^2},\]
<p>the laws \(\rho_k=\operatorname{Law}(X_k)\) satisfy, for every \(k\ge0\),</p>
\[\boxed{H_\nu(\rho_k)\le e^{-\alpha hk}H_\nu(\rho_0)+\frac{8hdL^2}{\alpha}.}\]
<p>This is the KL estimate of <a href="https://www.cs.yale.edu/homes/wibisono/VW19.pdf">Vempala–Wibisono (2019), Theorem 2</a>. The first term is the initial entropy contracted at an exponential rate. The second is the discretization floor. Convexity of \(U\) is not assumed. The proof uses the compatible inequality \(\alpha\le L\), derived below in positive dimension. If the initial entropy is infinite the extended-valued inequality is immediate; the finite case is the substantive assertion.</p>'''


ULA_PROOF=[
part('entropy','Relative density, Fisher information, and the LSI normalization',r'''<p>Write \(r=d\rho/d\nu\). For a positive differentiable relative density with \(\int r\,d\nu=1\),</p>
\[H_\nu(\rho)=\int r\log r\,d\nu,\qquad
I_\nu(\rho)=\int r\|\nabla\log r\|^2d\nu.\]
<p>The function formulation of LSI is \(\operatorname{Ent}_\nu(g^2)\le(2/\alpha)\int\|\nabla g\|^2d\nu\). Substituting \(g=\sqrt r\), using \(\nabla\sqrt r=(\sqrt r/2)\nabla\log r\), gives exactly \(2\alpha H\le I\). Conversely substitute \(r=g^2/\int g^2d\nu\), first for positive smooth \(g\), then use truncation and a positive regularization.</p>
<p>In Lean, <code>tiltedMeasure</code> is the measure \(r\nu\), and <code>relativeFisher</code> is an extended nonnegative integral. The KL divergence is Mathlib’s actual <code>klDiv</code>. The Radon–Nikodym derivative is identified before replacing KL by \(\int r\log r\). Finiteness is proved before taking <code>toReal</code>; infinity is never interpreted as zero entropy.</p>''',[
ref('UnadjustedLangevin/LSI/FunctionalInequality.lean','IsLogSobolev'),
ref('UnadjustedLangevin/LSI/KLOfDensity.lean','densityEntropy_eq_integral')],
'The KL/Fisher definitions and finite-density identities are checked. The Lean LSI definition uses the positive C¹ density test class; approximation to the full classical test class is an additional analytic step.'),

part('functional-consequences','The functional-inequality consequences used by the proof',r'''<p>Three consequences of LSI and smoothness control the moments. Their constants matter, because they determine the allowed step size.</p>
<p><strong>Gaussian tails.</strong> For a bounded 1-Lipschitz function \(F\), set \(\Lambda(s)=\log\int e^{s(F-\nu F)}d\nu\). Applying LSI to \(e^{sF/2}\) gives</p>
\[s\Lambda'(s)-\Lambda(s)\le\frac{s^2}{2\alpha},\qquad
\left(\frac{\Lambda(s)}s\right)'\le\frac1{2\alpha}.\]
<p>Since \(\Lambda(0)=\Lambda'(0)=0\), integration yields \(\Lambda(s)\le s^2/(2\alpha)\). Truncate the distance function before applying this argument. A fixed ball of mass at least one half bounds its medians uniformly, so the resulting tail estimate passes to the unbounded distance function. Consequently \(\nu\) has a finite exponential square moment for a sufficiently small positive coefficient. The entropy variational inequality</p>
\[\int F\,d\rho\le H_\nu(\rho)+\log\int e^F d\nu\]
<p>then implies that every finite-entropy \(\rho\) has a finite second moment. The inequality itself follows by nonnegativity of KL relative to the probability density proportional to \(e^F\) with respect to \(\nu\).</p>
<p><strong>The equilibrium score moment.</strong> For a smooth potential, integrate \(\operatorname{div}(e^{-U}\nabla U)\) with compact cutoffs and let their radius tend to infinity. The tail estimate and linear growth of \(\nabla U\) justify the limit. Thus</p>
\[\int\|\nabla U\|^2d\nu=\int\Delta U\,d\nu\le dL.\]
<p>The shared Lean proof obtains this bound by translation invariance of the partition function and a sub-Gaussian estimate for each score coordinate; it requires no strong convexity.</p>
<p><strong>Compatibility of constants.</strong> Expanding LSI at \(g=1+\varepsilon f\) gives the Poincaré inequality \(\alpha\operatorname{Var}_\nu(f)\le\int\|\nabla f\|^2d\nu\). For a coordinate \(x_j\), integration by parts gives</p>
\[1=\int(x_j-\nu x_j)\partial_jU\,d\nu,\qquad
\int(\partial_jU)^2d\nu=\int\partial_{jj}U\,d\nu\le L.\]
<p>Cauchy–Schwarz implies \(\operatorname{Var}(x_j)\ge1/L\), while Poincaré gives \(\operatorname{Var}(x_j)\le1/\alpha\). Therefore \(\alpha\le L\). Truncation justifies using a coordinate as a test. The differentiable, Lipschitz-gradient case follows by the smoothing argument at the end of the proof.</p>''',[
ref('UnadjustedLangevin/GibbsScore.lean','integral_norm_sq_gradient_gibbs_le'),
ref('UnadjustedLangevin/GibbsScore.lean','memLp_gradient_gibbsMeasure')],
'The equilibrium score moment is checked in Lean. The general LSI tail argument, Poincaré consequence, and derivation of α ≤ L are mathematical arguments here; the current Lean endpoint still lists compatibility explicitly.'),

part('transport','From LSI to transport, then to the current gradient moment',r'''<p>We first derive the transport estimate needed below, the <a href="https://www.sciencedirect.com/science/article/pii/S0022123699935577">Otto–Villani implication from LSI to quadratic transport</a>. Let \(\sigma_s\) be the Langevin evolution from a smooth finite-entropy law \(\sigma\), and write \(E(s)=H_\nu(\sigma_s)\). Global Lipschitzness of the drift constructs this nonexplosive diffusion by Picard iteration; its second moments stay finite by the quadratic moment inequality and Gronwall. At positive times its density solves the Langevin equation. The entropy cutoff chain rule proved below, now with zero drift error, gives its entropy identity. Its continuity equation gives</p>
\[E'(s)=-I_\nu(\sigma_s),\qquad
v_s=-\nabla\log(d\sigma_s/d\nu),\qquad
\|v_s\|_{L^2(\sigma_s)}=\sqrt{I_\nu(\sigma_s)}.\]
<p>A continuity equation with this velocity has transport length at most \(\int\|v_s\|_2ds\). To see the estimate for a smooth compactly supported velocity, transport each point by its ODE flow, use that flow as a coupling of the endpoint laws, and apply Minkowski to the path integral. For the finite-energy form one uses the transport length theorem for continuity equations: a narrowly continuous probability curve with finite second moments and velocity in spacetime L² has \(W_2(\sigma_a,\sigma_b)\le\int_a^b\|v_s\|_{L^2(\sigma_s)}ds\). It follows by approximating the continuity equation with smooth positive densities and smooth velocities, applying the flow estimate, then taking lower limits of the coupling costs. This is the standard dynamical characterization of quadratic Wasserstein distance; this analytic theorem is not asserted as Lean code here. Applying LSI to \(E\),</p>
\[\begin{aligned}
\int_0^T\sqrt{I_\nu(\sigma_s)}\,ds
&\le\int_0^T\frac{-E'(s)}{\sqrt{2\alpha E(s)}}\,ds\\
&=\sqrt{\frac2\alpha}\bigl(\sqrt{E(0)}-\sqrt{E(T)}\bigr).
\end{aligned}\]
<p>Make this calculation on intervals where \(E>0\). If entropy reaches zero, nonnegativity of KL identifies that law with \(\nu\), and stationarity keeps it there; the remaining transport length is zero. Since \(E(T)\le e^{-2\alpha T}E(0)\), the curve is Cauchy in \(W_2\). Its weak limit is \(\nu\), because entropy tends to zero and Pinsker controls total variation. Completeness of the finite-second-moment space identifies the same limit in \(W_2\). Hence</p>
\[W_2(\sigma,\nu)^2\le\frac2\alpha H_\nu(\sigma).\]
<p>For a coupling \((A,B)\) of \(\rho\) and \(\nu\), Lipschitzness and \(\|a+b\|^2\le2\|a\|^2+2\|b\|^2\) imply</p>
\[\mathbb E\|\nabla U(A)\|^2
\le2L^2\mathbb E\|A-B\|^2+2\mathbb E\|\nabla U(B)\|^2.\]
<p>Take the infimum over couplings, then use the transport inequality and equilibrium score bound. No optimal coupling is required:</p>
\[\boxed{G_\rho:=\int\|\nabla U\|^2d\rho
\le\frac{4L^2}{\alpha}H_\nu(\rho)+2dL.}\]
<p>The tail argument ensures that these are finite real integrals. The same inequalities extend to finite-entropy initial laws by truncation and lower semicontinuity, as detailed in the final step.</p>''',[ref('UnadjustedLangevin/LSI/GradientMoment.lean','gibbs_gradient_moment_bound_of_entropy_coupling')],
'The coupling-to-gradient-moment calculation, including integrability and the exact coefficient, is checked below. The existence of a coupling with the entropy-cost bound is an explicit premise: LSI-to-transport is not yet formalized, and the main entropy endpoint still retains its gradient-moment hypothesis.'),

part('gaussian-law','Interpolate the actual Gaussian transition',r'''<p>Fix one step and write \(X\sim\rho_k\), independently of \(Z\sim\mathcal N(0,I_d)\). For \(0\le t\le h\), let</p>
\[Y_t=X-t\nabla U(X)+\sqrt{2t}\,Z,\qquad\rho_t=\operatorname{Law}(Y_t).\]
<p>At time zero this law is \(\rho_k\), and at time \(h\) it is \(\rho_{k+1}\). The interpolation is a pushforward of the product measure, so its Gaussian noise is independent by construction. Expanding the square and using the zero Gaussian mean gives</p>
\[\mathbb E\|Y_t-X\|^2=t^2G_k+2td,\qquad G_k=\mathbb E\|\nabla U(X)\|^2.\]
<p>Indeed, the cross term is \(-2t\sqrt{2t}\,\mathbb E\langle\nabla U(X),Z\rangle=0\), and \(\mathbb E\|Z\|^2=d\). Square integrability follows from the preceding gradient-moment estimate. Lipschitzness now yields</p>
\[\mathbb E\|\nabla U(Y_t)-\nabla U(X)\|^2
\le L^2(t^2G_k+2td).\]
<p>These are estimates for the actual transition, rather than a recurrence postulated for an arbitrary sequence of errors. In Lean the independent product and the pushforward are explicit in <code>interpolationLaw</code>.</p>''',[
ref('UnadjustedLangevin/LSI/ULALaw.lean','interpolationLaw_endpoint'),
ref('UnadjustedLangevin/LSI/GaussianDrift.lean','frozen_displacement_second_moment'),
ref('UnadjustedLangevin/LSI/GaussianDrift.lean','frozen_gradient_error_energy')],
'The actual-law endpoint identities, Gaussian moment calculation, and joint gradient-error bound are checked.'),

part('density-and-flux','The density and its state-dependent drift error',r'''<p>For \(t>0\), the interpolation has the strictly positive density</p>
\[p_t(y)=\int (4\pi t)^{-d/2}
\exp\left(-\frac{\|y-x+t\nabla U(x)\|^2}{4t}\right)\rho_k(dx).\]
<p>Integrating the Gaussian kernel over \(y\) proves normalization. For times in a compact subinterval of \((0,h]\), \(tL<1\) implies \(\|x-t\nabla U(x)\|\ge(1-tL)\|x\|-t\|\nabla U(0)\|\). On a bounded set of \(y\), derivatives of the Gaussian kernel are bounded by a polynomial in \(\|x\|\) times a decaying Gaussian. That envelope is bounded and hence integrable against the initial probability law. Differentiation under the integral gives spatial smoothness and the time derivative. With \(q=Z^{-1}e^{-U}\), set \(r_t=p_t/q\). Differentiating the Gaussian kernel and integrating by parts in \(y\) gives</p>
\[\partial_t p_t=\Delta p_t+\operatorname{div}(p_t b_t),\qquad
b_t(y)=\mathbb E[\nabla U(X)\mid Y_t=y].\]
<p>Define \(e_t(y)=\nabla U(y)-b_t(y)\). The conditional expectation is a genuine state-space function: take the conditional expectation with respect to \(\sigma(Y_t)\), then factor it through \(Y_t\). Conditional Jensen gives</p>
\[\int\|e_t\|^2d\rho_t
\le\mathbb E\|\nabla U(Y_t)-\nabla U(X)\|^2
\le L^2(t^2G_k+2td).\]
<p>The defining property of conditional expectation also identifies the flux: for every measurable state-dependent test vector \(a(Y_t)\) for which the joint pairing is integrable (in particular, for an L² test),</p>
\[\mathbb E\langle e_t(Y_t),a(Y_t)\rangle
=\mathbb E\langle\nabla U(Y_t)-\nabla U(X),a(Y_t)\rangle.\]
<p>Thus the error used in the density equation is exactly the conditional mean of the joint discrepancy whose energy was computed in the preceding step. The new Lean construction proves this factorization, integrability, energy transfer, and flux identity.</p>''',[
ref('UnadjustedLangevin/LSI/InterpolationDensity.lean','tiltedMeasure_interpolationRelativeDensity'),
ref('UnadjustedLangevin/LSI/ConditionalDrift.lean','exists_frozen_drift_error_of_density'),
ref('UnadjustedLangevin/LSI/ConditionalDrift.lean','conditional_mean_inner_integral')],
'The actual positive-time Gaussian-mixture density, its positivity, spatial continuity, and Gibbs-relative law identity are checked, as are conditional drift, Jensen, and integrable flux transfer. Spatial C¹/time regularity, entropy domination, and the admissible weak equation remain formalization obligations.'),

part('production','Differentiate entropy and retain three quarters of Fisher information',r'''<p>In relative-density notation, the frozen-drift equation becomes</p>
\[\partial_t(p_t)=\operatorname{div}(p_t\nabla\log r_t)-\operatorname{div}(p_te_t).\]
<p>For positive times, differentiate \(H(t)=\int r_t\log r_t\,d\nu\). Conservation of mass removes the integral of \(\partial_t r_t\); integrating the two divergence terms against \(1+\log r_t\) gives</p>
\[H'(t)=-I(t)+\int\langle e_t,\nabla\log r_t\rangle d\rho_t.\]
<p>The needed score energy is finite at positive time. Differentiating the mixture and conditioning the Gaussian noise gives</p>
\[\nabla\log p_t(Y_t)=-\frac{\mathbb E[Z\mid Y_t]}{\sqrt{2t}},\qquad
\int\|\nabla\log p_t\|^2d\rho_t\le\frac d{2t}.\]
<p>Consequently \(I(t)\le d/t+2\int\|\nabla U\|^2d\rho_t<\infty\). The last moment follows from Lipschitzness and the finite second moment of \(Y_t\). These estimates and the error bound are uniform on each \([\varepsilon,h]\), so the Fisher, error, and cross-term energies are integrable in time there.</p>
<p>Here is the cutoff chain rule behind the displayed differentiation. Choose smooth truncations \(\chi_M\) of the identity, bounded by \(M\), with \(0\le\chi_M'\le1\) and \(\chi_M'\to1\). Let \(\Phi_M'(r)=\chi_M(\log r)\) and \(\Phi_M(1)=0\), choosing the truncations so that \(\Phi_M\uparrow r\log r-r+1\). Test the smooth positive-time equation with \(\chi_M(\log r)\) times a spatial cutoff of radius \(R\). Its boundary term is bounded by \(CM/R\) times the \(L^1(\rho_t)\) flux norm, which is controlled by the two energy integrals. Send \(R\to\infty\) with \(M\) fixed. The interior identity has dissipation and cross term multiplied by \(\chi_M'(\log r)\). Send \(M\to\infty\) using monotone convergence for entropy and dominated convergence for the two flux energies. This proves the integrated entropy identity on \([\varepsilon,h]\), local absolute continuity, and the derivative formula for almost every positive time. This a.e. formula suffices for the integrating-factor argument. Entropy continuity supplies the initial endpoint.</p>
<p>Young’s inequality in the exact form \(\langle a,b\rangle\le\|a\|^2+\|b\|^2/4\) gives</p>
\[H'(t)\le-\frac34I(t)+\int\|e_t\|^2d\rho_t
\le-\frac34I(t)+t^2L^2G_k+2tdL^2.\]
<p>The finiteness of the two energy integrals also proves integrability of the cross term. This is why the formal argument establishes measurable integrable terms before applying the weak equation; integration by parts is not obtained by an unsupported symbolic rewrite.</p>''',[
ref('UnadjustedLangevin/LSI/Regularity.lean','densityEntropy_derivative_bound_of_regular_weak_equation')],
'Lean derives this production inequality from local density regularity and an admissible weak equation. Its application to the Gaussian mixture still requires the analytic density and entropy-test justification just described.'),

part('one-step','Absorb the discretization error and prove the one-step bound',r'''<p>Apply LSI, \(I(t)\ge2\alpha H(t)\), and the current-gradient estimate:</p>
\[H'(t)\le-\frac32\alpha H(t)+t^2L^2
\left(\frac{4L^2}{\alpha}H(0)+2dL\right)+2tdL^2.\]
<p>The step restriction and \(\alpha\le L\) imply \(hL\le1/4\) and \(\alpha h\le1/4\). Squaring \(hL^2\le\alpha/4\) gives</p>
\[h^2L^2\frac{4L^2}{\alpha}\le\frac\alpha4,
\qquad h^2L^2(2dL)\le\frac12hdL^2.\]
<p>Since \(0\le t\le h\), all forcing terms are bounded by the constant</p>
\[B=\frac\alpha4H(0)+\frac52hdL^2.\]
<p>Multiply \(H'+(3\alpha/2)H\le B\) by \(e^{3\alpha t/2}\) and integrate. Because \((1-e^{-ah})/a\le h\) for \(a>0\),</p>
\[H(h)\le e^{-3\alpha h/2}H(0)+Bh.\]
<p>For \(0\le x\le1/4\), \(e^{-3x/2}\ge1/2\) and \(e^{x/2}\ge1+x/2\). Multiplying these two inequalities in the needed order gives</p>
\[e^{-x}\ge e^{-3x/2}+x/4.\]
<p>Apply this with \(x=\alpha h\), multiply by \(H(0)\ge0\), and absorb the entropy part of \(Bh\). We obtain the slightly stronger forcing \((5/2)h^2dL^2\), which is at most the published convenient coefficient \(6\):</p>
\[\boxed{H_\nu(\rho_{k+1})\le e^{-\alpha h}H_\nu(\rho_k)+6h^2dL^2.}\]
<p>The Lean names <code>hcoeff</code>, <code>hnoise</code>, <code>huniform</code>, and <code>hbound</code> correspond respectively to the two coefficient estimates, the combined forcing, and the affine differential inequality. <code>exp_three_halves_gap</code> supplies the last absorption.</p>''',[
ref('UnadjustedLangevin/LSI/OneStep.lean','one_step_entropy_of_interpolation')],
'This scalar implication, including every displayed coefficient and the right-derivative comparison, is fully checked.'),

part('iteration','Iterate the recurrence and obtain the coefficient eight',r'''<p>Set \(q=e^{-\alpha h}\) and \(c=6h^2dL^2\). Then \(0<q<1\), and induction on \(k\) gives</p>
\[H_k\le q^kH_0+c\sum_{j=0}^{k-1}q^j
=e^{-\alpha hk}H_0+c\frac{1-e^{-\alpha hk}}{1-e^{-\alpha h}}.\]
<p>The denominator is positive. For \(0\le x\le1/4\), the elementary inequality \(e^x\ge1+x\) implies \(e^{-x}\le1/(1+x)\), hence</p>
\[1-e^{-x}\ge\frac{x}{1+x}\ge\frac34x.\]
<p>Taking \(x=\alpha h\), bounding \(1-e^{-\alpha hk}\le1\), and cancelling positive \(\alpha h\),</p>
\[\frac{6h^2dL^2}{1-e^{-\alpha h}}
\le\frac{6h^2dL^2}{3\alpha h/4}
=\frac{8hdL^2}{\alpha}.\]
<p>Substitution proves the stated theorem. The exact finite-horizon geometric expression is retained in a separate Lean theorem, so the coarser bias floor does not hide the underlying recurrence or its constants.</p>''',[
ref('UnadjustedLangevin/LSI/DiscreteEntropy.lean','discrete_entropy_recurrence_bound')],
'The exact recurrence, exponential power identity, denominator estimate, and final bias floor are checked.'),

part('analytic-endpoints','Initial endpoints and extension beyond smooth positive densities',r'''<p>The differentiations above can be made on \(t\in(0,h)\), then extended to \(t=0\). Here is an explicit route that avoids assuming a two-sided smooth density path at the initial time.</p>
<p><strong>Entropy continuity at zero.</strong> For a smooth initial density of finite entropy and second moment, the map \(T_t(x)=x-t\nabla U(x)\) is a diffeomorphism when \(tL<1\). Its Jacobian singular values are at least \(1-tL\). If \(S\) denotes differential entropy, change of variables and entropy concavity under independent Gaussian convolution give</p>
\[S(\rho_t)\ge S(T_{t\#}\rho_0)
\ge S(\rho_0)+d\log(1-tL).\]
<p>The smooth upper model for \(U\), the zero Gaussian mean, and the exact displacement moment give</p>
\[\mathbb EU(Y_t)\le\mathbb EU(X)+(-t+Lt^2/2)G_0+tdL.\]
<p>Since \(H_\nu(\rho)=-S(\rho)+\int U\,d\rho+\log Z\),</p>
\[\limsup_{t\downarrow0}H_\nu(\rho_t)\le H_\nu(\rho_0).\]
<p>The reverse inequality follows from lower semicontinuity of KL and \(\rho_t\Rightarrow\rho_0\). This proves endpoint continuity. Integrating the entropy inequality on \([\varepsilon,h]\) and sending \(\varepsilon\downarrow0\) is therefore valid.</p>
<p><strong>Approximate a finite-entropy initial law.</strong> If \(r=d\rho_0/d\nu\), truncate it to \(r_M=\min(M,\max(M^{-1},r))\), normalize with respect to \(\nu\), and then mollify this relative density for fixed \(M\). Renormalize once more with respect to \(\nu\). Mollification retains positive lower and finite upper bounds. Dominated convergence gives normalization and entropy convergence. The bound \(r_M\le r+1\), together with the finite second moments of \(\rho_0\) and \(\nu\), supplies the weighted domination that proves convergence of second moments. For fixed \(M\), bounded relative densities give the same weighted domination during mollification. Apply the smooth argument to these laws. For any fixed number of ULA steps, the Lipschitz transition preserves convergence in \(W_2\). Lower semicontinuity of output KL and convergence of initial KL pass the same inequality to \(\rho_0\).</p>
<p><strong>Approximate a Lipschitz-gradient potential.</strong> A symmetric mollification \(U_\varepsilon\) has the same gradient Lipschitz constant and satisfies \(\sup_x|U_\varepsilon(x)-U(x)|\le c_\varepsilon\to0\), by the smooth upper and lower models with the linear term cancelled. The perturbed Gibbs density has ratio in an interval \([a_\varepsilon,b_\varepsilon]\) with \(b_\varepsilon/a_\varepsilon\le e^{2c_\varepsilon}\). The entropy infimum formula</p>
\[\operatorname{Ent}_\nu(f^2)=\inf_{s>0}\int\bigl[f^2\log(f^2/s)-f^2+s\bigr]d\nu\]
<p>shows directly that the perturbed LSI constant is at least \(\alpha_\varepsilon=\alpha e^{-2c_\varepsilon}\): compare the nonnegative entropy integrand with \(b_\varepsilon d\nu\), apply LSI, then compare energies with \(a_\varepsilon d\nu\). Use \(h_\varepsilon=h\alpha_\varepsilon/\alpha\), so its step condition holds even at the original upper endpoint. The gradients converge uniformly, the finite-step ULA laws converge, initial entropies change by at most \(2c_\varepsilon\), and joint lower semicontinuity of KL passes to the stated constants as \(\varepsilon\to0\).</p>
<p>These approximation arguments complete the classical mathematical proof under differentiability, Lipschitz gradient, and LSI. In dimension zero both probability laws are the unique point mass and the entropy is zero. The remaining entropy-test, LSI-to-transport, and approximation formalizations are distinct from the density, conditional-drift, coupling, and scalar results already checked.</p>''',[ref('UnadjustedLangevin/LSI/InteriorEntropy.lean','affine_decay_of_deriv_le_interior'),ref('UnadjustedLangevin/LSI/InteriorEntropy.lean','densityEntropy_hasDerivAt_of_regular_interior')],
'These analytic endpoint and approximation arguments are not all formalized. The current Lean theorem therefore remains conditional on its explicit regular interpolation and gradient-moment hypotheses. The positive-time derivative bridge and endpoint-continuous scalar comparison are checked in InteriorEntropy.lean; they have not yet replaced the older main endpoint interface. The page does not claim an unconditional Lean LSI theorem.')
]


IPLA_STATEMENT=r'''<p>Let \(N\ge1\), \(D=d_\theta+Nd_x\), assume \(D\ge1\), and let the joint potential \(U(\theta,x)\) have an \(L\)-Lipschitz gradient with \(L>0\). In scaled coordinates set</p>
\[z=(\theta,x^1/\sqrt N,\ldots,x^N/\sqrt N),\qquad
V_N(z)=\sum_{i=1}^NU(\theta,\sqrt N z_i),\quad
\Pi_N(dz)\propto e^{-V_N(z)}dz.\]
<p>Assume an LSI with constant \(\beta_N>0\) for this actual lifted target. Compatibility gives \(\beta_N\le NL\) by the positive-dimensional argument on the shared ULA page; this compatibility is still an explicit premise of the Lean theorem. For finite initial joint entropy and</p>
\[0<\gamma\le\frac{\beta_N}{4NL^2},\]
<p>the IPLA laws \(\mu_k\), equivalently ULA for \(V_N\) at step \(\gamma/N\), satisfy</p>
\[\frac{H_{\Pi_N}(\mu_k)}N\le
e^{-\beta_N\gamma k/N}\frac{H_{\Pi_N}(\mu_0)}N
+\frac{8\gamma DL^2}{\beta_N}.\]
<p>In particular, if the lifted target has the admissible constant \(\beta_N=N\alpha\), then</p>
\[\boxed{\frac{H_{\Pi_N}(\mu_k)}N\le
e^{-\alpha\gamma k}\frac{H_{\Pi_N}(\mu_0)}N
+\frac{8\gamma L^2}{\alpha}\left(d_x+\frac{d_\theta}N\right).}\]
<p>The condition is now \(0<\gamma\le\alpha/(4L^2)\). An LSI for the original pair target is not substituted for the lifted-target hypothesis. The Lean result also retains the regular interpolation data required by the shared ULA entropy theorem. If \(D=0\), both laws are the unique point mass and their entropy is zero.</p>'''


IPLA_PROOF=[
part('lift','The geometry fixes the dimension, gradient constant, and step',r'''<p>Each physical pair \((\theta,x^i)\) is extracted from the scaled state by \((\theta,\sqrt N z_i)\). Differentiating the lifted sum gives the averaged parameter drift and ordinary latent drifts at step \(\gamma/N\). The corresponding Euclidean state has</p>
\[D=d_\theta+Nd_x,\qquad L_N=NL,\qquad h_N=\gamma/N.\]
<p>The parameter block of the lifted gradient is a sum over particles; each latent block contributes a factor \(\sqrt N\). Squaring and summing the blocks, then applying Cauchy–Schwarz to the common-parameter sum, proves the gradient Lipschitz constant \(NL\). The coordinate Gaussian laws and independence identify the actual noise-driven IPLA law with this ULA transition. No equality between \(d_\theta\) and \(d_x\) is needed.</p>''',[
ref('IPLA/LSI/Theorem.lean','particleLaws_eq_laws')],
'The lifted geometry and identification with the actual Gaussian particle algorithm are checked.'),
part('step','Apply the ULA one-step estimate with the lifted target',r'''<p>Apply the ULA entropy argument to \((V_N,\Pi_N)\), with constant \(\beta_N\), dimension \(D\), smoothness \(NL\), and step \(\gamma/N\). Its step restriction becomes</p>
\[\frac\gamma N\le\frac{\beta_N}{4(NL)^2}
\quad\Longleftrightarrow\quad
\gamma\le\frac{\beta_N}{4NL^2}.\]
<p>The one-step forcing simplifies without losing a particle factor:</p>
\[6h_N^2D L_N^2=6(\gamma/N)^2D(NL)^2=6\gamma^2DL^2.\]
<p>Consequently the unnormalized joint entropy obeys</p>
\[H_{k+1}\le e^{-\beta_N\gamma/N}H_k+6\gamma^2DL^2.\]
<p>The Lean proof constructs probability and finite-KL guards first, applies the shared one-step theorem, and then rewrites the rescaled constants. The one-step recurrence is a conclusion of the regularity interface, not a field of the particle data.</p>''',[
ref('IPLA/LSI/Theorem.lean','particle_kl_one_step')],
'The particle substitution and scalar algebra are checked. This inherits the explicit analytic assumptions of the shared ULA formalization.'),
part('normalization','Normalize by the particle number only after deriving the joint bound',r'''<p>Iteration gives the unnormalized floor</p>
\[\frac{8h_NDL_N^2}{\beta_N}
=\frac{8\gamma NDL^2}{\beta_N}.\]
<p>Divide the entire inequality by positive \(N\), including the initial entropy and the floor. This proves</p>
\[\frac{H_k}N\le e^{-\beta_N\gamma k/N}\frac{H_0}N
+\frac{8\gamma DL^2}{\beta_N}.\]
<p>Now, and only under the separate lifted-target assumption \(\beta_N=N\alpha\), use \(D/N=d_x+d_\theta/N\). The rate is \(e^{-\alpha\gamma k}\), and the per-particle floor is \((8\gamma L^2/\alpha)(d_x+d_\theta/N)\). Shared parameter coordinates prevent a direct tensorization argument from a pair LSI; the target for which LSI is assumed remains \(\Pi_N\).</p>''',[
ref('IPLA/LSI/Theorem.lean','particle_kl_bound_normalized'),
ref('IPLA/LSI/Theorem.lean','particle_kl_bound_of_linear_lsi')],
'The general lifted-constant bound, division by N, and linear-LSI specialization are checked with their assumptions visible.'),
part('parameter','Project to the parameter marginal using data processing',r'''<p>Let \(P_\theta\) be the parameter projection, \(\mu_k^\theta=P_{\theta\#}\mu_k\), and \(\Pi_N^\theta=P_{\theta\#}\Pi_N\). Relative entropy decreases under a measurable map:</p>
\[H_{\Pi_N^\theta}(\mu_k^\theta)\le H_{\Pi_N}(\mu_k).\]
<p>This controls the unnormalized parameter KL. In particular, under \(\beta_N=N\alpha\),</p>
\[H_{\Pi_N^\theta}(\mu_k^\theta)
\le e^{-\alpha\gamma k}H_{\Pi_N}(\mu_0)
+\frac{8\gamma NL^2}{\alpha}\left(d_x+\frac{d_\theta}N\right).\]
<p>The initial entropy remains the full joint entropy. Data processing does not allow it to be replaced by the smaller initial parameter entropy on the right. Likewise, a normalized joint bound must be multiplied by \(N\) before it bounds the unscaled parameter KL. The Lean proof establishes finite joint KL, transfers finiteness to the marginal, and only then compares the real values.</p>''',[
ref('IPLA/LSI/Corollaries.lean','parameter_kl_bound_of_linear_lsi')],
'The parameter data-processing argument and all normalization factors are checked. This conclusion concerns a probability marginal, not distance to a likelihood maximizer.'),
]


ENTROPY_CONFIG={
 'UnadjustedLangevin/LSI':dict(label='Entropy convergence · Log-Sobolev inequality',
  title='Unadjusted Langevin under LSI',namespace='ULA.LSI',
  subtitle='An entropy-contraction argument that does not require convexity.',
  status='The full mathematical argument is developed below. The current Lean theorem proves the bound from explicit analytic interpolation and moment hypotheses; an unconditional formal derivation from LSI and smoothness alone remains incomplete.',
  formal_note='The adjacent Lean endpoint has additional regularity, weak-equation, and gradient-moment hypotheses. Its exact statement is shown so that the scope of the checked proof can be compared with the mathematical theorem.',
  archive='UnadjustedLangevin/LSI/exposition/proof.html',archive_label='Detailed source-by-source proof and reference audit',
  extra=[('UnadjustedLangevin/exposition/index.html','ULA under Strong Convexity'),('IPLA/LSI/exposition/index.html','Interacting Particle Langevin under LSI')],
  results=[dict(title='KL convergence of the Gaussian ULA algorithm',file='UnadjustedLangevin/LSI/RegularizedTheorem.lean',name='ula_kl_bound_of_regular_interpolation',body=ULA_STATEMENT)],
  proof=ULA_PROOF,
  diagram=[node('lsi',0,0,'UnadjustedLangevin/LSI/FunctionalInequality.lean','Normalize LSI and Fisher information','2 α H ≤ I'),
           node('gaussian',0,1,'UnadjustedLangevin/LSI/GaussianDrift.lean','Compute Gaussian error energy','Exact independent-product moments'),
           node('density',0,2,'UnadjustedLangevin/LSI/InterpolationDensity.lean','Construct the actual density','Positive Gaussian mixture; Gibbs law'),
           node('moment',1,0,'UnadjustedLangevin/LSI/GradientMoment.lean','Transfer the gradient moment','From an entropy-cost coupling',('lsi',)),
           node('conditional',1,1,'UnadjustedLangevin/LSI/ConditionalDrift.lean','Construct the conditional drift','State factorization, Jensen, flux',('gaussian',)),
           node('regularity',1,2,'UnadjustedLangevin/LSI/Regularity.lean','Derive entropy production','From the displayed weak equation',('density',)),
           node('scalar',2,0,'UnadjustedLangevin/LSI/OneStep.lean','Prove the one-step estimate','Retain and absorb exact constants',('moment','conditional','regularity')),
           node('iteration',2,1,'UnadjustedLangevin/LSI/DiscreteEntropy.lean','Iterate and bound the error floor','Geometric sum; coefficient 8',('scalar',)),
           node('endpoint',3,1,'UnadjustedLangevin/LSI/RegularizedTheorem.lean','Assemble the checked KL bound','Analytic hypotheses remain explicit',('iteration','regularity'),True)]),
 'IPLA/LSI':dict(label='Particle entropy · Lifted-target LSI',
  title='Interacting Particle Langevin under LSI',namespace='IPLA.LSI',
  subtitle='Joint entropy, per-particle scaling, and the parameter marginal.',
  status='The lifted-target entropy bound and its projection are proved from the shared regular interpolation interface. The LSI hypothesis concerns the actual lifted target; the remaining analytic scope is the same as for ULA under LSI.',
  formal_note='The data argument contains the analytic interpolation hypotheses inherited from ULA. The lifted LSI, step restriction, and independent parameter/latent dimensions are separate assumptions.',
  archive='IPLA/LSI/exposition/proof.html',archive_label='Detailed particle-entropy proof and normalization audit',
  extra=[('IPLA/exposition/index.html','IPLA under Strong Convexity'),('UnadjustedLangevin/LSI/exposition/index.html','Shared ULA entropy argument')],
  results=[dict(title='Joint KL bound and the linear lifted-LSI specialization',file='IPLA/LSI/Theorem.lean',name='particle_kl_bound_of_linear_lsi',body=IPLA_STATEMENT)],
  proof=IPLA_PROOF,
  diagram=[node('geometry',0,0,'IPLA/Geometry.lean','Rescale the particle geometry','D = dθ + N dx; smoothness NL'),
           node('laws',0,1,'IPLA/LSI/Theorem.lean','Identify the actual particle laws','ULA step γ/N'),
           node('shared',0,2,'UnadjustedLangevin/LSI/InterpolationData.lean','Use the shared entropy argument','Lifted-target LSI and regularity'),
           node('scaling',1,0,'IPLA/LSI/Scaling.lean','Track step and rate factors','β γ/N; forcing 6 γ² D L²',('geometry',)),
           node('joint',1,1,'IPLA/LSI/Theorem.lean','Derive full joint entropy bound','Unnormalized and per-particle forms',('laws','shared','scaling')),
           node('marginal',1,2,'IPLA/LSI/Marginal.lean','Apply KL data processing','Measurable parameter projection'),
           node('linear',2,0,'IPLA/LSI/Scaling.lean','Specialize β = N α','Bias uses dx + dθ/N',('scaling',)),
           node('final',2,1,'IPLA/LSI/Corollaries.lean','Parameter-marginal consequence','Retain full initial joint entropy',('joint','marginal','linear'),True)])
}
