"""Mathematics of the supplied kinetic Langevin and KIPLMC manuscripts.

These authored reading notes describe the paper arguments. A part is not a
certificate that all its analytic steps are proved in Lean. The site must pair
it with the exact checked declarations and show each development's scope audit.
No source path under papers/ is needed by a published page.
"""


def part(identifier, title, body, references=(), note=''):
    return dict(id=identifier, title=title, body=body,
                references=list(references), note=note)


KINETIC_STATEMENT = r'''<p>Let \(f:\mathbb R^p\to\mathbb R\) be twice differentiable and satisfy
\(mI\preceq\nabla^2f(x)\preceq MI\), with \(0&lt;m\le M\). Write
\(\pi(dx)=Z^{-1}e^{-f(x)}dx\). With independent Gaussian initial velocity
\(v_0\sim\mathcal N(0,I_p)\), independent of \(x_0\sim\nu_0\), the first-order kinetic exponential integrator satisfies</p>
\[W_2(\nu_k,\pi)\le\sqrt2\left(1-\frac{3mh}{4\gamma}\right)^kW_2(\nu_0,\pi)
+\frac{Mh\sqrt{2p}}m,\qquad
\gamma\ge\sqrt{m+M},\quad0&lt;h\le\frac m{4\gamma M}.\]
<p>The transient term measures loss of the initial error; the term proportional
to \(h\) is the accumulated numerical bias. The manuscript also studies the
continuous kinetic diffusion and a distinct Hessian-corrected algorithm called
KLMC2. </p><p class="formal-note">The source audit records the scope of the compiled results.</p>'''


KINETIC_PROOF = [
part('target', r'''The kinetic equation and its Gibbs phase measure''', r'''<p>Let the target potential be \(f\): the target density is proportional to \(e^{-f}\). The kinetic process has a velocity variable and a position variable satisfying</p>
\[dV_t=-(\gamma V_t+\nabla f(L_t))dt+\sqrt{2\gamma}\,dW_t,
\qquad dL_t=V_tdt.\]
<p>The linear friction \(\gamma V_t\) removes kinetic energy. The noise amplitude gives a standard Gaussian equilibrium velocity.
The candidate equilibrium has density</p>
\[\Pi(dx,dv)=\pi(dx)\,\varphi(dv)
\propto e^{-f(x)-\|v\|^2/2}dx\,dv.\]
<p>Position and velocity are independent under this law. Integrating out velocity
therefore leaves precisely the desired target. Thus the position marginal of this phase measure is the target sampling distribution.</p>
<p>Strong convexity supplies a quadratic lower bound on \(f\), so the partition
function is finite and the required position moments exist (see <cite data-report-ref="UnadjustedLangevin/Gibbs.lean" data-report-declaration="gibbsPartition_ne_top"></cite>, <cite data-report-ref="UnadjustedLangevin/Gibbs.lean" data-report-declaration="memLp_id_gibbsMeasure"></cite>). A proof of
stationarity still needs a solution process and a valid invariance
argument; checking that a formal generator integrates to zero is one component
of that argument.</p><p>The kinetic extension is useful because position is the time integral of velocity even though velocity contains Brownian forcing. This extra time integration reduces the local positional discretization defect. At equilibrium, the Gaussian velocity radius is exactly \(\sqrt p\) in second mean, which determines the dimension factor in the first-order error theorem.</p>'''),

part('time-scale', r'''Normalization of inverse mass''', r'''<p>The general paper equation includes inverse mass \(u&gt;0\):
\(dV=-(\gamma V+u\nabla f(L))dt+\sqrt{2\gamma u}\,dW\).
Its equilibrium velocity has covariance \(uI\). Normalize both the velocity
and the time variable:</p>
\[\bar V_t=u^{-1/2}V_{t/\sqrt u},\qquad
\bar L_t=L_{t/\sqrt u},\qquad \bar\gamma=\gamma/\sqrt u.\]
<p>The position equation becomes \(d\bar L_t=\bar V_tdt\). Brownian scaling
turns \(u^{1/4}W_{t/\sqrt u}\) into a standard Brownian motion; substitution
in the velocity equation gives the same kinetic system with \(u=1\) and
friction \(\bar\gamma\). This is Lemma 1 in the supplied manuscript.</p>
<p>The scaling explains why the rest of the paper fixes \(u=1\): it removes
a redundant clock parameter. When transferring a theorem back to another mass,
the step size, friction, Gaussian velocity law and physical time must all be
transformed together.</p><p>To check the transformation, write the position increment as an integral before changing variables: \(L_{t/\sqrt u}-L_0=\int_0^{t/\sqrt u}V_sds=\int_0^tu^{-1/2}V_{r/\sqrt u}dr\). The velocity equation transforms similarly. This verifies the normalized equation for integral solutions, including its initial data, rather than only manipulating differential notation.</p>'''),

part('synchronous', r'''The difference equation under common Brownian forcing''', r'''<p>Consider two kinetic solutions with different initial positions and the same Brownian input. The random forcing cancels in their difference. Put
\(q_t=L_t-L'_t\), \(r_t=V_t-V'_t\). Then</p>
\[q'_t=r_t,\qquad r'_t=-\gamma r_t-H_tq_t,\qquad
H_t=\int_0^1\nabla^2f(L'_t+s(L_t-L'_t))\,ds.\]
<p>The averaged Hessian is symmetric and obeys \(mI\preceq H_t\preceq MI\).
The problem has become a deterministic differential inequality along each pair
of paths. Existence and uniqueness of those common-input paths follow by applying the earlier additive-input solution theorems to the globally Lipschitz kinetic phase drift (see <cite data-report-ref="UnadjustedLangevin/LangevinIntegral.lean" data-report-declaration="exists_langevin_integral"></cite>, <cite data-report-ref="UnadjustedLangevin/LangevinUniqueness.lean" data-report-declaration="langevin_integral_unique"></cite>). No independent-noise variance is added to this comparison.</p>
<p>The usual Euclidean norm of \((r,q)\) need not decrease monotonically:
energy can move between position and velocity. The paper instead chooses a
linear transformation whose squared norm satisfies a differential inequality.</p><p>The cancellation takes place before expectations are taken. Consequently the same deterministic estimate holds on every sample path where the integral equations hold, and also in the Hilbert space of square-integrable random vectors. Independent forcing would instead introduce an extra random difference and would not produce this contraction comparison.</p>'''),

part('twisted-energy', r'''The transformed energy and its derivative''', r'''<p>Choose \(0\le v&lt;\gamma/2\), set \(\lambda_-=v\),
\(\lambda_+=\gamma-v\), and define</p>
\[a_t=r_t+\lambda_+q_t,\qquad b_t=-r_t-\lambda_-q_t,
\qquad \mathcal E_t=\|a_t\|^2+\|b_t\|^2.\]
<p>The change of variables is invertible because \(\lambda_+-\lambda_-&gt;0\).
Differentiate \(\mathcal E\), use the equations for \(q,r\), and exploit
symmetry of \(H_t\). The two off-diagonal inner products cancel exactly:</p>
\[\mathcal E'_t=
\frac{2}{\lambda_+-\lambda_-}
\bigl(\langle a_t,(\lambda_-^2I-H_t)a_t\rangle
+\langle b_t,(H_t-\lambda_+^2I)b_t\rangle\bigr).\]
<p>Consequently \(\mathcal E'_t\le2c(v)\mathcal E_t\), where</p>
\[c(v)=\frac{\max\{v^2-m,\ M-(\gamma-v)^2\}}{\gamma-2v}.\]
<p>Gronwall gives \(\sqrt{\mathcal E_t}\le e^{c(v)t}\sqrt{\mathcal E_0}\).
If the initial velocities agree, then
\(\mathcal E_0=((\gamma-v)^2+v^2)\|q_0\|^2\). Since
\(q_t=(a_t+b_t)/(\gamma-2v)\), the position estimate becomes</p>
\[\|q_t\|\le
\frac{\sqrt{2((\gamma-v)^2+v^2)}}{\gamma-2v}
e^{c(v)t}\|q_0\|.\]
<p>This is the explicit form of Proposition 1 and Theorem 1. Squaring and integrating first bounds the output cost for each initial coupling. The earlier coupling-cost bound and all-couplings infimum theorem then turn these bounds into a Wasserstein estimate (see <cite data-report-ref="UnadjustedLangevin/Coupling.lean" data-report-declaration="wasserstein2_le_Lp_cost_real"></cite>, <cite data-report-ref="UnadjustedLangevin/InitialCoupling.lean" data-report-declaration="wasserstein2_affine_bound_real_of_finite_couplings"></cite>).</p><p>The inverse position identity follows by adding the two transformed coordinates. Its norm bound is \(\|a_t+b_t\|^2\le2(\|a_t\|^2+\|b_t\|^2)\), obtained from the triangle inequality and \(2rs\le r^2+s^2\). This is the sole projection loss. Propagating the transformed norm through the entire evolution and projecting only once keeps that projection coefficient outside the iteration.</p>'''),

part('friction', r'''The friction regimes and their contraction coefficients''', r'''<p>At \(v=0\) the transformed energy is particularly simple:
\(\|r+\gamma q\|^2+\|r\|^2\). If \(\gamma^2\ge m+M\), then
\(c(0)=-m/\gamma\), so</p>
\[W_2(\mu P_t^L,\mu'P_t^L)
\le\sqrt2e^{-mt/\gamma}W_2(\mu,\mu').\]
<p>Here the two initial phase-space laws share the same independent velocity
marginal. The prefactor is \(\sqrt2\); this follows directly by substituting
\(v=0\) in the explicit formula. The supplied source's earlier
\(\sqrt2/\gamma\) prefactor in its unshifted display does not match
that substitution.</p>
<p>Friction that is very large makes the rate \(m/\gamma\) small: velocities
are damped before they transport position very far. The smallest friction
allowed by this simple estimate is \(\sqrt{m+M}\). The full table in the
paper improves the rate in other regimes by optimizing \(v\). For sufficiently
large friction it recovers</p>
\[\beta=\frac{\gamma-\sqrt{\gamma^2-4m}}2,\]
<p>This is the slow characteristic rate of a quadratic potential with curvature \(m\).
This explains the sharpness example. Singular prefactors at a repeated
characteristic root require separate limiting estimates.</p><p>The optimized exponent and the prefactor describe different effects. A more negative exponent improves long-time decay, while a large prefactor can make a finite-time bound less useful. Near the repeated-root boundary the coordinate transformation becomes singular, so rate optimization must retain its domain and cannot simply substitute the boundary into the prefactor.</p>'''),

part('exponential-step', r'''The exponential update with frozen force''', r'''<p>On an interval of length \(h\), replace the changing force
\(\nabla f(L_t)\) by its value at the current position \(x\). The remaining
velocity equation is linear and can be solved exactly. Define</p>
\[\psi_0(h)=e^{-\gamma h},\qquad
\psi_1(h)=\frac{1-e^{-\gamma h}}\gamma,\qquad
\psi_2(h)=\frac h\gamma-\frac{1-e^{-\gamma h}}{\gamma^2}.\]
<p>With velocity written first, the update is</p>
\[v^+=\psi_0(h)v-\psi_1(h)\nabla f(x)+\sqrt{2\gamma}\,\xi,
\quad x^+=x+\psi_1(h)v-\psi_2(h)\nabla f(x)+\sqrt{2\gamma}\,\xi'.\]
<p>The exponential terms handle friction at its exact continuous-time rate.
The coefficients of the force are its first and second time integrals. For
small \(h\), \(\psi_1(h)\approx h\) and \(\psi_2(h)\approx h^2/2\),
which are the first-order velocity and second-order position changes
under a constant force.</p>
<p>The only approximation here is freezing the nonlinear force. The linear
friction and its associated Gaussian forcing have already been integrated.
This is the KLMC exponential integrator reused by KIPLMC1.</p><p>An integrating factor gives \(v_t=e^{-\gamma t}v-\int_0^te^{-\gamma(t-s)}\nabla f(x)ds\) before noise is added. Since the force is constant inside this auxiliary problem, the integral equals \(\psi_1(t)\nabla f(x)\). Integrating this velocity once gives the \(\psi_2\) position coefficient. The two coefficient formulas therefore arise from the same exact frozen system.</p>'''),

part('noise', r'''The joint law of velocity and position innovations''', r'''<p>The two random increments come from the same Brownian motion:</p>
\[\xi=\int_0^h\psi_0(h-s)dW_s,
\qquad \xi'=\int_0^h\psi_1(h-s)dW_s.\]
<p>For each spatial coordinate their covariance is the two-by-two Gram matrix</p>
\[C=\int_0^h
\begin{pmatrix}\psi_0(t)^2&amp;\psi_0(t)\psi_1(t)\\
\psi_0(t)\psi_1(t)&amp;\psi_1(t)^2\end{pmatrix}dt.\]
<p>The off-diagonal entry is positive: both responses integrate the same Brownian increment with positive kernels. Replacing these increments with
two independent Gaussians changes the algorithm. Different spatial coordinates
and different time intervals use independent Gaussian pairs.</p>
<p>For any real \(a,b\),</p>
\[(a,b)C(a,b)^T=\int_0^h(a\psi_0(t)+b\psi_1(t))^2dt\ge0.\]
<p>This proves positive semidefiniteness. When \(h&gt;0\), the two coefficient
functions are linearly independent, which gives strict positivity. One may
therefore sample a pair using a Cholesky factor \(C=HH^T\) and two independent
standard normals. A complete law proof identifies this construction with the
Brownian integrals and establishes independence from the current state.</p><p>For an explicit scalar Gaussian construction, write \(C_{00}=a\), \(C_{10}=b\), and \(C_{11}=d\). Positive definiteness gives \(a>0\) and \(d-b^2/a>0\). With independent standard normals \(G,H\), the pair \((\sqrt aG,(b/\sqrt a)G+\sqrt{d-b^2/a}\,H)\) has exactly covariance \(C\). Its nonzero cross term retains the positive cross covariance.</p>'''),

part('first-local-defect', r'''The local velocity and position errors''', r'''<p>Compare one frozen-force step with the exact kinetic process started at
the same phase-space state. Their Brownian terms cancel. Gradient Lipschitzness
bounds the velocity defect by</p>
\[\|\Delta v_t\|_{L^2}
\le M\int_0^t\|L_s-L_0\|_{L^2}ds
\le\frac{Mt^2}{2}\sup_{0\le r\le h}\|V_r\|_{L^2}.\]
<p>Position is the integral of velocity, so its defect has an additional time
factor:</p>
\[\|\Delta x_h\|_{L^2}\le\frac{Mh^3}{6}
\sup_{0\le r\le h}\|V_r\|_{L^2}.\]
<p>At stationarity \(\|V_r\|_{L^2}=\sqrt p\). For the auxiliary exact path
started from the numerical state, contraction against the stationary exact
path controls its velocity norm by \(\sqrt p+A_k\), where \(A_k\) is the
current error in transformed coordinates. This prevents the initialization
error from reappearing in every step as a fixed additive penalty.</p>
<p>Under the paper's step restriction, combining the two coordinate defects
gives the transformed local estimate
\(\tfrac34Mh^2(\sqrt p+A_k)\). Constructing the auxiliary process, its
moments and the synchronous Gaussian law is part of the analytic proof behind
this estimate.</p><p>The orders follow from the two scalar integrals: \(\int_0^hsds=h^2/2\), whereas \(\int_0^h(h-s)sds=h^3/6\). Smoothness is used only to turn the position displacement into force variation. The reference velocity moment, rather than a bound on Brownian path derivatives, controls the remaining stochastic quantity.</p>'''),

part('first-recurrence', r'''Iteration of the first-order coupling inequality''', r'''<p>Let
\(A_k=\| (\Delta V_k+\gamma\Delta L_k,-\Delta V_k)\|_{L^2}\).
Exact kinetic evolution contracts this transformed norm. A triangle inequality
with the one-step defect gives</p>
\[A_{k+1}\le\left(e^{-mh/\gamma}+\frac34Mh^2\right)A_k
+\frac34Mh^2\sqrt p.\]
<p>For \(0&lt;h\le m/(4\gamma M)\), the quadratic correction is small enough
to retain most of the continuous contraction:</p>
\[A_{k+1}\le qA_k+b,\qquad
q=1-\frac{3mh}{4\gamma},\quad b=\frac34Mh^2\sqrt p.\]
<p>Induction gives the finite geometric sum
\(A_k\le q^kA_0+b\sum_{j=0}^{k-1}q^j\). Because \(0\le q&lt;1\),</p>
\[A_k\le q^kA_0+\frac{Mh\gamma\sqrt p}m.\]
<p>Equal initial velocities give \(A_0=\gamma W_2(\nu_0,\pi)\) for an
optimal initial coupling; approximate couplings and a limiting infimum work as
well. The position projection costs \(\sqrt2/\gamma\), yielding the displayed
KLMC theorem. The recurrence itself is elementary. The substantive stochastic
claim is that the chain admits the coupling from which it was derived. Equality of the explicit fresh-noise recursion and its iterated transition laws uses the earlier Markov-law identification (see <cite data-report-ref="UnadjustedLangevin/MarkovLaw.lean" data-report-declaration="noiseDrivenChain_law_eq_markovLaws"></cite>).</p><p>The geometric sum is finite for every iteration count: \(\sum_{j=0}^{n-1}q^j=(1-q^n)/(1-q)\). Bounding it by \((1-q)^{-1}\) separates transient and persistent errors. Because the local forcing is quadratic and the contraction gap is linear in \(h\), the persistent position-error term is linear in the step. The initial-error coefficient remains outside this sum.</p>'''),

part('second-order-method', r'''The Hessian-corrected exponential update''', r'''<p>If the Hessian is \(M_2\)-Lipschitz in operator norm, a first-order
Taylor expansion of the gradient leaves a quadratic position remainder:</p>
\[\|\nabla f(y)-\nabla f(x)-\nabla^2f(x)(y-x)\|
\le\frac{M_2}{2}\|y-x\|^2.\]
<p>The paper inserts the leading velocity and Brownian contributions to
\(L_s-L_0\) into this expansion. Define
\(\varphi_{j+1}(h)=\int_0^he^{-\gamma(h-s)}\psi_j(s)ds\). The resulting
KLMC2 update subtracts \(\varphi_2(h)H v\) from velocity and
\(\varphi_3(h)H v\) from position, where \(H=\nabla^2f(x)\). Its random
increments are also corrected by multiplying two additional correlated
Gaussian blocks by \(H\).</p>
<p>The joint covariance is the Gram integral of
\((\psi_0,\psi_1,\varphi_2,\varphi_3)\). This avoids a matrix exponential:
the operations involving the Hessian are matrix–vector products. The second
algorithm is therefore more elaborate than the frozen-force integrator, but
still explicit.</p>
<p>The name KLMC2 here refers to a Hessian method. KIPLMC2 in the particle
paper uses the OBABO splitting and first derivatives; its definition and proof
are separate.</p><p>The frozen Hessian acts on the displacement generated by the free Ornstein–Uhlenbeck velocity. That displacement contains both the initial-velocity response and fresh Brownian responses. Applying the Hessian to both parts is necessary to obtain the stated higher-order approximation; retaining only the deterministic Hessian–velocity correction would define a different algorithm.</p>'''),

part('second-order-estimates', r'''Fourth moments and stochastic Hessian corrections''', r'''<p>The Taylor remainder contains \(\|L_s-L_0\|^2\). Its
\(L^2\) norm therefore uses fourth moments. Under the stationary
kinetic law, each \(V_s\) is standard Gaussian and</p>
\[\mathbb E\|V_s\|^2=p,\qquad
\mathbb E\|V_s\|^4=p^2+2p.\]
<p>The kinematic equation \(L_s-L_0=\int_0^sV_rdr\) gives
\(\|L_s-L_0\|_{L^4}\le s(p^2+2p)^{1/4}\), without independence
between velocities at different times. The proof applies closed-convex
averaging to the existing \(L^2\) time integral. The Taylor forcing
is consequently bounded by \(M_2s^2\sqrt{p^2+2p}/2\).</p>
<p>Its damped integral gives the cubic velocity defect. A further force-memory
term uses the stationary score bound
\(\mathbb E_\pi\|\nabla f\|^2\le Mp\) from the earlier Gibbs score theorem (see <cite data-report-ref="UnadjustedLangevin/GibbsScore.lean" data-report-declaration="integral_norm_sq_gradient_gibbs_le_of_strongConvex"></cite>). Integrating the velocity error
once more gives the quartic position defect. Proposition 2 is thus for the defined four-kernel step:</p>
\[\|P^{-1}(V_h-\hat V_h,L_h-\hat L_h)\|_{L^2}
\le\frac{h^3}{4}\bigl(M_2\sqrt{p^2+2p}+M\sqrt{Mp}\bigr),
\qquad \gamma h\le\tfrac15.\]
<p>Proposition 3 requires an additional repair: the source's displayed
subtraction omits the Hessian difference multiplying the fresh
\(\varphi_2\) and \(\varphi_3\) noise. The proof keeps both terms.
Write \(D_H=H(L_0)-H(\widetilde L_0)\), and define the free-OU velocity
and complete Hessian responses on the same Brownian interval:</p>
\[U_r=\psi_0(r)V_0+\sqrt{2\gamma}\int_0^r\psi_0(r-s)dB_s,\]
\[C_j(t)=\varphi_j(t)V_0+\sqrt{2\gamma}
\int_0^t\varphi_j(t-s)dB_s,\qquad j=2,3.\]
<p>Kernel identities, proved by Hilbert-space Fubini and the Brownian
isonormal map, give</p>
\[C_2(t)=\int_0^te^{-\gamma(t-s)}\int_0^sU_rdrds,
\qquad C_2(t)+\gamma C_3(t)=\int_0^t\int_0^sU_rdrds.\]
<p>Each \(U_r\) has the standard Gaussian marginal, proved from the stationary reference velocity and its independent future Brownian interval.
The random operator \(D_H\) can depend on the coupled positions and velocity;
the cutoff argument below requires no independence from \(U_r\). The complete
correction therefore satisfies, for \(a\ge5p\),</p>
\[\|P^{-1}(D_HC_2(h),D_HC_3(h))\|_{L^2}
\le\frac{h^2}{\sqrt2}\left[
M_2\sqrt a\,\|L_0-\widetilde L_0\|_{L^2}
+2(M-m)e^{-(a-p)/8}\right].\]
<p>This retains the source constants while accounting for every stochastic
Hessian term. The frozen-linear part contracts by \(1-mh/(2\gamma)\)
under \(\gamma^2\ge m+M\) and \(5\gamma Mh\le m\); adding the complete
correction gives the repaired one-step comparison.</p><p>The fourth moment enters because a quadratic Taylor remainder is estimated in second mean: \(\|\|D\|^2\|_{L^2}=(\mathbb E\|D\|^4)^{1/2}\). Expanding the Gaussian fourth norm gives \(3p+p(p-1)=p^2+2p\). This exact coefficient is kept until any later dimension-dependent simplification is explicitly justified.</p>'''),

part('second-order-tail', r'''Gaussian truncation and the second-order sampling bound''', r'''<p>A Gaussian reference velocity need not be independent of the accumulated
position error. For any standard Gaussian vector and \(a\ge5p\),
the Gaussian exponential moment gives</p>
\[\|V\|^2\le a+(\|V\|^2-a)_+,\qquad
\mathbb E(\|V\|^2-a)_+\le4e^{-(a-p)/4}.\]
<p>The Hessian difference satisfies both
\(\|H(x)-H(y)\|\le M-m\) and
\(\|H(x)-H(y)\|\le M_2\|x-y\|\). On the bounded-velocity part use
the Lipschitz bound; on the tail use the curvature-width bound. Taking the
square root of the integrated estimate gives</p>
\[\|D_HV\|_{L^2}\le M_2\sqrt a\,\|L_0-\widetilde L_0\|_{L^2}
+2(M-m)e^{-(a-p)/8}.\]
<p>Apply this estimate to each free-OU velocity in the complete
correction, then combine the repaired comparison with the cubic local
defect. Choose</p>
\[a=\left(\frac{m}{4M_2h}\right)^2,\qquad
h\le\frac{m}{5\gamma M}\wedge\frac{m}{4M_2\sqrt{5p}}.\]
<p>Assume \(m,M_2&gt;0\), \(\gamma^2\ge m+M\), and initial phase law
\(\mathcal N(0,I_p)\otimes\nu_0\), with finite \(W_2(\nu_0,\pi)\).
The second step restriction ensures \(a\ge5p\), and the first enforces the
frozen-linear stability bound. The position-dependent comparison term is
absorbed into \(q=1-mh/(4\gamma)\). Iterating on the constructed common
Brownian source and taking the infimum over initial couplings proves
for the independently initialized, iid four-kernel Gaussian KLMC2 chain</p>
\[W_2(\nu_n^{\rm KLMC2},\pi)\le
\sqrt2q^n W_2(\nu_0,\pi)
+\frac{\sqrt2h^2}{m}\left(M_2\sqrt{p^2+2p}+M\sqrt{Mp}\right)
+\frac{8(M-m)h}{m}e^{-(a-p)/8}.\]
<p>The output transport distance is finite; the real-valued expression
does not conceal an infinite distance. No stationary-law, local-error,
independence, Gaussian-innovation or optimal-coupling premise is supplied to
this final sampler theorem.</p>
<p>The cutoff gives both \(e^{-(a-p)/8}\le e^{-p/2}\) and the stronger
\(e^{-(a-p)/8}\le e^{-m^2/(160M_2^2h^2)}\). The printed simplification
of the first bias term uses \(p^2+2p\le2p^2\), which requires
\(p\ge2\). Under that explicit restriction the bound implies</p>
\[W_2(\nu_n^{\rm KLMC2},\pi)\le
\sqrt2q^n W_2(\nu_0,\pi)
+\frac{2h^2M_2p}{m}+\frac{h^2M\sqrt{2Mp}}m
+\frac{8Mh}{m}e^{-p/2}.\]
<p>For \(p=1\), the exact fourth-moment expression in the preceding
sampling theorem remains the valid conclusion. The source's silently used
higher-dimensional simplification is not applied.</p><p>The cutoff gives two estimates. Its moderate-velocity contribution is proportional to the current displacement and is absorbed into the contraction gap. Its remaining excess is controlled solely by the Gaussian velocity marginal. Thus the argument remains valid when the displacement and velocity share the entire past of the coupled sampler.</p>'''),

part('complexity', r'''Step restrictions and iteration counts for prescribed accuracy''', r'''<p>Suppose an error bound has the form \(q^kD+Bh\). Choose
\(h\) small enough that \(Bh\) is bounded by one part of the error tolerance
\(\varepsilon\), and choose \(k\) large enough for the decaying initial
term to satisfy the remaining tolerance. The admissible \(h\) is the minimum of this accuracy
choice and the stability restriction.</p>
<p>For the first integrator, the bias scales as \(h\sqrt p\), giving
\(h\) of order \(\varepsilon/\sqrt p\), and a step count of order
\(\sqrt p/\varepsilon\) up to logarithmic and curvature factors.
For the Hessian method the leading bias scales as \(h^2p\), giving
\(h\) of order \(\sqrt{\varepsilon/p}\), and a step count of order
\(\sqrt{p/\varepsilon}\). These are asymptotic consequences of algorithmic estimates, with fixed geometry constants.</p>
<p>The paper's comparisons keep track of condition numbers as well. A kinetic
method gains from smooth position paths, but poor conditioning can make its
allowed step size small. The resulting iteration bound therefore depends on dimension, error tolerance, and curvature. A precise
complexity theorem also specifies integer rounding and the treatment of
already-small initialization error.</p>
<p>The source also gives a finer condition-number comparison after explicitly
omitting the Gaussian tail. We can audit that calculation using exact finite expressions. For target error \(\varepsilon/\sqrt m\), allocate
\(\varepsilon/(2\sqrt m)\) to the printed quadratic bias and set</p>
\[h_0=\min\left\{\frac m{5\gamma M},\;
\frac m{4\sqrt{5p}M_2},\;
\sqrt{\frac{\varepsilon\sqrt m}{4M_2p+2M\sqrt{2Mp}}}\right\}.\]
<p>Every denominator is positive. This step meets both source stability
restrictions and the stated quadratic-bias allocation. Its reciprocal is
exactly</p>
\[Q=\max\left\{\frac{5\gamma M}m,\;
\frac{4\sqrt{5p}M_2}m,\;
\sqrt{\frac{4M_2p+2M\sqrt{2Mp}}{\varepsilon\sqrt m}}\right\}.\]
<p>There is no hidden dimension or curvature factor in this identity. For
initial distance \(D\), the rounded logarithmic iteration prescription satisfies</p>
\[n\le1+\frac{4\gamma}{m}Q\,
\max\left\{0,\log\frac{24D\sqrt m}{\varepsilon}\right\}.\]
<p>This calculation concerns the source comparison with the tail omitted.
The sampler accuracy theorem retains the tail and chooses its step
using the complete quadratic envelope proved earlier.</p>
<p>To understand the refinement, write
\(\kappa=M/m\), \(\eta=M_2/m^{3/2}\), and</p>
\[\rho=\kappa_2=\eta^{2/3}+\kappa p^{-1/3}
=\frac{M_2^{2/3}+Mp^{-1/3}}m.\]
<p>With \(\gamma=\sqrt{m+M}\), the source tries to simplify the count
coefficient to \(\sqrt p\,\rho^2+\sqrt{p/\varepsilon}\,\rho^{5/4}\).
That simplification drops a factor. A valid refinement is</p>
\[\sqrt{\frac\kappa\rho}\left[
\sqrt p\,\rho^2+\sqrt{p/\varepsilon}\,\rho^{5/4}\right]\]
<p>This comparison holds up to a universal multiplicative constant and the displayed logarithm.
A convenient uniform upper bound uses
\(\widehat\kappa_2=\max\{\kappa,\rho\}\):</p>
\[\mathcal C\le64\left[\sqrt p\,\widehat\kappa_2^2+
\sqrt{p/\varepsilon}\,\widehat\kappa_2^{5/4}\right],\]
<p>Here \(\mathcal C=(4\gamma/m)Q\) is the exact count coefficient
above. The natural count is therefore less than one plus this bound times
the visible nonnegative logarithm. If \(\rho\ge\kappa\), the maximum
is simply \(\rho\), so the printed shape follows with the same explicit
constant.</p>
<p>The distinction matters because the modified number discounts gradient
curvature by \(p^{-1/3}\), while the stability restriction still
contains \(M/m\). Take a natural \(t\ge2\), dimension \(p=t^6\),
and the valid constants \(m=1\), \(M=t^2\), \(M_2=1\),
\(\varepsilon=1\). A diagonal quadratic potential can have smallest
curvature one and largest curvature \(t^2\); its constant Hessian satisfies
the stated Hessian-Lipschitz bound. Here \(\kappa=t^2\),
\(\eta=1\), and \(\rho=2\) exactly. The normalized iteration
coefficient is at least \(20t^4\), whereas the source expression is at most
\(8t^3\). No universal constant multiplying that expression can cover all
natural \(t\). This diagnoses the source's simplification of the sufficient step and iteration bound;
it asserts no lower bound on the best possible behavior of the algorithm.</p><p>All inverse-step branches must be retained when deriving a uniform work bound. Inverting a minimum of positive admissible steps produces a maximum of the corresponding positive reciprocal costs. The dominant branch may change with curvature, dimension, Hessian regularity, and requested precision. The integer ceiling then adds less than one iteration to the real logarithmic threshold.</p>''')
]


KIPLMC_STATEMENT = r'''<p>Let \(U(\theta,x)=-\log p_\theta(x,y)\) be jointly
\(\mu\)-strongly convex with \(L\)-Lipschitz gradient. Let
\(d_z=d_\theta+Nd_x\),
\(Z_0=(\theta_0,N^{-1/2}X_0^1,\ldots,N^{-1/2}X_0^N)\), and initialize
independent velocities with covariances \(N^{-1}I\) in the parameter block and
\(I\) in each latent block, independently of \(Z_0\). KIPLMC1 reuses the
kinetic exponential integrator and satisfies</p>
\[\bigl(\mathbb E\|\theta_n-\theta_*\|^2\bigr)^{1/2}
\le\sqrt2D_0\left(1-\frac{3\mu\eta}{4\gamma}\right)^n
+\sqrt2\frac L\mu\,\eta\sqrt{\frac{d_\theta}N+d_x}
+\sqrt{\frac{d_\theta}{\mu N}},\]
<p>Here \(D_0=W_2(\operatorname{Law}(Z_0),\widetilde\pi_Z)\),
\(\gamma\ge\sqrt{\mu+L}\), and \(0&lt;\eta\le\mu/(4\gamma L)\).
The manuscript's independently drawn stationary initial position gives a
possibly larger valid choice of \(D_0\). KIPLMC2 uses the OBABO splitting and
has a different numerical estimate; the scope is documented separately.</p>'''


KIPLMC_PROOF = [
part('statistical-objective', r'''The likelihood and interacting latent particles''', r'''<p>The observation \(y\) is fixed. A model gives a joint density
\(p_\theta(x,y)\), but the quantity to optimize is its integral over an
unobserved variable:</p>
\[p_\theta(y)=\int p_\theta(x,y)dx,
\qquad\theta_*=\arg\max_\theta\log p_\theta(y).\]
<p>Computing this integral and its gradient exactly can be difficult. The
particle method retains \(N\) latent states \(X^1,\ldots,X^N\), coupled
through the same parameter \(\theta\). The force on the parameter is the
average of the parameter gradients, while the latent drift uses the corresponding
latent gradient:</p>
\[F^\theta=\frac1N\sum_{i=1}^N\nabla_\theta U(\theta,X^i),
\qquad F^{x_i}=\nabla_xU(\theta,X^i).\]
<p>Adding a parameter noise of size \(N^{-1/2}\) makes the whole system a
Langevin system with an explicit Gibbs equilibrium. The particle number then
has two roles: it provides interacting latent samples and determines how
strongly the stationary parameter distribution concentrates near the optimizer.</p><p>The common parameter is represented once while each latent variable has its own coordinate. Conditional on that parameter, the equilibrium latent integrations factor into identical marginal likelihood integrals. Increasing particle count changes the parameter density by increasing the power of the likelihood, and increases the state dimension linearly.</p>'''),

part('joint-geometry', r'''Joint strong convexity and smoothness of the statistical potential''', r'''<p>The source paper assumes \(U\in C^2\), \(\mu&gt;0\), \(L&gt;0\), and</p>
\[\langle z-z',\nabla U(z)-\nabla U(z')\rangle
\ge\mu\|z-z'\|^2,\qquad
\|\nabla U(z)-\nabla U(z')\|\le L\|z-z'\|,\]
<p>Here \(z=(\theta,x)\). The proved convergence bounds require differentiability and the displayed gradient inequalities. Under the source’s additional twice-continuous-differentiability assumption, these inequalities are equivalent to
\(\mu I\preceq\nabla^2U(z)\preceq LI\). Thus \(\mu\le L\) in positive
dimension. Strong convexity in \(x\) with \(\theta\) fixed does not imply joint strong convexity: the lower bound must also hold in directions that change both variables.</p>
<p>The paper's unregularized logistic example illustrates the distinction.
Its Gaussian prior contributes a quadratic in \(x-\theta\), which leaves
common shifts partly uncontrolled; logistic curvature can vanish far from the
origin. Spanning covariates give strict convexity, while a uniform positive
strong-convexity constant requires additional regularization. The source itself
separates these experiments from its strong-convexity theorem.</p><p>The required lower curvature concerns arbitrary joint directions \((u,w)\), including directions that move parameter and latent variables together. Positive curvature in either coordinate with the other fixed is insufficient. A direction in which both move can remove a prior penalty and expose weak or vanishing curvature in the likelihood.</p>'''),

part('particle-sde', r'''The kinetic particle equations in physical coordinates''', r'''<p>KIPLD adds velocity blocks \(V^\theta,V^{x_i}\) and uses the same
friction in each:</p>
\[d\theta=V^\theta dt,\qquad dX^i=V^{x_i}dt,\]
\[dV^\theta=-(\gamma V^\theta+F^\theta)dt
+\sqrt{2\gamma/N}\,dB^0,
\quad dV^{x_i}=-(\gamma V^{x_i}+F^{x_i})dt+\sqrt{2\gamma}\,dB^i.\]
<p>The Brownian blocks are independent. The parameter velocity has equilibrium
covariance \(N^{-1}I\); every latent velocity has covariance \(I\). These
scales are chosen together with the average parameter force. Changing one
without changing the others generally changes the equilibrium target.</p>
<p>The noise acts on velocity, while positions are integrals of velocities.
This creates the smoother position paths responsible for the exponential
integrator's improved discretization dependence. The target remains a
statistical estimation problem: the final parameter distribution should
concentrate around \(\theta_*\) as the particle number grows.</p><p>The parameter noise is reduced by the square root of particle count, matching its averaged force and concentrated equilibrium marginal. Each physical latent equation retains unit temperature. Scaling all latent positions and velocities by \(N^{-1/2}\) turns these different physical amplitudes into one uniform phase-space temperature.</p>'''),

part('rescaling', r'''Transformation to unit-temperature kinetic coordinates''', r'''<p>The particle system looks anisotropic, but it becomes a standard kinetic
system in \(d_z=d_\theta+Nd_x\) dimensions. At rescaled time \(t\), define</p>
\[\widetilde Z_t=(\theta_{\sqrt Nt},N^{-1/2}X^1_{\sqrt Nt},\ldots),
\qquad\widetilde V_t=(\sqrt N V^\theta_{\sqrt Nt},V^{x_1}_{\sqrt Nt},\ldots).\]
<p>Set</p>
\[\bar U_N(\theta,z_1,\ldots,z_N)=\frac1N\sum_{i=1}^NU(\theta,\sqrt N z_i),
\qquad f_N=N\bar U_N,\qquad\widetilde\gamma=\sqrt N\gamma.\]
<p>Brownian scaling produces independent standard blocks
\(\widetilde B_t^i=N^{-1/4}B^i_{\sqrt Nt}\). Direct substitution yields</p>
\[d\widetilde Z_t=\widetilde V_tdt,\qquad
d\widetilde V_t=-(\widetilde\gamma\widetilde V_t+\nabla f_N(\widetilde Z_t))dt
+\sqrt{2\widetilde\gamma}\,d\widetilde B_t.\]
<p>This is Proposition A.1. The parameter position stays unchanged under the
spatial scaling, which will make projection of the final transport estimate
particularly simple. An original step \(\eta\) corresponds to a rescaled
step \(\widetilde\eta=\eta/\sqrt N\).</p><p>The latent spatial scaling is applied first. The subsequent velocity and clock transformation fixes these scaled position coordinates. The parameter position is unchanged throughout. Friction and step are changed inversely, preserving their dimensionless product. The normalized Gaussian velocity and transformed Brownian amplitude must be transformed together; a deterministic clock identity alone would not identify the sampler’s probability law.</p>'''),

part('lifted-geometry', r'''Curvature and smoothness of the scaled particle potential''', r'''<p>The gradients of the averaged potential are</p>
\[\nabla_\theta\bar U_N=\frac1N\sum_i\nabla_\theta U(\theta,\sqrt Nz_i),
\qquad\nabla_{z_i}\bar U_N=\frac1{\sqrt N}\nabla_xU(\theta,\sqrt Nz_i).\]
<p>Apply the lifted strong-convexity theorem from the earlier particle geometry report (see <cite data-report-ref="IPLA/Geometry.lean" data-report-declaration="potential_strongConvex"></cite>). Equivalently, apply joint strong convexity to each pair
\((\theta,\sqrt Nz_i),(\theta',\sqrt Nz'_i)\), divide by \(N\), and sum.
The repeated parameter term and the scaled latent terms combine exactly:</p>
\[\langle Z-Z',\nabla\bar U_N(Z)-\nabla\bar U_N(Z')\rangle
\ge\mu\left(\|\theta-\theta'\|^2+\sum_i\|z_i-z'_i\|^2\right).\]
<p>For smoothness, Jensen bounds the squared norm of the averaged parameter
gradient by the average of squared norms. Adding the latent-gradient squares
then permits one joint \(L\)-Lipschitz estimate per particle, giving
\(\|\nabla\bar U_N(Z)-\nabla\bar U_N(Z')\|\le L\|Z-Z'\|\). This is the earlier lifted-gradient Lipschitz theorem divided by \(N\) (see <cite data-report-ref="IPLA/Geometry.lean" data-report-declaration="potential_gradient_lipschitz"></cite>).</p>
<p>Thus the standard potential \(f_N=N\bar U_N\) has constants
\(m_N=N\mu\), \(M_N=NL\). Their ratio is \(L/\mu\), independent of
\(N\). These identities determine the dependence of the KIPLMC1 error bound on particle count.</p><p>The lifted sum potential has curvature and gradient Lipschitz constants multiplied by \(N\). Dividing the potential by \(N\) cancels both factors in physical time. As a result the synchronous rate depends on the original pair constants, while total coordinate dimension appears only through thermal and numerical moments.</p>'''),

part('powered-marginal', r'''The normalized powered-likelihood parameter marginal''', r'''<p>The rescaled kinetic Gibbs density is</p>
\[\widetilde\Pi(dz,dv)\propto
\exp\left[-\sum_iU(\theta,\sqrt Nz_i)-\frac12\|v\|^2\right]dz\,dv.\]
<p>Integrating the Gaussian velocity gives a constant. For each latent block,
substitute \(x_i=\sqrt Nz_i\). Its Jacobian is independent of \(\theta\),
so it is absorbed in normalization. The earlier exact parameter-marginal theorem identifies the normalized pushforward after the same coordinate change (see <cite data-report-ref="IPLA/MarginalConcentration.lean" data-report-declaration="gibbsTarget_parameter_marginal"></cite>). The remaining product separates:</p>
\[\pi_\Theta(\theta)\propto
\prod_{i=1}^N\int e^{-U(\theta,x_i)}dx_i
=p_\theta(y)^N=e^{-N\kappa(\theta)},\quad
\kappa=-\log p_\theta(y).\]
<p>At stationarity, more particles therefore sharpen the likelihood density
rather than changing its maximizer. The maximizer is unchanged by taking a positive integer power.
It relies on the parameter noise being present at the prescribed scale; a
noise-free parameter gradient flow has a different invariant structure.</p>
<p>The density computation identifies the candidate marginal. Normalization and finite second moments follow from the earlier lifted-target construction (see <cite data-report-ref="IPLA/Foundations.lean" data-report-declaration="gibbsTarget_isProbability"></cite>, <cite data-report-ref="IPLA/Foundations.lean" data-report-declaration="gibbsTarget_memLp"></cite>). Invariance is a separate dynamical assertion, supplied by the kinetic phase-stationarity theorem after the clock change (see <cite data-report-ref="KineticLangevin/ContinuousGibbs.lean" data-report-declaration="phaseFlow_gibbs_stationary"></cite>).</p><p>The latent variables become independent under the conditional Gibbs density for a fixed parameter. Fubini multiplies their identical integrals into \(\ell(\theta)^N\). Dividing by the finite positive full partition function gives the powered marginal, so the concentration argument applies to a normalized probability measure.</p>'''),

part('concentration', r'''The sharp parameter second moment about the maximizer''', r'''<p>Strong Prékopa–Leindler preserves the parameter curvature when the latent
variable is integrated out: \(\kappa\) is \(\mu\)-strongly convex (see <cite data-report-ref="IPLA/StrongLogConcavity.lean" data-report-declaration="marginalPotential_strongConvex"></cite>). Thus its minimizer \(\theta_*\) is unique (see <cite data-report-ref="IPLA/StrongLogConcavity.lean" data-report-declaration="existsUnique_marginalMaximizer"></cite>), and the potential of \(\pi_\Theta\) has curvature \(N\mu\).</p>
<p>The sharp moment theorem in the earlier proximal report compares Gibbs partition integrals under dilation toward the minimizer (see <cite data-report-ref="ProximalLangevin/SharpConcentration.lean" data-report-declaration="sharp_integral_sq_dist_gibbs_le"></cite>). It requires continuity and strong convexity of the marginal potential, without a differentiability assumption on that potential. Applied to \(N\kappa\), and then to the exact powered particle marginal (see <cite data-report-ref="ProximalLangevin/SharpIPLA.lean" data-report-declaration="sharp_marginalTarget_secondMoment_le"></cite>), it gives</p>
\[W_2(\pi_\Theta,\delta_{\theta_*})
=\bigl(\mathbb E_{\pi_\Theta}\|\theta-\theta_*\|^2\bigr)^{1/2}
\le\sqrt{\frac{d_\theta}{N\mu}}.\]
<p>The coefficient is sharp: an isotropic Gaussian with covariance
\((N\mu)^{-1}I\) attains equality. This explains why a proof with an extra
\(\sqrt2\) coefficient, although valid, would not reproduce Proposition 2
exactly.</p><p>The radius is a root-mean-square statement around the maximizer, rather than a covariance statement around the marginal mean. Its explicit coefficient is important for the final triangle inequality. No equality of the mean and maximizer is required to add this equilibrium contribution to the numerical sampling error.</p>'''),

part('error-split', r'''Transport to equilibrium and concentration about the maximizer''', r'''<p>The only coupling of a probability law with a point mass fixes the second
coordinate, so Wasserstein distance to a point is exactly root mean square
error. The triangle inequality gives</p>
\[\bigl(\mathbb E\|\theta_n-\theta_*\|^2\bigr)^{1/2}
\le W_2(\operatorname{Law}(\theta_n),\pi_\Theta)
+\sqrt{\frac{d_\theta}{N\mu}}.\]
<p>The first term is a numerical sampling error; the second is the equilibrium
statistical radius. Increasing \(n\) reduces the transient sampling error.
Decreasing the step reduces discretization bias. Increasing \(N\) reduces
the concentration term. These operations affect different pieces of the bound.</p>
<p>The map from full rescaled position, or full phase space, to its parameter
block is 1-Lipschitz. The earlier particle-geometry result gives operator norm at most one for this projection (see <cite data-report-ref="IPLA/Geometry.lean" data-report-declaration="norm_parameterCLM_le_one"></cite>). Applying it to any coupling cannot
increase its quadratic transport cost. Therefore a bound on the ordinary
kinetic sampler immediately controls the parameter sampling term once the
algorithm-law correspondence has been proved.</p><p>The projected root-mean-square transport inequality gives the next step (see <cite data-report-ref="UnadjustedLangevin/Projection.lean" data-report-declaration="projectedRMSReal_le_wasserstein2Real_add"></cite>): for any coupling of the numerical position and an equilibrium position, project both to parameters and use Minkowski’s inequality around the maximizer. The projected discrepancy is bounded by the full scaled-state discrepancy because the projection is nonexpansive. Infimizing the latter cost yields the sampling term plus the equilibrium parameter radius.</p>'''),

part('first-integrator', r'''The KIPLMC1 exponential update and its change of coordinates''', r'''<p>Reuse \(\psi_0,\psi_1,\psi_2\) and the frozen-force exponential update from the earlier kinetic report (see <cite data-report-ref="KineticLangevin/Integrator.lean" data-report-declaration="exponentialStep"></cite>). With fresh
correlated Gaussian pairs of covariance \(C\), KIPLMC1 updates</p>
\[\theta^+=\theta+\psi_1(\eta)V^\theta-\psi_2(\eta)F^\theta
+\sqrt{2\gamma/N}\,\varepsilon^{0\prime},\]
\[V^{\theta+}=\psi_0(\eta)V^\theta-\psi_1(\eta)F^\theta
+\sqrt{2\gamma/N}\,\varepsilon^0.\]
<p>Each latent block uses the same formulas with \(X^i,V^{x_i},F^{x_i}\)
and noise scale \(\sqrt{2\gamma}\). This is Algorithm 1.</p>
<p>Proposition B.1 proves the correspondence by changing variables in the
ordinary exponential step with \(\widetilde\gamma=\sqrt N\gamma\) and
\(\widetilde\eta=\eta/\sqrt N\). The coefficients obey</p>
\[\widetilde\psi_0(\widetilde\eta)=\psi_0(\eta),\quad
\widetilde\psi_1(\widetilde\eta)=N^{-1/2}\psi_1(\eta),\quad
\widetilde\psi_2(\widetilde\eta)=N^{-1}\psi_2(\eta).\]
<p>The velocity and position Gaussian integrals scale by \(N^{-1/4}\) and
\(N^{-3/4}\), respectively. Their covariance entries therefore scale by
\(N^{-1/2},N^{-1},N^{-3/2}\). Matching these laws, in addition to matching
the deterministic terms, permits reuse of the same kinetic convergence proof.</p><p>The parameter force contains a particle mean because the common parameter occurs in every potential summand. A latent force belongs to only one summand. Undoing its spatial scaling cancels the averaging factor, explaining why the physical latent update uses its individual gradient and ordinary thermal amplitude.</p>'''),

part('first-bound', r'''The physical-time KIPLMC1 error bound''', r'''<p>Apply the constructed KLMC sampling theorem from the earlier kinetic report (see <cite data-report-ref="KineticLangevin/GenericCanonicalKLMC.lean" data-report-declaration="klmc_wasserstein_bound"></cite>) with
\(m_N=N\mu\), \(M_N=NL\), \(h_N=\eta/\sqrt N\), and
\(\gamma_N=\sqrt N\gamma\). Then</p>
\[\frac{m_Nh_N}{\gamma_N}=\frac{\mu\eta}{\gamma},\qquad
\frac{M_Nh_N}{m_N}\sqrt{2d_z}
=\sqrt2\frac L\mu\eta\sqrt{\frac{d_\theta}N+d_x}.\]
<p>The linear friction and step restrictions reduce exactly to
\(\gamma\ge\sqrt{\mu+L}\) and \(\eta\le\mu/(4\gamma L)\).
The projected-RMS transport inequality (see <cite data-report-ref="UnadjustedLangevin/Projection.lean" data-report-declaration="projectedRMSReal_le_wasserstein2Real_add"></cite>) and the sharp particle concentration radius (see <cite data-report-ref="ProximalLangevin/SharpIPLA.lean" data-report-declaration="sharp_gibbsTarget_parameter_concentration"></cite>) then give</p>
\[\mathcal E_n\le\sqrt2D_0
\left(1-\frac{3\mu\eta}{4\gamma}\right)^n
+\sqrt2\frac L\mu\eta\sqrt{\frac{d_\theta}N+d_x}
+\sqrt{\frac{d_\theta}{N\mu}}.\]
<p>The initial position Wasserstein distance is a valid \(D_0\).
The paper instead upper-bounds it by the root mean square distance to an
independently sampled stationary position. Initialization must include mutually
independent Gaussian velocity blocks, independent of position, so that the
rescaled velocity is precisely the standard Gaussian product needed by the
shared theorem.</p>
<p>Choosing \(N\) of order \(d_\theta/\varepsilon^2\) and \(\eta\) of
order \(\varepsilon/\sqrt{d_x}\), subject to stability, bounds both persistent terms. The transient then needs order \(\sqrt{d_x}/\varepsilon\) steps,
up to logarithmic and curvature factors.</p><p>The total scaled dimension is \(D=d_\theta+Nd_x\), and thermal variance per coordinate is \(1/N\). Thus the stationary velocity radius is \(\sqrt{D/N}=\sqrt{d_\theta/N+d_x}\). This identity is the probabilistic meaning of the particle-factor cancellation in the first-order discretization term.</p>'''),

part('obabo-subflows', r'''The five OBABO substeps''', r'''<p>KIPLMC2 uses the symmetric five-subflow composition established in the earlier kinetic report (see <cite data-report-ref="KineticLangevin/OBABO.lean" data-report-declaration="obaboStep_expanded"></cite>). Write
\(O\) for friction plus noise, \(B\) for the force kick, and \(A\) for free
transport. The composition is</p>
\[O(\eta/2)\;B(\eta/2)\;A(\eta)\;B(\eta/2)\;O(\eta/2).\]
<p>Let \(\delta=e^{-\gamma\eta/2}\),
\(s=\sqrt{1-\delta^2}\). For a standard velocity block, an \(O\) half-step
is \(v\mapsto\delta v+s\xi\); for the parameter block it is
\(V^\theta\mapsto\delta V^\theta+s\xi/\sqrt N\).
A \(B\) half-step subtracts \(\eta F/2\), and the full \(A\) step sends
\(x\mapsto x+\eta v\).</p>
<p>The second \(B\) kick must use the force at the newly computed position.
The last \(O\) step uses an independent Gaussian vector. Symmetry gives the
method its second-order splitting structure, while only first derivatives of
\(U\) are evaluated. This is an entirely different construction from the
Hessian-corrected KLMC2 in the first paper.</p><p>Each thermostat half step separately preserves the appropriate Gaussian velocity law, each force kick is a velocity translation, and each drift is a position translation. Their order determines which refreshed velocity moves position and where the second nonlinear force is evaluated.</p>'''),

part('obabo-expanded', r'''The expanded OBABO update''', r'''<p>For one standard block with force \(g\), combine the first \(O\) and
\(B\) operations:</p>
\[v_{1/2}=\delta v+s\xi-\frac\eta2g(x),
\qquad x^+=x+\eta v_{1/2}.\]
<p>Apply the final force kick and OU refresh:</p>
\[v^+=\delta\left(v_{1/2}-\frac\eta2g(x^+)\right)+s\xi'
=\delta^2v-\frac{\eta\delta}2\bigl(g(x)+g(x^+)\bigr)
+s(\delta\xi+\xi').\]
<p>In the parameter block replace \(g\) by the average \(F^\theta\), and
both Gaussian amplitudes by \(s/\sqrt N\). The latent blocks use individual
forces and amplitude \(s\). These identities reproduce Algorithm 2 and
Proposition B.2.</p>
<p>The resulting law is determined by two independent standard Gaussian
vectors, independent of the current state. Proving the displayed algebra for
arbitrary supplied noise vectors verifies the deterministic update;
proving the stochastic theorem additionally constructs this Gaussian kernel,
its iterates and the required moment estimates.</p><p>The final combined noise is \(s(\delta\xi+\xi^{\prime})\), but position depends only on the first refresh through the half velocity. Therefore the full phase output has a nontrivial shared-noise structure even though the two input thermostat vectors are independent. The expanded formula retains this structure exactly.</p>'''),

part('discrete-equilibrium', r'''Comparison through a discrete invariant measure''', r'''<p>A finite-step OBABO kernel \(P_h\) generally has its own invariant law
\(\Pi_h\), different from the kinetic Gibbs law \(\Pi\). The cited
Monmarché analysis supplies phase-space contraction and invariant bias bounds
of the form</p>
\[W_2(\rho P_h^n,\sigma P_h^n)\le A q^{n/2}W_2(\rho,\sigma),
\qquad b=W_2(\Pi_h,\Pi)\le B.\]
<p>Apply the triangle inequality twice, using invariance of \(\Pi_h\):</p>
\[W_2(\rho P_h^n,\Pi)
\le A q^{n/2}\bigl(W_2(\rho,\Pi)+B\bigr)+B.\]
<p>This explains two different occurrences of the numerical bias: a persistent
\(B\) and a transient \(Aq^{n/2}B\). Dropping the latter would lose a term
present in the supplied paper's revised theorem.</p>
<p>These inequalities are substantial results about the OBABO kernel,
including existence of \(\Pi_h\). A theorem that takes them as hypotheses
checks the transport combination but does not prove the cited OBABO analysis.
The coverage audit distinguishes that conditional use from a completed
argument.</p>'''),

part('obabo-scaling', r'''Particle dependence of the OBABO coefficients''', r'''<p>For comparison with the direct bound, the manuscript’s cited discrete-invariant-law analysis uses the following rescaled constants</p>
\[A_N=\sqrt3\max\{\sqrt{NL},(NL)^{-1/2}\},\qquad
q=1-\frac{\mu\eta}{3\gamma}.\]
<p>Under \(\gamma\ge2\sqrt L\) and
\(0&lt;\eta\le\eta_0=\mu/(33\gamma^3)\), one has \(0&lt;q&lt;1\).
Write \(M_L=\max\{\sqrt L,L^{-1/2}\}\). Because \(N\ge1\),
\(A_N\le\sqrt{3N}M_L\). The detailed bias expression in the source
can be bounded by</p>
\[B_N\le\sqrt3G_*\eta\sqrt{Nd_z},\]
\[G_*=\frac{6\gamma L}{\mu}M_L
\left(1+\frac{\eta_0L}{2\sqrt\mu}\right)
\left(1+e^{L\eta_0^2}
\left(\frac{\eta_0}{6}+\frac{\eta_0^2L}{24}\right)\right).\]
<p>All factors increase with a nonnegative step, so evaluating at the fixed
upper limit \(\eta_0\) removes hidden step dependence. This makes \(G_*\)
a constant depending only on \(\mu,L,\gamma\).</p>
<p>The product \(A_NB_N\) is proportional to \(\eta N\sqrt{d_z}\), while
\(B_N\) itself is proportional to \(\eta\sqrt{Nd_z}\). The two terms have
different powers of \(N\), which is why the source tracks them separately
before introducing the implicit constant.</p><p>The clock changes both curvature constants and friction, while leaving the physical contraction ratio unchanged. Simplifying the bias only after substituting every factor avoids introducing spurious growing powers of \(N\). The direct position sampling theorem from the earlier kinetic report instead gives a bound with thermal dimension factor (see <cite data-report-ref="KineticLangevin/OBABOPosition.lean" data-report-declaration="obabo_position_sampling_bound"></cite>), which is stronger than the coarser printed bound.</p>'''),

part('obabo-bound', r'''The KIPLMC2 bound with both transient terms''', r'''<p>Independent Gaussian initialization gives the same velocity marginal as
\(\widetilde\Pi\). Coupling these equal velocity blocks and using position
projection proves the exact identity</p>
\[W_2(\rho_0,\widetilde\Pi)
=W_2(\nu,\widetilde\pi_Z)=D_0.\]
<p>Insert the scaled \(A_N,B_N\) into the discrete equilibrium comparison,
project to \(\theta\), and add the concentration radius. With a constant
\(C\) depending only on \(\mu,L,\gamma\), the supplied manuscript obtains</p>
\[\mathcal E_n\le C\left[
\bigl(\sqrt N D_0+\eta N\sqrt{d_\theta+Nd_x}\bigr)
e^{-\mu\eta n/(6\gamma)}
+\eta\sqrt{N(d_\theta+Nd_x)}
+\sqrt{d_\theta/N}\right].\]
<p>The exponential follows from
\((1-\mu\eta/(3\gamma))^{n/2}\le e^{-\mu\eta n/(6\gamma)}\).
The paper gives an explicit common coefficient by taking the maximum of
\(\sqrt3M_L,\sqrt3G_*,3M_LG_*\) and absorbing the concentration factor
\(\mu^{-1/2}\).</p>
<p>This bound has worse particle dependence than the KIPLMC1 bound. The paper
regards that dependence as a limitation of the available estimate and compares
it with numerical behavior; the experiments do not themselves remove the
factor from the theorem.</p><p>The extra transient term is harmless for validity but matters when reproducing the displayed manuscript formula. It decays with the same rate as the initial transport discrepancy. The sharper invariant-comparator estimate from the earlier kinetic report bounds the chain directly (see <cite data-report-ref="KineticLangevin/OBABOPosition.lean" data-report-declaration="obabo_position_sampling_bound"></cite>) and implies this coarser statement by nonnegative termwise enlargements.</p>'''),

part('complexity-and-experiments', r'''Iteration counts and the scope of the experimental examples''', r'''<p>For KIPLMC2, choosing \(N\asymp d_\theta/\varepsilon^2\) gives</p>
\[\sqrt{N(d_\theta+Nd_x)}
\asymp\frac{d_\theta}{\varepsilon}
\sqrt{1+\frac{d_x}{\varepsilon^2}}.\]
<p>To make the persistent numerical error of order \(\varepsilon\), take
the minimum of the stability threshold and
\(\varepsilon/\sqrt{N(d_\theta+Nd_x)}\). In the small-error regime this
is a step of order \(\varepsilon^3/(d_\theta\sqrt{d_x})\). Both transient
terms can then be controlled after
\(\widetilde O(d_\theta\sqrt{d_x}/\varepsilon^3)\) steps, provided the
initial transport error grows at most polynomially in particle number and
dimension so that its logarithm remains in the suppressed factor.</p>
<p>The manuscript also studies logistic regression, Wisconsin cancer data, a
Bayesian neural network, a multi-well model and runtime comparisons. Its signed
weighted area between error curves is
\(\sum_{i=1}^M2i(c^{\mathrm{IPLA}}(i)-c^{\mathrm{KIPLMC2}}(i))/(M(M+1))\).
Positive values favor KIPLMC2 by this metric. Its predictive log score averages
the log probability assigned to each correct test label.</p>
<p>These are empirical comparisons with concrete data and numerical settings.
The strong-convexity convergence theorems, their asymptotic complexity
corollaries, the algorithm definitions and the experimental metrics are
different kinds of content. The logistic example is globally smooth and can be strictly convex under a full-span feature condition, while common-translation directions still prevent a positive uniform strong-convexity constant without additional regularization.</p><p>The statistical choice of particle count first fixes the dimension-dependent numerical coefficient. The discretization-error bound then fixes a step, and the contraction rate fixes the iteration count. Empirical advantages at particular model settings remain separate from these global sufficient conditions, especially when a model lacks uniform joint strong convexity.</p>''')
]


# Exact correspondences between the mathematical explanation and checked Lean.
def _attach(parts, mapping):
    for item in parts:
        refs, note = mapping[item['id']]
        item['references'] = [dict(file=file, name=name) for file, name in refs]
        item['note'] = note


# Every exposition section names its final checked source-law theorems.

_attach(KINETIC_PROOF, {
    'target': ([('KineticLangevin/ContinuousGibbs.lean','phaseFlow_gibbs_stationary'),('KineticLangevin/ContinuousGibbs.lean','positionLaw_gibbs')], r'''The specified Brownian kinetic flow and its full Gaussian-times-Gibbs stationarity are proved. The proof uses exact Hamiltonian invariance and a controlled splitting limit.'''),
    'time-scale': ([('KineticLangevin/MassScaling.lean','kinetic_mass_integral'),('KineticLangevin/MassScaling.lean','kinetic_mass_noise_amplitude'),('KineticLangevin/BrownianScaling.lean','clockBrownian_isPreBrownian')], 'The complete inverse-mass integral equation, transformed noise coefficient, Brownian finite-dimensional laws, and independent changed-clock coordinates are proved.'),
    'synchronous': ([('KineticLangevin/SynchronousFlow.lean','kinetic_integral_position_decay'),('KineticLangevin/ContinuousGibbs.lean','wasserstein2_gibbs_general')], r'''Common forcing cancels in the integral solutions. The final theorem applies this argument to the constructed Brownian laws and the Wasserstein coupling infimum.'''),
    'twisted-energy': ([('KineticLangevin/Geometry.lean','transform'),('KineticLangevin/Contraction.lean','spectral_identity'),('KineticLangevin/GeneralContraction.lean','potential_general_force_dissipativity')], r'''The transformed energy and general shifted dissipation are proved from the strong-convexity and gradient-Lipschitz assumptions.'''),
    'friction': ([('KineticLangevin/Friction.lean','contractionExponent_low_optimal'),('KineticLangevin/Friction.lean','contractionExponent_middle_optimal'),('KineticLangevin/Friction.lean','contractionExponent_high_optimal')], r'''All three scalar optimality regimes are proved on the admissible nonsingular shift interval. The Brownian theorem retains the complete prefactor and exponent.'''),
    'exponential-step': ([('KineticLangevin/Integrator.lean','exponentialStep'),('KineticLangevin/Integrator.lean','klmcStep')], r'''These are the deterministic update definitions reused directly by KIPLMC1.'''),
    'noise': ([('KineticLangevin/BrownianConvolution.lean','klmc_jointLaw'),('KineticLangevin/CanonicalVectorSegments.lean','canonicalKLMCInnovation_independent'),('KineticLangevin/Gaussian.lean','kernelNoisePath_independent')], r'''The Brownian convolutions have the specified joint Gaussian Gram law, with independent spatial and time blocks. The sampler law is identified through the joint response construction.'''),
    'first-local-defect': ([('KineticLangevin/LocalError.lean','velocityDefect_bound'),('KineticLangevin/LocalError.lean','positionDefect_bound'),('KineticLangevin/CanonicalKLMC.lean','globalReferenceFlow_stationary')], r'''The local integrals are bounded in L², and the constructed reference supplies the required stationary Gaussian velocity moments.'''),
    'first-recurrence': ([('KineticLangevin/Recurrence.lean','firstOrder_coupling_recurrence_bound'),('KineticLangevin/CanonicalKLMC.lean','klmc_wasserstein_bound')], r'''The sampler theorem constructs the reference, derives the numerical local inequality, identifies both output laws, and takes the initial-coupling infimum internally.'''),
    'second-order-method': ([('KineticLangevin/Integrator.lean','klmc2Step'),('KineticLangevin/BrownianConvolution.lean','klmc2_jointLaw')], r'''The four-kernel Hessian update and its exact Brownian Gaussian innovation law are constructed. The separate completion audit tracks the chain error bound.'''),
    'second-order-estimates': ([('KineticLangevin/GaussianFourth.lean','stdGaussian_norm_fourth_moment'),('KineticLangevin/SecondOrderOneStep.lean','klmc2Step_stationary_local_bound'),('KineticLangevin/SecondOrderComparison.lean','klmc2SourceStep_comparison_bound'),('KineticLangevin/CanonicalFreeOU.lean','referenceChain_freeOUResponse_hasLaw')], r'''The four-kernel local error and repaired synchronous comparison are proved. Both fresh stochastic Hessian terms are retained through the complete free Ornstein–Uhlenbeck response, whose Gaussian marginals follow from the constructed past/future law.'''),
    'second-order-tail': ([('KineticLangevin/GaussianTail.lean','gaussian_norm_square_positivePart_le'),('KineticLangevin/GaussianTruncation.lean','gaussian_truncation_Lp'),('KineticLangevin/SecondOrderRecurrence.lean','secondOrderCutoff_tail'),('KineticLangevin/CanonicalKLMC2.lean','klmc2_wasserstein_bound_exact'),('KineticLangevin/CanonicalKLMC2.lean','klmc2_wasserstein_bound')], r'''The exact-dimensional theorem is proved for the KLMC2 Gaussian Markov chain, with all reference laws, noise laws, local errors, and coupling infima derived from the stated hypotheses. The printed coefficient is provided with its necessary dimension restriction p at least two; the one-dimensional exact-moment bound is retained.'''),
    'complexity': ([('KineticLangevin/Accuracy.lean','klmc_accuracy_explicit'),('KineticLangevin/Complexity.lean','firstOrderIterationCount_spec')], r'''The first-order sampler has a proved positive minimum step, 0.94-epsilon bias allocation, and rounded natural logarithmic iteration count giving error at most epsilon.'''),
})

_attach(KIPLMC_PROOF, {
    'statistical-objective': ([('KIPLMC/Target.lean','existsUnique_mmle'),('KIPLMC/Target.lean','gibbsPhaseTarget_parameter')], r'''The unique MMLE and exact powered parameter marginal are proved for the normalized target.'''),
    'joint-geometry': ([('KIPLMC/Geometry.lean','averagePotential_strongConvex'),('KIPLMC/Geometry.lean','force_lipschitz')], 'The global joint assumptions imply the required particle geometry. Experiments outside these assumptions are recorded separately.'),
    'particle-sde': ([('KIPLMC/Continuous.lean','kipldBrownianFlow_integral'),('KIPLMC/Continuous.lean','kipldBrownianFlow_initial_hasLaw')], 'The constructed Brownian physical-time flow satisfies the exact particle integral equation and has the required independent thermal initialization.'),
    'rescaling': ([('KIPLMC/KineticClock.lean','kinetic_integral_clock'),('KineticLangevin/BrownianScaling.lean','clockBrownian_isPreBrownian'),('KIPLMC/Continuous.lean','kipldBrownianPositionLaw_eq_canonical')], r'''The drift, complete integral equation, Brownian scaling, independent coordinates, and endpoint law all transform with the exact particle clock.'''),
    'lifted-geometry': ([('KIPLMC/Geometry.lean','gradient_averagePotential'),('KIPLMC/Geometry.lean','averagePotential_strongConvex'),('KIPLMC/Geometry.lean','force_lipschitz')], r'''The averaged potential has the stated force, curvature and smoothness, independently of particle count.'''),
    'powered-marginal': ([('KIPLMC/Target.lean','gibbsPhaseTarget_probability'),('KIPLMC/Target.lean','gibbsPhaseTarget_parameter'),('KineticLangevin/ContinuousGibbs.lean','phaseFlow_gibbs_stationary')], 'Normalization, full kinetic Gibbs stationarity under the standard clock, and the exact parameter marginal are proved.'),
    'concentration': ([('KIPLMC/Target.lean','existsUnique_mmle'),('KIPLMC/Target.lean','parameter_secondMoment_le'),('KIPLMC/Target.lean','parameter_concentration')], 'The normalized powered marginal satisfies the dimension-sharp concentration bound about its unique maximizer.'),
    'error-split': ([('KIPLMC/Continuous.lean','kipld_parameter_RMS_bound'),('KIPLMC/CanonicalExponential.lean','kiplmc1_parameter_bound'),('KIPLMC/OBABOBound.lean','kiplmc2_parameter_bound')], r'''The diffusion and both Gaussian chains combine transport and sharp equilibrium concentration by the checked projected L² triangle inequality.'''),
    'first-integrator': ([('KIPLMC/Exponential.lean','kiplmc1Step'),('KIPLMC/Exponential.lean','kiplmc1Step_parameter_position'),('KIPLMC/Exponential.lean','kiplmc1Step_particle_velocity'),('KIPLMC/CanonicalExponential.lean','kiplmc1GaussianPositionLaws_eq_canonical')], r'''KIPLMC1 uses the shared exponential step. Exact correlated-Gaussian and chain-law conjugacies identify its output with the shared kinetic sampler.'''),
    'first-bound': ([('KIPLMC/CanonicalExponential.lean','kiplmc1_parameter_bound_independent'),('KIPLMC/Accuracy.lean','kiplmc1_accuracy')], r'''The complete printed Gaussian RMS theorem and its finite epsilon-accuracy corollary are proved, including the independent initial coupling constant.'''),
    'obabo-subflows': ([('KineticLangevin/OBABO.lean','obaboStep_expanded'),('KIPLMC/Splitting.lean','kiplmc2Step')], r'''The five-subflow composition and its exact algebraic expansion are proved.'''),
    'obabo-expanded': ([('KIPLMC/Splitting.lean','halfVelocity_parameter'),('KIPLMC/Splitting.lean','halfVelocity_particle'),('KIPLMC/Splitting.lean','kiplmc2Step_velocity'),('KIPLMC/Laws.lean','kiplmc2Laws_probability')], r'''The coordinate equations use the new-position force and two independent Gaussian thermostat vectors. Their Markov law is constructed.'''),
    'discrete-equilibrium': ([('KineticLangevin/ExactOBABO.lean','exactObaboStep_preserves_target'),('KineticLangevin/OBABOBias.lean','obabo_wasserstein_bound')], r'''The proof obtains a stronger direct sampling estimate by comparing OBABO with an exact Gibbs-preserving O–Hamiltonian–O step and accumulating its local defect. No discrete invariant-law or external bias theorem is assumed.'''),
    'obabo-scaling': ([('KIPLMC/OBABORescaling.lean','kiplmc2Laws_unitTemperature'),('KIPLMC/OBABOBound.lean','obaboBias_unitTemperature'),('KIPLMC/OBABOPaperRate.lean','kiplmc2_paper_envelope')], r'''Exact algorithm and Gaussian-law conjugacy cancel the particle clock factors. The smaller thermal discretization term implies the supplied coarse rate with an explicit constant depending only on m, L and gamma.'''),
    'obabo-bound': ([('KIPLMC/OBABOPaperRate.lean','kiplmc2_parameter_paper_bound'),('KIPLMC/Accuracy.lean','kiplmc2_accuracy')], r'''The supplied theorem, including both transient terms, follows for the Gaussian sampler. Positive step, integer particle and rounded iteration prescriptions give a finite epsilon guarantee.'''),
    'complexity-and-experiments': ([('KIPLMC/Accuracy.lean','accuracyParticleCount_spec'),('KIPLMC/Accuracy.lean','accuracyStep_spec'),('KIPLMC/Accuracy.lean','complexity_dimension_identity'),('KIPLMC/Accuracy.lean','kiplmc2_accuracy')], r'''The finite error allocations and source dimension identity are proved. Reported numerical traces and timing measurements remain empirical observations, not mathematical universal claims.'''),
})

for _item in KIPLMC_PROOF:
    if _item['id'] == 'discrete-equilibrium':
        _item['body'] += r'''<p>A second argument compares the chain with a transition preserving Gibbs and does not require a discrete invariant law. The earlier kinetic report proves that an exact O–Hamiltonian–O step preserves the continuous Gibbs target (see <cite data-report-ref="KineticLangevin/ExactOBABO.lean" data-report-declaration="exactObaboStep_preserves_target"></cite>). Compare it with the OBABO update on the same initial state and the same Gaussian vectors. The Verlet local defect has L² cost of order \(h^2\sqrt{d_z}\). The earlier kinetic perturbation theorem sums this cost directly over the chain (see <cite data-report-ref="KineticLangevin/OBABOBias.lean" data-report-declaration="obabo_wasserstein_bound"></cite>). The resulting bound with the thermal dimension factor is stronger than the supplied coarse estimate, so it also implies every term retained in the printed theorem.</p>'''

for _item in KINETIC_PROOF:
    if _item['id'] == 'complexity':
        _item['references'] += [dict(file='KineticLangevin/SecondOrderAccuracy.lean',name='klmc2_accuracy_explicit'),dict(file='KineticLangevin/SecondOrderBudget.lean',name='secondOrderAccuracyStep_spec')]
        _item['note'] = r'''Both samplers now have explicit epsilon guarantees, positive minimum steps, and rounded natural logarithmic counts. The second-order prescription uses the exact dimension term and the proved inverse-step-square tail envelope.'''
    if _item['id'] == 'noise':
        _item['references'] += [dict(file='KineticLangevin/GaussianFactor.lean',name='klmc_cholesky_independent_normals')]
        _item['note'] += r''' The paper’s explicit positive-diagonal Cholesky factor maps two independent standard normals to exactly this same innovation law.'''

for _item in KIPLMC_PROOF:
    if _item['id'] == 'joint-geometry':
        _item['references'] += [dict(file='KIPLMC/LogisticExample.lean',name='jointPotential_gradient_lipschitz'),dict(file='KIPLMC/LogisticExample.lean',name='jointHessian_quadratic'),dict(file='KIPLMC/LogisticExample.lean',name='potential_strictConvex_of_span'),dict(file='KIPLMC/LogisticExample.lean',name='jointPotential_not_strongConvex')]
        _item['note'] = r'''The finite-observation logistic potential has the exact source gradient, block Hessian, global Lipschitz constant, convexity, and full-span strict convexity. Its failure of positive global joint strong convexity in a nontrivial space is proved, rather than inferred from strict convexity. The experimental example therefore has exactly the source’s stated assumption caveat.'''

# The additional source complexity paragraph has its own checked correction.
for _item in KINETIC_PROOF:
    if _item['id'] == 'complexity':
        _item['references'] += [
            dict(file='KineticLangevin/SecondOrderComplexity.lean',name='secondOrderTailFreeStep_spec'),
            dict(file='KineticLangevin/SecondOrderComplexity.lean',name='secondOrderTailFreeStep_inverse'),
            dict(file='KineticLangevin/SecondOrderComplexity.lean',name='secondOrderTailFree_iterationCount_conditionNumber'),
            dict(file='KineticLangevin/ConditionNumber.lean',name='secondOrderNormalizedWork_physical_regime'),
            dict(file='KineticLangevin/ConditionNumber.lean',name='secondOrderSourceRefinement_no_uniform_constant')]
        _item['note'] += r''' The source paragraph that omits the Gaussian tail is also audited: its exact step and natural count are proved, the corrected condition-number envelope has constant 64, and a formal natural-dimension counterexample rules out the unrestricted printed bound.'''
