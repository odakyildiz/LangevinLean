"""Detailed mathematical arguments for the strongly convex developments.

These are authored mathematical explanations, shared by the web overviews and
paper exports. References identify the corresponding statements on the website.
"""


def part(identifier, title, body, file, name):
    return dict(id=identifier, title=title, body=body,
                references=[dict(file=file, name=name)])


ULA_PROOF = [
part('quadratic-models', 'From convexity and smoothness to sharp contraction', r'''
<p>Write \(g=\nabla U\). Strong convexity and gradient Lipschitzness give the complementary quadratic models</p>
\[U(x)+\langle g(x),y-x\rangle+\frac m2\|y-x\|^2
\le U(y)\le U(x)+\langle g(x),y-x\rangle+\frac L2\|y-x\|^2.\]
<p>The lower inequality follows by subtracting \(m\|x\|^2/2\) and using the supporting-plane inequality for a differentiable convex function. For the upper inequality, integrate the gradient along the segment from \(x\) to \(y\); the remainder is bounded by \(L\int_0^1t\,dt\,\|y-x\|^2\). Thus no Hessian assumption is required.</p>
<p>Apply cocoercivity to the shifted function \(U-m\|\cdot\|^2/2\), whose quadratic upper-model constant is \(L-m\). With \(d=x-y\) and \(v=g(x)-g(y)\), expanding its conclusion yields</p>
\[mL\|d\|^2+\|v\|^2\le(m+L)\langle v,d\rangle.\]
<p>Completing the square makes the geometry explicit:</p>
\[\left\|v-\frac{m+L}{2}d\right\|\le\frac{L-m}{2}\|d\|.\]
<p>Consequently the triangle inequality bounds \(\|d-hv\|\) by</p>
\[\left(\left|1-\frac{m+L}{2}h\right|+\frac{L-m}{2}h\right)\|d\|.\]
<p>For \(0\le h\le2/(m+L)\), the factor is \(1-mh\). For \(2/(m+L)\le h\le2/L\), it is \(Lh-1\). The boundary \(m=L\) is included because the centered ball then has radius zero; there is no division by \(L-m\).</p>
''', 'UnadjustedLangevin/SharpContraction.lean', 'strong_smooth_gradient_step_contract_max'),
part('gibbs-moments', 'Normalize the target and control its score', r'''
<p>Strong convexity gives, at any fixed \(x_0\), a quadratic lower bound for \(U(x)\). Completing its square shows that \(e^{-U(x)}\), even when multiplied by any fixed quadratic polynomial in \(x\), is dominated by an integrable translated Gaussian. Therefore the partition function is finite, strictly positive, and the normalized Gibbs law has a finite second moment.</p>
<p>A second moment needed below concerns the gradient. The smooth upper model implies, for any \(v\),</p>
\[U(x-v)\le U(x)-\langle g(x),v\rangle+\frac L2\|v\|^2.\]
<p>Exponentiate the rearranged inequality and integrate. Translation of Lebesgue measure preserves the partition function, giving</p>
\[\int e^{\langle g(x),v\rangle}\,\pi(dx)\le e^{L\|v\|^2/2}.\]
<p>For each unit coordinate vector, use both signs of a scalar multiple of that vector. The resulting sub-Gaussian bound yields a centered directional score with second moment at most \(L\). Summing over an orthonormal basis gives</p>
\[\int\|g(x)\|^2\,\pi(dx)\le Ld.\]
<p>This derivation uses the original first-derivative assumptions. It also proves the gradient integrability that will justify drift integrals, rather than treating that integrability as an additional assumption.</p>
''', 'UnadjustedLangevin/GibbsScore.lean', 'integral_norm_sq_gradient_gibbs_le_of_strongConvex'),
part('stationary-reference', 'Construct a stationary comparison diffusion', r'''
<p>Take the constructed centered Gaussian process \(B_t\), with independent increments, covariance \(\mathbb E[B_sB_t^{\mathsf T}]=\min(s,t)I_d\), and continuous dependence on time in mean square. Choose it independently of \(Y_0\sim\pi\). In the Hilbert space of square-integrable random vectors, solve</p>
\[Y_t=Y_0-\int_0^t g(Y_s)\,ds+\sqrt2 B_t.\]
<p>The drift induces an \(L\)-Lipschitz map on that Hilbert space. Picard iteration converges on finite time intervals, and the integral inequality for the difference of two candidate solutions gives uniqueness by Gronwall. The resulting process is continuous in mean square. Brownian increments on disjoint intervals are independent and have covariance equal to the interval length.</p>
<p>Stationarity needs a separate argument. Start a Metropolis-adjusted Euler chain in \(\pi\). Detailed balance makes every adjusted marginal exactly \(\pi\). At a mesh size \(\delta\), the expected rejection-weighted displacement under Gibbs is at most \(C\delta^{3/2}\), where \(C\) is finite and independent of sufficiently small \(\delta\). Common-noise proposals are nonexpansive in the small-step regime, so iterating the coupled transition for \(n\) steps gives a joint law of the unadjusted and adjusted endpoints with mean separation at most \(nC\delta^{3/2}\).</p>
<p>Fix a horizon \(T>0\), take \(\delta=T/n\), and realize the unadjusted endpoint using the Brownian mesh increments. The bound becomes</p>
\[\mathbb E\|X_n^{\mathrm{Euler}}-X_n^{\mathrm{adjusted}}\|
\le TC\sqrt\delta\longrightarrow0.\]
<p>The matching-input Euler theorem also gives convergence of the unadjusted endpoint to \(Y_T\) in mean square. For a frequency \(v\), the bounded characteristic test \(x\mapsto e^{i\langle v,x\rangle}\) has Lipschitz constant \(\|v\|\). Its expectations therefore converge both under the vanishing mean-separation coupling and under mean-square Euler convergence. Since the adjusted endpoint has law \(\pi\), the characteristic function of \(Y_T\) equals that of \(\pi\). Uniqueness of characteristic functions proves \(\operatorname{Law}(Y_T)=\pi\). At \(T=0\), the conclusion is the initialization assumption.</p>
<p>Hence \(\|g(Y_t)\|_{L^2}\le\sqrt{Ld}\) uniformly in time. The construction supplies both the stationary law and the independent future Brownian increments needed for the one-step comparison.</p>
''', 'UnadjustedLangevin/GibbsStationarity.lean', 'lp_langevin_gibbs_stationary'),
part('local-defect', 'Integrate the local Euler error with its constants', r'''
<p>On an interval of length \(h\), start the stationary process at \(Y_0\). Define the omitted drift integral</p>
\[R_h=\int_0^h\bigl(g(Y_s)-g(Y_0)\bigr)\,ds.\]
<p>The integral equation is exactly \(Y_h=Y_0-hg(Y_0)+\sqrt2B_h-R_h\). Minkowski's inequality and stationarity first give</p>
\[\|Y_s-Y_0\|_{L^2}\le s\sqrt{Ld}+\sqrt{2ds}.\]
<p>Indeed the drift integral has norm at most \(\int_0^s\sqrt{Ld}\,du\), and \(\|B_s\|_{L^2}=\sqrt{ds}\). Lipschitzness now controls the integrand defining \(R_h\), so</p>
\[\begin{aligned}
\|R_h\|_{L^2}
&\le L\int_0^h\bigl(s\sqrt{Ld}+\sqrt{2ds}\bigr)\,ds\\
&=L\left(\frac{h^2}{2}\sqrt{Ld}+\frac23h^{3/2}\sqrt{2d}\right).
\end{aligned}\]
<p>If \(Lh\le2\), factor out \(Lh\sqrt{hd}\). The remaining coefficient is at most \(\sqrt2/2+2\sqrt2/3=7\sqrt2/6\le33/20\). Thus</p>
\[\|R_h\|_{L^2}\le\frac{33}{20}Lh\sqrt{hd}.\]
<p>The factor \(h^{3/2}\) is crucial: dividing this local error by a contraction gap of order \(h\) will leave the global \(\sqrt h\) bias.</p>
''', 'UnadjustedLangevin/LocalError.lean', 'localDefect_dalalyan_bound'),
part('synchronous-coupling', 'Compare the discrete and stationary paths', r'''
<p>Choose any initial coupling of \(X_0\sim\mu_0\) and \(Y_0\sim\pi\) having finite quadratic cost. Extend it with Brownian noise independent of both initial states. Use the increments \((B_{(k+1)h}-B_{kh})/\sqrt h\) as the Gaussian innovations for the numerical chain. Their independence identifies its marginals with \(\mu_k\), regardless of the chosen initial coupling.</p>
<p>Subtracting the integral equation for \(Y\) from the numerical update cancels the common Gaussian increment. With \(T_h(x)=x-hg(x)\),</p>
\[X_{k+1}-Y_{(k+1)h}=T_h(X_k)-T_h(Y_{kh})+R_{k,h}.\]
<p>The deterministic contraction applies pointwise to the first difference, and the local estimate applies to the stationary reference on every interval. Consequently, for \(a_k=\|X_k-Y_{kh}\|_{L^2}\),</p>
\[a_{k+1}\le q a_k+b,\qquad b=\frac{33}{20}Lh\sqrt{hd},\]
<p>where \(q=1-mh\) or \(q=Lh-1\) in the corresponding step regime. Both satisfy \(0\le q&lt;1\). Every \((X_k,Y_{kh})\) is a coupling of \(\mu_k\) with \(\pi\), so its cost bounds the Wasserstein distance. All variables remain square-integrable by the Lipschitz update and the Gaussian second moment.</p>
''', 'UnadjustedLangevin/HilbertDalalyan.lean', 'dalalyan_small_step_of_integral_reference'),
part('geometric-sum', 'Sum the recurrence and take the transport infimum', r'''
<p>Induction on \(k\) gives the exact finite geometric sum</p>
\[a_k\le q^ka_0+b\sum_{j=0}^{k-1}q^j
=q^ka_0+\frac{b(1-q^k)}{1-q}
\le q^ka_0+\frac b{1-q}.\]
<p>The denominator is positive because \(q&lt;1\). This bound holds for every finite-cost initial coupling, and its output laws do not depend on that coupling. Taking the infimum over the initial costs therefore replaces \(a_0\) by \(W_2(\mu_0,\pi)\); an optimal coupling need not be selected.</p>
<p>For the first regime, \(1-q=mh\), hence \(b/(1-q)=(33/20)(L/m)\sqrt{hd}\). For the second regime, \(1-q=2-Lh\), hence \(b/(1-q)=(33/20)Lh\sqrt{hd}/(2-Lh)\). These are exactly the two stated bounds. At \(h=2/(m+L)\), the two contraction factors and the two floors agree.</p>
<p>For fixed positive \(h\), only the initial-error term vanishes as \(k\) grows. To obtain arbitrarily small error one must also reduce \(h\). This explains separately the roles of iteration count and step size.</p>
''', 'UnadjustedLangevin/Recurrence.lean', 'affine_recurrence_exact'),
]


IPLA_PROOF = [
part('scaled-geometry', 'Lift the joint model in the right Euclidean geometry', r'''
<p>For \(N\ge1\), introduce \(z=(\theta,x^1/\sqrt N,\ldots,x^N/\sqrt N)\). Its squared norm is \(\|\theta\|^2+N^{-1}\sum_i\|x^i\|^2\). Let \(J_i z=(\theta,x^i)\). Replication of the common parameter and unscaling of the particle block give the exact identity</p>
\[\sum_{i=1}^N\|J_i(z-z')\|^2=N\|z-z'\|^2.\]
<p>Sum the strong-convexity inequalities for the joint potential at these pairs. The quadratic corrections sum to \(Nm\|z-z'\|^2/2\), proving that \(V_N=\sum_iU_y\circ J_i\) is \(Nm\)-strongly convex. To prove the \(NL\) gradient Lipschitz constant, differentiate through the linear maps \(J_i\), pair the gradient difference with a unit test vector, and apply Cauchy–Schwarz to the sum over particles. The same norm identity controls both factors.</p>
<p>Neither argument requires the parameter and latent dimensions to agree. The state dimension is \(D=d_\theta+Nd_x\), and zero-dimensional blocks contribute zero to all sums and norms.</p>
''', 'IPLA/Geometry.lean', 'potential_gradient_lipschitz'),
part('algorithm-law', 'Identify the particle algorithm with a Gaussian Euler step', r'''
<p>The derivatives of the lifted potential are</p>
\[\nabla_\theta V_N(z)=\sum_i\nabla_\theta U_y(\theta,x^i),\qquad
\nabla_{z_i}V_N(z)=\sqrt N\nabla_xU_y(\theta,x^i).\]
<p>Apply Gaussian ULA to \(V_N\) with step \(s=\gamma/N\). In the parameter coordinates, its drift is the average of the joint parameter gradients and its noise amplitude is \(\sqrt{2\gamma/N}\). In a latent block, multiply the update by \(\sqrt N\); the drift coefficient becomes \(\gamma\), and the noise amplitude becomes \(\sqrt{2\gamma}\). This recovers exactly the two displayed IPLA updates.</p>
<p>The innovation vectors are independent of the full past, so conditioning on the present state gives the lifted Gaussian transition. Iterating this kernel therefore gives the laws of the stated particle recursion. The scaled step condition \(s\le2/(Nm+NL)\) is precisely \(\gamma\le2/(m+L)\).</p>
''', 'IPLA/Geometry.lean', 'scaledUpdate_particle'),
part('parameter-target', 'Integrate out the latent variables', r'''
<p>Strong convexity normalizes the lifted Gibbs density and gives its second moment. To identify its parameter marginal, first change variables from the scaled blocks to the original latent vectors. The Jacobian is constant in \(\theta\) and disappears upon normalization. The remaining latent integral factors:</p>
\[\int\exp\!\left(-\sum_iU_y(\theta,x^i)\right)\prod_i dx^i
=\prod_i\int e^{-U_y(\theta,x)}dx=\ell_y(\theta)^N.\]
<p>All integrands are nonnegative, so Tonelli justifies the factorization before finiteness is used. Positivity and finiteness of each marginal integral make \(F(\theta)=-\log\ell_y(\theta)\) well-defined.</p>
<p>To show that \(F\) is \(m\)-strongly convex, remove the parameter quadratic from \(U_y\). The resulting exponential is jointly log-concave. The Prékopa–Leindler inequality, proved by coordinate tensorization, preserves log-concavity after latent integration. Restoring the quadratic yields the claimed curvature. Coercivity and continuity give a minimizer, and strong convexity makes it unique. This point is exactly the marginal-likelihood maximizer \(\theta_\star\).</p>
''', 'IPLA/StrongLogConcavity.lean', 'marginalPotential_strongConvex'),
part('equilibrium-radius', 'Bound equilibrium parameter fluctuations', r'''
<p>The parameter marginal has potential \(NF\), hence curvature \(Nm\), and its minimizer is \(\theta_\star\). The strongly log-concave concentration estimate used for this theorem gives</p>
\[\int\|\theta-\theta_\star\|^2\,\Pi_N(dz)\le\frac{2d_\theta}{Nm}.\]
<p>This is a bound around the marginal mode, rather than the joint mode in the full particle space. The distinction matters: minimizing the joint potential over latent coordinates is generally different from integrating those coordinates out. Taking a square root gives the equilibrium parameter radius \(r_N=\sqrt{2d_\theta/(Nm)}\).</p>
<p>The radius depends on the parameter dimension alone, even though the numerical process evolves in dimension \(D\). If \(d_\theta=0\), the projection has a single value and the radius is zero. The sharper concentration estimate used in later proximal and kinetic results is established separately in the supporting arguments.</p>
''', 'IPLA/Concentration.lean', 'gibbsTarget_parameter_concentration'),
part('transport-projection', 'Project the full-state transport bound', r'''
<p>Let \(Pz=\theta\). It is a linear contraction: \(\|P(z-z')\|\le\|z-z'\|\). For any coupling \((Z,Z_*)\) of the numerical state law \(\mu_k\) and \(\Pi_N\), Minkowski's inequality gives</p>
\[\begin{aligned}
\|PZ-\theta_\star\|_{L^2}
&\le\|P(Z-Z_*)\|_{L^2}+\|PZ_*-\theta_\star\|_{L^2}\\
&\le\|Z-Z_*\|_{L^2}+r_N.
\end{aligned}\]
<p>Take the infimum over all finite-cost couplings. This proves \(\|\theta_k-\theta_\star\|_{L^2}\le W_2(\mu_k,\Pi_N)+r_N\). Finiteness of the Gibbs and algorithmic second moments ensures that these are ordinary finite quantities. The projection step uses no independence among particles at equilibrium or at finite time.</p>
''', 'IPLA/Geometry.lean', 'norm_parameterCLM_apply_le'),
part('particle-scaling', 'Simplify the sampling constants and assemble the result', r'''
<p>Insert the lifted curvature \(Nm\), smoothness \(NL\), dimension \(D=d_\theta+Nd_x\), and step \(s=\gamma/N\) into the ULA theorem. Its contraction factor becomes \(1-(Nm)s=1-m\gamma\), while</p>
\[\frac{NL}{Nm}\sqrt{sD}
=\frac Lm\sqrt{\gamma\left(d_x+\frac{d_\theta}{N}\right)}.\]
<p>Adding the equilibrium radius from the projection argument produces the stated IPLA parameter bound. Every power of \(N\) comes from an explicit coordinate or time scaling: the parameter noise and equilibrium radius decrease with \(N\), while the latent contribution to the discretization floor remains of order \(\sqrt{\gamma d_x}\).</p>
<p>Thus increasing particle count alone does not remove numerical bias. The three error contributions are controlled by different choices: \(N\) controls equilibrium concentration, \(\gamma\) controls discretization, and \(k\) controls the remaining initialization error. Unequal dimensions require no further change in the proof.</p>
''', 'IPLA/Theorem.lean', 'theorem1'),
]


PROXIMAL_PROOF = [
part('proximal-calculus', 'Construct the proximal map and differentiate the envelope', r'''
<p>For \(\eta&gt;0\), adding \(\|p-x\|^2/(2\eta)\) to the finite convex function \(g_2(p)\) gives a coercive, strictly convex objective. It therefore has a unique minimizer \(P_\eta(x)\). The optimality inequalities at two starting points, added together, give firm nonexpansiveness:</p>
\[\|P_\eta(x)-P_\eta(y)\|^2\le
\langle P_\eta(x)-P_\eta(y),x-y\rangle.\]
<p>Expanding the squared difference of the residuals shows that \(I-P_\eta\) is also nonexpansive. Comparing the envelope value at \(x+u\) using the minimizer at \(x\), and conversely, gives upper and lower first-order bounds with a quadratic remainder. Their common derivative is</p>
\[\nabla g_2^\eta(x)=\frac{x-P_\eta(x)}\eta.\]
<p>The residual estimate makes this gradient \(\eta^{-1}\)-Lipschitz. The envelope is convex, so \(V_\eta=g_1+g_2^\eta\) retains curvature \(m\) and has smoothness \(L_\eta=L_1+\eta^{-1}\). These facts permit the smoothed particle recursion to use the preceding sampling theorem.</p>
''', 'ProximalLangevin/Moreau.lean', 'gradient_moreau'),
part('finite-smoothing-gap', 'Control smoothing by a finite potential sandwich', r'''
<p>The minimizer comparison \(p=x\) gives \(g_2^\eta(x)\le g_2(x)\). Lipschitzness supplies the reverse estimate: for every \(p\),</p>
\[g_2(p)+\frac{\|p-x\|^2}{2\eta}
\ge g_2(x)-K\|p-x\|+\frac{\|p-x\|^2}{2\eta}
\ge g_2(x)-\frac{\eta K^2}{2}.\]
<p>The last inequality completes the scalar square in \(\|p-x\|\). Evaluating at the actual minimizer proves</p>
\[V_\eta\le U\le V_\eta+\delta_\eta,\qquad\delta_\eta=\eta K^2/2.\]
<p>Exponentiation and latent integration preserve this finite sandwich. If \(F_U,F_\eta\) are the negative log marginal likelihoods, then \(F_\eta\le F_U\le F_\eta+\delta_\eta\). In particular the nonsmooth original marginal is integrable and its center exists by comparison with the strongly convex smoothed model.</p>
''', 'ProximalLangevin/Moreau.lean', 'moreau_gap_of_lipschitz'),
part('center-stability', 'Transfer the potential gap to the statistical centers', r'''
<p>Let \(\theta_U\) and \(\theta_\eta\) minimize \(F_U\) and \(F_\eta\), respectively. Strong convexity of \(F_\eta\) gives quadratic growth at its minimizer. Combining it with the sandwich and minimality of \(\theta_U\) gives the full chain</p>
\[\begin{aligned}
\frac m2\|\theta_U-\theta_\eta\|^2
&\le F_\eta(\theta_U)-F_\eta(\theta_\eta)\\
&\le F_U(\theta_U)-F_\eta(\theta_\eta)\\
&\le F_U(\theta_\eta)-F_\eta(\theta_\eta)
\le\delta_\eta.
\end{aligned}\]
<p>Hence \(\|\theta_U-\theta_\eta\|\le K\sqrt{\eta/m}\). This is a finite estimate for actual marginal-likelihood centers, valid for every positive \(\eta\). It does not require differentiating the original nonsmooth potential. Its order is \(\sqrt\eta\), so a linear smoothing rate cannot be substituted into the final theorem.</p>
''', 'ProximalLangevin/Perturbation.lean', 'marginal_center_distance'),
part('smoothed-particle-bound', 'Derive the MYIPLA bound around the original center', r'''
<p>MYIPLA is exactly IPLA for \(V_\eta\). Its scaled target has curvature \(Nm\), smoothness \(NL_\eta\), and dimension \(D=d_\theta+Nd_x\). The ULA step is \(\gamma/N\), so the contraction factor is \(1-m\gamma\). Apply the shared sampling theorem and then project to the parameter coordinates.</p>
<p>The sharp concentration result for the smoothed marginal gives radius \(\sqrt{d_\theta/(Nm)}\). Finally Minkowski's inequality adds the deterministic displacement between the smoothed and original centers. Thus the four terms are respectively</p>
\[K\sqrt{\eta/m},\quad\sqrt{\frac{d_\theta}{Nm}},\quad
(1-m\gamma)^nW_2(\rho_0,\Pi_{N,\eta}),\quad
\frac{33}{20}\frac{L_\eta}{m}\sqrt{\gamma\left(d_x+\frac{d_\theta}{N}\right)}.\]
<p>Reducing \(\eta\) improves the first term but increases \(L_\eta\) and tightens the admissible step restriction. The smoothing and discretization parameters must therefore be chosen together. Each term has been controlled for the actual Gaussian particle law.</p>
''', 'ProximalLangevin/Theorem.lean', 'moreau_myipla_parameter_rms_original'),
part('splitting-energy', 'Control PIPGLA at the matching proximal parameter', r'''
<p>First take \(\lambda=\gamma\). The smooth-gradient/noise step is followed by pairwise proximal maps, and the common parameter is their average. Use the same Gaussian increment for the numerical step and a stationary reference for \(V_\gamma\). Expanding the squared coupling error keeps the inner products generated by the proximal optimality inequality; these terms must be combined before any absolute-value estimate is made.</p>
<p>With \(a=Nm\), \(b=NL_1\), \(c=NK\), the stationary drift and noise bounds can be expressed as \(G=\sqrt{2b^2D/a+2c^2}+c\) and \(\sigma=\sqrt{2D}\). The local increment bound is \(Gs+\sigma\sqrt s\). Squaring it uses \((u+v)^2\le2u^2+2v^2\), and \(s\le1/a\) absorbs its higher-order powers into the explicit constant</p>
\[C_N=\frac{4b^2}{a^2}\left(\frac{G^2}{a}+\sigma^2\right)+\frac2a(Gc+c^2).\]
<p>More explicitly, with \(\delta=N\gamma K^2/2=sc^2/2\), the one-step forcing is</p>
\[\mathcal F=(1+(as)^{-1})[bs(Gs+\sigma\sqrt s)]^2+2s\delta+2s^2Gc+s^2c^2.\]
<p>The first term is the weighted smooth drift defect. Convex support, stationarity and orthogonality to future Brownian increments combine the reference-force cross term with the original nonsmooth energy difference, leaving \(2s\delta+2s^2Gc\). The last term is the genuine proximal energy remainder. Since \(s\le1/a\), bounding the drift-plus-noise square gives \(\mathcal F\le as^2C_N\). The resulting squared-error recurrence has contraction \(1-a s=1-m\gamma\). Taking the initial coupling infimum and summing the geometric series gives</p>
\[W_2(\rho_n,\Pi_{N,\gamma})^2
\le(1-m\gamma)^nW_2(\rho_0,\Pi_{N,\gamma})^2+\frac\gamma N C_N.\]
<p>After taking a square root, projection adds the sharp equilibrium radius, and the finite center comparison adds \(K\sqrt{\gamma/m}\). The squared recurrence explains why its transient factor occurs inside a square root in the theorem.</p>
''', 'ProximalLangevin/SplittingRate.lean', 'splittingCouplingForcing_le'),
part('proximal-parameter', 'Compare different positive proximal parameters', r'''
<p>For a convex \(K\)-Lipschitz penalty, the proximal optimality relations and monotonicity of its subgradient give</p>
\[\|P_\lambda(x)-P_\eta(x)\|\le K|\lambda-\eta|.\]
<p>Apply this comparison particle by particle, using the same initial state and innovations in the two splitting chains. Averaging the parameter outputs and using the scaled norm controls the full-state discrepancy by \(K|\lambda-\eta|\) per step. The smooth step contracts by \(q=1-m\gamma\); nonexpansiveness of the proximal map preserves that contraction.</p>
<p>Starting from zero discrepancy, the finite geometric sum therefore bounds the difference of the two chains by \(K|\lambda-\eta|/(1-q)=K|\lambda-\eta|/(m\gamma)\), uniformly in iteration count. Set \(\eta=\gamma\) and combine with the matching-parameter result. The triangle inequality for parameter RMS adds precisely the first term of the displayed PIPGLA theorem.</p>
''', 'ProximalLangevin/SplittingTheorem.lean', 'pipgla_parameter_rms_prox_comparison'),
part('noise-removal', 'Compare MYPGD with the full-noise chain', r'''
<p>Start from any finite-cost coupling of the current MYPGD and MYIPLA laws, and extend it by a fresh independent standard Gaussian vector. Use that vector's latent block in both updates and retain its parameter block only in the full-noise update. The omitted parameter innovation is centered and has squared \(L^2\) norm \(2\gamma d_\theta/N\). Independence therefore cancels its expected cross term with the deterministic forward discrepancy.</p>
<p>The shared forward map contracts by \(1-m\gamma\). Thus the constructed output coupling has squared cost at most \((1-m\gamma)^2\) times the input squared cost plus the omitted-noise variance. Taking the infimum over input couplings proves, for \(E_n=W_2(\rho_n^{\mathrm{PGD}},\rho_n^{\mathrm{MYIPLA}})^2\),</p>
\[E_{n+1}\le(1-m\gamma)^2E_n+\frac{2\gamma d_\theta}{N},\qquad E_0=0.\]
<p>The initial distance is zero because the two chains have the same initial law. Their finite moments justify all transport squares. The step restriction implies \(0\le m\gamma\le1\). Hence \(1-(1-m\gamma)^2=m\gamma(2-m\gamma)\ge m\gamma\), and geometric summation gives \(E_n\le2d_\theta/(Nm)\). The parameter projection is nonexpansive, so the coupling RMS inequality and this transport bound add \(\sqrt{2d_\theta/(Nm)}\) to the MYIPLA parameter bound.</p>
<p>This establishes the stated finite-particle MYPGD guarantee directly. The added radius is conservative and remains present for finite \(N\); it does not imply a stronger mean-field metric estimate. The supporting mean-field construction and particle comparisons are developed separately.</p>
''', 'ProximalLangevin/MYPGDTheorem.lean', 'mypgd_myipla_actual_transport_sq'),
]
