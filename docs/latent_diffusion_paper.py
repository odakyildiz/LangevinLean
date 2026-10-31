"""Readable source statements and corrections for the latent-diffusion report.

This is authoring content, not an independent proof certificate.  Source labels,
line ranges, exact TeX and Lean endpoints come from reference_audit.json.  Every
entry states the mathematical claim before discussing its formal scope.  In
particular, analytical repair suggestions are not presented as proved Lean
theorems merely because their scalar consequences have been checked.
"""

MAIN = "papers/Latent_diffusion/main_aistats.tex"
SUPP = "papers/Latent_diffusion/supp_aistats.tex"


PAPER_RESULTS = {
    "prop:ftildemins": {
        "title": "Variational characterization of the tilted likelihood",
        "statement": r"""<p>Let \(M\ge1\), let \(\rho_u^m(z)=\widetilde p_u(x^m,z)\),
        and suppose \(0\lt A_u^m=\int\rho_u^m\,dz\lt\infty\). Set
        \(\pi_u^m=\rho_u^m/A_u^m\) and
        \(\widetilde\ell(u)=M^{-1}\sum_m\log A_u^m\). On the domain where the
        density integrals and relative entropies are finite, and the normalized
        posteriors are admissible comparison laws,</p>
        \[\widetilde F(u,q)=-\widetilde\ell(u)
          +\frac1M\sum_m\mathrm{KL}(q^m\Vert\pi_u^m).\]
        <p>Consequently \((u_\star,q_\star)\) is a global minimizer exactly when
        \(u_\star\) globally maximizes \(\widetilde\ell\) and
        \(q_\star^m=\pi_{u_\star}^m\) for every datum. In particular \(u\)
        maximizes \(\widetilde\ell\) if and only if it is the parameter
        component of some global variational minimizer.</p>""",
        "correction": r"""The normalizer integrates the tilted density over
        \(z=z_0\), the latent variable on which it was defined in
        <code>eq:ptildedef</code> (main, lines 100–102). The occurrence of
        \(z_{0:K}\) in the proposition's normalizer is inconsistent with that
        definition. Positivity, finiteness, admissibility and integrability are
        explicit here. On the paper's \(\mathcal P_2\) domain the normalized
        posteriors must in particular have finite second moments; positive
        finite normalizers alone do not guarantee this. Arbitrary extended-integral conventions are not silently
        converted to real arithmetic. This proposition concerns the tilted
        likelihood. The subsequent inference about the original likelihood
        requires the separate zero-tilt correction below.""",
        "scope": 'The corrected literal-density variational characterization is proved for every actual finite-KL trial law. Its Radon–Nikodym density, posterior normalization and integral identity are derived. R1 makes the chosen finite-second-moment comparison domain explicit.',
    },
    "thm:exp_convg_informal": {
        "title": "Unique tilted optimizer and exponential parameter convergence",
        "statement": r"""<p>Let \(M\ge1\), and let the actual tilted potentials \(U_m=-\log\rho^m\) be differentiable and satisfy A3. Under the explicitly stated extra assumptions R1–R4, the average tilted evidence has a unique maximizer \(u_\star=(\theta_\star,\phi_\star)\). The classical parameter/density equations satisfy</p>
 \[\|u_t-u_\star\|\le\sqrt{\frac{2[\widetilde F(u_0,q_0)-\widetilde F_\star]}{\lambda}}e^{-\lambda t},\qquad t\ge0.\]
 <p>The potential normalizers and finite-second-moment posteriors are constructed from their actual integrals. Energy dissipation, the entropy transport tangent, extended LSI and the decay estimate are proved from the equations and the orange extra assumptions.</p>""",
        "correction": r"""A2 must be interpreted on an admissible initial class,
        or require smooth densities only for positive time. Its literal
        quantification over all \(\mathcal P_2\) initial laws is contradicted by
        Dirac laws. Entropy differentiation and transport control need the
        explicit analytic hypotheses above. The averaged joint potential is
        strongly convex in the normalized product norm
        \(\|u\|^2+M^{-1}\sum_m\|z^m\|^2\); the sketch at main lines 168–174
        must use that norm when retaining the constant \(\lambda\).""",
        "scope": 'The actual strongly convex density model has a unique evidence maximizer and finite-second-moment posteriors. Under R1–R4, the classical flow equations prove de Bruijn; regular transport proves extended LSI and the parameter and product-state exponential estimates. Dissipation and first-order transport inequalities are not added assumptions.'    },
    "thrm:error-bound": {
        "title": "Nonasymptotic error of the full-batch Euler scheme",
        "statement": r"""<p>For the full-batch exact-gradient Euler–Maruyama
        recursion in <code>eq:disc_theta</code>–<code>eq:disc_par</code>, the source
        assumes A1–A4 and Lipschitz gradients of \(R\). For sufficiently small
        \(h>0\) it states</p>
        \[\bigl(\mathbb E\|u_T^{N,h}-u_\star\|^2\bigr)^{1/2}
          \le C_{h,N}+C\rho^T,\qquad
          C_{h,N}=O(\sqrt h+N^{-1/2}),\quad T\in\mathbb N.\]
        <p>Here \(C_{h,N}\) is independent of \(T\), \(C\) is independent of
        \((h,N,T)\), and \(0\lt\rho\lt1\) may depend on \(h\). The checked
        contraction factor is \(\rho=1-\lambda h/2\), with
        \(\rho^T\le e^{-\lambda hT/2}\). Uniform constants require the stated initialization and
        moment controls. With \(K=MN\), latent dimension \(d_z\) and the R7
        per-copy score variance bound \(V_0\), the checked bound has
        \(C=\|X_0-S_0\|_{L^2}\), the normalized initial distance from the
        Euler initialization \(X_0\) to the posterior-initialized reference
        \(S_0\), and
        \(C_{h,N}=\frac2\lambda\sqrt{V_0/K}+\frac L\lambda\bigl(h\sqrt{Ld_z}+\frac43\sqrt{2d_z}\sqrt h\bigr)\).</p>""",
        "correction": r"""The temporal lemma contains an extra square-root
        factor; its corrected general estimate is \(C\sqrt h\), not the
        \(O(h)\) accidentally written there. The empirical comparison needs a
        specified coupling, and the spatial comparison needs compatible
        initialization and uniform moments. This theorem concerns the full
        batch method, as the paper itself states at main line 314. It gives no
        guarantee for Algorithm 1's changed minibatch temperature or the adaptive
        algorithm.""",
        "scope": 'The corrected full-batch result uses actual continuous \\(L^2\\) Brownian integral dynamics and stable Euler recursion under R7, with a fixed per-copy variance bound \\(V_0\\) independent of particle count. Global reference paths, Gibbs stationarity, score centering at the evidence optimum, moment bounds and finite-particle fluctuations are derived from the primitive model and initialization data. The separate orange new-theory result extends the error budget to a centered stochastic oracle.'    },
    "app:lemma_1st_var": {
        "title": "First variations of the free energy",
        "statement": r"""<p>For one datum, write
        \(V_u(z)=\mathcal L_D(\theta,z)-\log p_\phi(x\mid z)\) and
        \(\widetilde F(u,q)=\int[V_u+\log q]\,q\,dz\). For admissible
        variations \(r\) with \(\int r\,dz=0\), and parameter directions for
        which differentiation may pass through the integrals,</p>
        \[\delta_q\widetilde F=\log q+V_u\pmod{\mathbb R},\qquad
        \nabla_\theta\widetilde F=\int\nabla_\theta\mathcal L_D\,dq,\qquad
        \nabla_\phi\widetilde F=-\int\nabla_\phi\log p_\phi(x\mid z)\,dq.\]
        <p>Equivalently \(D_q\widetilde F[r]=\int(\log q+V_u)r\,dz\).
        The derivative of \(q\log q\) contains \(+1\); its integral against a
        probability tangent direction vanishes.</p>""",
        "correction": "The density first variation is a cotangent equivalence class modulo constants, as the source's own tangent construction specifies. An integrable dominating derivative or another valid interchange argument is needed for both the parameter Taylor remainder and entropy differentiation.",
        "scope": 'The actual parameter-integral Fréchet derivative and zero-mass density-direction derivative are proved under R2. For an actual continuity-equation variation, R3 integration by parts also derives its score pairing. The omitted additive constant is justified by the zero-total-mass tangent condition.'
    },
    "unlabelled-product-gradient": {
        "title": "Gradient under the normalized Euclidean–Wasserstein metric",
        "statement": r"""<p>Equip the product state with
        \(d^2((u,q),(v,r))=\|u-v\|^2+M^{-1}\sum_mW_2(q^m,r^m)^2\), and let
        \(V_u^m=\mathcal L_D(\theta,\cdot)-\log p_\phi(x^m\mid\cdot)\).
        Under the explicit first-variation and continuity-equation
        extra assumptions R2–R3, the parameter and density gradients are</p>
        \[\nabla_u\widetilde F=\frac1M\sum_m\int\nabla_u V_u^m\,dq^m,
        \qquad
        \nabla_{q^m}\widetilde F=-\nabla_z\!\cdot
           \bigl(q^m\nabla_z(\log q^m+V_u^m)\bigr).\]
        <p>Thus the descent flow has
        \(\dot u=-M^{-1}\sum_m\int\nabla_uV_u^m\,dq^m\) and
        \(\partial_tq^m=\nabla_z\cdot(q^m\nabla_zV_u^m)+\Delta q^m\).</p>""",
        "correction": r"""The inverse metric in each law block contributes
        \(M\), cancelling the objective's \(1/M\). There is consequently no
        additional \(1/M\) in the density drift or diffusion. These formulas
        use the descent loss \(V\), avoiding the inconsistent concise-loss sign
        in main lines 222–226.""",
        "scope": 'For every admissible parameter direction and classical continuity-equation velocity, R2–R3 prove the differential of the actual normalized density energy as its Riesz pairing with the averaged parameter force and each unscaled law score. Thus the density-block factor is derived from the normalized tangent metric.',
    },
    "prop:de_bruijin": {
        "title": "de Bruijn identity for the joint flow",
        "statement": r"""<p>For a solution with finite energy, finite score work,
        justified differentiation under the integrals, and vanishing boundary
        terms or a valid cutoff limit, set</p>
        \[I(u,q)=\|\nabla_u\widetilde F(u,q)\|^2+
          \frac1M\sum_m\int
          \left\|\nabla_z\log\frac{q^m}{\rho_u^m}\right\|^2dq^m.\]
        <p>The source identity, on that analytic domain, is</p>
        \[\frac d{dt}\widetilde F(u_t,q_t)=-I(u_t,q_t),\qquad t>0.\]""",
        "correction": "Classical local smoothness in A2 does not by itself supply entropy integrability, a dominating time derivative, finite Fisher information or integration by parts at infinity. The argument at supplement lines 503–524 needs those analytic justifications. A consistent initial-law version of A2 is also required.",
        "scope": 'Under R2–R3, the classical parameter ODE and Fokker–Planck PDE prove the derivative of the actual normalized energy equals minus the displayed source Fisher information. Fisher integrability is proved from the spatial tail products; neither dissipation nor an energy inequality is a premise.',
    },
    "lem:geodesic": {
        "title": "Geodesics in the normalized product space",
        "statement": r"""<p>On R4, assume finite-cost optimal maps exist
        between every pair of intermediate laws and the endpoint optimal maps
        \(T_m:q^m\to r^m\) are unique up to \(q^m\)-null sets.
        A path is a constant-speed geodesic for the normalized product distance
        if and only if, for the same \(s\in[0,1]\),</p>
        \[u_s=(1-s)u+sv,\qquad q_s^m=((1-s)\mathrm{id}+sT_m)_\#q^m.\]
        <p>For the R4 regular Brenier-map data, \(T_m=\nabla f^m\) with
        a convex potential and its actual gradient certificate, giving the
        source's gradient-map formula. Both directions of the product
        characterization are proved.</p>""",
        "correction": "Use the constant-speed endpoint parameterization in all factors. The corrected formal domain supplies finite-cost regular optimal maps between intermediate laws and uniqueness of endpoint maps; the gradient formulation additionally supplies the convex-potential gradient certificate. These are explicit R4 transport assumptions.",
        "scope": 'The corrected transport domain is R4: actual probability-law displacement interpolations supplied by smooth optimal maps with positive Jacobians and finite quadratic cost. The coupling infimum and normalized product geometry are used explicitly. Existence of a smooth map for arbitrary probability laws is not asserted.',
    },
    "lem:geodesic_convexity": {
        "title": "Strong geodesic convexity of the tilted free energy",
        "statement": r"""<p>Suppose each
        \(U_m(u,z)=-\log\rho_u^m(z)\) is jointly
        \(\lambda\)-strongly convex. For a constant-speed product
        Wasserstein geodesic \(\gamma_s\) between states \(a,b\), on a
        finite, integrable R1/R4 density-energy domain, the corrected result is</p>
        \[\widetilde F(\gamma_s)\le(1-s)\widetilde F(a)
          +s\widetilde F(b)-\frac\lambda2s(1-s)d(a,b)^2,
          \qquad 0\le s\le1.\]
        <p>The potential term uses joint strong convexity along optimal
        displacement interpolations; the negative entropy term uses
        displacement convexity.</p>""",
        "correction": 'The normalized product distance is essential for the constant to remain independent of \\(M\\). The corrected theorem uses finite entropy and integrable potentials along the full displacement interpolation; finite second moments alone do not imply those conditions.',
        "scope": 'Entropy displacement convexity is proved from the positive Jacobian change-of-variables formula. Joint A3 convexity gives the potential part, and the normalized data average yields the actual product transport inequality on R4. Entropy convexity itself is not an assumed bridge.',
    },
    "lem:lower_deriv": {
        "title": "First-order lower bound along a transport geodesic",
        "statement": r"""<p>Let \(\gamma_s\) run from \((u,q)\) to
        \((v,r)\), with initial optimal transport velocities
        \(w_m=T_m-\mathrm{id}\). Write
        \(s_m=\nabla_z\log(q^m/\rho_u^m)\). On R2–R4, use locally dominated
        time derivatives, the initial continuity equation for these actual
        transport velocities, and integrable spatial tails. Then</p>
        \[\liminf_{s\downarrow0}
          \frac{\widetilde F(\gamma_s)-\widetilde F(\gamma_0)}s
          \ge\langle v-u,\nabla_u\widetilde F(u,q)\rangle
          +\frac1M\sum_m\int\langle w_m,s_m\rangle\,dq^m.\]""",
        "correction": "Almost-everywhere differentiability of a density alone is insufficient. A finite-energy entropy-subgradient domain, finite score norm or another condition giving integrable transport pairings is required. The velocity formulation explicitly identifies the Wasserstein tangent pairing used in the source.",
        "scope": 'The actual density-energy derivative follows from dominated differentiation, the continuity equation and spatial integration by parts. Equality with the actual probability-law energy gives its right derivative and the displayed lower liminf with the law-integrated source pairing. This endpoint requires no strong-convexity or A3 hypothesis.',
    },
    "thm:sLC_implies_xLSI": {
        "title": "Strong log-concavity implies extended log-Sobolev control",
        "statement": r"""<p>For \(M\ge1\), jointly \(\lambda\)-strongly convex tilted potentials with \(\lambda>0\), and the finite-energy density/transport domain R1, R3 and R4,</p>
 \[2\lambda[\widetilde F(u,q)-\widetilde F_\star]\le I(u,q).\]
 <p>Sum the actual entropy and potential tangent pairings first. Completing one square for the averaged parameter force and the normalized latent squares proves the inequality with exactly the source Fisher information. The posterior optimizer is independently constructed before it is used.</p>""",
        "correction": "The proof chooses an admissible minimizer at supplement line 587 before its existence has been established in that chain. The checked marginal/posterior construction supplies it first. The entropy and potential tangent inequalities are then proved from the explicit extra assumptions.",
        "scope": 'Under A3, R1, R3 and R4, sum the actual entropy and potential tangent pairings toward the constructed posterior optimizer and complete the normalized parameter and latent squares. This proves extended LSI for the exact source Fisher information without assuming a first-order inequality.',
    },
    "lem:distance_deriv": {
        "title": "Metric-speed control of distance along the flow",
        "statement": r"""<p>Under the R3 equations and R5 characteristic
        realization, the actual normalized product-distance upper-right slope
        to every fixed state \(b\) is at most \(\sqrt{I(a_t)}\).
        With integrable characteristic velocities, the proved integrated
        estimate is, for \(s\le t\),</p>
        \[|d(a_t,b)-d(a_s,b)|\le\int_s^t\sqrt{I(a_r)}\,dr.\]
        <p>Where the ordinary distance derivative exists it is also at most
        \(\sqrt{I(a_t)}\). Both conclusions follow from the actual coupling
        costs and characteristic derivatives; a speed inequality is not an
        assumption.</p>""",
        "correction": "The source says the ordinary derivative exists and satisfies the bound at every positive time. Even a smooth Euclidean path can have a corner in its distance to a fixed point when it crosses that point. An almost-everywhere metric-derivative statement, or an upper-Dini-derivative formulation, supplies the integrated estimate actually needed by the proof.",
        "scope": 'For actual square-integrable characteristic curves and target laws under R5, the infimum over genuine coupling costs gives the distance-increment bound. The corrected upper-right-slope and integrated-speed statements are proved. They cover crossing times where the printed ordinary derivative need not exist.',
    },
    "lem:lower_semi_continuous": {
        "title": "Lower semicontinuity of the tilted energy",
        "statement": r"""<p>On the R6 density chart equipped with the
        actual normalized product transport metric, assume pointwise
        continuous densities and potentials and a common local integrable
        envelope for \(q\log q+qU\). The actual normalized energy</p>
        \[\widetilde F(x)=\frac1M\sum_m\int q_x^m(z)
          [\log q_x^m(z)+U_m(u_x,z)]\,dz\]
        <p>is continuous, hence lower semicontinuous. In particular, for
        \(x_n\to x\) in this chart,</p>
        \[\widetilde F(x_n)\longrightarrow\widetilde F(x),\qquad
          \widetilde F(x)\le\liminf_n\widetilde F(x_n).\]
        <p>Dominated convergence proves this statement on the explicitly
        identified probability-law domain.</p>""",
        "correction": 'Joint continuity of \\(R\\) is used at supplement line 665 but is not an explicit displayed assumption. The corrected proof instead states the sufficient R6 pointwise density/potential continuity and local integrable domination for the total energy. The limiting argument uses a complete admissible R6 domain; differentiable densities alone do not form a complete Wasserstein space.',
        "scope": 'On the complete regular density domain specified by R6, pointwise density/potential continuity and a local integrable energy envelope prove continuity of the actual density energy by dominated convergence, hence its lower semicontinuity. Pointwise density continuity is an explicit added domain condition, not an inference from Wasserstein convergence alone.',
    },
    "lem:cauchy": {
        "title": "A Cauchy flow sequence with optimal energies reaches a minimizer",
        "statement": r"""<p>The corrected compactness step is: let the
        ambient metric space be complete and the energy \(E\) be lower
        semicontinuous with finite infimum \(E_\star\). If
        \(t_n\uparrow\infty\), \((a_{t_n})\) is Cauchy, and
        \(E(a_{t_n})\to E_\star\), then there is \(a_\star\) such that</p>
        \[a_{t_n}\longrightarrow a_\star,
          \qquad E(a_\star)=E_\star.\]
        <p>The Cauchy property yields a limit in the complete ambient space;
        lower semicontinuity and optimal-energy convergence identify it as a
        minimizer.</p>""",
        "correction": 'The printed hypothesis gives an arbitrary Cauchy sequence unrelated to the flow, then concludes convergence of a flow subsequence. The proof needs the Cauchy sequence to be the stated flow sequence and its energies to approach the infimum. Completeness of all \\(\\mathcal P_2\\) does not ensure that its limit retains a differentiable density; the energy domain and admissibility of the limit need separate treatment.',
        "scope": 'For the actual energy in a complete R6 chart, a Cauchy flow sequence whose energies approach the infimum has an admissible minimizing limit. Energy lower semicontinuity is proved from the density envelope; the original unrelated-Cauchy-sequence formulation is corrected.',
    },
    "thm:xLSI_implies_xTalagrand": {
        "title": "Extended log-Sobolev control implies distance to the minimizing set",
        "statement": r"""<p>For the given state \(a=(u,q)\), the intended
        extended Talagrand inequality is</p>
        \[\lambda\,d(a,\mathcal M_\star)^2
          \le2[\widetilde F(a)-\widetilde F_\star],\qquad
          d(a,\mathcal M_\star)=\inf_{b\in\mathcal M_\star}d(a,b).\]
        <p>A corrected flow proof requires a consistent global flow,
        dissipation, the metric-speed bound, extended LSI, lower
        semicontinuity and the preceding complete-space minimizer argument.
        Integrating the speed gives a total remaining path length at most
        \(\sqrt{2[\widetilde F(a)-\widetilde F_\star]/\lambda}\).</p>""",
        "correction": r"""The definition <code>defn:xTalagrand</code> at
        supplement lines 614–620 takes a redundant infimum over the starting
        state itself. If a minimizer exists, that literal right-hand side is
        zero. Remove this infimum and keep the given starting state fixed; the
        only infimum is over the minimizing set. Section-wide A1/A2 and the
        analytic lemmas are also used, even though the theorem's local sentence
        mentions only xLSI.""",
        "scope": 'The connected density-flow theorem uses xLSI as its sole functional-inequality premise, with no A3 or geodesic-convexity assumption. Bare parameter/Fokker–Planck equations prove de Bruijn; actual characteristic derivatives and coupling anchors prove metric speed in the actual R6 chart. The same theorem then constructs a minimizing limit and proves the corrected Talagrand bound, including zero-energy times. Neither dissipation nor a speed inequality is an input to this endpoint.',
    },
    "thm:exp_convg_appendix": {
        "title": "Full product-state exponential convergence",
        "statement": r"""<p>The appendix's stronger form of the main
        convergence theorem asserts a unique minimizer
        \(a_\star=(u_\star,\pi_{u_\star}^{1:M})\) and</p>
        \[d(a_t,a_\star)\le
          \sqrt{\frac{2[\widetilde F(a_t)-\widetilde F_\star]}\lambda}
          \le\sqrt{\frac{2[\widetilde F(a_0)-\widetilde F_\star]}\lambda}
             e^{-\lambda t},\qquad t>0.\]
        <p>Here \(d^2=\|u-v\|^2+M^{-1}\sum_mW_2(q^m,r^m)^2\). The first
        inequality uses the corrected Talagrand statement; the second uses
        dissipation, xLSI and Grönwall.</p>""",
        "correction": "Read A2 on a consistent initial class and supply the analytic entropy/transport hypotheses, the corrected Talagrand definition, and the corrected Cauchy-flow argument. An independent optimizer construction avoids the circular use of a minimizer in the source xLSI proof.",
        "scope": 'The source normalized product-state bound combines the proved transport Talagrand inequality and extended LSI with the actual classical de Bruijn identity and Grönwall decay under R1–R4. The actual marginal/posterior construction identifies the unique target.',
    },
    "lem:cont-time-convg": {
        "title": "Continuous mean-field solution and empirical-cloud comparison",
        "statement": r"""<p>Under R7, construct a continuous
        \(L^2\) Brownian mean-field integral solution \(Y_t\), with
        deterministic initial parameter, and a synchronous
        stationary posterior reference \(S_t\). The reference parameter is the
        actual optimizer \(u_\star\), and every physical reference particle for
        datum \(m\) has law \(\pi_{u_\star}^m\). For their per-datum empirical
        laws \(Q_t^{m,N},Q_{\star,t}^{m,N}\), the corrected comparison is</p>
        \[\left(\mathbb E\left[\|u_t-u_\star\|^2+
          \frac1M\sum_m W_2(Q_t^{m,N},Q_{\star,t}^{m,N})^2\right]
          \right)^{1/2}
          \le\|Y_t-S_t\|_{L^2}\le e^{-\lambda t}\|Y_0-S_0\|_{L^2}.\]
        <p>The cloud norm averages physical squared particle distances by
        \(MN\). Both the empirical statistic's measurability/integrability and
        its bound by this actual coupling norm are proved.</p>""",
        "correction": 'Arbitrary independent target samples do not satisfy the identity equating their pairwise \\(L^2\\) cost to \\(W_2\\) at supplement line 781. The corrected theorem uses a constructed synchronous stationary posterior reference and an explicit initial coupling norm as its prefactor. The solution class is continuous \\(L^2\\) Brownian integral solutions. Replicating each datum potential \\(N\\) times identifies the target with the original \\(M\\)-datum optimizer; different data may have different posterior laws.',
        "scope": 'The connected source endpoint constructs the actual optimizer and posterior reference, proves its posterior marginals at every time, derives full normalized cloud contraction, and proves the displayed per-datum empirical Wasserstein RMS estimate. All sampling, initial-law, local domination and coupling conditions are explicit R1/R2/R7 assumptions. No reference, zero-score, stationary-law or empirical-comparison conclusion is an input.',
    },
    "lem:spatial_discretization": {
        "title": "Uniform finite-particle approximation error",
        "statement": r"""<p>Couple the interacting particle system and the
        mean-field copies with the same Brownian motions and matching initial
        states, so \(\xi_0^N=0\). Let</p>
        \[\xi_t^N=\|u_t^N-u_t\|^2+
          \frac1{MN}\sum_{m,n}\|\bar Z_t^{m,n}-Z_t^{m,n}\|^2.\]
        <p>Under A3/A4 and a uniform centered-force moment bound supplying a
        finite constant \(C_{\mathrm{sp}}\), the corrected source estimate is</p>
        \[(\mathbb E\xi_t^N)^{1/2}\le
          (1-e^{-\lambda t})\frac{C_{\mathrm{sp}}}{\lambda\sqrt N}.\]
        <p>With a per-copy centered score variance bound \(V_0\) over the
        \(K=MN\) copies, the checked constant is
        \(C_{\mathrm{sp}}=\sqrt{V_0/M}\), so the bound equals
        \((1-e^{-\lambda t})\sqrt{V_0/K}/\lambda\).
        It is \(O(N^{-1/2})\) uniformly in time when the initial coupling
        error is zero. Independence from \(M\) requires a moment bound uniform
        in the data, or a bounded averaged replacement.</p>""",
        "correction": "The statement omits the matched initialization that the proof uses at supplement line 837. The heterogeneous initial laws and force moments must be specified; a single undeclared \\(Z_0\\) does not give a uniform data-independent constant. Any origin-based moment expression must also control the drift's offset or be centered about an equilibrium.",
        "scope": 'Under R7 matched initial coupling, independent centered particle scores and one fixed per-copy variance bound \\(V_0\\), the continuous \\(L^2\\) interacting/mean-field integral comparison yields the stated uniform finite-particle estimate. The empirical fluctuation and its inverse-square-root rate are derived from the score variables.',
    },
    "lem:temporal_discretization": {
        "title": "Uniform Euler–Maruyama time-discretization error",
        "statement": r"""<p>Use matching initial states, Brownian increments
        indexed by both \((m,n)\), and uniform normalized moment controls.
        Under A3/A4 and the explicit stable-step restriction
        \(0\lt h,\quad\lambda h\le1,\quad hL^2\le\lambda\), the corrected order asserted by the source's
        main theorem is</p>
        \[d_{\mathrm{RMS}}((u_k^{N,h},\bar Q_k^{N,h}),
                    (u_{kh}^{N},\bar Q_{kh}^{N}))\le C\sqrt h,
          \qquad k\in\mathbb N,\]
        <p>where \(C\) is independent of \(k,N\) provided the moment controls
        and the normalized drift-at-origin bound are uniform in \(N\).
        The explicit drift radius is \(G=\|F(0)\|+LR\), where
        \(\sup_t\|X_t\|_{L^2}\le R\).</p>""",
        "correction": r"""The printed lemma simultaneously writes
        \(C(h)=O(\sqrt h)\) and error \(\le\sqrt h\,C(h)\)
        (supplement, lines 847–850), which would assert \(O(h)\). Retain one
        square root: either \(C(h)=O(1)\) in that display or error
        \(\le C(h)=O(\sqrt h)\). The noise \(W_k^n\) at line 845 must retain
        the datum index \(m\), and the heterogeneous drift keeps its superscript
        \(\widetilde\ell^m\). The checked force-level proof uses the stated
        stronger stable-step restriction; it does not claim the full printed
        step-size interval without the corresponding sharper gradient estimate.""",
        "scope": 'Under R7, the actual continuous \\(L^2\\) Brownian integral equation and stable Euler recursion yield the corrected square-root-in-step-size temporal error, with explicit normalized drift and Brownian modulus constants. The proof uses the declared particle-indexed noise and compatible initial states.'    },
    "thrm_app:error-bound": {
        "title": "Appendix full-batch parameter error theorem",
        "statement": r"""<p>This is the appendix repetition of the main
        full-batch error theorem, with \(\widetilde\theta=(\theta,\phi)\):</p>
        \[\bigl(\mathbb E\|\widetilde\theta_T^{N,h}
                    -\widetilde\theta_\star\|^2\bigr)^{1/2}
          \le C_{h,N}+C\rho^T,\qquad
          C_{h,N}=O(\sqrt h+N^{-1/2}).\]
        <p>Its proof combines continuous convergence, spatial approximation and
        temporal approximation by the triangle inequality. It retains the
        initialization, coupling, integrability and moment requirements of those
        component estimates.</p>""",
        "correction": "Use the corrected temporal order, empirical coupling and initialization hypotheses above. The source theorem concerns exact full-batch gradients; subsampled, reweighted, annealed or adaptive updates require a separate theorem for their actual recursions.",
        "scope": 'The appendix full-batch bound is proved on the same R7 Brownian initialization and moment domain as the main theorem. Primitive dynamics, posterior centering, normalized force geometry, finite-particle fluctuations and Euler consistency give the displayed parameter error. The oracle extension remains separately identified as new theory.',
    },
}


def reference(file, start_line, end_line, label):
    return {"file": file, "start_line": start_line, "end_line": end_line, "label": label}


PAPER_CORRECTIONS = [
    {
        "id": "C-A2",
        "title": "Universal time-zero density existence is impossible",
        "prose": r"""A2 includes every finite-second-moment initial law and
        requires a smooth density at \(t=0\). A Dirac law has finite second
        moment but cannot have a density relative to nonatomic Lebesgue measure.
        Restrict the initial class to the required smooth densities, or require
        smoothing only for \(t>0\) and continuity in \(W_2\) at zero. Merely
        restricting to absolutely continuous laws still permits discontinuous
        initial densities. The Dirac obstruction is proved. Existence is proved
        for the particle and mean-field equations in the continuous \(L^2\)
        Brownian integral solution class under R7. The corrected density
        calculus and decay estimates apply to every classical solution in the
        class specified by extra assumptions R1–R4; existence of such a classical density
        solution is not constructed.""",
        "references": [reference(MAIN, 151, 154, "assump:solution_reg"), reference(SUPP, 436, 455, "eq:multi_datapoint_prodmetric")],
        "refs": [("LatentDiffusion/SourceObstruction.lean", "not_solutionRegularity_of_null_singleton"), ("LatentDiffusion/SourceObstruction.lean", "not_solutionRegularity_of_noAtoms")],
        "status": 'The literal time-zero premise is refuted in Lean; R1 states the corrected admissible initial domain.',
    },
    {
        "id": "C-ZERO-TILT",
        "title": "Zero tilt at the tilted optimum does not identify the original optimum",
        "prose": r"""The pointwise comparison
        \(\widetilde\ell\le\ell\) and equality at a tilted maximizer do not
        imply that this point maximizes \(\ell\). On two points take log
        likelihoods \((0,1)\) and nonnegative gaps \((0,2)\): the tilted
        objective \((0,-1)\) is maximized at the zero-gap point, but the original
        objective is maximized at the other point. A sufficient corrected
        condition is that an original-objective maximizer has zero gap; then
        every tilted maximizer attains the original optimal value. Uniform zero
        penalty across the whole model also suffices.""",
        "references": [reference(MAIN, 107, 110, "discussion following prop:ftildemins")],
        "refs": [("LatentDiffusion/Variational.lean", "zero_gap_at_tilted_max_not_sufficient"), ("LatentDiffusion/Variational.lean", "zero_gap_comparator")],
        "status": "Counterexample and sufficient comparator proved in Lean",
    },
    {
        "id": "C-MINIBATCH-TEMPERATURE",
        "title": "Algorithm 1 reduces noise temperature without reducing mean drift",
        "prose": r"""Let \(p=B/M\). The selected gradient has amplitude
        \(h/p\), so its average drift has the full rate, while every particle
        receives noise variance \(2hp\), rather than \(2h\). For
        \(U(x)=ax^2/2\), direct Gaussian integration gives
        \(\mathbb E[X_{k+1}^2\mid X_k=x]=(1-2ah+a^2h^2/p)x^2+2hp\).
        When its denominator is positive, the fixed second moment is
        \(p/[a(1-ah/(2p))]\). For \(p=1/2,a=1,h=1/4\), target second moment
        \(1\) becomes \(7/8\) in one step and the fixed moment is \(2/3\).
        Two checked corrections are full noise \(\sqrt{2h}\) with the
        inverse-inclusion drift, or a random scan that applies uninflated drift
        and full noise only to selected particles. Their finite-step variances
        differ; these are scalar moment results, not a general invariant-law
        theorem for nonlinear IPLD.""",
        "references": [reference(MAIN, 232, 258, "algo:train_basic")],
        "refs": [("LatentDiffusion/BatchAudit.lean", "paperConditionalSecondMoment_eq"), ("LatentDiffusion/BatchAudit.lean", "paper_half_batch_counterexample"), ("LatentDiffusion/BatchAudit.lean", "randomScanConditionalSecondMoment_eq"), ("LatentDiffusion/BatchAudit.lean", "fullNoiseConditionalSecondMoment_eq")],
        "status": "Exact Gaussian moment counterexample and scalar alternatives proved in Lean",
    },
    {
        "id": "C-TEMPORAL-ORDER",
        "title": "Remove the duplicated square root in the temporal estimate",
        "prose": r"""The temporal lemma says both \(C(h)=O(\sqrt h)\) and
        error \(\le\sqrt h\,C(h)\), which asserts \(O(h)\). The general
        order used by the main theorem is \(O(\sqrt h)\): write error
        \(\le C\sqrt h\) with \(C=O(1)\), or error
        \(\le C(h)=O(\sqrt h)\). The Gaussian increments also require the datum
        index \(m\). The Brownian integral/Euler comparison proves this order
        under the explicit R7 moments and stable-step restriction.""",
        "references": [reference(SUPP, 841, 855, "lem:temporal_discretization"), reference(MAIN, 208, 212, "thrm:error-bound")],
        "refs": [('LatentDiffusion/RegularMeanField.lean', 'temporal_comparison'), ('LatentDiffusion/RegularStochastic.lean', 'full_batch_parameter_bound')],
        "status": 'Corrected square-root temporal order proved from actual Brownian integral dynamics under R7.',
    },
    {
        "id": "C-EMPIRICAL-COUPLING",
        "title": "Specify the target-cloud coupling and compatible initialization",
        "prose": r"""The equality between an expected particle-pair cost and
        \(W_2^2\) requires an optimal coupling. Independently drawn, fixed target
        samples do not give a decaying empirical distance. Use an explicitly
        optimal fixed-time coupling or formulate a synchronous stationary
        reference process and prove its comparison. The spatial proof also
        discards its initial error only because the initial states were matched;
        state this hypothesis and provide uniform heterogeneous moment bounds.
        Independence and identical distribution apply across particle replicas
        for a fixed datum, not across different data with different potentials.""",
        "references": [reference(SUPP, 766, 781, "lem:cont-time-convg"), reference(SUPP, 786, 837, "lem:spatial_discretization")],
        "refs": [('LatentDiffusion/RegularMeanField.lean', 'exists_spatial_comparison'), ('LatentDiffusion/RegularTransport.lean', 'OptimalMap')],
        "status": 'Actual optimal-law coupling and matched-initialization comparisons are proved on R4/R7.',
    },
    {
        "id": "C-TALAGRAND",
        "title": "Keep the initial state fixed in the Talagrand inequality",
        "prose": r"""The intended right side is
        \(\lambda\inf_{b\in\mathcal M_\star}d(a,b)^2\) for the given state
        \(a\). The source instead takes an extra infimum over \(a\), making
        that term zero whenever a minimizer exists. Remove the extra infimum.
        R2, R3, R5 and R6 supply the density, characteristic and complete-domain hypotheses;
        the dissipation, speed control and minimizing-limit steps are proved below.""",
        "references": [reference(SUPP, 614, 620, "defn:xTalagrand"), reference(SUPP, 688, 711, "thm:xLSI_implies_xTalagrand")],
        "refs": [('LatentDiffusion/RegularFlowTalagrand.lean', 'exists_minimizer_talagrand'), ('LatentDiffusion/RegularFlowTalagrand.lean', 'distance_right_slope')],
        "status": 'Corrected definition and full xLSI-to-Talagrand flow-length implication proved; no convexity premise is needed in that implication.',
    },
    {
        "id": "C-COMPACTNESS",
        "title": "Use a Cauchy flow sequence in a complete energy domain",
        "prose": r"""The Cauchy sequence in the printed lemma is unrelated to
        the flow. It must be a flow sequence \(a_{t_n}\), with
        \(t_n\uparrow\infty\) and energy tending to the infimum. The limit
        argument requires a lower semicontinuous energy on a complete ambient
        domain, plus admissibility of a finite-energy limit. Density-only
        subspaces are not complete in \(W_2\). The lower-semicontinuity proof
        separately uses joint continuity of \(R\); nonnegative joint lower
        semicontinuity is a sufficient explicit replacement. The xLSI proof's
        chosen minimizer must also be constructed before it is used.""",
        "references": [reference(SUPP, 587, 587, "proof of thm:sLC_implies_xLSI"), reference(SUPP, 656, 685, "lem:lower_semi_continuous and lem:cauchy")],
        "refs": [('LatentDiffusion/RegularVariational.lean', 'DominatedDensityChart.lowerSemicontinuous_energy'), ('LatentDiffusion/RegularVariational.lean', 'DominatedDensityChart.cauchy_minimizer')],
        "status": 'Actual density energy is continuous on R6; the corrected complete-domain minimizing-limit argument is proved.',
    },
    {
        "id": "C-ENTROPY-DOMAIN",
        "title": "State entropy differentiation and transport-domain hypotheses",
        "prose": r"""Pointwise smoothness and finite second moments alone do
        not ensure finite positive entropy, finite Fisher information, an
        integrable time derivative, vanishing boundary terms or integrable
        transport-gradient pairings. The source's first-variation, de Bruijn and
        initial-geodesic-derivative arguments need those hypotheses or a proved
        approximation argument. For distance to a fixed point, use a metric
        derivative almost everywhere or an upper-Dini derivative, since an
        ordinary distance derivative may fail at a crossing time.""",
        "references": [reference(SUPP, 188, 221, "app:lemma_1st_var"), reference(SUPP, 488, 524, "prop:de_bruijin"), reference(SUPP, 568, 575, "lem:lower_deriv"), reference(SUPP, 623, 651, "lem:distance_deriv")],
        "refs": [('LatentDiffusion/RegularFlowCalculus.lean', 'normalized_product_gradient_representation'), ('LatentDiffusion/RegularFlowCalculus.lean', 'normalized_product_deBruijn'), ('LatentDiffusion/RegularTransportFirstOrder.lean', 'lower_directional_liminf')],
        "status": 'Actual first variations, normalized gradient representation, de Bruijn and entropy transport tangents are proved under R2–R4.',
    },
    {
        "id": "C-GAUSSIAN-CONDITIONAL",
        "title": "Correct the Gaussian bridge covariance and transition KL",
        "prose": r"""For the stated forward chain, the conditional covariance
        in \(q(z_{k-1}\mid z_k,z_0)\) is
        \(\widetilde\beta_k I\), where
        \(\widetilde\beta_k=\beta_k(1-\bar\alpha_{k-1})/(1-\bar\alpha_k)\),
        rather than \(\beta_k I\). If the reverse covariance is
        \(s_k I\), the corresponding isotropic Gaussian KL is
        \[\frac12\left[d_z\!\left(\log\frac{s_k}{\widetilde\beta_k}
             -1+\frac{\widetilde\beta_k}{s_k}\right)
             +\frac{\|\widetilde\mu_k-\mu_{\theta,k}\|^2}{s_k}\right].\]
        With the supplement's choice \(s_k=\beta_k\), this gives the
        \(\epsilon\)-prediction weight
        \(\beta_k/[2\alpha_k(1-\bar\alpha_k)]\). The main text instead
        writes reverse covariance \(\beta_k^2I\); a single variance convention
        must be chosen before using these formulas. In the reconstruction
        substituted into \(\widetilde\mu_k\) at supplement line 85,
        \(\widehat z_0=(z_k-\sqrt{1-\bar\alpha_k}\,\epsilon_\theta)/
        \sqrt{\bar\alpha_k}\): its denominator needs \(\bar\alpha_k\),
        rather than \(\alpha_k\). The following simplified backward mean at
        line 86 then has the usual outer factor \(1/\sqrt{\alpha_k}\).""",
        "references": [reference(SUPP, 57, 77, "Gaussian Transition Kernel derivation"), reference(SUPP, 84, 90, "Reparametrization"), reference(MAIN, 57, 57, "DDPM backward kernels")],
        "refs": [],
        "status": 'The printed Gaussian covariance and KL formulas are corrected under the stated variance convention.',
    },
    {
        "id": "C-GAUSSIAN-TERMINAL",
        "title": "Correct the terminal Gaussian KL and final decoder variance",
        "prose": r"""For
        \(q(z_K\mid z_0)=N(\sqrt{\bar\alpha_K}z_0,(1-\bar\alpha_K)I)\)
        and \(p_K=N(0,I)\), the correct terminal KL is
        \[\frac12\left[\bar\alpha_K\|z_0\|^2-d_z\bar\alpha_K
                    -d_z\log(1-\bar\alpha_K)\right].\]
        The source squares the variance and gives the wrong logarithm
        coefficient. Its retained \(z_0\)-quadratic term is nevertheless
        \(\bar\alpha_K\|z_0\|^2/2\). The decoder is declared to have identity
        covariance at supplement line 73, so its negative log density should be
        \(d_z\log(2\pi)/2+\|z_0-\mu_{\theta,1}(z_1)\|^2/2\). The expression
        at line 79 instead uses covariance \((1-\bar\alpha_1)I\).""",
        "references": [reference(SUPP, 70, 80, "eq_app:extra_term and eq_app:discrete_gaussian")],
        "refs": [],
        "status": 'The terminal Gaussian KL and decoder-variance formulas are corrected as displayed.',
    },
    {
        "id": "C-RANDOM-TIME",
        "title": 'Restore the factor \\(K\\) for an unbiased random-time loss estimator',
        "prose": r"""For a summed diffusion objective
        \(c(z_0)+\sum_{k=1}^{K}L_k\), uniformly sampled
        \(J\in\{1,\ldots,K\}\) gives the unbiased estimator
        \(c(z_0)+K L_J\). The displayed estimator omits the factor \(K\)
        multiplying the chosen summand. Its separately added terminal quadratic
        \(c(z_0)=\bar\alpha_K\|z_0\|^2/2\) must not be multiplied by
        \(K\). Terms independent of \(\theta\) may still depend on \(z_0\),
        and therefore cannot be discarded in particle gradients. The simplified
        reweighted loss intentionally changes the objective; it is not an
        unbiased estimator of the exact summed diffusion loss.""",
        "references": [reference(SUPP, 92, 113, "app_eq:diffusion_likelihood and app:one_sample_simplified_diffusion"), reference(MAIN, 228, 232, "eq:batch_loss")],
        "refs": [("LatentDiffusion/SourceResults.lean", "uniform_time_unscaled"), ("LatentDiffusion/SourceResults.lean", "uniform_time_corrected")],
        "status": "Exact finite uniform-mean estimator normalization proved in Lean; no stochastic sampling construction is assumed",
    },
    {
        "id": "C-LOSS-SIGN",
        "title": "Use the descent loss consistently",
        "prose": r"""The concise update subtracts gradients but defines its
        loss from \(\mathcal L^m=\log p_\phi-\mathcal L_D\), the opposite of
        the loss used by the following minibatch equation. Define the descent
        loss as \(V^m=\mathcal L_D-\log p_\phi\); then the full-batch parameter
        and particle updates subtract its gradients, with the particle factor
        \(MN\) applied to the averaged loss. This agrees with the original
        full-batch coordinate equations.""",
        "references": [reference(MAIN, 131, 132, "eq:single_loss_drift"), reference(MAIN, 192, 197, "eq:disc_theta–eq:disc_par"), reference(MAIN, 222, 231, "concise updates and eq:batch_loss")],
        "refs": [("LatentDiffusion/Cloud.lean", "fullBatchStep_parameter"), ("LatentDiffusion/Cloud.lean", "fullBatchStep_particle")],
        "status": "Sign correction; full-batch coordinate realization proved in Lean",
    },
    {
        "id": "C-ANNEALING-SIGN",
        "title": "Correct the sign of the annealed Wasserstein gradient",
        "prose": r"""For
        \(F_\gamma(q)=\int[\gamma\log q+\gamma\mathcal L_D-
        \log p_\phi]\,dq\), the density gradient is
        \(\nabla_z\cdot(q\nabla_z\log p_\phi)-
        \gamma\nabla_z\cdot(q\nabla_z[\log q+\mathcal L_D])\).
        The minus sign on \(\mathcal L_D\) inside the source's bracket must
        become plus. The following SDE already uses the expected drift
        \(\nabla\log p_\phi-\gamma\nabla\mathcal L_D\) and noise
        \(\sqrt{2\gamma}\). A time-dependent annealing schedule defines a
        changing objective and requires its own convergence argument.""",
        "references": [reference(SUPP, 260, 279, "app:kl_anneal_deriv")],
        "refs": [],
        "status": 'The objective/update signs are corrected; the named source convergence results concern the fixed objective.',
    },
    {
        "id": "C-ADAPTIVE",
        "title": "The adaptive algorithm needs its own signed, indexed and normalized update",
        "prose": r"""The momentum tracks the positive gradient of the
        descent loss, but the particle update adds it. With that momentum
        convention, descent requires \(-h_zGM\). The loop's particle index is
        \(\mathcal B\times[N]\), not \(\mathcal B\times[M]\). The equation
        scales noise variance by \(1/M\), and the implementation paragraph adds
        a further noise-amplitude factor \(1/B\); these change the sampler.
        The pseudocode also overwrites its drifted temporary value when adding
        noise, so the intended update should add drift and noise to the same
        new state. For a state-dependent preconditioner a target-preserving
        Langevin diffusion generally needs the appropriate divergence drift;
        momentum requires an enlarged-state invariant-law analysis. None of
        these changes is covered by the source's full-batch theorem.""",
        "references": [reference(SUPP, 289, 304, "eq:adam_vz_update and eq:vz_momentum"), reference(SUPP, 306, 328, "algo:train_1"), reference(MAIN, 314, 314, "discussion of theoretical scope")],
        "refs": [],
        "status": 'The adaptive algorithm specification is corrected; the source convergence theorem applies to the full-batch fixed-step method.',
    },
    {
        "id": "C-LIPSCHITZ-NOTATION",
        "title": "Keep the tilt and the normalized geometry in the assumptions",
        "prose": r"""A4 in the main text concerns the gradient of the tilted
        joint log density. The supplementary restatement drops the tilde from
        \(p\) while retaining \(\widetilde\ell\); use the tilted potential
        throughout, or explicitly combine an untilted Lipschitz bound with a
        bound for \(\nabla R\). The averaged joint potential has the same
        convexity constant in the normalized product metric. In the unscaled
        Euclidean latent product norm its latent curvature can instead be
        \(\lambda/M\). These coordinate and metric choices are part of the
        theorem, not additional conclusions about the experimental neural
        parameterization.""",
        "references": [reference(MAIN, 168, 174, "eq:tilde-ell"), reference(MAIN, 200, 212, "assump:lipschitz_grad and thrm:error-bound"), reference(SUPP, 753, 759, "restated assump:lipschitz_grad"), reference(SUPP, 449, 455, "eq:multi_datapoint_prodmetric")],
        "refs": [("LatentDiffusion/Cloud.lean", "potential_strongConvex"), ("LatentDiffusion/Cloud.lean", "meanForce_regular")],
        "status": "Notation/metric correction; normalized finite-cloud geometry proved in Lean",
    },
]


assert len(PAPER_RESULTS) == 19
