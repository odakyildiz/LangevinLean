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
        \(q_\star^m=\pi_{u_\star}^m\) for every datum. In particular a parameter
        maximizer exists if and only if it is the parameter component of some
        global variational minimizer.</p>""",
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
        "scope": "The normalized finite-KL equivalence and the actual density-integral identity are proved in Lean. The density identity uses explicit normalization and entropy-integrability hypotheses. No reconstruction of every arbitrary-law or extended-integral reading of the original statement is claimed.",
    },
    "thm:exp_convg_informal": {
        "title": "Unique tilted optimizer and exponential parameter convergence",
        "statement": r"""<p>The source assumes A1–A3 and states that
        \(\widetilde\ell\) has a unique maximizer \(u_\star=(\theta_\star,\phi_\star)\),
        with \(\lambda>0\) independent of \(M\), and that its gradient flow satisfies</p>
        \[\|u_t-u_\star\|\le
        \sqrt{\frac{2[\widetilde F(u_0,q_0)-\widetilde F_\star]}{\lambda}}
        e^{-\lambda t},\qquad t\ge0.\]
        <p>The checked version uses differentiable jointly
        \(\lambda\)-strongly convex potentials \(U_m=-\log\rho^m\), their actual
        marginal integrals, and a normalized posterior family with the matching
        log evidence. Along the supplied finite-KL path it additionally requires
        continuity of the energy gap \(E\), dissipation \(E'=-I\), \(I\ge0\),
        and the first-order transport estimate
        \(E\le\sqrt I\,r-\lambda r^2/2\). These give precisely the displayed
        parameter rate.</p>""",
        "correction": r"""A2 must be interpreted on an admissible initial class,
        or require smooth densities only for positive time. Its literal
        quantification over all \(\mathcal P_2\) initial laws is contradicted by
        Dirac laws. Entropy differentiation and transport control need the
        explicit analytic hypotheses above. The averaged joint potential is
        strongly convex in the normalized product norm
        \(\|u\|^2+M^{-1}\sum_m\|z^m\|^2\); the sketch at main lines 168–174
        must use that norm when retaining the constant \(\lambda\).""",
        "scope": "Lean proves existence and uniqueness of the actual marginal optimizer from joint convexity, and the sharp parameter rate conditional on the displayed entropy and transport bridges. Those bridges and the PDE flow are not derived from raw A1–A3. The full Wasserstein-state conclusion is a separate source claim below.",
    },
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
        \((h,N,T)\), and \(0\lt\rho\lt1\) may depend on \(h\). Writing the
        transient as \(e^{-\lambda hT}\) makes the dependence on physical time
        explicit. Uniform constants require the stated initialization and
        moment controls.</p>""",
        "correction": r"""The temporal lemma contains an extra square-root
        factor; its corrected general estimate is \(C\sqrt h\), not the
        \(O(h)\) accidentally written there. The empirical comparison needs a
        specified coupling, and the spatial comparison needs compatible
        initialization and uniform moments. This theorem concerns the full
        batch method, as the paper itself states at main line 314. It gives no
        guarantee for Algorithm 1's changed minibatch temperature or the adaptive
        algorithm.""",
        "scope": "The coordinate recursion and cloud geometry are checked. A new explicit RMS theorem is proved under an integral reference, moment, residual and oracle hypotheses, and is presented in the new-theory part. It is not a recovery of this source theorem from raw A1–A4; the required stochastic reference construction remains open.",
    },
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
        "scope": "SourceCalculus proves the actual parameter-integral Fréchet derivative and the density-direction integral derivative. The displayed Lean hypotheses give a common neighborhood, pointwise derivatives, measurable integrands, base integrability and an integrable derivative bound. On zero-mass directions the +1 disappears. This proves the corrected first variations on that explicit dominated domain; the paper's A1 alone does not establish the domination hypotheses or a Wasserstein-gradient identification.",
    },
    "unlabelled-product-gradient": {
        "title": "Gradient under the normalized Euclidean–Wasserstein metric",
        "statement": r"""<p>Equip the product state with
        \(d^2((u,q),(v,r))=\|u-v\|^2+M^{-1}\sum_mW_2(q^m,r^m)^2\), and let
        \(V_u^m=\mathcal L_D(\theta,\cdot)-\log p_\phi(x^m\mid\cdot)\).
        Wherever the first variations and Otto metric representation are
        justified, the parameter and density gradients are</p>
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
        "scope": "SourceResults proves the exact M-times-inverse-M cancellation for any real module and positive data count. The full-cloud finite-dimensional coordinate identities are checked separately. This factor calculation does not construct the continuum Wasserstein tangent metric or its gradient, which remain unproved.",
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
        "scope": "The dissipation identity is an explicit premise of the checked decay theorems, not a proved consequence of source A2. No faithful Lean endpoint currently derives this continuum identity.",
    },
    "lem:geodesic": {
        "title": "Geodesics in the normalized product space",
        "statement": r"""<p>A constant-speed product geodesic between
        \((u,q)\) and \((v,r)\) consists of
        \(u_s=(1-s)u+sv\) and constant-speed Wasserstein geodesics in each law
        coordinate, with the same parameter \(s\in[0,1]\). If
        \(\varrho^m\) is an optimal coupling of \(q^m,r^m\), then</p>
        \[q_s^m=((z,z')\mapsto(1-s)z+sz')_\#\varrho^m.\]
        <p>If the first marginal \(q^m\) is absolutely continuous with respect
        to Lebesgue measure, Brenier's representation yields
        \(q_s^m=((1-s)\mathrm{id}+s\nabla f^m)_\#q^m\) for a convex
        potential \(f^m\).</p>""",
        "correction": "The equivalence requires the constant-speed endpoint parameterization in all factors. The map representation needs an absolutely continuous first marginal; without it the optimal-plan formulation is the appropriate one.",
        "scope": "These optimal-transport and Brenier theorems have no faithful Lean reconstruction in the current LatentDiffusion development. Finite-dimensional cloud normalization is not a proof of this result for probability laws.",
    },
    "lem:geodesic_convexity": {
        "title": "Strong geodesic convexity of the tilted free energy",
        "statement": r"""<p>Suppose each
        \(U_m(u,z)=-\log\rho_u^m(z)\) is jointly
        \(\lambda\)-strongly convex. For a constant-speed product
        Wasserstein geodesic \(\gamma_s\) between states \(a,b\), on a
        well-defined finite or extended-energy domain, the source states</p>
        \[\widetilde F(\gamma_s)\le(1-s)\widetilde F(a)
          +s\widetilde F(b)-\frac\lambda2s(1-s)d(a,b)^2,
          \qquad 0\le s\le1.\]
        <p>The potential term uses joint strong convexity along optimal
        displacement interpolations; the negative entropy term uses
        displacement convexity.</p>""",
        "correction": "The normalized product distance is essential for the constant to remain independent of M. The entropy functional must be defined on a domain where the interpolation inequality has a consistent extended-real meaning; finite second moments alone do not imply finite entropy.",
        "scope": "Lean proves strong convexity of the finite-cloud potential and the actual marginal potential. It does not prove displacement convexity of entropy or this full probability-law geodesic statement.",
    },
    "lem:lower_deriv": {
        "title": "First-order lower bound along a transport geodesic",
        "statement": r"""<p>Let \(\gamma_s\) run from \((u,q)\) to
        \((v,r)\), with initial optimal transport velocities
        \(w_m=T_m-\mathrm{id}\). Write
        \(s_m=\nabla_z\log(q^m/\rho_u^m)\). If the entropy subgradient and
        all pairings below are defined and integrable, the source states</p>
        \[\liminf_{s\downarrow0}
          \frac{\widetilde F(\gamma_s)-\widetilde F(\gamma_0)}s
          \ge\langle v-u,\nabla_u\widetilde F(u,q)\rangle
          +\frac1M\sum_m\int\langle w_m,s_m\rangle\,dq^m.\]""",
        "correction": "Almost-everywhere differentiability of a density alone is insufficient. A finite-energy entropy-subgradient domain, finite score norm or another condition giving integrable transport pairings is required. The velocity formulation explicitly identifies the Wasserstein tangent pairing used in the source.",
        "scope": "No faithful Lean endpoint proves this transport/entropy derivative. The checked extendedLSI_of_firstOrder theorem begins after the needed first-order bound has been supplied.",
    },
    "thm:sLC_implies_xLSI": {
        "title": "Strong log-concavity implies extended log-Sobolev control",
        "statement": r"""<p>The source states that A1 and A3 give, for all
        admissible states,</p>
        \[2\lambda[\widetilde F(u,q)-\widetilde F_\star]\le I(u,q).\]
        <p>The checked implication is the exact final step: for
        \(\lambda>0\), \(I\ge0\), and a first-order bound
        \(E\le\sqrt I\,r-\lambda r^2/2\), completing the square gives
        \(2\lambda E\le I\). The paper obtains the first-order bound by
        combining its geodesic convexity and derivative lemmas toward a
        minimizer.</p>""",
        "correction": "The proof chooses an admissible minimizer at supplement line 587 before its existence has been established in that chain. Existence can instead be supplied by the independently checked marginal optimizer theorem, with a normalized posterior family and matching evidence. That does not supply the remaining entropy/transport inequality.",
        "scope": "SourceResults proves the right-derivative consequence of a supplied strong geodesic-convexity interpolation inequality. extendedLSI_of_firstOrder checks the final completing-the-square argument. Identifying those scalar inputs with actual Wasserstein geodesics, entropy subgradients and source A1/A3 remains unproved; this is a partial reconstruction of the paper's xLSI theorem.",
    },
    "lem:distance_deriv": {
        "title": "Metric-speed control of distance along the flow",
        "statement": r"""<p>The robust version is an absolutely continuous
        product-metric path \(a_t=(u_t,q_t)\) with
        \(|a'|(t)\le\sqrt{I(a_t)}\) for almost every time. Then for any fixed
        state \(b\) and \(s\le t\),</p>
        \[|d(a_t,b)-d(a_s,b)|\le\int_s^t\sqrt{I(a_r)}\,dr.\]
        <p>In particular \(\frac d{dt}d(a_t,b)\le\sqrt{I(a_t)}\) at almost
        every time where the distance derivative exists.</p>""",
        "correction": "The source says the ordinary derivative exists and satisfies the bound at every positive time. Even a smooth Euclidean path can have a corner in its distance to a fixed point when it crosses that point. An almost-everywhere metric-derivative statement, or an upper-Dini-derivative formulation, supplies the integrated estimate actually needed by the proof.",
        "scope": "Neither absolute continuity of the Wasserstein flow nor its metric-speed bound is proved in the current Lean development. The corrected integrated formulation is an analytic obligation, not a checked endpoint.",
    },
    "lem:lower_semi_continuous": {
        "title": "Lower semicontinuity of the tilted energy",
        "statement": r"""<p>If the untilted energy \(F\) is lower
        semicontinuous, \(R(u,z)\ge0\) is jointly lower semicontinuous, and the
        extended-energy sum is well defined, then the corrected statement is</p>
        \[\widetilde F(u,q)\le
          \liminf_{n\to\infty}\widetilde F(u_n,q_n)
          \quad\text{when }u_n\to u,\quad W_2(q_n^m,q^m)\to0.\]
        <p>The penalty part follows by weak convergence of
        \(\delta_{u_n}\otimes q_n^m\) and the nonnegative Portmanteau
        inequality. The source uses the stronger hypothesis that \(R\) is
        jointly continuous.</p>""",
        "correction": "Joint continuity of R is used at supplement line 665 but is not an explicit displayed assumption. It must be verified or replaced by the sufficient joint lower semicontinuity. For the later completeness argument the energy should be extended to the complete ambient P₂ space; restricting to differentiable densities alone does not give a complete metric space.",
        "scope": "No faithful Lean theorem currently proves this continuum lower-semicontinuity statement. The marginal potential continuity theorem concerns a different finite-dimensional object.",
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
        "correction": "The printed hypothesis gives an arbitrary Cauchy sequence unrelated to the flow, then concludes convergence of a flow subsequence. The proof needs the Cauchy sequence to be the stated flow sequence and its energies to approach the infimum. Completeness of all P₂ does not ensure that its limit retains a differentiable density; the energy domain and admissibility of the limit need separate treatment.",
        "scope": "cauchy_minimizing_sequence proves the corrected statement for a real-valued lower-semicontinuous energy on a complete metric space, with an explicit lower bound and convergent minimizing values. It constructs the limit and proves global minimality. Its Wasserstein-flow application still needs a Cauchy flow sequence, the actual energy's lower semicontinuity and an admissible limit in a complete energy domain.",
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
        "scope": "geodesic_quadratic_growth proves the exact scalar quadratic-growth consequence of a strong geodesic-convexity interpolation bound and a minimizer. This alternative uses a stronger convexity premise; it does not prove the source's general xLSI-to-Talagrand implication or displacement convexity of the actual energy. The full Wasserstein-flow argument remains open.",
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
        "scope": "Existence and uniqueness of the marginal optimizer and conditional parameter decay are checked. The full product-state Wasserstein estimate in this displayed source theorem is not independently reconstructed in Lean.",
    },
    "lem:cont-time-convg": {
        "title": "Continuous mean-field solution and empirical-cloud comparison",
        "statement": r"""<p>The source states strong well-posedness of the
        mean-field SDE and exponential convergence of its empirical clouds to
        target clouds. A precise fixed-time comparison is: for each datum and
        time \(t\), choose independent particle pairs
        \((Z_t^{m,n},Y_t^{m,n})\) from an optimal coupling of
        \(q_t^m,q_\star^m\). With empirical laws \(Q_t^{m,N},Q_{\star,t}^{m,N}\),</p>
        \[\left(\|u_t-u_\star\|^2+
          \frac1M\sum_m\mathbb E W_2(Q_t^{m,N},Q_{\star,t}^{m,N})^2
          \right)^{1/2}
          \le d((u_t,q_t),(u_\star,q_\star))\le Ce^{-\lambda t}.\]
        <p>This coupling comparison is at a fixed time. It does not specify a
        single time-independent sampled target cloud for an entire trajectory.</p>""",
        "correction": "Arbitrary independent target samples do not satisfy the identity equating their pairwise L² cost to W₂ at supplement line 781. An optimal fixed-time coupling makes that step valid; a synchronous reference process gives a different, explicitly coupled comparison. Particles may be identically distributed across n for a fixed datum m, but different data generally have different latent laws.",
        "scope": "Neither the source mean-field SDE strong-solution construction nor this optimal-coupling empirical theorem is currently proved in Lean. New numerical reference theorems assume their own integral reference rather than proving the source statement.",
    },
    "lem:spatial_discretization": {
        "title": "Uniform finite-particle approximation error",
        "statement": r"""<p>Couple the interacting particle system and the
        mean-field copies with the same Brownian motions and compatible initial
        conditions. Let</p>
        \[\xi_t^N=\|u_t^N-u_t\|^2+
          \frac1{MN}\sum_{m,n}\|\bar Z_t^{m,n}-Z_t^{m,n}\|^2.\]
        <p>Under A3/A4 and a uniform centered-force moment bound supplying a
        finite constant \(C_{\mathrm{sp}}\), the corrected source estimate is</p>
        \[(\mathbb E\xi_t^N)^{1/2}\le
          e^{-\lambda t}(\mathbb E\xi_0^N)^{1/2}
          +(1-e^{-\lambda t})\frac{C_{\mathrm{sp}}}{\lambda\sqrt N}.\]
        <p>It is \(O(N^{-1/2})\) uniformly in time when the initial coupling
        error is zero. Independence from \(M\) requires a moment bound uniform
        in the data, or a bounded averaged replacement.</p>""",
        "correction": "The statement omits the matched initialization that the proof uses at supplement line 837. The heterogeneous initial laws and force moments must be specified; a single undeclared Z₀ does not give a uniform data-independent constant. Any origin-based moment expression must also control the drift's offset or be centered about an equilibrium.",
        "scope": "The source propagation-of-chaos/SDE argument is not reconstructed in Lean. Orthogonal heterogeneous averaging is proved separately and yields an explicit variance term for the new theorem once its residual representation and reference moments are supplied.",
    },
    "lem:temporal_discretization": {
        "title": "Uniform Euler–Maruyama time-discretization error",
        "statement": r"""<p>Use matching initial states, Brownian increments
        indexed by both \((m,n)\), and uniform normalized moment controls.
        Under A3/A4 and a stable step such as
        \(0\lt h\le1/(\lambda+L)\), the corrected order asserted by the source's
        main theorem is</p>
        \[d_{\mathrm{RMS}}((u_k^{N,h},\bar Q_k^{N,h}),
                    (u_{kh}^{N},\bar Q_{kh}^{N}))\le C\sqrt h,
          \qquad k\in\mathbb N,\]
        <p>where \(C\) is independent of \(k,N\) provided the moment controls
        are uniform in \(N\).</p>""",
        "correction": r"""The printed lemma simultaneously writes
        \(C(h)=O(\sqrt h)\) and error \(\le\sqrt h\,C(h)\)
        (supplement, lines 847–850), which would assert \(O(h)\). Retain one
        square root: either \(C(h)=O(1)\) in that display or error
        \(\le C(h)=O(\sqrt h)\). The noise \(W_k^n\) at line 845 must retain
        the datum index \(m\), and the heterogeneous drift keeps its superscript
        \(\widetilde\ell^m\).""",
        "scope": "No faithful Lean endpoint proves this source SDE/Euler coupling lemma from A3/A4. The new integral-reference consistency theorem derives an explicit O(√h) term under its own primitive drift/noise bounds and step condition.",
    },
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
        "scope": "The current explicit parameter RMS theorem is a new conditional analogue. It has not discharged the application obligations needed to recover this appendix theorem directly from the original four assumptions.",
    },
}


def reference(file, start_line, end_line, label):
    return {"file": file, "start_line": start_line, "end_line": end_line, "label": label}


PAPER_CORRECTIONS = [
    {
        "id": "C-A2",
        "title": "Universal time-zero density regularity is impossible",
        "prose": r"""A2 includes every finite-second-moment initial law and
        requires a smooth density at \(t=0\). A Dirac law has finite second
        moment but cannot have a density relative to nonatomic Lebesgue measure.
        Restrict the initial class to the required smooth densities, or require
        smoothing only for \(t>0\) and continuity in \(W_2\) at zero. Merely
        restricting to absolutely continuous laws still permits discontinuous
        initial densities. The Dirac obstruction is proved; the repaired flow
        existence theorem is an outstanding analytic task.""",
        "references": [reference(MAIN, 151, 154, "assump:solution_reg"), reference(SUPP, 436, 455, "eq:multi_datapoint_prodmetric")],
        "refs": [("LatentDiffusion/SourceObstruction.lean", "not_solutionRegularity_of_null_singleton"), ("LatentDiffusion/SourceObstruction.lean", "not_solutionRegularity_of_noAtoms")],
        "status": "Lean counterexample; analytic repair remains unproved",
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
        index \(m\). This repairs the displayed order; it does not complete
        the omitted source SDE/Euler proof.""",
        "references": [reference(SUPP, 841, 855, "lem:temporal_discretization"), reference(MAIN, 208, 212, "thrm:error-bound")],
        "refs": [],
        "status": "Source statement correction; full analytic reconstruction remains open",
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
        "refs": [],
        "status": "Source coupling/initialization repair; continuum bridge remains open",
    },
    {
        "id": "C-TALAGRAND",
        "title": "Keep the initial state fixed in the Talagrand inequality",
        "prose": r"""The intended right side is
        \(\lambda\inf_{b\in\mathcal M_\star}d(a,b)^2\) for the given state
        \(a\). The source instead takes an extra infimum over \(a\), making
        that term zero whenever a minimizer exists. Remove the extra infimum.
        A full proof still needs the stated dissipation, metric-speed and
        compactness bridges.""",
        "references": [reference(SUPP, 614, 620, "defn:xTalagrand"), reference(SUPP, 688, 711, "thm:xLSI_implies_xTalagrand")],
        "refs": [("LatentDiffusion/SourceResults.lean", "geodesic_quadratic_growth")],
        "status": "Definition correction; scalar quadratic growth proved from strong interpolation convexity; full Wasserstein implication open",
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
        "refs": [("LatentDiffusion/SourceResults.lean", "cauchy_minimizing_sequence"), ("LatentDiffusion/Marginal.lean", "existsUnique_averageMarginalMinimizer")],
        "status": "Corrected abstract minimizing-sequence theorem proved; actual energy-domain and flow hypotheses remain open",
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
        "refs": [("LatentDiffusion/SourceCalculus.lean", "parameter_freeEnergy_hasFDerivAt"), ("LatentDiffusion/SourceCalculus.lean", "density_firstVariation_of_zero_mass")],
        "status": "Actual first variations proved under explicit integral domination; continuum de Bruijn and transport obligations remain open",
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
        "status": "Algebraic correction recorded; not yet formalized as a Gaussian-kernel Lean theorem",
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
        "status": "Algebraic corrections recorded; no Gaussian-density Lean certificate yet",
    },
    {
        "id": "C-RANDOM-TIME",
        "title": "Restore the factor K for an unbiased random-time loss estimator",
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
        "status": "Sign correction; no annealed-flow Lean convergence claim",
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
        "status": "Algorithmic statement repairs; adaptive invariant-law and convergence proof remain open",
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
