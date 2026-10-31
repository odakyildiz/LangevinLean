"""Paper labels and hypothesis correspondence for the classical developments.

Labels are those of the cited edition. Unnumbered source conditions keep their
equation/theorem reference; they are never assigned invented assumption numbers.
The replacement estimates in ProximalLangevin are deliberately marked corrected:
their Lean proofs do not establish the numerical statements printed in the paper.
"""

DK = "https://arxiv.org/html/1710.00095v4"
VW = "https://www.cs.yale.edu/homes/wibisono/VW19.pdf"
SF = "https://arxiv.org/html/2409.07101v2"
PX = "https://arxiv.org/html/2406.14292v3"


def assumption(label, title, body, location, url, paper=None):
    row = dict(label=label, title=title, body=body, location=location, url=url)
    if paper:
        row["paper"] = paper
    return row


_ULA_ASSUMPTIONS = [
    assumption("Condition (2)", "Strong convexity and gradient Lipschitzness",
        r'''<p>Write the paper's \(f,m,M,p\) as \(U,m,L,d\). For all \(x,y\in\mathbb R^d\), with \(m,L>0\),</p>
        \[U(y)\ge U(x)+\langle\nabla U(x),y-x\rangle+\frac m2\|y-x\|^2,
        \qquad\|\nabla U(y)-\nabla U(x)\|\le L\|y-x\|.\]
        <p>Lean assumes differentiability and these two inequalities. Continuity of the gradient follows from its Lipschitz bound.</p>''',
        "Section 1, condition (2); Theorem 1", DK),
    assumption("Equation (4)", "Gaussian algorithm and initialization",
        r'''<p>\(X_{k+1}=X_k-h\nabla U(X_k)+\sqrt{2h}\,\xi_{k+1}\), where the \(\xi_k\) are independent \(\mathcal N(0,I_d)\) vectors independent of \(X_0\). Write \(\mu_0=\operatorname{Law}(X_0)\) and \(\pi(dx)\propto e^{-U(x)}dx\).</p>''',
        "Section 1, equation (4); Section 2.1, Theorem 1", DK),
]

_LSI_ASSUMPTIONS = [
    assumption("Conditions in Theorem 2", "Target and smoothness",
        r'''<p>\(\nu(dx)=Z^{-1}e^{-U(x)}dx\) is a probability measure. The differentiable potential obeys \(\|\nabla U(x)-\nabla U(y)\|\le L\|x-y\|\), with \(L>0\).</p>''',
        "Section 3.1, Theorem 2, p. 6; smoothness defined in Section 1", VW),
    assumption("Equation (4)", "Logarithmic Sobolev inequality",
        r'''<p>For \(\alpha>0\), \(2\alpha\operatorname{KL}(r\nu\Vert\nu)\le\int\|\nabla\log r\|^2r\,d\nu\). Lean quantifies over every strictly positive \(C^1\) function \(r\) with \(\int r\,d\nu=1\), using extended-valued entropy and Fisher information.</p>''',
        "Section 2.2, equation (4), p. 4; Theorem 2, p. 6", VW),
    assumption("Equation (11) and Theorem 2", "Gaussian updates and step size",
        r'''<p>\(X_{k+1}=X_k-h\nabla U(X_k)+\sqrt{2h}\,\xi_{k+1}\), with independent standard Gaussian innovations independent of initialization, and \(0&lt;h\le\alpha/(4L^2)\).</p>''',
        "Section 3, equation (11), p. 5; Section 3.1, Theorem 2, p. 6", VW),
]

_IPLA_ASSUMPTIONS = [
    assumption("Lemma 1 and Appendix B", "Joint-potential curvature and smoothness",
        r'''<p>For fixed data \(y\), the differentiable joint potential \(U_y(\theta,x)\) obeys, for every pair \(z,z'\),</p>
        \[U_y(z')\ge U_y(z)+\langle\nabla U_y(z),z'-z\rangle+\frac m2\|z'-z\|^2,
        \qquad\|\nabla U_y(z')-\nabla U_y(z)\|\le L\|z'-z\|,\quad m>0.\]
        <p>The source obtains curvature from its quadratic Poisson model. The formal theorem takes these conditions on a general joint potential.</p>''',
        "Section 4.1, Lemma 1, equation (33); Appendix B, equation (49)", SF),
    assumption("Conditions in Theorem 1", "Step and finite initial transport",
        r'''<p>\(N\ge1\), \(0&lt;\gamma\le2/(m+L)\), and \(W_2(\nu_0,\pi_N)&lt;\infty\) for the scaled state \(z=(\theta,x^1/\sqrt N,\ldots,x^N/\sqrt N)\) and \(\pi_N(dz)\propto\exp[-\sum_iU_y(\theta,\sqrt N z_i)]dz\). Lean's square-integrable initialization is equivalent to this transport condition because target second moments are proved.</p>''',
        "Section 4.1, Theorem 1, equation (34); Appendix B, equation (49)", SF),
    assumption("Equations (24)–(25)", "Gaussian particle recursion",
        r'''<p>The parameter update has noise amplitude \(\sqrt{2\gamma/N}\), and every physical latent update has amplitude \(\sqrt{2\gamma}\). All innovation coordinates and iterations are independent standard Gaussians and are independent of initialization.</p>''',
        "Section 3.1, equations (24)–(25); Appendix B, Gaussian Euler recursion", SF),
]

_PROXIMAL_ASSUMPTIONS = [
    assumption("A1", "Convex split potential",
        r'''<p>On \(\mathbb R^{d_\theta+d_x}\), write \(U=g_1+g_2\). The function \(g_1\) is convex, bounded below and \(C^1\), with \(\|\nabla g_1(z)-\nabla g_1(z')\|\le L_1\|z-z'\|\). The function \(g_2\) is proper, convex, lower semicontinuous and bounded below. The displayed Lean results use finite real-valued \(g_2\); A3 implies its continuity.</p>''',
        "Section 4.1, A1, p. 5", PX),
    assumption("A2", "Initial second moment",
        r'''<p>Define the scaled initial state by</p>\[Z_0^N=(\theta_0,N^{-1/2}X_0^{1,N},\ldots,N^{-1/2}X_0^{N,N}).\]<p>Assume \(\mathbb E\|Z_0^N\|^2\le H&lt;\infty\). Lean represents this initialization in \(L^2\).</p>''',
        "Section 4.1, A2, p. 5", PX),
    assumption("A3", "Lipschitz nonsmooth part",
        r'''<p>For some \(K\ge0\), \(|g_2(z)-g_2(z')|\le K\|z-z'\|\) for every \(z,z'\). All three displayed Lean bounds use this condition, including the replacement for Theorem 4.2.</p>''',
        "Section 4.1, A3, p. 5", PX),
    assumption("A4", "Strong convexity of the smooth part",
        r'''<p>For \(m>0\), \(g_1(z')\ge g_1(z)+\langle\nabla g_1(z),z'-z\rangle+\frac m2\|z'-z\|^2\), for every \(z,z'\).</p>''',
        "Section 4.1, A4, p. 5", PX),
    assumption("C1", "Source premise for Theorem 4.2",
        r'''<p>For some \(C\ge0\), \(\|\nabla^0 g_2(\theta,x)\|^2\le C\) for every \((\theta,x)\), where \(\nabla^0 g_2\) is the least-norm element of the convex subdifferential. This is the source premise of Theorem 4.2. The corrected Lean estimate below uses A3 instead and does not impose condition C1 as a separate premise.</p>''',
        "Section 4.4, condition C1, p. 6; Theorem 4.2", PX),
]


PAPER_SOURCES = {
    "UnadjustedLangevin": {
        "paper": "dalalyan-karagulyan",
        "assumptions": _ULA_ASSUMPTIONS,
        "extras": [
            dict(label="Extra A1", body=r'''<p>The quantitative real-valued endpoint assumes \(W_2(\mu_0,\pi)&lt;\infty\). The source does not separately impose this condition in Theorem 1; its extended-valued inequality is vacuous when the initial distance is infinite. This restriction makes the displayed Lean bound a finite estimate.</p>'''),
        ],
        "scope": r"The source uses unnumbered condition (2), rather than an Assumption 1. Both displayed bounds reproduce Theorem 1 with its coefficient \(1.65\), for finite initial transport distance as specified in Extra A1.",
        "results": {
            "dalalyan": dict(label="Theorem 1(a)", location="Section 2.1, Theorem 1(a)", url=DK,
                status="proved", note=r"The source bound for the small-step regime, with \(33/20=1.65\). Stationarity, moments and the Brownian reference are proved from condition (2).", extras=["Extra A1"]),
            "dalalyan_large_step": dict(label="Theorem 1(b)", location="Section 2.1, Theorem 1(b)", url=DK,
                status="proved", note=r"The source bound for the larger-step regime. The displayed restriction \(Lh&lt;2\) is the source theorem's stability condition.", extras=["Extra A1"]),
        },
    },
    "UnadjustedLangevin/LSI": {
        "paper": "vempala-wibisono",
        "assumptions": _LSI_ASSUMPTIONS,
        "extras": [
            dict(label="Extra A1", body=r'''<p>The quantitative endpoint assumes \(\operatorname{KL}(\mu_0\Vert\nu)&lt;\infty\). The source does not list initial entropy finiteness as a separate premise in Theorem 2; for infinite initial entropy its extended-valued upper bound is immediate. The Lean statement proves finite entropy at every iterate under this finite-initial-entropy restriction.</p>'''),
        ],
        "scope": "The paper states its hypotheses within Theorem 2 and equation (4); it gives them no A1/A2 numbering. The main discrete entropy inequality is formalized for the finite-entropy endpoint in Extra A1. Its separate logarithmic iteration threshold and stationary-bias corollary are outside this displayed theorem.",
        "results": {
            "ula_kl_bound": dict(label="Theorem 2", location="Section 3.1, Theorem 2, p. 6; Appendix B.2.2, p. 19", url=VW,
                status="proved", note=r"The discrete KL inequality and coefficient \(8\) agree with the source. Lean also proves finiteness at each iterate. Positive-time density differentiation and the initial endpoint estimate are proved, so no extra interpolation assumption is imposed.", extras=["Extra A1"]),
        },
    },
    "IPLA": {
        "paper": "statfem-ipla",
        "assumptions": _IPLA_ASSUMPTIONS,
        "extras": [],
        "scope": r"Theorem 1 is the paper's forcing-estimation bound. The formal theorem generalizes its equal dimensions to independent parameter and latent dimensions. Its potential smoothness follows Appendix B: \(L\) bounds the same joint posterior potential that drives the algorithm. The printed theorem instead names the prior-free potential \(\Phi\); those constants are not identified here.",
        "results": {
            "theorem1": dict(label="Theorem 1", location="Section 4.1, Theorem 1, equation (34); Appendix B", url=SF,
                status="corrected", note=r"Equation (34) is recovered when \(d_\theta=d_x=n_u\), using \(L\) for the joint posterior potential as in Appendix B. The displayed independent-dimension and general-potential formulation is an unpublished extension; the Poisson-specific Hessian calculation is not the theorem proved by this declaration.", extras=[]),
        },
    },
    "IPLA/LSI": {
        "paper": "statfem-ipla",
        "assumptions": [
            assumption("Equations (24)–(25) and Appendix B", "Particle algorithm and scaled target",
                r'''<p>Use the Gaussian IPLA recursion and \(V_N(z)=\sum_{i=1}^N U(\theta,\sqrt N z_i)\), with \(N\ge1\) and \(z=(\theta,x^1/\sqrt N,\ldots,x^N/\sqrt N)\). Its scaled laws are ULA laws with step \(\gamma/N\).</p>''',
                "Section 3.1, equations (24)–(25); Appendix B, equation (49)", SF, "statfem-ipla"),
            assumption("Smoothness condition in Theorem 2", "ULA smoothness applied to the particle potential",
                r'''<p>Assume \(U\) is differentiable and \(\|\nabla U(z)-\nabla U(z')\|\le L\|z-z'\|\), with \(L>0\). The proved lifted gradient constant is \(NL\). This transfers the smoothness premise of the cited ULA theorem; strong convexity is not required for this entropy extension.</p>''',
                "Vempala–Wibisono, Section 3.1, Theorem 2, p. 6", VW, "vempala-wibisono"),
        ],
        "extras": [
            dict(label="Extra A1", body=r'''<p>For the actual joint probability target \(\Pi_N(dz)=Z_N^{-1}e^{-V_N(z)}dz\), assume \(\beta_N>0\) and \(2\beta_N\operatorname{KL}(r\Pi_N\Vert\Pi_N)\le\int\|\nabla\log r\|^2r\,d\Pi_N\) for every strictly positive \(C^1\) probability density \(r\) relative to \(\Pi_N\). An inequality for one parameter–latent pair alone does not imply this premise.</p>'''),
            dict(label="Extra A2", body=r'''<p>The initial joint probability law satisfies \(\operatorname{KL}(\mu_0\Vert\Pi_N)&lt;\infty\). For the general bound assume \(0&lt;\gamma\le\beta_N/(4NL^2)\). Finite parameter-marginal entropy alone does not supply the initial joint entropy.</p>'''),
            dict(label="Extra A3", body=r'''<p>For the linear specialization, assume \(\alpha>0\), that the actual joint target \(\Pi_N\) satisfies the inequality in Extra A1 with \(\beta_N=N\alpha\), and that \(0&lt;\gamma\le\alpha/(4L^2)\). This is an assumption on the shared-parameter particle target, not a proved tensorization statement.</p>'''),
        ],
        "scope": "This page is an unpublished entropy extension. It applies Vempala–Wibisono's Theorem 2 to the scaled IPLA algorithm. Neither cited paper states these IPLA entropy conclusions as a numbered theorem.",
        "results": {
            "particle_kl_bound_linear_lsi_of_finite_kl": dict(label="New result — IPLA joint entropy and linear-LSI specialization", location="Unpublished extension of Vempala–Wibisono, Theorem 2, to the StatFEM IPLA lift", url=VW,
                status="new", note=r"The full and per-particle joint entropy bounds, the specialization \(\beta_N=N\alpha\), and the parameter data-processing consequence are new results in this project. No entropy theorem from the StatFEM paper is claimed to be formalized. Parameter entropy is bounded by full joint entropy, without division by \(N\).", extras=["Extra A1", "Extra A2", "Extra A3"]),
        },
    },
    "ProximalLangevin": {
        "paper": "proximal-ipla",
        "assumptions": _PROXIMAL_ASSUMPTIONS,
        "extras": [
            dict(label="Extra A1", body=r'''<p>The exported PIPGLA theorem explicitly assumes \(m\le L_1\); the exported MYPGD theorem explicitly assumes \(m\le L_\eta=L_1+\eta^{-1}\). A1 and A4 imply these comparisons whenever the joint Euclidean dimension is positive. They remain explicit numerical side conditions in the declarations, including degenerate dimensions.</p>'''),
        ],
        "scope": "The labels below identify the source statements to which the Lean results correspond. All three are corrected replacement estimates with different conclusions; the printed Theorems 4.1, 4.2 and B.1 are not proved verbatim. The alternative smoothing argument uses A1–A4 and a uniform value gap, rather than the paper's A5 Taylor argument. Each Gaussian realization uses the independent innovations specified by its source algorithm.",
        "results": {
            "moreau_myipla_parameter_rms_original": dict(label="Theorem 4.1", title="MYIPLA", location="Section 4.3, Theorem 4.1, p. 6; restated as Theorem A.5, p. 17", url=PX,
                status="corrected", note=r"Replacement bound: the smoothing displacement is \(K\sqrt{\eta/m}\), and the explicit discretization coefficient uses \(L_\eta=L_1+1/\eta\). The paper's linear smoothing expansion and smoothing-independent discretization coefficient are not established. The displayed step restriction is the one in Lean.", extras=[]),
            "pipgla_parameter_rms_original": dict(label="Theorem 4.2", title="PIPGLA", location="Section 4.4, Theorem 4.2, p. 6; restated as Theorem A.15, p. 25", url=PX,
                status="corrected", note=r"Replacement bound with a smoothed reference target, an explicit transport constant, square-root smoothing displacement, and sensitivity term \(K|\lambda-\gamma|/(m\gamma)\). It assumes the paper's A3 rather than imposing condition C1 as a premise, and allows every \(\lambda>0\) under the displayed Lean step restriction. The source's constants and unsmoothed-target formula are not reproduced.", extras=["Extra A1"]),
            "moreau_mypgd_parameter_rms_original": dict(label="Theorem B.1", title="MYPGD", location="Appendix B.2, Theorem B.1, p. 26", url=PX,
                status="corrected", note=r"Replacement bound obtained by coupling MYPGD with MYIPLA and controlling omitted parameter noise. It has conservative constants and initial \(W_2\) distance to the smoothed Gibbs target. The paper's mean-field transient, Taylor bias, and propagation-of-chaos conclusion are not reproduced.", extras=["Extra A1"]),
        },
    },
}
