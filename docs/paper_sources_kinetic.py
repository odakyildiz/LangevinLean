"""Exact manuscript labels for the kinetic and average-smoothness landing pages.

The supplied manuscripts are the statement authority.  ``source_label`` is a
TeX cross-reference identifier, never a printed theorem number.  In particular,
kinetic th:3/th:4 print Theorem 2/Theorem 3, and average-LMC th:3 prints Theorem 2.
The KIPLMC assumption environment prints H1 and H2.  Neither the kinetic nor
average-LMC manuscript introduces numbered assumption environments, so their
hypotheses are cited by the theorem in which they appear instead of invented A's.
Public URLs remain usable in the published site; source coordinates allow an
independent comparison with the audited manuscript.
"""

KINETIC_URL = "https://doi.org/10.3150/19-BEJ1178"
KIPLMC_URL = "https://doi.org/10.1007/s11222-026-10980-z"
AVERAGE_URL = "https://arxiv.org/abs/2605.31413v1"
KINETIC_FILE = "papers/kinetic_Langevin/mainDR_dec_18.tex"
KIPLMC_FILE = "papers/KIPLMC/sections/analysis.tex"
AVERAGE_FILE = "papers/Average_LMC/Arxiv_version_May_26.tex"


def source(label, location, url, source_file, start, end, source_label=None):
    return dict(label=label, location=location, url=url,
                source_file=source_file, source_start=start, source_end=end,
                source_label=source_label)


def result(file, label, location, url, source_file, start, end,
           source_label=None, status="proved", note="", extras=(), title=""):
    return dict(file=file, **source(label, location, url, source_file, start, end,
                                   source_label),
                status=status, note=note, extras=list(extras), title=title)


PAPER_SOURCES = {
    "KineticLangevin": dict(
        paper="dalalyan-riou-durand",
        source_version="Supplied mainDR_dec_18.tex (the audited manuscript; its exact public version date is not encoded)",
        scope="The audited kinetic manuscript prints Theorem 1 (mixing), Theorem 2 (KLMC), and Theorem 3 (KLMC2). Its TeX identifiers th:3 and th:4 do not determine their printed numbers. The exact-moment KLMC2 and condition-number bounds below are explicit corrections, distinguished from literal paper statements.",
        assumption_note="The manuscript has no numbered assumptions. The entries below retain its standing hypotheses and the original theorem numbers; they are not new Assumptions A1, A2, etc.",
        assumptions=[
            dict(**source("Standing hypotheses", "Introduction, paragraph immediately before the Langevin equation", KINETIC_URL, KINETIC_FILE, 157, 161),
                 title="The target and its curvature bounds",
                 body=r'''<p>Let \(p\ge1\), \(0&lt;m\le M\), and \(\pi(dx)=Z^{-1}e^{-f(x)}dx\) on \(\mathbb R^p\). The potential \(f\) is differentiable, \(m\)-strongly convex, and its gradient is \(M\)-Lipschitz: for every \(x,y\in\mathbb R^p\),</p>
\[f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle+\frac m2\|y-x\|^2,
\qquad \|\nabla f(x)-\nabla f(y)\|\le M\|x-y\|.\]
<p>The inverse mass is set to \(u=1\) after Lemma 1. Strong convexity proves \(0&lt;Z&lt;\infty\); normalization and Gibbs moments are conclusions of the formalization.</p>''',
                 refs=[("KineticLangevin/HessianAssumptions.lean", ""), ("KineticLangevin/MassScaling.lean", "")]),
            dict(**source("Theorem 1 hypotheses", "Section 2, Theorem 1 (th:1), equations exp1 and exp2", KINETIC_URL, KINETIC_FILE, 293, 316, "th:1"),
                 title="Hessian bounds and common initial velocity",
                 body=r'''<p>The paper assumes that \(f\) is twice differentiable and</p>
\[mI_p\preceq\nabla^2f(x)\preceq MI_p\qquad(x\in\mathbb R^p).\]
<p>The initial phase laws are \(\eta\otimes\mu\) and \(\eta\otimes\nu\): they share a velocity law \(\eta\), and velocity is independent of position in each law. The friction and time satisfy \(\gamma,t&gt;0\), and the shift in the explicit bound satisfies \(0\le v&lt;\gamma/2\). The checked endpoint proves the same explicit bound under the weaker differentiability, strong-convexity and gradient-Lipschitz hypotheses above, and allows every shift \(v&lt;\gamma/2\).</p>''',
                 refs=[("KineticLangevin/HessianAssumptions.lean", ""), ("KineticLangevin/FlowLaw.lean", "kineticPositionLaw_wasserstein2Real_general")]),
            dict(**source("Theorem 2 hypotheses", "Section 3, Theorem 2 (th:3) and the KLMC recursion", KINETIC_URL, KINETIC_FILE, 513, 526, "th:3"),
                 title="Thermal initialization and the first-order step cap",
                 body=r'''<p>Use the Hessian bounds of Theorem 1. Initialize the phase law as \(\mathcal N(0,I_p)\otimes\nu_0\). The KLMC recursion uses the independent centered Gaussian innovation pairs with the joint covariance specified beside the recursion. Take</p>
\[\gamma\ge\sqrt{m+M},\qquad 0&lt;h\le\frac{m}{4\gamma M}.\]
<p>These are paper hypotheses, including the prescribed correlated Gaussian law; their independence and covariance are built into the constructed chain.</p>''',
                 refs=[("KineticLangevin/CanonicalKLMC.lean", "klmc_wasserstein_bound")]),
            dict(**source("Theorem 3 hypotheses", "Section 4, Theorem 3 (th:4) and the KLMC2 recursion", KINETIC_URL, KINETIC_FILE, 668, 690, "th:4"),
                 title="A Lipschitz Hessian and the second-order step caps",
                 body=r'''<p>In addition to \(m\)-strong convexity and the \(M\)-Lipschitz gradient, the Hessian exists and is \(M_2\)-Lipschitz in operator norm, with \(M_2&gt;0\):</p>
\[\|\nabla^2 f(x)-\nabla^2 f(y)\|_{\mathrm{op}}\le M_2\|x-y\|\qquad(x,y\in\mathbb R^p).\]
<p>Initialize with \(\mathcal N(0,I_p)\otimes\nu_0\), independently of the four-kernel Gaussian innovation stream specified by the KLMC2 recursion, and take</p>
\[\gamma\ge\sqrt{m+M},\qquad
0&lt;h\le\min\!\left\{\frac{m}{5\gamma M},\frac{m}{4\sqrt{5p}\,M_2}\right\}.\]
<p>The supplied Hessian map \(H\) satisfies \(D(\nabla f)(x)=H(x)\) and \(\|H(x)-H(y)\|_{\mathrm{op}}\le M_2\|x-y\|\). These identify the actual Hessian, rather than a separate matrix-valued approximation.</p>''',
                 refs=[("KineticLangevin/CanonicalKLMC2.lean", "klmc2_wasserstein_bound_exact")]),
        ],
        extras=[
            dict(label="Extra A1", title="Finite initial quadratic transport for the real-valued endpoints",
                 body=r'''<p>For the displayed real-valued law-to-law theorem require \(W_2(\mu,\nu)&lt;\infty\). For the displayed Gibbs-target diffusion and sampler theorems require \(W_2(\nu_0,\pi)&lt;\infty\), equivalently \(\int\|x\|^2\,\nu_0(dx)&lt;\infty\). This finiteness is an explicit premise of the displayed theorem; the paper's main theorem statements do not explicitly impose it. The general endpoint-map contraction also has an extended-nonnegative version for arbitrary probability laws.</p>''',
                 refs=[("KineticLangevin/FlowLaw.lean", "kineticPositionLaw_wasserstein2Real_general"), ("KineticLangevin/ContinuousGibbs.lean", "wasserstein2_gibbs_general"), ("KineticLangevin/CanonicalKLMC.lean", "klmc_wasserstein_bound"), ("KineticLangevin/CanonicalKLMC2.lean", "klmc2_wasserstein_bound_exact")]),
            dict(label="Extra A2", title="Dimension restriction only for the printed KLMC2 coefficient",
                 body=r'''<p>Require \(p\ge2\) only when replacing the exact fourth-moment coefficient by the paper's displayed coefficient. The necessary comparison is</p>
\[\sqrt2\,\sqrt{p^2+2p}\le2p\quad\Longleftrightarrow\quad p\ge2
\qquad(p&gt;0).\]
<p>The corrected exact-moment version of Theorem 3 remains valid for \(p=1\) and does not use Extra A2.</p>''',
                 refs=[("KineticLangevin/CanonicalKLMC2.lean", "klmc2_wasserstein_bound")]),
            dict(label="Extra A3", title="Optional regime for the printed condition-number shorthand",
                 body=r'''<p>Set \(\kappa=M/m\) and \(\rho=(M_2^{2/3}+Mp^{-1/3})/m\). To recover the paper's condition-number expression from the uniform corrected count, assume</p>
\[M(1-p^{-1/3})\le M_2^{2/3},\qquad\text{equivalently }\kappa\le\rho.\]
<p>The checked uniform count instead uses \(\max\{\kappa,\rho\}\) and requires no Extra A3. This optional regime does not justify dropping the exponential tail from a sampler accuracy statement.</p>''',
                 refs=[("KineticLangevin/SecondOrderComplexity.lean", "secondOrderTailFree_iterationCount_conditionNumber"), ("KineticLangevin/ConditionNumber.lean", "")]),
        ],
        results={
            "kineticPositionLaw_wasserstein2Real_general": result(
                "KineticLangevin/FlowLaw.lean", "Theorem 1", "Section 2, Theorem 1, explicit equation exp2 (th:1)", KINETIC_URL, KINETIC_FILE, 293, 316, "th:1",
                status="corrected", extras=["Extra A1"], title="The explicit shifted contraction bound",
                note=r'''The explicit equation exp2 is proved, with the true Wasserstein infimum. The separate printed exp1 claim \(\alpha\le\sqrt2/\gamma\) is corrected: setting the shift to zero in exp2 gives prefactor \(\sqrt2\). The selected endpoint-map theorem also applies to any common continuous forcing independent of initial position; the Brownian specialization is proved separately.'''),
            "wasserstein2_gibbs_general": result(
                "KineticLangevin/ContinuousGibbs.lean", "Theorem 1", "Section 2, Theorem 1 (th:1), specialized to the invariant Gibbs position law", KINETIC_URL, KINETIC_FILE, 293, 316, "th:1",
                status="corrected", extras=["Extra A1"], title="Brownian convergence to Gibbs equilibrium",
                note=r'''This is a Gibbs-target specialization of Theorem 1, rather than a separately numbered paper theorem. Gibbs stationarity is proved internally. It uses the explicit exp2 coefficient and therefore avoids the erroneous exp1 prefactor. The constructed Brownian integral solution is continuous in \(L^2\); almost-sure continuity of paths is not claimed.'''),
            "klmc_wasserstein_bound": result(
                "KineticLangevin/CanonicalKLMC.lean", "Theorem 2", "Section 4, Theorem 2 (TeX identifier th:3)", KINETIC_URL, KINETIC_FILE, 513, 526, "th:3",
                extras=["Extra A1"], title="KLMC convergence",
                note="The paper's displayed KLMC coefficient, contraction factor and step restriction are proved for the constructed correlated-Gaussian chain. The finite initial transport premise is explicit in this real-valued endpoint."),
            "klmc2_wasserstein_bound_exact": result(
                "KineticLangevin/CanonicalKLMC2.lean", "Theorem 3", "Section 4, Theorem 3 (TeX identifier th:4), corrected exact-moment version", KINETIC_URL, KINETIC_FILE, 668, 690, "th:4",
                status="corrected", extras=["Extra A1"], title="KLMC2 with the exact Gaussian fourth moment",
                note=r'''The correction retains \(\sqrt{p^2+2p}\), so the result includes dimension one. The proof also restores the stochastic Hessian-difference terms omitted in the manuscript subtraction. The exact Gaussian cutoff yields both the displayed \(e^{-p/2}\) relaxation and the sharper inverse-step-square tail in the paper's footnote. Extra A2 is unnecessary here.'''),
            "klmc2_wasserstein_bound": result(
                "KineticLangevin/CanonicalKLMC2.lean", "Theorem 3", "Section 4, Theorem 3 (TeX identifier th:4), displayed KLMC2 simplification", KINETIC_URL, KINETIC_FILE, 668, 690, "th:4",
                status="corrected", extras=["Extra A1", "Extra A2"], title="The printed KLMC2 bound with its required dimension condition",
                note=r'''The printed expression is proved with the additional dimension condition \(p\ge2\). Without that condition the exact-moment version above is the proved conclusion; the all-dimension printed coefficient is not claimed.'''),
            "secondOrderTailFree_iterationCount_conditionNumber": result(
                "KineticLangevin/SecondOrderComplexity.lean", "New result", "Section 4, unnumbered discussion immediately after Theorem 3; condition-number refinement", KINETIC_URL, KINETIC_FILE, 693, 708,
                status="new", title="A corrected uniform bound for the tail-free iteration prescription",
                note=r'''This is a new, explicit integer-count correction to the paper's unnumbered asymptotic discussion, not an additional paper theorem. It uses \(R=\max\{\kappa,\rho\}\) and an explicit constant \(64\). Extra A3 is needed only to replace \(R\) by the paper's \(\rho\). The count concerns the prescription that omits the exponential tail; it is not by itself a complete KLMC2 accuracy guarantee.'''),
        },
    ),
    "KIPLMC": dict(
        paper="kinetic-ipla",
        source_version="Supplied main.tex and sections/*.tex (the audited multifile manuscript; its exact public version date is not encoded)",
        scope="The source assumptions are H1 and H2. Proposition 3 and Theorems 1 and 2 are the paper convergence statements; Proposition 2 gives concentration. The two coordinate identities are Algorithm 1 and Algorithm 2 correspondence statements, not additional paper theorems.",
        assumption_note="The source prints its assumptions as H1 and H2. The theorem-specific initialization and step restrictions below are also in the paper; they are not extra assumptions.",
        assumptions=[
            dict(**source("H1", "Section 4.1, H1 (assump:strongconvexity)", KIPLMC_URL, KIPLMC_FILE, 10, 16, "assump:strongconvexity"),
                 title="Joint strong convexity of the model potential",
                 body=r'''<p>Let \(U\in C^2(\mathbb R^{d_\theta+d_x})\). There is \(\mu&gt;0\) such that, for all \(z,z'\in\mathbb R^{d_\theta+d_x}\),</p>
\[\langle z-z',\nabla U(z)-\nabla U(z')\rangle\ge\mu\|z-z'\|^2.\]
<p>Equivalently, \(\nabla^2U(z)\succeq\mu I\) for every \(z\). The condition concerns \((\theta,x)\) jointly. The checked endpoints use differentiability and the corresponding strong-convexity inequality; they prove the results under weaker assumptions than \(C^2\).</p>''',
                 refs=[("KIPLMC/Geometry.lean", "")]),
            dict(**source("H2", "Section 4.1, H2 (assump:lipschitz)", KIPLMC_URL, KIPLMC_FILE, 19, 25, "assump:lipschitz"),
                 title="A global Lipschitz bound for the joint gradient",
                 body=r'''<p>There is \(L&gt;0\) such that, for all \(z,z'\in\mathbb R^{d_\theta+d_x}\),</p>
\[\|\nabla U(z)-\nabla U(z')\|\le L\|z-z'\|.\]
<p>Together H1 and H2 imply \(\mu\le L\). The displayed notation uses \(m=\mu\).</p>''',
                 refs=[("KIPLMC/Geometry.lean", "")]),
            dict(**source("Proposition 3 hypotheses", "Section 4.3.2, Proposition 3 (prop:kipld_conv)", KIPLMC_URL, KIPLMC_FILE, 74, 91, "prop:kipld_conv"),
                 title="KIPLD initialization and friction",
                 body=r'''<p>For \(N\ge1\), set \(d_z=d_\theta+Nd_x\) and \(Z_0=(\Theta_0,N^{-1/2}X_0^1,\ldots,N^{-1/2}X_0^N)\). Its law \(\nu\) satisfies \(\int\|z\|^2\nu(dz)&lt;\infty\). Independently of \(Z_0\), initialize mutually independent velocities with</p>
\[V_0^\theta\sim\mathcal N(0,N^{-1}I_{d_\theta}),\qquad
V_0^{x_i}\sim\mathcal N(0,I_{d_x}).\]
<p>Use H1, H2 and \(\gamma\ge\sqrt{\mu+L}\). The reference \(\bar Z_\star\sim\widetilde\pi_Z\) in the bound is independent of \(Z_0\).</p>''',
                 refs=[("KIPLMC/Continuous.lean", "kipld_parameter_sampling_bound")]),
            dict(**source("Theorem 1 hypotheses", "Section 4.3.3, Theorem 1 (thm:KPLMC1)", KIPLMC_URL, KIPLMC_FILE, 96, 107, "thm:KPLMC1"),
                 title="KIPLMC1 initialization and step restriction",
                 body=r'''<p>Use H1, H2, \(N\ge1\), the finite-second-moment scaled initial position, and the independent thermal velocity law described above. Run Algorithm 1 with its prescribed independent correlated-Gaussian innovation pairs and</p>
\[\gamma\ge\sqrt{\mu+L},\qquad0&lt;\eta\le\frac{\mu}{4\gamma L}.\]
<p>The theorem's initial constant is the root mean square of \(Z_0-\bar Z_\star\) for the independent product \(\nu\otimes\widetilde\pi_Z\), rather than an assumed optimal coupling.</p>''',
                 refs=[("KIPLMC/CanonicalExponential.lean", "kiplmc1_parameter_bound_independent")]),
            dict(**source("Theorem 2 hypotheses", "Section 4.3.4, Theorem 2 (thm:KIPLMC2)", KIPLMC_URL, KIPLMC_FILE, 120, 143, "thm:KIPLMC2"),
                 title="KIPLMC2 initialization and step restriction",
                 body=r'''<p>Use H1, H2, \(N\ge1\), a finite-second-moment law for \(Z_0\), and mutually independent thermal velocities independent of \(Z_0\). Algorithm 2 uses fresh independent standard Gaussian vectors for its thermostat half-steps. Require</p>
\[\gamma\ge2\sqrt L,\qquad0&lt;\eta\le\frac{\mu}{33\gamma^3}.\]
<p>The implicit constant in the paper may depend on \(\mu,L,\gamma\), and is independent of \(n,N,\eta,d_\theta,d_x\). The formalization supplies such a constant explicitly.</p>''',
                 refs=[("KIPLMC/OBABOPaperRate.lean", "kiplmc2_parameter_paper_bound")]),
        ],
        extras=[],
        results={
            "kipld_parameter_sampling_bound": result(
                "KIPLMC/Continuous.lean", "Proposition 3", "Section 4.3.2, Proposition 3 (prop:kipld_conv)", KIPLMC_URL, KIPLMC_FILE, 74, 91, "prop:kipld_conv",
                title="Convergence of KIPLD to its stationary parameter law",
                note=r"The printed physical-time estimate is proved with the independent initial-position/reference coupling specified in the source. The constructed integral solution is continuous in \(L^2\); almost-sure path continuity is not asserted."),
            "kiplmc1_parameter_bound_independent": result(
                "KIPLMC/CanonicalExponential.lean", "Theorem 1", "Section 4.3.3, Theorem 1 (thm:KPLMC1)", KIPLMC_URL, KIPLMC_FILE, 96, 107, "thm:KPLMC1",
                title="KIPLMC1 parameter root mean square error",
                note=r"The displayed \(C_1,C_2,C_3\) are proved for the actual correlated-Gaussian recursion, including the source's independent initial coupling constant."),
            "kiplmc2_parameter_paper_bound": result(
                "KIPLMC/OBABOPaperRate.lean", "Theorem 2", "Section 4.3.4, Theorem 2 (thm:KIPLMC2)", KIPLMC_URL, KIPLMC_FILE, 120, 143, "thm:KIPLMC2",
                title="KIPLMC2 parameter root mean square error",
                note="The printed coarse rate is proved with an explicit constant depending only on the allowed curvature and friction parameters. The argument first proves a stronger Gaussian-chain estimate and then deduces the paper's rate."),
            "parameter_secondMoment_le": result(
                "KIPLMC/Target.lean", "Proposition 2", "Section 4.3.1, Proposition 2 (prop:mmleerror)", KIPLMC_URL, KIPLMC_FILE, 56, 63, "prop:mmleerror",
                title="Concentration of the stationary parameter marginal",
                note=r'''The squared-moment statement implies the printed \(W_2(\pi_\Theta,\delta_{\theta_\star})\le\sqrt{d_\theta/(N\mu)}\). The normalized target and unique marginal maximizer are also proved.'''),
            "kiplmc1Step_particle_velocity": result(
                "KIPLMC/Exponential.lean", "Algorithm 1", "Section 3.1, Algorithm 1 (alg:KIPLMC1), KIPLMC1 coordinate recursion", KIPLMC_URL, "papers/KIPLMC/sections/kiplmc.tex", 80, 111, "alg:KIPLMC1",
                status="auxiliary", title="The KIPLMC1 coordinate update",
                note="This checked identity is a coordinate component of the paper's Algorithm 1. It is an algorithm correspondence statement, not a separately numbered convergence theorem."),
            "kiplmc2Step_velocity": result(
                "KIPLMC/Splitting.lean", "Algorithm 2", "Section 3.2, Algorithm 2 (alg:KIPLMC2), the OBABO update", KIPLMC_URL, "papers/KIPLMC/sections/kiplmc.tex", 164, 213, "alg:KIPLMC2",
                status="auxiliary", title="The KIPLMC2 coordinate update",
                note="This checked identity expands the paper's Algorithm 2. It specifies the two thermostat half-steps, the position step, and the force evaluated at the updated position; it is not a separately numbered convergence theorem."),
        },
    ),
    "AverageLMC": dict(
        paper="average-lmc",
        source_version="arXiv:2605.31413v1, identical to the audited Arxiv_version_May_26.tex",
        scope="The original main-result labels are Theorem 1 (one-step and constant-step LMC), Proposition 1 (decreasing steps), Theorem 2 (Laplacian LMC), and Theorem 3 (SGLD). The TeX identifier th:3 belongs to printed Theorem 2. The source has no numbered assumptions.",
        assumption_note="The paper has no numbered assumptions. Its hypotheses are stated with the original theorem or proposition number below; no replacement A1, A2 numbering is introduced.",
        assumptions=[
            dict(**source("Theorem 1 hypotheses", "Section 2.1, Theorem 1 (th:1); standing condition Lip:1 and definitions coordM", AVERAGE_URL, AVERAGE_FILE, 531, 554, "th:1"),
                 title="Strong convexity, smoothness, and the Gaussian LMC step",
                 body=r'''<p>Let \(p\ge1\), \(0&lt;m\le M_\infty\), and let \(f:\mathbb R^p\to\mathbb R\) be differentiable with</p>
\[\frac m2\|y-x\|^2\le f(y)-f(x)-\langle\nabla f(x),y-x\rangle\le\frac{M_\infty}{2}\|y-x\|^2\qquad(x,y\in\mathbb R^p).\]
<p>Equivalently, \(f\) is \(m\)-strongly convex with \(M_\infty\)-Lipschitz gradient. With \(e_j\) the coordinate vectors, use the paper's literal constants</p>
\[M_j=\sup_{x\in\mathbb R^p,\,t\ne0}\frac{2[f(x+te_j)-f(x)-t\,\partial_jf(x)]}{t^2},\qquad M_{\mathrm{av}}=\frac1p\sum_{j=1}^p M_j.\]
<p>The step is \(X^+=X-h\nabla f(X)+\sqrt{2h}\,\xi\), with \(\xi\sim\mathcal N(0,I_p)\) independent of \(X\). The local inequality allows \(h\ge0\); the constant-step conclusion uses \(0\le h\le1/M_\infty\). Across iterations, the Gaussian vectors are mutually independent and independent of the initialization.</p>''',
                 refs=[("AverageLMC/Assumptions.lean", ""), ("AverageLMC/GaussianLMC.lean", "lmc_one_step")]),
            dict(**source("Proposition 1 hypotheses", "Section 2.3, Proposition 1 (prop:VSS)", AVERAGE_URL, AVERAGE_FILE, 712, 735, "prop:VSS"),
                 title="The specified decreasing-step schedule",
                 body=r'''<p>Use the hypotheses of Theorem 1, put \(\kappa_\infty=M_\infty/m\) and \(\kappa_{\mathrm{av}}=M_{\mathrm{av}}/m\), and assume \(W_2^2(\nu_0,\pi)\le\varepsilon_0^2p/m\). Set</p>
\[k_0=\left\lceil\frac{\kappa_\infty}{2}\log_+\!\left(\frac{2\kappa_\infty\varepsilon_0^2}{\kappa_{\mathrm{av}}+1}\right)\right\rceil,
\qquad h_k=\frac1{M_\infty+m(k-k_0)_+}.\]
<p>The conclusion is stated for \(k\ge k_0\). The initial upper bound in the paper already implies finite initial quadratic transport when interpreted in \([0,\infty]\).</p>''',
                 refs=[("AverageLMC/Theorem.lean", "lmc_variable_step")]),
            dict(**source("Theorem 2 hypotheses", "Section 4, Theorem 2 (TeX identifier th:3); condition lip:2", AVERAGE_URL, AVERAGE_FILE, 1017, 1031, "th:3"),
                 title="The gradient-of-Laplacian condition",
                 body=r'''<p>Use the curvature and smoothness hypotheses of Theorem 1. In addition, \(f\in C^3(\mathbb R^p)\) and, for a finite \(M_\Delta\ge0\),</p>
\[\sup_{x\in\mathbb R^p}\|\nabla\Delta f(x)\|^2\le M_\Delta^2p.\]
<p>Take a constant step \(0&lt;h&lt;1/M_\infty\). The proof uses this condition directly and adds neither a Lipschitz-Hessian condition nor a fourth derivative.</p>''',
                 refs=[("AverageLMC/LaplacianTheorem.lean", "lmc_laplacian")]),
            dict(**source("Theorem 3 hypotheses", "Section 5, Theorem 3 (th:sgld), finite-sum setup and eq:Mtwo", AVERAGE_URL, AVERAGE_FILE, 1160, 1178, "th:sgld"),
                 title="Finite-sum smoothness and fixed-point control-variate SGLD",
                 body=r'''<p>Let \(n\ge1\), \(f=\sum_{i=1}^n f_i\), and let each \(f_i\) be differentiable with finite gradient Lipschitz seminorm \(L_i=\|\nabla f_i\|_{\mathrm{Lip}}\). The full potential is \(n\bar m\)-strongly convex with \(n\bar M_\infty\)-Lipschitz gradient, where \(0&lt;\bar m\le\bar M_\infty\). Define</p>
\[M_{\mathrm{rms}}^2=\frac1n\sum_{i=1}^n L_i^2,\qquad
\bar M_{\mathrm{av}}=M_{\mathrm{av}}(f/n)=M_{\mathrm{av}}(f)/n.\]
<p>Let \(\theta_\star\) be the unique minimizer of \(f\). Use the update \(X^+=X-hn(\nabla f_I(X)-\nabla f_I(\theta_\star))+\sqrt{2h}\,\xi\), where \(I\) is uniform on \(\{1,\ldots,n\}\), \(\xi\sim\mathcal N(0,I_p)\), and all fresh indices, Gaussian vectors and the initialization are independent. Require</p>
\[0\le h\le\frac{\bar m}{3nM_{\mathrm{rms}}^2}.\]
<p>The individual \(f_i\) need not be convex.</p>''',
                 refs=[("AverageLMC/SGLDTheorem.lean", "sgld_constant_step_paper"), ("AverageLMC/SGLDEstimator.lean", "")]),
        ],
        extras=[
            dict(label="Extra A1", title="Finite quadratic transport for the signed one-step inequality",
                 body=r'''<p>The real-valued signed one-step inequality requires \(W_2(\nu,\pi)&lt;\infty\). This makes its signed score-energy formula an inequality of finite real quantities. It is explicit in the displayed theorem and is not explicit in the corresponding paper statement. The displayed constant-step, Laplacian and SGLD global estimates use extended-nonnegative transport and permit every probability initialization, so they do not require Extra A1.</p>''',
                 refs=[("AverageLMC/GaussianLMC.lean", "lmc_one_step")]),
        ],
        results={
            "lmc_one_step": result(
                "AverageLMC/GaussianLMC.lean", "Theorem 1", "Section 2.1, Theorem 1, one-step inequality claim1", AVERAGE_URL, AVERAGE_FILE, 531, 554, "th:1",
                extras=["Extra A1"], title="The one-step average-smoothness inequality",
                note="The exact printed signed score-energy coefficient is proved for every nonnegative step. The displayed endpoint is real-valued and therefore makes finite initial transport explicit."),
            "lmc_constant_step_extended": result(
                "AverageLMC/Theorem.lean", "Theorem 1", "Section 2.1, Theorem 1, constant-step inequality claim3", AVERAGE_URL, AVERAGE_FILE, 531, 554, "th:1",
                title="Constant-step LMC convergence",
                note="The source coefficient and exponential factor are proved for the actual Gaussian marginal laws and every probability initialization. The displayed bound uses extended-nonnegative transport, so no additional moment assumption is imposed. Its finite real-valued form is a corollary."),
            "lmc_variable_step": result(
                "AverageLMC/Theorem.lean", "Proposition 1", "Section 2.3, Proposition 1, prop:VSS; W2VS and kVS", AVERAGE_URL, AVERAGE_FILE, 712, 735, "prop:VSS",
                title="The decreasing-step schedule",
                note="The exact source schedule, burn-in ceiling, error bound and integer accuracy threshold are proved. The source's initial error upper bound supplies the required finiteness; an extended formulation derives it directly."),
            "lmc_laplacian_extended": result(
                "AverageLMC/LaplacianTheorem.lean", "Theorem 2", "Section 4, Theorem 2 (TeX identifier th:3), inequality claim3c", AVERAGE_URL, AVERAGE_FILE, 1017, 1031, "th:3",
                title="LMC under the paper's Laplacian condition",
                note=r"The exact printed coefficient is proved using the paper's \(C^3\) and gradient-of-Laplacian hypotheses for every probability initialization. The displayed bound uses extended-nonnegative transport, so no additional moment assumption is imposed. Its finite real-valued form is a corollary."),
            "sgld_constant_step_paper": result(
                "AverageLMC/SGLDTheorem.lean", "Theorem 3", "Section 5, Theorem 3 (th:sgld), inequality claim-sgld-3a", AVERAGE_URL, AVERAGE_FILE, 1160, 1178, "th:sgld",
                title="Fixed-point control-variate SGLD convergence",
                note="The source's component RMS seminorm, scaled coordinate-average constant, step restriction and coefficients are unchanged. This source-facing endpoint uses extended-nonnegative transport and permits every probability initialization."),
        },
    ),
}
