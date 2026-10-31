r"""Explicit extra assumptions for the corrected source-paper theorems.

These panels belong with the paper results.  They are distinct from the source's
A1--A4 and from the independent new-theory assumptions.  A panel describes
primitive analytic/domain/solution data, never a desired energy inequality.
The builder supplies the added-assumption colour and the exact Lean excerpts.
"""

EXTRA_ASSUMPTION_PANELS = [
    {
        "id": "R1",
        "title": "Positive normalized densities and the finite-KL domain",
        "prose": r"""Let \(M\in\mathbb N\), \(M>0\), let \(\nu\) be the reference measure on the latent space, and let \(a\) range over the parameter domain. For every datum \(m\), assume that \(\rho_a^m:Z\to(0,\infty)\) is measurable, \(\rho_a^m\in L^1(\nu)\), and
        \[0<Z_m(a):=\int\rho_a^m\,d\nu<\infty,\qquad
          \pi_a^m(dz):=Z_m(a)^{-1}\rho_a^m(z)\,\nu(dz).\]
        For a trial family \(q=(q^m)_{m=1}^M\), the domain condition is
        \(\mathrm{KL}(q^m\|\pi_a^m)<\infty\) for every \(m\). If minimization is restricted to a law domain \(\mathcal D\), assume \((\pi_a^m)_m\in\mathcal D\) for every \(a\). For the paper's domain take \(\mathcal D=\mathcal P_2(Z)^M\), so \(\int\|z\|^2\,d\pi_a^m<\infty\) is required. The real Radon–Nikodym density \(f_m=dq^m/d\pi_a^m\), its normalization and \(f_m\log f_m\in L^1(\pi_a^m)\) follow from finite KL. The literal density \(q_m=f_m\rho_a^m/Z_m(a)\) and the energy identity are then derived. This variational domain does not impose smoothness on arbitrary trial laws. The classical-flow statements additionally require the positive differentiable initial density specified in R2–R3; a Dirac initial law does not satisfy it.""",
        "refs": [
            ("LatentDiffusion/RegularVariational.lean", "DensityModel"),
            ("LatentDiffusion/RegularVariational.lean", "DensityModel.literal_integral"),
            ("LatentDiffusion/RegularVariational.lean", "DensityModel.literal_minimizers_on_iff"),
        ],
    },
    {
        "id": "R2",
        "title": "Quantified domination for differentiation under the integral",
        "prose": r"""For each differentiated normalizer at a parameter \(a_0\), assume a single neighbourhood \(V\ni a_0\) and \(g\in L^1(\nu)\) such that, outside one \(\nu\)-null set, for every \(b\in V\), \(U_m(\cdot,z)\) is differentiable at \(b\) and
        \[e^{-U_m(b,z)}\|\nabla_aU_m(b,z)\|\le g(z).\]
        Require \(e^{-U_m(a_0,\cdot)}\in L^1(\nu)\), almost-everywhere strong measurability of \(z\mapsto e^{-U_m(b,z)}\) for all \(b\) in a neighbourhood of \(a_0\), and of \(z\mapsto e^{-U_m(a_0,z)}\nabla_aU_m(a_0,z)\). These are the exact domination inputs for the normalizing integral.</p>
        <p>For an energy derivative at \(t_0\), write \(U_t(z)=U_m(a(t),z)\), \(\dot U_t(z)=D_aU_m(a(t),z)[\dot a(t)]\), and
        \[H_t(z)=q_t(z)(\log q_t(z)+U_t(z)),\qquad
          D_t(z)=\dot q_t(z)(\log q_t(z)+U_t(z)+1)+q_t(z)\dot U_t(z).\]
        Assume one neighbourhood \(J\ni t_0\) and \(g\in L^1(\nu)\) such that, outside one null set and for every \(t\in J\), \(q_t>0\), \(\partial_tq_t=\dot q_t\), and \(|D_t|\le g\). Require \(H_{t_0}\in L^1(\nu)\), almost-everywhere strong measurability of \(D_{t_0}\), and of \(H_t\) for all \(t\) in a neighbourhood of \(t_0\). For a direct potential derivative require, outside one null set, \(\partial_tU_t(z)=\dot U_t(z)\) for every \(t\in J\); the chain-rule constructor instead uses differentiability of \(a\) at every such time and of \(U_m(\cdot,z)\) at the corresponding parameter. In the flow and directional statements also require \(q_t\nabla_aU_m(a(t),\cdot)\in L^1(\nu)\). These quantified conditions, rather than an assumed derivative of an integral, define R2.""",
        "refs": [
            ("LatentDiffusion/RegularFlowCalculus.lean", "LocalEnergyDomination"),
            ("LatentDiffusion/RegularFlowCalculus.lean", "LocalEnergyDomination.along_parameter_path"),
            ("LatentDiffusion/RegularEvidence.lean", "LocalNormalizerRegularity"),
            ("LatentDiffusion/RegularEvidence.lean", "sum_posterior_parameter_gradient_eq_zero"),
        ],
    },
    {
        "id": "R3",
        "title": "Classical equations, differentiability and spatial integrability",
        "prose": r"""On the Euclidean latent space \(Z=\mathbb R^{d_z}\), put \(\psi_t^m=\log q_t^m+U_m(a(t),\cdot)\) and \(J_t^m=q_t^m\nabla_z\psi_t^m\). The density-dynamics contract requires, for every \(t\in\mathbb R\) and \(m\), \(q_t^m(z)>0\) for every \(z\), \(q_t^m,U_m(a(t),\cdot)\in C^1(Z)\), differentiability of \(a\), differentiability of \(U_m(\cdot,z)\) at every parameter, the R2 energy domination, and \(q_t^m\nabla_aU_m(a(t),\cdot)\in L^1(dz)\). For \(t\ge0\), impose
        \[\dot a(t)=-\frac1M\sum_m\int q_t^m(z)\nabla_aU_m(a(t),z)\,dz,
          \qquad \partial_tq_t^m=\nabla_z\!\cdot J_t^m\quad\text{a.e.}\]
        For every spatial coordinate \(j\), require \(J_{t,j}^m\) differentiable and all three functions
        \[J_{t,j}^m(\psi_t^m+1),\qquad
          (\partial_jJ_{t,j}^m)(\psi_t^m+1),\qquad
          J_{t,j}^m\partial_j\psi_t^m\]
        in \(L^1(dz)\). This is the precise no-boundary-term hypothesis. For a first variation along \(a_s=(1-s)a+sb\), \(T_s=(1-s)\mathrm{id}+sT\), impose the same R2 domination at \(s=0\), the equation \(\dot q_0=-\nabla\cdot(q_0(T-\mathrm{id}))\), differentiability of every component of \(q_0(T-\mathrm{id})\), and these three integrability conditions with flux \(q_0(T-\mathrm{id})\) and test \(\log q_0+U_m(a,\cdot)+1\). Require also \(U_m(a_s,\cdot)\in L^1(q_s^m)\) for every \(s\in[0,1]\). The gradient-pairing statement imposes the corresponding continuity equation and three integrable products for each velocity under consideration. Fisher integrability and de Bruijn are conclusions of these equations and hypotheses.""",
        "refs": [
            ("LatentDiffusion/RegularFlowCalculus.lean", "NoBoundaryFlux"),
            ("LatentDiffusion/RegularFlowCalculus.lean", "integral_divergence_mul"),
            ("LatentDiffusion/RegularFlowCalculus.lean", "normalized_product_gradient_representation"),
            ("LatentDiffusion/RegularFlowCalculus.lean", "normalized_product_deBruijn"),
            ("LatentDiffusion/RegularFlowTalagrand.lean", "RegularDensityDynamics"),
            ("LatentDiffusion/RegularDirectional.lean", "DirectionalRegularity"),
        ],
    },
    {
        "id": "R4",
        "title": "Density change of variables and certified optimal maps",
        "prose": r"""For each displacement argument supply a measurable map \(T:Z\to Z\), differentiable at every point, and \(T_s=(1-s)\mathrm{id}+sT\). For every \(z\), require an orthonormal eigenbasis of \(DT(z)\) with eigenvalues \(\lambda_j(z)>0\). For every \(s\in[0,1]\), supply a measurable everywhere positive density \(q_s\) satisfying
        \[(T_s)_\#\mu=q_s\,dz,\qquad
          q_s(T_s z)=\frac{q_0(z)}{\prod_{j=1}^{d_z}(1-s+s\lambda_j(z))},\qquad
          \log(q_s\circ T_s)\in L^1(\mu).\]
        For each datum the tangent dataset contract further requires \(q_0\in C^1(Z)\), \(\nabla\log q_0\in L^2(\mu)\), \(\mathrm{id}-T\in L^2(\mu)\), and \(z\mapsto\nabla_{(a,z)}U_m(a,z)\in L^2(\mu)\). With \(a_s=(1-s)a+sb\), require \(U_m(a_s,T_s\cdot)\in L^1(\mu)\) for every \(s\in[0,1]\). For \(w=T-\mathrm{id}\), every \(w_j\) is differentiable and \(w_jq_0\), \((\partial_jw_j)q_0\), \(w_j\partial_jq_0\) belong to \(L^1(dz)\). These are the transport-score integration-by-parts inputs, distinct from the flux/test pair in R3.</p>
        <p>Whenever a map from \(\mu\) to \(\eta\) is used to identify an exact Wasserstein distance, require \(T_\#\mu=\eta\), \(z\mapsto z-Tz\in L^2(\mu)\), and, for every probability coupling \(\gamma\in\Gamma(\mu,\eta)\),
        \[\left(\int\|z-Tz\|^2\,d\mu\right)^{1/2}
          \le\left(\int\|x-y\|^2\,d\gamma(x,y)\right)^{1/2}.\]
        Here coupling costs use the extended nonnegative integral, allowing \(+\infty\). The constant-speed geodesic statements additionally require such an optimal map between \(q_s\) and \(q_t\) for every \(s,t\in[0,1]\). Their converse assumes endpoint uniqueness: every optimal \(S:q_0\to q_1\) satisfies \(S=T\), \(q_0\)-a.e. The gradient-map version also supplies a convex function \(\Phi:Z\to\mathbb R\) with \(\nabla\Phi(z)=T(z)\) at every \(z\). These are assumptions on the chosen transport data. Entropy displacement convexity and the score tangent inequality are derived from them and R3.""",
        "refs": [
            ("LatentDiffusion/RegularTransport.lean", "RegularDisplacement"),
            ("LatentDiffusion/RegularTransportFirstOrder.lean", "DatasetRegularity"),
            ("LatentDiffusion/RegularTransport.lean", "OptimalMap"),
            ("LatentDiffusion/RegularTransportGeodesic.lean", "RegularBrenierMap"),
            ("LatentDiffusion/RegularTransport.lean", "entropy_displacement_convex"),
            ("LatentDiffusion/RegularTransportFirstOrder.lean", "entropy_tangent"),
        ],
    },
    {
        "id": "R5",
        "title": "Differentiable characteristics and optimal coupling anchors",
        "prose": r"""For each datum choose a probability space \((\Omega_m,P_m)\), maps \(Y_m,v_m:\mathbb R\to L^2(P_m;Z)\), and a curve \(x:\mathbb R\to X\), continuous on \([0,\infty)\), in the R6 chart. For every \(t\in\mathbb R\), require
        \[\operatorname{Law}(Y_m(t))=q_{x(t)}^m\,dz,\qquad
          \frac{d}{dt}Y_m(t)=v_m(t)\text{ in }L^2(P_m;Z),\qquad
          v_m(t)=-\nabla_z(\log q_t^m+U_m(a(t),\cdot))(Y_m(t))\quad P_m\text{-a.s.}\]
        Match the chart parameter and density exactly to those of the R3 dynamics: \(a(x(t))=a(t)\), \(q_{x(t)}^m=q_t^m\). For every \(s,t\in\mathbb R\) and \(m\), supply \(A_{s,t}^m\in L^2(P_m;Z)\) with law \(q_{x(s)}^m\,dz\), such that for every \(\gamma\in\Gamma(\operatorname{Law}(Y_m(t)),q_{x(s)}^m dz)\),
        \[\|Y_m(t)-A_{s,t}^m\|_{L^2(P_m)}
          \le\left(\int\|z-w\|^2\,d\gamma(z,w)\right)^{1/2}.\]
        The coupling cost on the right is an extended nonnegative integral. The scalar integrated-speed lemma additionally assumes Bochner interval integrability \(v_m\in L^1([s,t];L^2(P_m;Z))\). The product statement requires the entire lifted velocity \(u\mapsto(\dot a(u),(v_m(u)/\sqrt M)_m)\) Bochner interval integrable on \([s,t]\). The product-space realization uses \(Y_m/\sqrt M\). Distance increments, upper-right slopes and integrated speed bounds follow from these hypotheses; an ordinary distance derivative at a target crossing is not required.""",
        "refs": [
            ("LatentDiffusion/RegularMetricFlow.lean", "OptimalAnchor"),
            ("LatentDiffusion/RegularProductMetricFlow.lean", "distance_integral_bound"),
            ("LatentDiffusion/RegularProductMetricFlow.lean", "distance_right_slope"),
            ("LatentDiffusion/RegularProductMetricFlow.lean", "kinetic_energy_eq_fisher"),
            ("LatentDiffusion/RegularFlowTalagrand.lean", "CharacteristicRealization"),
        ],
    },
    {
        "id": "R6",
        "title": "A complete density chart with the exact transport metric",
        "prose": r"""Let \((X,d_X)\) be a complete metric space with a parameter map \(a:X\to A\), positive measurable densities \(q_x^m\), and laws \(\mu_x^m=q_x^m dz\in\mathcal P_2(Z)\). For every \(x,y\in X\), require the exact identity
        \[d_X(x,y)^2=\|a(x)-a(y)\|^2+
          \frac1M\sum_m W_2(\mu_x^m,\mu_y^m)^2.\]
        For every \(m,z\), assume both \(x\mapsto q_x^m(z)\) and \(x\mapsto U_m(a(x),z)\) continuous. Require spatial measurability of each density and potential. For every \(x\in X\) and \(m\), assume a neighbourhood \(V_{x,m}\) and \(g_{x,m}\in L^1(dz)\) such that for every \(y\in V_{x,m}\), almost every \(z\),
        \[\left|q_y^m(z)\log q_y^m(z)+q_y^m(z)U_m(a(y),z)\right|\le g_{x,m}(z).\]
        These assumptions imply continuity of \(F(x)=M^{-1}\sum_m\int(q_x^m\log q_x^m+q_x^mU_m(a(x),\cdot))\,dz\). For the minimizing-limit statement, assume a finite lower bound \(F_\star\le F(x)\) for every \(x\), a Cauchy sequence \(x_n\) in this same chart, and \(F(x_n)\to F_\star\). A minimizing limit in \(X\) is then proved. The flow application constructs the Cauchy sequence from \(x(t_n)\), \(t_n\to\infty\). Pointwise density continuity and completeness of this chosen chart are extra assumptions; neither is inferred from membership in \(\mathcal P_2\).""",
        "refs": [
            ("LatentDiffusion/RegularDensityDomain.lean", "ProductDensityChart"),
            ("LatentDiffusion/RegularDensityDomain.lean", "ProductDensityChart.continuous_energy"),
            ("LatentDiffusion/RegularDensityDomain.lean", "ProductDensityChart.lowerSemicontinuous_energy"),
            ("LatentDiffusion/RegularDensityDomain.lean", "ProductDensityChart.cauchy_minimizer"),
        ],
    },
    {
        "id": "R7",
        "title": "Brownian inputs, posterior initialization and score moments",
        "prose": r"""Write \(K=MN>0\) and use the normalized cloud norm \(\|(a,z)\|_K^2=\|a\|^2+K^{-1}\sum_{i=1}^K\|z_i\|^2\). On a probability space \((\Omega,P)\), supply \(Z_0\in L^2(P;Z^K)\) whose law is the actual Gibbs law
        \[\operatorname{Law}(Z_0)(dz)=
          \frac{\exp(-\sum_{i=1}^K U_i(a_\star,z_i))}{\int_{Z^K}\exp(-\sum_{i=1}^K U_i(a_\star,w_i))\,dw}\,dz,\qquad
          \operatorname{Law}(Z_{0,i})=\pi_{a_\star}^i.\]
        Here \(a_\star\) is the proved evidence optimizer, the datum potentials are repeated across their \(N\) copies, and R2 normalizer domination holds at \(a_\star\). Require the parameter scores \(S_i=\nabla_aU_i(a_\star,Z_{0,i})\) to be independent across all \(i\). For the explicit particle-count rate assume
        \[\mathbb E\|S_i-\mathbb ES_i\|^2\le V_0\quad(1\le i\le K).\]
        The hypotheses of the rate theorem supply one \(V_0\); a claim uniform in \(N\) requires that same bound for every \(N\).</p>
        <p>Supply real coordinate processes \(B_{i,j}(t)\), \(t\ge0\), whose every finite-dimensional law is centered Gaussian with covariance \(\mathbb E[B_{i,j}(s)B_{i,j}(t)]=\min(s,t)\). In particular, \(B_{i,j}(0)=0\) almost surely and \(B_{i,j}(t)-B_{i,j}(s)\sim N(0,t-s)\) for \(0\le s\le t\). For every \(s>0\), the entire family \(\Delta B_{n,i,j}^{(s)}=B_{i,j}((n+1)s)-B_{i,j}(ns)\), indexed by \((n,i,j)\), must be independent, and \(Z_0\) must be independent of the complete sequence \((\Delta B_{n,i,j}^{(s)})_{n,i,j}\). The continuous comparisons use \(L^2(P)\)-continuous curves solving the actual Bochner integral equations for their displayed forces and these same Brownian inputs. For example, the full particle curve satisfies
        \[X_t-X_0=-\int_0^t F(X_r)\,dr+
          (0,\sqrt2(B_t-B_0)),\qquad t\ge0,\]
        The force components are \[F_a(a,z)=K^{-1}\sum_i\nabla_aU_i(a,z_i),\qquad F_{z_i}(a,z)=\nabla_zU_i(a,z_i),\] and norms are measured by \(\|\cdot\|_K\). The frozen curve starts at \((a_\star,Z_0)\); its existence and stationarity are derived from the Gibbs initialization and independent increments. A spatial comparison that omits an initial-error term assumes identical coupled initial states; otherwise it retains that term. The nonstationary mean-field comparison separately requires independent parameter-score copies at every \(t\ge0\) and \(\mathbb E\|S_i(t)-\mathbb ES_i(t)\|^2\le V_0\) for every such \(t\) and \(i\). The direct temporal comparison assumes \(\|X_t\|_{L^2(P;\|\cdot\|_K)}\le R_K\) for every \(t\ge0\). Constants uniform in the particle count require \(\sup_KR_K<\infty\) and \(\sup_K\|F_K(0)\|_K<\infty\) in that branch.</p>
        <p>For the full-batch Euler bound require an arbitrary \(X_0\in L^2(P)\) and the exact stable-step restrictions
        \[h>0,\qquad \lambda>0,\qquad L\ge0,\qquad \lambda h\le1,\qquad hL^2\le\lambda.\]
        A count-independent transient requires \(\sup_N\|X_0-(a_\star,Z_0)\|_{L^2(P;\|\cdot\|_K)}<\infty\). The endpoint derives its frozen-force moment bound from A3–A4 and the Gibbs law; it does not assume a temporal error recurrence. The asserted continuous solution class is continuity in \(L^2(P)\) with the displayed integral identity.""",
        "refs": [
            ("LatentDiffusion/RegularStochastic.lean", "sourceReference"),
            ("LatentDiffusion/RegularMeanField.lean", "exists_spatial_comparison"),
            ("LatentDiffusion/RegularMeanField.lean", "temporal_comparison"),
            ("LatentDiffusion/RegularStochastic.lean", "independent_average_norm_sq"),
            ("LatentDiffusion/RegularStochastic.lean", "full_batch_parameter_bound"),
            ("LatentDiffusion/RegularSourceTheorem.lean", "full_batch_optimizer_rms_rate"),
            ("LatentDiffusion/RegularSourceTheorem.lean", "optimizer_replication"),
            ("LatentDiffusion/RegularEvidence.lean", "sum_posterior_parameter_gradient_eq_zero"),
        ],
    },
]
