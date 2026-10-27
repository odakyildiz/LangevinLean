r"""Explicit added regularity for the corrected source-paper theorems.

These panels belong with the paper results.  They are distinct from the source's
A1--A4 and from the independent new-theory assumptions.  A panel describes
primitive analytic/domain/solution data, never a desired energy inequality.
The builder supplies the added-assumption colour and the exact Lean excerpts.
"""

REGULARITY_PANELS = [
    {
        "id": "R1",
        "title": "Admissible density laws and finite energies",
        "prose": r"""Use \(M\ge1\), actual positive finite normalizers, and the
        probability posteriors obtained by dividing the supplied tilted density
        by its integral. Work on the finite-KL energy domain, and require the
        posterior comparison laws to belong to the chosen finite-second-moment
        domain. The initial laws must have the regularity used by the proof;
        arbitrary Dirac initial laws cannot simultaneously have positive smooth
        densities at time zero. Positive-time smoothing is an alternative when
        the initial energy is defined by its right limit. Normalization and the
        variational identity are proved from the densities, rather than added
        as assumptions.""",
        "refs": [
            ("LatentDiffusion/RegularVariational.lean", "DensityModel"),
            ("LatentDiffusion/RegularVariational.lean", "DensityModel.literal_integral"),
            ("LatentDiffusion/RegularVariational.lean", "DensityModel.literal_minimizers_on_iff"),
        ],
    },
    {
        "id": "R2",
        "title": "Local domination for differentiation of actual integrals",
        "prose": r"""On one common neighbourhood of the time or parameter in
        question, require measurable positive densities, pointwise density and
        potential derivatives, finite base energy, and an integrable bound for
        the differentiated integrand. For normalizers the bound is on
        \(e^{-U_u(z)}\|\nabla_uU_u(z)\|\); for the evolving energy it is on
        \(\dot q(\log q+U+1)+q\dot U\). Require the weighted parameter
        gradient to be integrable. These are ordinary sufficient conditions for
        differentiating under the integral sign. The potential time derivative
        is derived by the chain rule, and evidence optimality then proves that
        the average posterior parameter score is zero.""",
        "refs": [
            ("LatentDiffusion/RegularFlowCalculus.lean", "LocalEnergyDomination"),
            ("LatentDiffusion/RegularFlowCalculus.lean", "LocalEnergyDomination.along_parameter_path"),
            ("LatentDiffusion/RegularEvidence.lean", "LocalNormalizerRegularity"),
            ("LatentDiffusion/RegularEvidence.lean", "sum_posterior_parameter_gradient_eq_zero"),
        ],
    },
    {
        "id": "R3",
        "title": "Classical flow equations and integrable spatial tails",
        "prose": r"""Use the parameter gradient ODE and the actual classical
        Fokker–Planck equation
        \(\partial_tq^m=\nabla\!\cdot(q^m\nabla(\log q^m+U_m))\).
        To integrate by parts, require differentiable flux components and
        absolute integrability of each component times the test, its derivative
        times the test, and the component times the test derivative. These are
        the explicit hypotheses of ordinary Lebesgue integration by parts on
        the unbounded latent domain. Applying them to the chemical potential
        proves Fisher integrability and the full de Bruijn identity. Applying
        them to arbitrary admissible continuity-equation velocities proves the
        normalized product-gradient pairing. Neither conclusion is assumed.""",
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
        "title": "Regular displacement charts and actual optimal transports",
        "prose": r"""For the transport arguments, use smooth displacement
        maps with positive Jacobian eigenvalues, actual pushforward density
        laws, the density/Jacobian change-of-variables equation, and integrable
        logarithms and quadratic transport costs. When an exact Wasserstein
        distance is needed, supply an optimal map by its pushforward and
        minimality against every genuine coupling. For the geodesic
        equivalence, require optimal maps between all intermediate laws and
        endpoint-map uniqueness up to source-law null sets. Its gradient-map
        version uses an actual convex potential and its gradient certificate.
        This is explicit regular
        transport data; arbitrary probability laws are not asserted to possess
        a smooth positive-Jacobian map. Entropy displacement convexity and its
        score tangent inequality are proved from the Jacobian formula and
        spatial integration by parts. No entropy-convexity, first-order
        transport or log-Sobolev inequality is an assumption in these data.""",
        "refs": [
            ("LatentDiffusion/RegularTransport.lean", "RegularDisplacement"),
            ("LatentDiffusion/RegularTransport.lean", "OptimalMap"),
            ("LatentDiffusion/RegularTransportGeodesic.lean", "RegularBrenierMap"),
            ("LatentDiffusion/RegularTransport.lean", "entropy_displacement_convex"),
            ("LatentDiffusion/RegularTransportFirstOrder.lean", "entropy_tangent"),
        ],
    },
    {
        "id": "R5",
        "title": "Square-integrable characteristic curves for metric bounds",
        "prose": r"""Realize the evolving law by an actual
        square-integrable characteristic curve with its stated time derivative.
        Require the characteristic velocity to be integrable on finite time
        intervals. Represent transport to a fixed target by an optimal anchor
        whose law is that target and whose cost is minimal among all couplings.
        The law-distance increment and integrated speed bounds are then proved
        from the characteristic curve and coupling costs. At a crossing of the
        target, use the upper-right-slope statement; an ordinary distance
        derivative need not exist there.""",
        "refs": [
            ("LatentDiffusion/RegularMetricFlow.lean", "OptimalAnchor"),
            ("LatentDiffusion/RegularProductMetricFlow.lean", "distance_right_slope"),
            ("LatentDiffusion/RegularProductMetricFlow.lean", "kinetic_energy_eq_fisher"),
            ("LatentDiffusion/RegularFlowTalagrand.lean", "CharacteristicRealization"),
        ],
    },
    {
        "id": "R6",
        "title": "A complete dominated density domain for the limit argument",
        "prose": r"""For compactness in the regular density domain, require a
        complete metric chart with pointwise continuous densities and potentials
        and a common local integrable envelope for \(q\log q+qU\). When this
        chart carries the source product transport metric, pointwise density
        continuity is an additional regular-domain requirement; it does not
        follow from Wasserstein convergence alone. Dominated convergence proves
        continuity, hence lower semicontinuity, of the actual energy. A Cauchy
        sequence of flow states whose energies approach the infimum then has an
        admissible minimizing limit. Completeness is not attributed to the
        unrestricted subspace of smooth densities.""",
        "refs": [
            ("LatentDiffusion/RegularDensityDomain.lean", "ProductDensityChart"),
            ("LatentDiffusion/RegularDensityDomain.lean", "ProductDensityChart.continuous_energy"),
            ("LatentDiffusion/RegularDensityDomain.lean", "ProductDensityChart.lowerSemicontinuous_energy"),
            ("LatentDiffusion/RegularDensityDomain.lean", "ProductDensityChart.cauchy_minimizer"),
        ],
    },
    {
        "id": "R7",
        "title": "Stochastic initialization and uniform moment control",
        "prose": r"""Use square-integrable initial clouds, the actual
        continuous \(L^2\) Brownian integral equation, Brownian increments independent
        across their declared particle coordinates and independent of the
        initial state, and compatible coupled initializations. Initialize the
        frozen posterior comparison with its actual Gibbs law. The Gibbs
        stationarity theorem then constructs the stationary frozen reference;
        independence and the evidence-optimum score identity control its
        empirical parameter-force fluctuation. Explicitly require one fixed
        per-copy bound \(\mathbb E\|S_i-\mathbb ES_i\|^2\le V_0\),
        with \(V_0\) independent of the particle count, and a uniform normalized
        initialization radius when quoting a count-independent transient.
        These are sampling/initialization and moment assumptions in addition
        to analytic regularity. The solution class is continuous in \(L^2\) and
        solves the actual Brownian integral equation; a separate progressively
        measurable, almost-sure continuous-path realization is not asserted.
        Numerical errors and their
        recurrences are proved from these inputs, rather than assumed. For
        Count-independent temporal constants also require a uniform bound on
        the normalized force at the origin, as well as the state moment bound.
        For Euler discretization use the explicit additional restriction
        \(0<h,\;\lambda h\le1,\;hL^2\le\lambda\).""",
        "refs": [
            ("LatentDiffusion/RegularStochastic.lean", "sourceReference"),
            ("LatentDiffusion/RegularStochastic.lean", "independent_average_norm_sq"),
            ("LatentDiffusion/RegularStochastic.lean", "full_batch_parameter_bound"),
            ("LatentDiffusion/RegularSourceTheorem.lean", "full_batch_optimizer_rms_rate"),
            ("LatentDiffusion/RegularSourceTheorem.lean", "optimizer_replication"),
            ("LatentDiffusion/RegularEvidence.lean", "sum_posterior_parameter_gradient_eq_zero"),
        ],
    },
]
