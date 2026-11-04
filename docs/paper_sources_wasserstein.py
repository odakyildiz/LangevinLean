"""Exact source labels for the direct proof under the original assumptions."""

SOURCE = "https://arxiv.org/html/2608.02430v1"
ENDPOINT_STATUS = "proved"

PAPER_SOURCES = {
    "WassersteinMixing": {
        "paper": "wasserstein-mixing",
        "scope": r"Theorem 1 and Corollary 1.1 are proved under the original \(C^2\) Hessian assumptions for the actual Gibbs target, independent-Gaussian ULA laws and constructed invariant measure. The proof constructs the stationary Brownian dynamics, reversible Markov semigroup and bounded Poisson corrector directly at \(C^2\) regularity. No eigenbasis, Markov realization, invariant law, comparison estimate or smoothing hypothesis is added to the final statements.",
        "assumptions": [
            dict(label="Assumption 1.1", title="Strong log-concavity and log-smoothness",
                 location="Section 1, Assumption 1.1", url=SOURCE + "#Thm1.1",
                 body=r'''<p>Let \(V\in C^2(\mathbb R^d)\) and let \(0&lt;\alpha\le\beta\).
                 For every \(x\in\mathbb R^d\),</p>
                 \[\alpha I_d\preccurlyeq\nabla^2V(x)\preccurlyeq\beta I_d,
                 \qquad\kappa=\frac\beta\alpha.\]
                 <p>The target is \(\pi(dx)=Z^{-1}e^{-V(x)}dx\).
                 The source step restriction is \(0&lt;h\le1/\beta\).
                 The quadratic-form bounds on the actual Hessian derive the
                 strong-convexity and gradient-Lipschitz contract used internally.</p>'''),
            dict(label="Equations (1)–(2)", title="Diffusion and Gaussian ULA recursion",
                 location="Section 1, equations (1)–(2), and the definition of quadratic transport", url=SOURCE,
                 body=r'''\[dX_t=-\nabla V(X_t)\,dt+\sqrt2\,dB_t,
                 \qquad\widehat X_{k+1}=\widehat X_k-h\nabla V(\widehat X_k)
                 +\sqrt2(B_{(k+1)h}-B_{kh}).\]
                 <p>The source defines \(W_2\) on
                 \(\mathcal P_2(\mathbb R^d)\), so the finite-time and accuracy
                 statements take a probability initialization with finite second moment.
                 The biased law \(\widehat\pi\) is constructed from an iid Gaussian past,
                 with finite second moment, actual ULA invariance and transport attraction.</p>'''),
            dict(label="Assumption 2.1", title="Temporary regularity in the source proof",
                 location="Section 2, Assumption 2.1; removed in Section 2.2", url=SOURCE + "#Thm2.1",
                 body=r'''<p>The source first assumes that \(V\) is smooth and
                 every partial derivative has at most polynomial growth, then
                 removes this temporary assumption by Gaussian convolution.
                 The formal proof instead constructs the actual reversible
                 semigroup and its corrector directly under \(C^2\).
                 This temporary source-proof hypothesis is therefore not used
                 by the final statements, and no smoothing comparison is required.</p>'''),
        ],
        "extras": [],
        "results": {
            "bias_bound": dict(
                label="Theorem 1", location="Section 1, Theorem 1, equation (3)", url=SOURCE,
                status=ENDPOINT_STATUS, extras=[],
                note=r"The literal bound \(W_2(\pi,\widehat\pi)\le6h\sqrt{\kappa\beta d}\), under the original \(C^2\) Hessian bounds and \(0<h\le1/\beta\). The Gibbs target and Gaussian ULA invariant law are actual constructed measures. The direct \(C^2\) semigroup argument proves the required corrector and stochastic comparison without additional realization assumptions."),
            "convergence_bound": dict(
                label="Corollary 1.1", location="Section 1, Corollary 1.1, equation (4)", url=SOURCE,
                status=ENDPOINT_STATUS, extras=[],
                note=r"The literal finite-time bound for the actual independent-Gaussian ULA iterates and a \(\mathcal P_2\) initialization. The exact contraction factor, invariant law, transport triangle inequality and stationary bias estimate are all derived."),
            "accuracy_bound": dict(
                label="Corollary 1.1", location="Section 1, Corollary 1.1, equation (5)", url=SOURCE,
                status=ENDPOINT_STATUS, extras=[],
                note=r"The source minimum step formula and logarithmic iteration count imply \(\sqrt\alpha\,W_2(\mu_k,\pi)\le\varepsilon\) for the actual Gaussian ULA laws. Only the original Hessian assumptions, \(\mathcal P_2\) initialization, positive accuracy and the displayed step/count restrictions occur in the endpoint."),
        },
    },
}
