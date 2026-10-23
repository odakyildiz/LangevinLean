"""Shared paper citations and publication status for the proof pages.

Publication metadata comes from the publisher/proceedings records linked below.
Version links identify the editions used by the existing correspondence audits.
An unpublished proof notice describes this project's proof, not a novelty claim.
"""
from html import escape


PAPERS = {
    "average-lmc": dict(
        authors="Arnak S. Dalalyan and Avetik Karagulyan", year="undated manuscript",
        title="Improved Guarantees for Langevin Monte Carlo with Average Smoothness",
        venue="Supplied Arxiv_version_May_26.tex; publication status not established",
        url="https://github.com/odakyildiz/LangevinLean/blob/b42a1459e2e8f19f3135893291699bcb9d6b6235/papers/Average_LMC/Arxiv_version_May_26.tex",
        links=[]),
    "monmarche-obabo": dict(
        authors="Pierre Monmarché", year="2021",
        title="High-dimensional MCMC with a standard splitting scheme for the underdamped Langevin diffusion",
        venue="Electronic Journal of Statistics 15(2), 4117–4166",
        url="https://arxiv.org/abs/2007.05455v4",
        links=[("Full paper", "https://arxiv.org/pdf/2007.05455v4")]),
    "dalalyan-riou-durand": dict(
        authors="Arnak S. Dalalyan and Lionel Riou-Durand", year="2020",
        title="On sampling from a log-concave density using kinetic Langevin diffusions",
        venue="Bernoulli 26(3), 1956–1988",
        url="https://doi.org/10.3150/19-BEJ1178",
        links=[("arXiv", "https://arxiv.org/abs/1807.09382")]),
    "kinetic-ipla": dict(
        authors="Paul Valsecchi Oliva and Ö. Deniz Akyildiz", year="2026",
        title="Kinetic interacting particle Langevin Monte Carlo",
        venue="Statistics and Computing 36, article 221",
        url="https://doi.org/10.1007/s11222-026-10980-z",
        links=[("arXiv", "https://arxiv.org/abs/2407.05790")]),
    "dalalyan-karagulyan": dict(
        authors="Arnak S. Dalalyan and Avetik G. Karagulyan",
        year="2019",
        title="User-friendly guarantees for the Langevin Monte Carlo with inaccurate gradient",
        venue="Stochastic Processes and their Applications 129(12), 5278–5311",
        url="https://doi.org/10.1016/j.spa.2019.02.016",
        links=[("arXiv", "https://arxiv.org/abs/1710.00095v4")]),
    "dalalyan": dict(
        authors="Arnak Dalalyan", year="2017",
        title="Further and stronger analogy between sampling and optimization: Langevin Monte Carlo and gradient descent",
        venue="Proceedings of the 2017 Conference on Learning Theory, Proceedings of Machine Learning Research 65, 678–689",
        url="https://proceedings.mlr.press/v65/dalalyan17a.html", links=[]),
    "vempala-wibisono": dict(
        authors="Santosh S. Vempala and Andre Wibisono", year="2019",
        title="Rapid Convergence of the Unadjusted Langevin Algorithm: Isoperimetry Suffices",
        venue="Advances in Neural Information Processing Systems 32, 8094–8106",
        url="https://proceedings.neurips.cc/paper/2019/hash/65a99bb7a3115fdede20da98b08a370f-Abstract.html",
        links=[("Full paper with appendices", "https://www.cs.yale.edu/homes/wibisono/VW19.pdf")]),
    "statfem-ipla": dict(
        authors="Alex Glyn-Davies, Connor Duffin, Ieva Kazlauskaite, Mark Girolami, and Ö. Deniz Akyildiz",
        year="2025", title="Statistical Finite Elements via Interacting Particle Langevin Dynamics",
        venue="SIAM/ASA Journal on Uncertainty Quantification 13(3), 1200–1227",
        url="https://doi.org/10.1137/24M1693593",
        links=[("Audited version: arXiv:2409.07101v2", "https://arxiv.org/abs/2409.07101v2")]),
    "proximal-ipla": dict(
        authors="Paula Cordero Encinar, Francesca Romana Crucinio, and Omer Deniz Akyildiz",
        year="2025", title="Proximal Interacting Particle Langevin Algorithms",
        venue="Proceedings of the Forty-first Conference on Uncertainty in Artificial Intelligence, Proceedings of Machine Learning Research 286, 1220–1265",
        url="https://proceedings.mlr.press/v286/encinar25a.html",
        links=[("Audited version: arXiv:2406.14292v3", "https://arxiv.org/abs/2406.14292v3")]),
}


DEVELOPMENTS = {
    "AverageLMC": dict(
        label="Supplied manuscript; checked sampling proofs and separate source mistakes",
        status="corrected", papers=["average-lmc"],
        scope="The exact supplied manuscript is the correspondence authority. Its main average-smoothness LMC, decreasing-step, Laplacian-smooth LMC and fixed-point control-variate SGLD statements are proved for actual Gaussian sampling laws with the source constants. Extended transport endpoints cover arbitrary probability initializations. The Laplacian proof uses exactly C3 regularity and the gradient-of-Laplacian condition. Verified counterexamples to the false Gaussian-design proposition, its empirical fourth-moment event and an intermediate SGLD transient comparison have separate pages linked from the top of the overview. The complete source inventory distinguishes this main-theorem review scope from broader auxiliary statements not reproduced in full standalone generality; literal full-paper proof coverage is not claimed.",
        card="Actual average-smoothness LMC, decreasing-step, Laplacian LMC and control-variate SGLD bounds, with separate checked counterexamples to manuscript mistakes."),
    "KineticLangevin": dict(
        label="Published source; corrected checked proofs", status="corrected",
        papers=["dalalyan-riou-durand"],
        scope="The audit follows the supplied mainDR_dec_18.tex manuscript. Actual canonical Brownian integral-solution mixing, full Gibbs stationarity, both correlated-Gaussian KLMC/KLMC2 Wasserstein bounds, literal Cholesky sampling, and explicit accuracy guarantees are proved. The corrected proofs checked here are unpublished: the audit records the continuous prefactor correction, the stationary local reference, and the retained stochastic Hessian-difference terms. KLMC2 keeps the exact fourth-moment factor in every dimension and states p≥2 for the printed coarser simplification; its sharper inverse-step-square tail is proved. Continuous solutions are continuous in L² on finite horizons; no separate almost-surely continuous sample-path modification theorem is claimed.",
        card="Actual kinetic mixing, Gibbs stationarity, KLMC and KLMC2 sampling bounds, and accuracy guarantees are checked, with the supplied source corrections stated explicitly."),
    "KIPLMC": dict(
        label="Published source; checked diffusion and sampler proofs", status="extended",
        papers=["kinetic-ipla", "dalalyan-riou-durand", "monmarche-obabo"],
        scope="The audit uses the supplied KIPLMC main.tex and sections, including the stated particle-dependent OBABO rate. KIPLMC1 reuses the shared kinetic exponential integrator with its exact Cholesky-generated correlated Gaussian law; KIPLMC2 uses the checked O-B-A-B-O scheme. Physical-time Brownian integral-solution mixing, full Gibbs stationarity, both actual Gaussian parameter RMS theorems, exact clock and algorithm conjugacies, sharp MMLE concentration, explicit accuracy budgets, and the logistic analytic example are proved. The internal OBABO proof gives a stronger direct estimate and recovers the supplied coarse rate with an explicit uniform constant. Continuous solutions use the canonical continuous-L² model; empirical experiments are recorded separately.",
        card="Actual KIPLD mixing, both Gaussian particle sampler RMS bounds, sharp MMLE concentration, exact integrator reuse, and explicit accuracy guarantees are checked."),
    "UnadjustedLangevin": dict(
        label="Paper references", status="published",
        papers=["dalalyan-karagulyan", "dalalyan"],
        scope="The two step-size regimes and the coefficient 1.65 follow Theorem 1(a)–(b) of Dalalyan and Karagulyan (2019). Dalalyan (2017), Theorem 1 and Section 6, gives the earlier synchronous-coupling argument.",
        card="The displayed coefficient 1.65 and both step-size regimes follow Theorem 1 of Dalalyan and Karagulyan (2019)."),
    "UnadjustedLangevin/LSI": dict(
        label="Paper reference", status="published", papers=["vempala-wibisono"],
        scope="The entropy bound follows Theorem 2, Section 3.1, and Appendices B.2.1–B.2.2 of Vempala and Wibisono (2019). The Lean development supplies the regularity and endpoint arguments for the actual Gaussian ULA laws.",
        card="Source: Theorem 2 and Appendices B.2.1–B.2.2."),
    "IPLA": dict(
        label="Published source and unpublished extension", status="extended",
        papers=["statfem-ipla", "dalalyan-karagulyan"],
        scope="Source: Theorem 1, equation (34), and Appendix B of arXiv:2409.07101v2 (27 May 2025), using the ULA estimate of Dalalyan and Karagulyan. The independent parameter- and latent-dimension extension and its proof presented here are unpublished; equal dimensions recover the paper’s displayed bound. The assumption audit explains the joint-potential smoothness condition.",
        card="Source: Theorem 1, equation (34), and Appendix B of arXiv:2409.07101v2. The independent-dimension extension and its proof presented here are unpublished."),
    "IPLA/LSI": dict(
        label="Unpublished proof", status="unpublished",
        papers=["vempala-wibisono", "statfem-ipla"],
        scope="The IPLA LSI proof presented here is unpublished. It derives the joint entropy bound, per-particle normalization, and parameter-marginal consequence by applying the shared ULA entropy theorem to the actual lifted IPLA target. The papers below are background references for that construction.",
        card="The IPLA LSI proof presented here is unpublished. The cited papers provide the ULA entropy theorem and IPLA background."),
    "ProximalLangevin": dict(
        label="Published source; unpublished corrected proofs", status="corrected",
        papers=["proximal-ipla"],
        scope="The algorithms are from the published paper below; the correspondence audit uses arXiv:2406.14292v3 (29 May 2025). The corrected MYIPLA, PIPGLA, and MYPGD bounds and proofs presented here are unpublished. The audit records their differences from the paper’s printed rates and constants, and the claims that remain outside the formalization.",
        card="The corrected bounds and proofs presented here are unpublished. The paper supplies the algorithms; the audit uses arXiv:2406.14292v3."),
}


def citation(identifier):
    paper = PAPERS[identifier]
    links = " · ".join(f'<a href="{escape(url)}">{escape(label)}</a>' for label, url in paper["links"])
    return (f'{escape(paper["authors"])} ({paper["year"]}). '
            f'<a href="{escape(paper["url"])}"><cite>{escape(paper["title"])}</cite></a>. '
            f'{escape(paper["venue"])}.' + (f' <span class="reference-links">{links}</span>' if links else ""))


def reference_notice(key, supporting=False):
    development = DEVELOPMENTS[key]
    heading = "References and publication status for this development" if supporting else development["label"]
    return (f'<aside class="paper-reference" data-reference="{escape(key)}" '
            f'data-publication-status="{development["status"]}" aria-label="Paper references and publication status">'
            f'<p class="reference-heading"><strong>{escape(heading)}</strong></p>'
            + (f'<p class="publication-label"><strong>{escape(development["label"])}</strong></p>' if supporting else "")
            + f'<p class="reference-scope">{escape(development["scope"])}</p><ul class="reference-list">'
            + "".join(f'<li>{citation(identifier)}</li>' for identifier in development["papers"])
            + '</ul></aside>')


def reference_card(key):
    development = DEVELOPMENTS[key]
    return (f'<div class="card-reference" data-reference="{escape(key)}" '
            f'data-publication-status="{development["status"]}">'
            f'<p><strong>{escape(development["label"])}</strong></p>'
            f'<p>{citation(development["papers"][0])}</p>'
            f'<p>{escape(development["card"])}</p></div>')


REFERENCE_CSS = """
.paper-reference{margin:20px 0;padding:16px 18px;border:1px solid #cbd8cf;border-left:3px solid #426e5d;border-radius:6px;background:#f3f7f3;color:#243d34;font:14px/1.65 system-ui,sans-serif;overflow-wrap:anywhere}
.paper-reference .reference-heading,.paper-reference .publication-label{margin:0 0 8px;font-size:14px;letter-spacing:0;text-transform:none}
.paper-reference .reference-scope{margin:0 0 12px}.paper-reference .reference-list{margin:0;padding-left:20px}.reference-list li+li{margin-top:12px}.paper-reference a{color:#245b4a}.reference-links{font-size:.92em}.paper-reference cite,.card-reference cite{font-style:italic}
.card-reference{font-size:12px;line-height:1.65;border-top:1px solid #cbd8cf;margin-top:18px;padding-top:8px;overflow-wrap:anywhere}.card-reference p{margin:8px 0}.card-reference p:last-child{margin-bottom:0}
@media print{.paper-reference{background:white;color:#111;break-inside:avoid}}
"""
