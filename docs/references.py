"""Shared paper citations and publication status for the proof pages.

Publication metadata comes from the publisher/proceedings records linked below.
Version links identify the editions used by the existing correspondence audits.
An unpublished proof notice describes this project's proof, not a novelty claim.
"""
from html import escape


PAPERS = {
    'wasserstein-mixing': dict(
        authors="Francesco Pedrotti and Peter A. Whalley", year="2026",
        title="Wasserstein mixing time of the unadjusted Langevin algorithm",
        venue="arXiv preprint arXiv:2608.02430, version 1 (3 August 2026)",
        url="https://arxiv.org/abs/2608.02430v1",
        links=[("Paper HTML", "https://arxiv.org/html/2608.02430v1"),
               ("Full paper", "https://arxiv.org/pdf/2608.02430v1")]),
    'average-lmc': dict(
        authors="Arnak S. Dalalyan and Avetik Karagulyan", year="2026",
        title="Improved Guarantees for Langevin Monte Carlo with Average Smoothness",
        venue="arXiv preprint arXiv:2605.31413, version 1 (29 May 2026)",
        url="https://arxiv.org/abs/2605.31413v1",
        links=[("Full paper", "https://arxiv.org/pdf/2605.31413v1")]),
    'pbgso': dict(
        authors="Jiechen Jackie Zhang and O. Deniz Akyildiz", year="2026",
        title="Particle-based Generalised Stochastic Optimisation",
        venue="arXiv preprint arXiv:2608.02844, version 2 (9 October 2026)",
        url="https://arxiv.org/abs/2608.02844v2",
        links=[("Full paper", "https://arxiv.org/pdf/2608.02844v2")]),
    'latent-diffusion': dict(
        authors="Tim Y. J. Wang, Juan Kuntz, and O. Deniz Akyildiz", year="2026",
        title="Training Latent Diffusion Models with Interacting Particle Algorithms",
        venue="Proceedings of The 29th International Conference on Artificial Intelligence and Statistics, Proceedings of Machine Learning Research 300, 2791–2799",
        url="https://proceedings.mlr.press/v300/wang26f.html",
        links=[("Audited version: arXiv:2505.12412v3", "https://arxiv.org/abs/2505.12412v3")]),
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
    'WassersteinMixing': dict(
        label="Preprint source; original statements proved by a modified argument",
        status="extended", papers=["wasserstein-mixing"],
        scope=r"The supplied manuscript is audited by exact source hashes and compared with arXiv:2608.02430v1. Theorem 1 and Corollary 1.1 are proved under their original \(C^2\) Hessian assumptions, with the same constants, using a modified proof. The actual Langevin dynamics, reversible semigroup, corrector, Gaussian ULA invariant law and comparison estimates are constructed. The paper's generator/eigenbasis construction and Gaussian-smoothing passage are not formalized. The separate IPLA application derives new bounds by combining this result with Project 03's particle geometry and parameter concentration.",
        card="Original theorem statements and constants proved by a modified argument; a separate application improves the IPLA discretization rate."),
    'AverageLMC': dict(
        label="Preprint source; checked main sampling proofs",
        status="corrected", papers=["average-lmc"],
        scope=r"The correspondence uses arXiv:2605.31413v1, identical to the manuscript audited here. Its main average-smoothness LMC, decreasing-step, Laplacian-smooth LMC and fixed-point control-variate SGLD statements are proved for actual Gaussian sampling laws with the source constants. Extended transport endpoints cover arbitrary probability initializations. The Laplacian proof uses exactly \(C^3\) regularity and the gradient-of-Laplacian condition. The source audit distinguishes this main-theorem scope from broader auxiliary statements not reproduced in full standalone generality; literal full-paper proof coverage is not claimed.",
        card="Actual average-smoothness LMC, decreasing-step, Laplacian LMC and control-variate SGLD bounds with exact source hypotheses and constants."),
    'PBGSO': dict(
        label="Preprint source; checked theorems and new unpublished bounds",
        status="extended", papers=["pbgso"],
        scope=r"The correspondence uses arXiv:2608.02844v2, identical to the manuscript audited here. The four main theorems of the paper are proved under its assumptions A1–A5, the extra assumptions Extra A1–Extra A3 and explicit solution interpretations: A2 is read as stationary weak frozen invariance, and constant-diffusion contraction uses the finite signed-work convention. The time-uniform discretisation bounds New A and New B for M-MFPO and HOL-MYPGD, with explicit constants, are new and unpublished. The source audit records these interpretations and the printed HOL coefficient defect.",
        card="The four main theorems under explicit assumptions, and new time-uniform discretisation bounds for M-MFPO and HOL-MYPGD."),
    'LatentDiffusion': dict(
        label="Published source; corrected checked proofs and new theory",
        status="corrected", papers=["latent-diffusion"],
        scope=r"The correspondence uses arXiv:2505.12412v3, the camera-ready version of the AISTATS 2026 paper, identical to the manuscript audited here. The 19 inventoried results have corrected proofs under the paper's assumptions A1–A4 and the extra assumptions Extra A1–Extra A7. The literal printed statements are not certified as stated. Each paper label, correction and extra assumption is identified separately; the additional numerical and model-bias results are unpublished. The source audit records the corrected minibatch scaling and a counterexample to universal time-zero density differentiability.",
        card="All 19 source results in corrected form, with explicit error budgets and accuracy choices."),
    "KineticLangevin": dict(
        label="Published source; corrected checked proofs", status="corrected",
        papers=["dalalyan-riou-durand"],
        scope=r"The comparison uses the supplied mainDR_dec_18.tex manuscript. The results prove Wasserstein convergence of the kinetic diffusion, invariance of its Gibbs measure, KLMC and KLMC2 error estimates for correlated Gaussian increments, their Cholesky representations, and explicit iteration counts for a prescribed error. The corrected proofs are unpublished. The reference table records the correction to the continuous prefactor and the stochastic Hessian-difference terms retained in the second-order comparison. The KLMC2 estimate retains the exact fourth Gaussian moment in every dimension; the coarser displayed simplification assumes \(p\ge2\). The stronger inverse-step-square exponential term is also proved. Continuous solutions are continuous in \(L^2\) on finite time intervals. Almost-sure continuity of sample paths is not proved here.",
        card="The results cover kinetic diffusion convergence, Gibbs invariance, KLMC and KLMC2 error bounds, and iteration counts. The reference table specifies the corrections to the source proofs."),
    "KIPLMC": dict(
        label="Published source; checked diffusion and sampler proofs", status="extended",
        papers=["kinetic-ipla", "dalalyan-riou-durand", "monmarche-obabo"],
        scope=r"The comparison uses the supplied KIPLMC main.tex and its sections, including the OBABO rate that depends on the particle number. KIPLMC1 is the kinetic exponential integrator applied to the scaled particle potential, with correlated Gaussian increments represented by a Cholesky factor. KIPLMC2 uses the \(O\)-\(B\)-\(A\)-\(B\)-\(O\) splitting. The results prove diffusion convergence in physical time, Gibbs invariance, root mean square parameter estimates for both Gaussian recursions, time-rescaling identities, concentration about the marginal maximizer, and iteration counts. The logistic example is checked analytically. The OBABO argument proves a stronger estimate and then deduces the stated coarser rate with a uniform constant. The continuous solutions are continuous in \(L^2\). Numerical experiments are reported separately from these estimates.",
        card="The results give KIPLD convergence, parameter estimates for both Gaussian particle recursions, concentration about the marginal maximizer, and explicit iteration counts."),
    "UnadjustedLangevin": dict(
        label="Paper references", status="published",
        papers=["dalalyan-karagulyan", "dalalyan"],
        scope=r"The two step-size regimes and the coefficient \(1.65\) follow Theorem 1(a)–(b) of Dalalyan and Karagulyan (2019). Dalalyan (2017), Theorem 1 and Section 6, gives the earlier synchronous-coupling argument.",
        card=r"The displayed coefficient \(1.65\) and both step-size regimes follow Theorem 1 of Dalalyan and Karagulyan (2019)."),
    "UnadjustedLangevin/LSI": dict(
        label="Paper reference", status="published", papers=["vempala-wibisono"],
        scope="The entropy bound is Theorem 2 of Vempala and Wibisono (2019); its proof is in Section 3.1 and Appendices B.2.1–B.2.2. The proof here establishes Gaussian density regularity, entropy differentiation at positive times, and the limit as elapsed time decreases to zero.",
        card="Source: Theorem 2 and Appendices B.2.1–B.2.2."),
    "IPLA": dict(
        label="Published source and unpublished extension", status="extended",
        papers=["statfem-ipla", "dalalyan-karagulyan"],
        scope="Source: Theorem 1, equation (34), and Appendix B of arXiv:2409.07101v2 (27 May 2025), using the ULA estimate of Dalalyan and Karagulyan. The independent parameter- and latent-dimension extension and its proof presented here are unpublished; equal dimensions recover the paper’s displayed bound. The assumption audit explains the joint-potential smoothness condition.",
        card="Source: Theorem 1, equation (34), and Appendix B of arXiv:2409.07101v2. The independent-dimension extension and its proof presented here are unpublished."),
    "IPLA/LSI": dict(
        label="Unpublished proof", status="unpublished",
        papers=["vempala-wibisono", "statfem-ipla"],
        scope="The IPLA LSI proof presented here is unpublished. It applies the ULA entropy theorem to the joint particle Gibbs measure, proves the joint entropy estimate and its normalization by particle number, and bounds the parameter-marginal entropy by data processing. The papers below provide the ULA and IPLA results used in the argument.",
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
.paper-reference{margin:20px 0;padding:16px 18px;border:1px solid var(--line,#dedbd7);border-left:3px solid var(--accent,#a80000);border-radius:2px;background:var(--white,#fff);color:var(--ink,#1b1818);font:15px/1.65 var(--font-prose,"Latin Modern",Georgia,serif);overflow-wrap:anywhere}
.paper-reference .reference-heading,.paper-reference .publication-label{margin:0 0 8px;font-size:14px;letter-spacing:0;text-transform:none}
.paper-reference .reference-scope{margin:0 0 12px}.paper-reference .reference-list{margin:0;padding-left:20px}.reference-list li+li{margin-top:12px}.paper-reference a{color:var(--accent,#a80000)}.reference-links{font-size:.92em}.paper-reference cite,.card-reference cite{font-style:italic}
.card-reference{font-size:14px;line-height:1.65;border-top:1px solid var(--line,#dedbd7);margin-top:18px;padding-top:8px;overflow-wrap:anywhere}.card-reference p{margin:8px 0}.card-reference p:last-child{margin-bottom:0}
@media print{.paper-reference{background:white;color:#111;break-inside:avoid}}
"""
