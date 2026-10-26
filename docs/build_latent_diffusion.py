#!/usr/bin/env python3
"""Source-derived, statement-first report for the latent-diffusion manuscript.

Every displayed Lean contract is extracted from the current Lean source.  This
builder is deliberately independent of the published report/PDF catalogue.
Use --check to verify all generated files without modifying the working tree.
"""
from __future__ import annotations

import argparse
import hashlib
import html
import json
import os
from pathlib import Path
import re
import shutil
from urllib.parse import unquote, urlsplit

from build_site import ROOT, HELPERS, anchor, code, commands, relative, shell, toolbar
from build_pbgso import pbgso_declarations, header_lines, header_text, context_text, source_docstring

E = html.escape
PAGE = "LatentDiffusion/exposition/index.html"
INVENTORY = "LatentDiffusion/exposition/source_inventory.json"
STATEMENT_CHECKS = "LatentDiffusion/exposition/statement_checks.lean"
AUDIT = "LatentDiffusion/exposition/reference_audit.json"


def paper_audit():
    return json.loads((ROOT / AUDIT).read_text())


def paper_page(path):
    return "LatentDiffusion/exposition/paper/" + Path(path).stem + ".html"


def paper_reference(path, start, end, label):
    """Line anchors resolve in generated, verbatim views of the supplied paper."""
    if path not in paper_audit()["source"]["source_hashes"]:
        raise ValueError("Untracked manuscript reference: " + path)
    if not 1 <= start <= end <= len((ROOT / path).read_text().splitlines()):
        raise ValueError(f"Invalid manuscript line range: {path}:{start}-{end}")
    return (f'<a class="paper-reference" data-source-path="{E(path)}" '
            f'data-source-start="{start}" data-source-end="{end}" '
            f'href="{relative(paper_page(path), PAGE)}#L{start}">'
            f'{E(label)} · {E(Path(path).name)}:{start}–{end}</a>')


def exact_paper_statement(record):
    # Encode trailing source whitespace: keep the verbatim DOM text without
    # introducing whitespace errors into generated HTML diffs.
    verbatim = re.sub(r"[ \t]+(?=\n|$)",
                      lambda match: ''.join('&#32;' if c == ' ' else '&#9;' for c in match[0]),
                      E(record["exact_tex"]))
    return ('<details class="printed-source"><summary>Exact statement as printed in the paper</summary>'
            '<pre class="paper-tex"><code>' + verbatim + '</code></pre></details>')

MODULES = {
    "LatentDiffusion": ("Latent diffusion: checked imports", "Imports the formal development."),
    "Variational": ("Tilted free energy and variational optimality", "Variational identities and the exact assumptions used by their proofs."),
    "Density": ("Density normalization and the actual KL identity", "Actual posterior and trial probability measures, finite KL and the log-density free-energy identity follow from normalization and entropy integrability."),
    "Cloud": ("Count-independent interacting force geometry", "Per-datum strong convexity and gradient Lipschitz bounds imply full-cloud regularity in the normalized particle geometry."),
    "Flow": ("Scalar free-energy comparison", "Completion of the square and Grönwall components; the regular density modules derive their analytic inputs from the equations."),
    "Numerics": ("Nonasymptotic Euler stability and perturbation bounds", "The actual Euler map and its finite-step trajectories, with local consistency and noise assumptions exposed."),
    "BatchAudit": ("Minibatch normalization and empirical-distance audit", "Exact counterexamples and corrected scaling identities for source claims."),
    "Check": ("Lean checks and axiom audit", "Public theorem checks and their transitive logical axioms."),
    "SourceAssumptions": ("Literal manuscript assumptions", "Model and solution regularity as source contracts, including the universal initial-law premise and the time-zero density requirement."),
    "SourceObstruction": ("The time-zero regularity obstruction", "A Dirac initial law disproves the literal universal density-at-zero premise for a reference measure with null singletons."),
    "SourceResults": ("Corrected source arguments and integral identities", "First-variation algebra, normalized geometry, minimizing-sequence convergence and tilted density identities, with their precise domains."),
    "SourceCalculus": ("First variations under explicit integral domination", "Actual differentiation of the parameter and entropy-density integrals from pointwise derivatives and integrable domination."),
    "Marginal": ("Unique evidence and variational optimizers", "Finite-dimensional joint strong convexity is passed through actual Lebesgue marginal integrals using the established Prékopa theorem."),
    "Lift": ("Actual pointwise forces on square-integrable random variables", "The lifted force agrees almost everywhere with the original force, and inherits its constants by integration."),
    "Equilibrium": ("Uniform numerical error relative to a frozen reference", "Explicit finite-cloud residual, temporal discretization and centered stochastic-oracle terms, derived from actual integral equations."),
    "MiniBatchVariance": ("Heterogeneous averaging and finite-population variance", "Exact variance formulae from orthogonality and first and pair batch inclusion probabilities."),
    "MainResults": ("The full interacting-particle inference bound", "The actual heterogeneous cloud force is lifted to L² and its parameter RMS error is bounded with explicit particle, time and stochastic-oracle terms."),
    "Accuracy": ("Explicit particle, step-size and burn-in choices", "Arithmetic corollaries of the main error budget, with five allocated accuracy terms and division-free conditions."),
    "RegularVariational": ("Actual density variational problem and limiting energies", "Radon–Nikodym derivatives realize arbitrary finite-KL trial laws, and dominated density charts prove continuity and the corrected minimizing-limit theorem."),
    "RegularModel": ("Normalized strongly convex density models", "Jointly strongly convex potentials construct actual positive finite normalizers, finite-second-moment posteriors and a unique literal variational optimizer."),
    "RegularFlowCalculus": ("Classical density calculus and normalized product gradient", "Dominated differentiation and ordinary spatial integration by parts prove the full product-gradient representation, Fisher integrability and de Bruijn identity."),
    "RegularEvidence": ("Differentiating evidence and centering posterior scores", "The actual normalizer derivative and evidence optimality prove that the average posterior parameter score vanishes."),
    "RegularEvidenceScores": ("Evidence scores in the actual particle cloud", "Parameter-gradient projection and posterior-law initialization transfer the evidence first-order condition to actual L² particle score means."),
    "RegularTransport": ("Regular displacement transport and entropy convexity", "Actual pushforwards, positive Jacobians and coupling costs prove displacement convexity and identify optimal transport distances on the stated regular domain."),
    "RegularTransportFirstOrder": ("Transport score calculus and extended inequalities", "The Jacobian formula and proved integration by parts give entropy tangents, the full normalized first-order bound, extended LSI and Talagrand control."),
    "RegularMetricFlow": ("Actual law distances along characteristic curves", "Optimal anchors and square-integrable characteristic curves prove upper-right distance slopes and integrated metric-speed bounds."),
    "RegularProductMetricFlow": ("Normalized product-law metric speed", "The actual parameter and characteristic velocities give the source product-distance slope, and their kinetic energy equals the normalized Fisher information."),
    "RegularDensityDomain": ("Complete regular density domains in the actual source metric", "The domain metric is explicitly the normalized parameter/Wasserstein metric of actual laws; domination proves continuity and the complete-domain minimizing-limit theorem."),
    "RegularTransportGeodesic": ("Actual law and normalized product geodesics", "Optimal coupling maps identify constant-speed displacement interpolations and characterize the regular normalized product geodesics."),
    "RegularSourceTheorem": ("Full-batch error to the actual unique optimizer", "Actual evidence maximization centers posterior scores, a global Gibbs reference is constructed, and the pointwise full-batch Euler code obeys the explicit optimizer RMS bound."),
    "RegularTalagrand": ("Extended LSI implies Talagrand by flow length", "Dissipation and metric speed give finite remaining length, a constructed minimizing limit and Talagrand without a geodesic-convexity premise."),
    "RegularFlowTalagrand": ("Connected density dynamics imply Talagrand from xLSI", "Bare parameter/Fokker–Planck equations prove dissipation; actual characteristics and coupling anchors prove metric speed; xLSI then constructs a minimizing limit in the actual complete source metric, without A3."),
    "RegularConvergence": ("Convergence from classical equations and regular transport", "ClassicalFlow contains primitive regularity and differential equations; de Bruijn, extended LSI and exponential decay are proved from them."),
    "RegularDirectional": ("Actual initial transport derivative without convexity", "Dominated differentiation, the continuity equation and integrable spatial tails prove the actual probability-law energy right derivative and lower liminf without a convexity assumption."),
    "RegularStochastic": ("Actual Brownian particle equations and Euler bounds", "Global Picard construction, Gibbs stationarity, independent posterior scores and normalized moments yield explicit full-batch parameter error bounds."),
    "RegularMeanField": ("Actual mean-field equations and coupled particle error", "The deterministic parameter projection and averaged interaction force support continuous contraction and finite-particle comparison on actual L² paths."),
}


def source_inventory():
    paths = sorted(p.relative_to(ROOT).as_posix() for p in (ROOT / "LatentDiffusion").glob("*.lean"))
    if (ROOT / "LatentDiffusion.lean").is_file():
        paths.insert(0, "LatentDiffusion.lean")
    if not paths:
        raise ValueError("No LatentDiffusion Lean sources found")
    sources = {p: (ROOT / p).read_text() for p in paths}
    return sources, {p: parse_declarations(s) for p, s in sources.items()}


def parse_declarations(source):
    """Include indented namespace declarations while retaining exact columns."""
    rows, shifted = source.splitlines(), {}
    normalized = []
    for number, row in enumerate(rows, 1):
        trimmed = row.lstrip()
        if HELPERS.DECL.match(trimmed):
            shifted[number] = len(row) - len(trimmed)
            row = trimmed
        normalized.append(row)
    parsed = pbgso_declarations("\n".join(normalized))
    for decl in parsed.values():
        decl["marker_column"] += shifted.get(decl["marker"], 0)
    return parsed


def proof_page(path):
    return "LatentDiffusion/exposition/proofs/" + Path(path).stem + ".html"


def exact_contract(path, name, sources, parsed, *, page=PAGE):
    """Complete assumption definition or exact theorem header, never a proof."""
    decl = parsed[path][name]
    shared = context_text(sources[path], parsed[path])
    result = ('<details class="statement-context"><summary>Exact shared Lean context</summary>'
              + commands(shared, "context-" + anchor(Path(path).stem + "." + name), "Copy context")
              + '</details>')
    if decl["kind"] in ("structure", "inductive", "def", "abbrev"):
        result += code(path, decl["start"], decl["end"], sources, page, "contract", name)
    else:
        clipped = dict(sources)
        rows = sources[path].splitlines()
        rows[decl["marker"] - 1] = header_lines(sources[path], decl)[-1]
        clipped[path] = "\n".join(rows)
        result += code(path, decl["start"], decl["marker"], clipped, page, "statement", name)
    # Lean short names can occur in different modules.
    result = result.replace(' id="' + anchor(name), ' id="' + anchor(Path(path).stem + "." + name))
    return result


def eq(tex):
    return '<div class="statement-equation">\\[' + tex + '\\]</div>'


def ref(module, *names):
    return [("LatentDiffusion/" + module + ".lean", name) for name in names]


def panels():
    """Authored mathematics; declaration text is supplied solely by Lean files."""
    result = []
    def add(identifier, section, category, title, prose, refs):
        result.append(dict(id=identifier, section=section, category=category,
                           title=title, prose=prose, refs=refs))

    add("source-model-regularity", "assumptions", "original", "A1 — Model regularity", r'''
<p>Put \(a=(\theta,\phi)\), \(\tilde\rho_a(z)=\tilde p_a(x,z)\), and \(\tilde\pi_a(z)=\tilde\rho_a(z)/A_a\). For every \(z\), the maps \(a\mapsto\tilde\pi_a(z)\) and \(a\mapsto A_a\) are differentiable. For every \(a\), the spatial map \(z\mapsto\tilde\pi_a(z)\) is \(C^2\), and \(\tilde\rho_a(z)>0\) everywhere.</p>
<p>Here \(A_a\) is the model's normalizing constant. The regularity contract records these conditions; it does not establish differentiation under integrals or boundary integration by parts.</p>''',
        ref("SourceAssumptions", "normalizedPosterior", "ModelRegularity"))
    add("source-solution-regularity", "assumptions", "original", "A2 — Classical solutions for every initial law", r'''
<p>For every parameter \(a_0\) and every collection \(\mu_0^{1:M}\in\mathcal P_2(Z)^M\), the source assumes a classical solution of its gradient flow with those initial values. The parameter path is \(C^1\) on \([0,\infty)\). Each law has a positive Lebesgue density \(q_t^m(z)\), jointly \(C^{1,2}\) in time and space on \([0,\infty)\times Z\).</p>
<p>The Lean contract uses a supplied reference measure \(\nu\), instantiated by Lebesgue measure, and the actual flow equation as an explicit predicate. Its \(C^{1,2}\) contract requires continuous first time derivatives and first and second spatial derivatives, including right time derivatives at zero.</p>
<p><strong>Source issue.</strong> The universal quantifier includes singular initial laws, while the density and positivity conditions include \(t=0\). This premise is displayed literally and is not claimed to follow from A1, A3 or A4. The source audit records the resulting limitation.</p>''',
        ref("SourceAssumptions", "ClassicalDensityRegularity", "ClassicalSolution", "SolutionRegularity"))
    add("source-joint-concavity", "assumptions", "original", "A3 — Joint strong log-concavity", r'''
<p>For every datum \(m\), the tilted joint density is \(\lambda\)-strongly log-concave in the full pair \((a,z)\), with one \(\lambda>0\). Equivalently, for \(U_m(a,z)=-\log\tilde p_a(x^m,z)\),</p>'''
        + eq(r'U_m(sx+(1-s)y)\le sU_m(x)+(1-s)U_m(y)-\tfrac\lambda2s(1-s)\|x-y\|^2,\quad 0\le s\le1.')
        + r'''<p>The particle-average geometry used below is normalized in the latent coordinates. The same constant does not hold in an unweighted replicated Euclidean norm without accounting for that normalization.</p>''',
        ref("SourceAssumptions", "JointStrongLogConcavity"))
    add("source-gradient-lipschitz", "assumptions", "original", "A4 — Joint Lipschitz gradient", r'''
<p>Every \(U_m\) is differentiable and, for one \(L>0\),</p>'''
        + eq(r"\|\nabla U_m(a,z)-\nabla U_m(a',z')\|\le L\|(a,z)-(a',z')\|.")
        + r'''<p>Negating the log tilted density leaves the Lipschitz constant unchanged. The source's discretization theorem additionally assumes Lipschitz gradients of the tilting penalty \(\mathcal R\); the numerical results below instead expose the complete force and its approximation error directly.</p>''',
        ref("SourceAssumptions", "LipschitzGradient"))
    add("variational-domain", "assumptions", "bridge", "V1 — Normalized free energy and finite KL domain", r'''
<p>Let \(M>0\), let \(\ell(a)\) be the average tilted log evidence, and let \(\pi_a^m\) be the actual normalized posterior probability laws. Set</p>'''
        + eq(r'\mathcal F(a,q)=-\ell(a)+\frac1M\sum_{m=1}^M\mathrm{KL}(q^m\|\pi_a^m),\qquad\mathrm{KL}(q^m\|\pi_a^m)<\infty.')
        + r'''<p>KL here is the actual measure-theoretic divergence. Finite KL is required before conversion to real numbers. The density-normalization result below proves the log-density integral identity under explicit normalization and entropy-integrability conditions. Those conditions are not inferred from pointwise smoothness.</p>''',
        ref("Variational", "PosteriorFamily", "Admissible", "freeEnergy", "IsGlobalMin"))
    add("flow-analytic-bridges", "assumptions", "bridge", "Classical flow — Regularity and equations with proved entropy calculus", r'''
<p>The blue R assumptions specify positive density paths, their actual time derivatives, common-neighbourhood integral domination, regular transport charts and integrable spatial tails. The parameter and density equations are</p>'''
        + eq(r'\dot a_t=-\frac1M\sum_m\int\nabla_a U_m(a_t,z)q_t^m(z)\,dz,\qquad\partial_tq_t^m=\nabla\!\cdot\!\bigl(q_t^m\nabla_z(\log q_t^m+U_m(a_t,\cdot))\bigr).')
        + r'''<p><code>ClassicalFlow</code> records these primitive equations and regularity data. The displayed theorems derive the actual energy derivative, normalized extended LSI and exponential energy decay. For the source xLSI-to-Talagrand implication, the separate bare <code>RegularDensityDynamics</code> omits A3 entirely: actual characteristics and coupling anchors derive its metric speed, and xLSI is the sole functional-inequality premise. Dissipation and speed are conclusions of the connected theorem.</p>''',
        ref("RegularConvergence", "ClassicalFlow", "deBruijn", "extendedLSI", "energy_decay")
        + ref("RegularFlowTalagrand", "RegularDensityDynamics", "CharacteristicRealization",
              "exists_minimizer_talagrand"))
    add("density-normalization", "source-results", "bridge", "Density bridge — The actual log-density integral equals KL minus log evidence", r'''
<p>Let \(\rho>0\) be measurable and integrable relative to \(\nu\), with \(Z=\int\rho\,\mathrm d\nu>0\). Put \(\pi=(\rho/Z)\nu\). Let \(r\ge0\) be measurable and integrable under \(\pi\), with \(\int r\,\mathrm d\pi=1\) and \(r\log r\in L^1(\pi)\). Set \(q_\nu=r\rho/Z\) and \(q=q_\nu\nu\).</p>'''
        + eq(r'\int q_\nu\log\!\left(\frac{q_\nu}{\rho}\right)\,\mathrm d\nu=\int\log\!\left(\frac{q_\nu}{\rho}\right)\,\mathrm dq=\mathrm{KL}(q\|\pi)-\log Z.')
        + r'''<p>The theorem constructs both actual probability measures, proves that KL is finite, and proves integrability of the log ratio and this identity. It permits the relative density to vanish. The regular variational module additionally realizes every finite-KL trial law by its actual Radon–Nikodym density.</p>''',
        ref("Density", "density_freeEnergy_eq_kl", "density_weighted_freeEnergy_eq_kl"))
    add("variational-optimality", "source-results", "original", "Source proposition prop:ftildemins — Exact variational optimality", r'''
<p>Under V1,</p>'''
        + eq(r'(a_\star,q_\star)\in\operatorname*{argmin}\mathcal F\quad\Longleftrightarrow\quad a_\star\in\operatorname*{argmax}\ell\ \text{ and }\ q_\star^m=\pi_{a_\star}^m\ \ (m\in[M]).')
        + r'''<p>Thus \(a_\star\) maximizes the tilted evidence if and only if some variational collection completes it to a free-energy minimizer. This statement proves the equivalence and identifies the posterior; it does not assert that an evidence maximizer exists.</p>''',
        ref("Variational", "global_minimizers_iff", "maximizer_iff_exists_minimizer"))
    add("time-zero-obstruction", "source-results", "corrected", "Correction — Universal density regularity fails at time zero", r'''
<p>Suppose \(M>0\) and the reference measure \(\nu\) has a null singleton \(\nu(\{z_0\})=0\). Then the literal solution premise A2 is false, for any proposed flow equation.</p>
<p>The admissible initial collection can have every marginal equal to the actual Dirac probability measure \(\delta_{z_0}\), which has a finite second moment. A density realization at zero would force \(\delta_{z_0}\ll\nu\), contradicting its unit mass on \(\{z_0\}\). In particular, this obstruction applies to positive-dimensional Lebesgue measure.</p>
<p>A meaningful repaired premise must restrict the initial densities or impose the classical density condition only for positive times. The continuous bounds below expose their analytic inputs separately.</p>''',
        ref("SourceObstruction", "not_solutionRegularity_of_null_singleton", "not_solutionRegularity_of_noAtoms"))
    add("marginal-optimizer", "source-results", "bridge", "Continuous theorem, optimizer component — Unique marginal maximizer", r'''
<p>Let \(M>0\), and let each datum potential \(U_m\) be differentiable and \(\lambda\)-strongly convex in the full Euclidean parameter–latent pair, \(\lambda>0\). Define the actual marginal potential</p>'''
        + eq(r'V(a)=-\frac1M\sum_{m=1}^M\log\int_{\mathbb R^{d_z}}e^{-U_m(a,z)}\,\mathrm dz.')
        + r'''<p>Then \(V\) is \(\lambda\)-strongly convex and coercive, and has a unique global minimizer. Consequently, the actual average log evidence \(-V\) has a unique maximizer.</p>
<p>The regular model constructs its actual positive normalizers and posterior laws, proves finite second moments, and identifies the unique joint variational optimizer \((a_\star,q_\star)\), with \(q_\star^m=\pi_{a_\star}^m\).</p>''',
        ref("RegularConvergence", "existsUnique_optimizer_and_flow_convergence"))
    add("continuous-energy-decay", "source-results", "bridge", "Continuous theorem, decay component — Parameter and product-state convergence", r'''
<p>Under the blue R regularity hypotheses, the classical equations prove de Bruijn; regular transport and A3 prove extended LSI. Grönwall therefore gives</p>'''
        + eq(r'2\lambda E(t)\le I(t)\quad(0\le t<T),\qquad E(t)\le E(0)e^{-2\lambda t}\quad(0\le t\le T).')
        + r'''<p>Under the marginal optimizer hypotheses above, put \(F_\star=\mathcal F(a_\star,\pi_{a_\star})\). The actual normalized product distance and parameter error obey</p>'''
        + eq(r'd((a_t,q_t),(a_\star,\pi_{a_\star}))\le\sqrt{2E(t)/\lambda}\le\sqrt{2E(0)/\lambda}\,e^{-\lambda t},')
        + eq(r'\|a_t-a_\star\|\le\sqrt{\frac{2E(0)}\lambda}\,e^{-\lambda t}.')
        + r'''<p>The sharp prefactor follows from quadratic growth and the actual transport inequality. The chain uses the proved density energy derivative and entropy/transport calculus. R1–R7 identify the additional analytic domain; A1–A4 retain the paper's original colour and provenance.</p>''',
        ref("RegularConvergence", "ClassicalFlow", "deBruijn", "extendedLSI", "energy_decay",
            "full_product_exponential_convergence", "parameter_exponential_convergence")
        + ref("RegularProductMetricFlow", "distance_right_slope", "kinetic_energy_eq_fisher")
        + ref("RegularDensityDomain", "ProductDensityChart.lowerSemicontinuous_energy")
        + ref("RegularFlowTalagrand", "exists_minimizer_talagrand"))
    add("zero-tilt-correction", "source-results", "corrected", "Correction — A zero penalty at a tilted optimum is insufficient", r'''
<p>A two-point model gives a checked counterexample. Let \(\ell(0)=0\), \(\ell(1)=1\), and let the nonnegative evidence gap satisfy \(r(0)=0\), \(r(1)=2\). Then \(0\) maximizes \(\tilde\ell=\ell-r\) with zero gap, but fails to maximize \(\ell\).</p>
<p>A sufficient corrected condition is a <em>true</em> evidence maximizer \(b\) with \(\tilde\ell(b)=\ell(b)\). If \(\tilde\ell\le\ell\), every tilted maximizer \(a\) then obeys \(\ell(a)=\ell(b)\).</p>''',
        ref("Variational", "zero_gap_at_tilted_max_not_sufficient", "zero_gap_comparator"))
    add("batch-temperature", "source-results", "corrected", "Correction — Minibatch noise changes the target temperature", r'''
<p>For the quadratic potential \(U(x)=ax^2/2\), a datum is selected with probability \(p\in(0,1]\). The printed algorithm has inverse-inclusion drift and noise on every particle:</p>'''
        + eq(r'X^+=X-\frac hp I\,aX+\sqrt{2hp}\,W,\qquad I\sim\operatorname{Bernoulli}(p),\quad W\sim N(0,1).')
        + eq(r'\mathbb E[(X^+)^2\mid X=x]=\left(1-2ah+\frac{a^2h^2}p\right)x^2+2hp.')
        + r'''<p>The second-moment fixed point, when the denominator is nonzero, is</p>'''
        + eq(r'v_\star=\frac{p}{a(1-ah/(2p))}.')
        + r'''<p>For \(p=1/2\), \(h=1/4\), \(a=1\), a target second moment of one changes to \(7/8\) after one step, and \(v_\star=2/3\). The claimed matching of the full-batch noise variance is therefore false.</p>''',
        ref("BatchAudit", "paperConditionalSecondMoment_eq", "paper_moment_all_iterations", "paper_half_batch_counterexample", "paper_gaussian_target_not_invariant"))
    add("batch-corrections", "numerics", "new", "New result — Two explicit minibatch temperature corrections", r'''
<p><strong>Random scan:</strong> select both an uninflated drift and its \(\sqrt{2h}\) noise with probability \(p\), leaving the particle fixed otherwise. Its scalar second-moment fixed point is</p>'''
        + eq(r'v_{\mathrm{scan}}=\frac1{a(1-ah/2)}.')
        + r'''<p><strong>Full noise:</strong> retain the inverse-inclusion drift and replace the printed noise by \(\sqrt{2h}\,W\) on every particle. Its second-moment fixed point is</p>'''
        + eq(r'v_{\mathrm{full}}=\frac1{a(1-ah/(2p))}.')
        + r'''<p>The denominators must be nonzero in the algebraic identities. For meaningful positive stable scalar moments take \(a>0\) and respectively \(0<ah<2\) or \(0<ah<2p\). These exact quadratic calculations expose the remaining Euler bias and the \(1/p\) cost of random drift. They do not assert invariant-law existence for the adaptive nonlinear algorithm.</p>''',
        ref("BatchAudit", "randomScan_stationary_variance", "fullNoise_stationary_variance"))
    add("tilted-model-bias", "numerics", "new", "New result — Quantitative robustness to diffusion tilting", r'''
<p>Let the true evidence \(\ell\) be \(\lambda\)-strongly concave, \(\lambda>0\), with global maximizer \(a_\star\). Assume a uniform one-sided tilting gap and an approximate tilted optimizer:</p>'''
        + eq(r'0\le\ell(a)-\tilde\ell(a)\le\delta,\qquad\tilde\ell(a)\le\tilde\ell(\hat a)+\varepsilon\quad\text{for every }a,\qquad\delta,\varepsilon\ge0.')
        + r'''<p>Then both the true-objective and true-parameter errors are controlled:</p>'''
        + eq(r'\ell(a_\star)-\ell(\hat a)\le\delta+\varepsilon,\qquad\|\hat a-a_\star\|\le\sqrt{\frac{2(\delta+\varepsilon)}\lambda}.')
        + r'''<p>This quantifies the source's expressiveness discussion with an explicit model-bias assumption; it does not infer a uniform evidence gap from a pointwise training penalty.</p>''',
        ref("Marginal", "tilted_objective_bias", "tilted_parameter_bias"))
    add("force-regularity", "assumptions", "new", "N1 — Monotone, Lipschitz force", r'''
<p>Let \(H\) be a real inner-product space. The positive force \(F\), equal to minus the drift, satisfies for every \(x,y\in H\)</p>'''
        + eq(r'\lambda\|x-y\|^2\le\langle F(x)-F(y),x-y\rangle,\qquad \|F(x)-F(y)\|\le L\|x-y\|,\quad L\ge0.')
        + r'''<p>This is an explicit assumption on the complete force of the parameter and particle system in the chosen norm. Applying a per-datapoint hypothesis to that complete system requires its own lifting argument.</p>''',
        ref("Numerics", "ForceRegularity"))
    add("stable-step", "assumptions", "new", "N2 — Stable step size", r'''
<p>Require</p>''' + eq(r'\lambda>0,\qquad h>0,\qquad\lambda h\le1,\qquad hL^2\le\lambda.')
        + r'''<p>For \(L>0\), the familiar sufficient condition is \(0<h\le\min\{1/\lambda,\lambda/L^2\}\). These restrictions depend on the complete force constants.</p>''',
        ref("Numerics", "StableStep", "stableStep_of_min"))
    add("reference-consistency", "assumptions", "new", "N3 — Force error and reference consistency", r'''
<p>Write \(E_F(x,\xi)=x-hF(x)+\xi\), and let \(X_{n+1}=E_G(X_n,\xi_n)\) be the implemented scheme. A reference path \(y_n\) uses the same additive increments. For every step require</p>'''
        + eq(r'\|G(X_n)-F(X_n)\|\le B,\qquad \|y_{n+1}-E_F(y_n,\xi_n)\|\le D h\sqrt h,\qquad B,D\ge0.')
        + r'''<p>The numerical theorem is pathwise. An application to an exact SDE skeleton must establish the displayed local defect bound. Brownian increments, stochastic independence, moment estimates and propagation of chaos are not inferred from this premise.</p>''',
        [("LatentDiffusion/Numerics.lean", "trajectory_error_bound", "hforce"),
         ("LatentDiffusion/Numerics.lean", "trajectory_error_bound", "hdefect")])
    add("integral-reference", "assumptions", "new", "N4 — Primitive integral-path bounds", r'''
<p>Let \(H\) be complete. On each step, an exact segment \(Y_n(t)\), \(0\le t\le h\), starts at \(y_n\), ends at \(y_{n+1}\), and satisfies</p>'''
        + eq(r'Y_n(t)-Y_n(0)=-\int_0^t F(Y_n(s))\,\mathrm ds+W_n(t),\qquad W_n(h)=\xi_n.')
        + r'''<p>Assume the drift is integrable on each segment and, uniformly in \(n\),</p>'''
        + eq(r'\|F(Y_n(t))\|\le G,\qquad\|W_n(t)\|\le N\sqrt t,\qquad G,N\ge0.')
        + r'''<p>These are primitive integral and moment bounds. In an \(L^2\) realization, the norms are root mean squares. An application must supply the SDE reference and verify these uniform estimates. The pointwise-force lift below establishes the required \(L^2\) force regularity from N1.</p>''',
        ref("Numerics", "IntegralReference"))
    add("centered-innovation", "assumptions", "new", "N5 — Centered stochastic force innovations", r'''
<p>Compare \(X_{n+1}=E_F(X_n,\xi_n)+h\zeta_n\) with \(Y_{n+1}=E_F(Y_n,\xi_n)\), and put \(A_n=E_F(X_n,\xi_n)-E_F(Y_n,\xi_n)\). In the chosen Hilbert space require</p>'''
        + eq(r'\langle A_n,\zeta_n\rangle=0,\qquad\|\zeta_n\|^2\le\sigma^2\quad(n\ge0).')
        + r'''<p>In \(L^2(\Omega,P;E)\), these are precisely a zero expected cross term and a second-moment bound. Conditional centering given the states and shared increment suffices when justified. The premise states the needed orthogonality explicitly.</p>''',
        ref("Numerics", "HilbertInnovationControl"))
    add("frozen-reference", "assumptions", "new", "N6 — Frozen reference and empirical-force residual", r'''
<p>In the genuine space \(L^2(\Omega;\text{scaled cloud})\), a reference force \(R\) is \(L\)-Lipschitz and admits actual segments satisfying N4, with nonnegative drift radius \(G\) and noise bound \(W\sqrt t\). It need not contract in the fixed parameter coordinate.</p>
<p>The actual physical parameter projection \(C\) has norm at most one and satisfies \(Cy_n=a_\star\) almost surely for every \(n\). The norms in N4 are root mean squares. The construction and stationarity of a frozen posterior process, and its uniform drift/noise moment bounds, must be supplied by the application. The theorem accepts any such fixed reference parameter. An inference guarantee to the paper's tilted maximizer additionally identifies this \(a_\star\) with the optimizer proved in Part I.</p>''',
        [("LatentDiffusion/MainResults.lean", "particle_oracle_parameter_bound", field)
         for field in ("hR", "hr", "htarget")])
    add("empirical-reference-residual", "assumptions", "new", "N7 — Primitive centered-copy residual and variance", r'''
<p>Let \(K=MN>0\). The difference between the actual interacting force \(F_K\) and the reference force along \(y_n\) is represented by actual square-integrable fluctuations:</p>'''
        + eq(r'F_K(y_n)-R(y_n)=\frac1K\sum_{i=1}^K g_{n,i},\quad\langle g_{n,i},g_{n,j}\rangle_{L^2}=0\ (i\ne j),\quad\|g_{n,i}\|_{L^2}^2\le V,\quad V\ge0.')
        + r'''<p>These are a residual identity and primitive cross-moment and variance conditions. They permit heterogeneous data. A posterior-cloud application must prove that its chosen independent-copy reference has this representation and these moments. The \(K^{-1/2}\) force-residual bound is derived below.</p>''',
        [("LatentDiffusion/MainResults.lean", "particle_oracle_parameter_bound", field)
         for field in ("hres", "horth", "hvariance")])
    add("euler-contraction", "numerics", "new", "New result — Sharp Euler contraction", r'''
<p>Under N1 and \(h\ge0\), the same increment cancels in two Euler updates:</p>'''
        + eq(r'\|E_F(x,\xi)-E_F(y,\xi)\|^2\le(1-2\lambda h+L^2h^2)\|x-y\|^2.')
        + r'''<p>Under N2 this gives, with \(q=1-\lambda h/2\in[0,1)\),</p>'''
        + eq(r'\|E_F(x,\xi)-E_F(y,\xi)\|\le q\|x-y\|.')
        + r'''<p>The result holds for arbitrary common increments and the actual update map.</p>''',
        ref("Numerics", "euler_sq_contraction", "euler_contraction"))
    add("particle-normalized-geometry", "numerics", "new", "New result — Count-independent full-batch contraction", r'''
<p>Let \(K=MN>0\) count all datum–particle pairs. Give every coordinate its own datum potential \(U_i\), each satisfying A3–A4 with the same \(\lambda,L\). Use scaled state \(s=(a,z_1/\sqrt K,\ldots,z_K/\sqrt K)\), and put</p>'''
        + eq(r'F_K(s)=\frac1K\nabla_s\sum_{i=1}^K U_i(a,\sqrt K\,s_i),\qquad\|s-\bar s\|^2=\|a-\bar a\|^2+\frac1K\sum_i\|z_i-\bar z_i\|^2.')
        + r'''<p>The full force \(F_K\) is \(\lambda\)-strongly monotone and \(L\)-Lipschitz with exactly the original pair constants. Thus, under N2, the actual Euler map contracts synchronously:</p>'''
        + eq(r'\|E_{F_K}(s,\xi)-E_{F_K}(\bar s,\xi)\|\le(1-\lambda h/2)\|s-\bar s\|.')
        + r'''<p>The step restriction and contraction constant are independent of both data and particle counts. The coordinate-gradient identities are checked from the full lifted potential.</p>''',
        ref("Cloud", "meanForce_regular", "full_batch_contraction"))
    add("robust-euler", "numerics", "new", "New result — Uniform discretization and model-bias budget", r'''
<p>Under N1–N3, for every integer \(n\ge0\),</p>'''
        + eq(r'\begin{aligned}\|X_n-y_n\|&\le q^n\|X_0-y_0\|+(hB+Dh\sqrt h)\frac{1-q^n}{1-q}\\&\le q^n\|X_0-y_0\|+\frac2\lambda(B+D\sqrt h).\end{aligned}')
        + r'''<p>The bound separates the initial error, implemented-force bias and temporal consistency. Its constants are explicit and the error floor is uniform in the number of steps. Particle-count or dimension dependence can enter through \(\lambda,L,B,D\).</p>''',
        ref("Numerics", "trajectory_error_exact", "trajectory_error_bound"))
    add("integral-euler", "numerics", "new", "New result — Local consistency derived from integral dynamics", r'''
<p>Under N1 and N4 with \(h\ge0\), the local Euler defect is derived, rather than assumed:</p>'''
        + eq(r'\|y_{n+1}-E_F(y_n,\xi_n)\|\le L\left(\frac{h^2G}{2}+\frac23h\sqrt h\,N\right).')
        + r'''<p>Under N2 and an implemented-force error \(\|A(X_n)-F(X_n)\|\le B\), \(B\ge0\), this yields the uniform bound</p>'''
        + eq(r'\|X_n-y_n\|\le q^n\|X_0-y_0\|+\frac{2B}{\lambda}+\frac L\lambda\left(hG+\frac43N\sqrt h\right).')
        + r'''<p>The same theorem applies in any complete real Hilbert space. Its \(O(h+\sqrt h)\) term follows from the displayed integral equation and uniform drift and noise bounds.</p>''',
        ref("Numerics", "integral_reference_local_defect", "integral_reference_error_bound"))
    add("stochastic-oracle", "numerics", "new", "New result — Stochastic-oracle mean-square error floor", r'''
<p>Under N1, N2 and N5,</p>'''
        + eq(r'\|X_n-Y_n\|^2\le(1-\lambda h)^n\|X_0-Y_0\|^2+\frac{h\sigma^2}{\lambda}.')
        + r'''<p>For the actual Hilbert space \(L^2(\Omega,P;E)\) of square-integrable random variables on an arbitrary probability space, this is the genuine expectation bound</p>'''
        + eq(r'\mathbb E\|X_n-Y_n\|^2\le(1-\lambda h)^n\mathbb E\|X_0-Y_0\|^2+\frac{h\sigma^2}{\lambda}.')
        + r'''<p>The force regularity in this version is an explicit \(L^2\) premise. The theorem accepts Gaussian innovations and does not replace nonintegrable expectations by totalized real values.</p>''',
        ref("Numerics", "hilbert_innovation_sq_bound", "l2_innovation_mean_square_bound"))
    add("pointwise-probability-lift", "numerics", "new", "New result — Genuine probability-space lift of the pointwise force", r'''
<p>On any probability space, a pointwise force \(F:E\to E\) satisfying N1 induces a genuine operator \(\mathscr F:L^2(\Omega;E)\to L^2(\Omega;E)\) with</p>'''
        + eq(r'(\mathscr F X)(\omega)=F(X(\omega))\quad\text{almost surely}.')
        + r'''<p>The lifted force inherits the same monotonicity and Lipschitz constants. Its Euler iterates agree almost surely with the pointwise recursion. Therefore the stochastic-oracle expectation bound holds from regularity of the original pointwise force, together with N2 and the explicit innovation condition N5:</p>'''
        + eq(r'\mathbb E\|X_n-Y_n\|^2\le(1-\lambda h)^n\mathbb E\|X_0-Y_0\|^2+\frac{h\sigma^2}{\lambda}.')
        + r'''<p>No separate lifted-force regularity assumption or condition \(F(0)=0\) is needed.</p>''',
        ref("Lift", "liftedForce_coe", "liftedForce_regular", "lifted_eulerTrajectory_coe", "pointwise_force_mean_square_bound"))
    add("heterogeneous-average", "numerics", "new", "New result — Heterogeneous particle-average variance", r'''
<p>Let \(K>0\), and let \(g_1,\ldots,g_K\) be vectors in a real Hilbert space, such as centered random force errors in \(L^2\). If \(\langle g_i,g_j\rangle=0\) for \(i\ne j\), then</p>'''
        + eq(r'\left\|\frac1K\sum_i g_i\right\|^2=\frac1{K^2}\sum_i\|g_i\|^2\le\frac VK\quad\text{when }\|g_i\|^2\le V.')
        + r'''<p>Hence a residual represented by this average has \(B\le\sqrt{V/K}\). The copies may have different laws, as occurs for different data. Orthogonality is the explicit cross-moment premise; independence and centering must be verified when used to establish it.</p>''',
        ref("MiniBatchVariance", "mean_sq_sum_of_orthogonal", "mean_sum_of_orthogonal_le"))
    add("finite-population-oracle", "numerics", "new", "New result — Exact minibatch finite-population correction", r'''
<p>Let \(M>1\), \(b>0\). An actual finite probability space carries batches of size \(b\), with inclusion probabilities</p>'''
        + eq(r'\mathbb P(i\in\mathcal B)=\frac bM,\qquad\mathbb P(i,j\in\mathcal B)=\frac{b(b-1)}{M(M-1)}\quad(i\ne j).')
        + r'''<p>For arbitrary heterogeneous per-datum gradients \(g_i\), put \(\bar g=M^{-1}\sum_i g_i\). The actual raw-gradient oracle obeys</p>'''
        + eq(r'\mathbb E\left\|\frac1b\sum_{i\in\mathcal B}g_i-\bar g\right\|^2=\frac{M-b}{b(M-1)}\,\frac1M\sum_i\|g_i-\bar g\|^2.')
        + r'''<p>For \(b\le M\), a population dispersion bound \(M^{-1}\sum_i\|g_i-\bar g\|^2\le V\) therefore gives the derived oracle variance \(\sigma^2\le (M-b)V/[b(M-1)]\). The theorem derives this from the primitive first and pair inclusion laws, including zero sampling variance at full batch. Applying this identity to the whole-cloud stochastic force requires its actual scaled blocks and inverse-inclusion factors: the dispersion \(V\) may depend on both \(M\) and \(N\), so a count-independent \(\sigma^2\) bound does not follow automatically.</p>''',
        ref("MiniBatchVariance", "BatchInclusionLaw", "minibatch_gradient_variance", "minibatch_oracle_variance_bound"))
    add("complete-numerical-budget", "numerics", "new", "New main bound — Uniform inference error with a stochastic oracle", r'''
<p>Let \(K=MN>0\), and impose A3–A4 on each actual datum potential and N2, N5–N7 on the reference and innovations. Construct the complete interacting force \(F_K\) from those potentials, and use its actual noisy Euler update \(X_{n+1}=X_n-hF_K(X_n)+\xi_n+h\zeta_n\). Write \(a_n=CX_n\) for the physical parameter and \(q=1-\lambda h/2\). For every \(n\ge0\),</p>'''
        + eq(r'\begin{aligned}\left(\mathbb E\|a_n-a_\star\|^2\right)^{1/2}\le{}&q^n\|X_0-y_0\|_{L^2}+\frac2\lambda\sqrt{\frac VK}\\&+\frac L\lambda\left(hG+\frac43W\sqrt h\right)+\sqrt{\frac{h\sigma^2}{\lambda}}.\end{aligned}')
        + r'''<p>The force regularity is derived from the original per-datum potentials, including the exact pointwise-to-\(L^2\) lift. The output norm is proved equal to the physical parameter root mean-square error. The four explicit terms quantify initialization, finite-particle averaging, temporal discretization and the centered stochastic oracle. The finite-population identity below calibrates oracle variance from batch dispersion.</p>
<p>The bound is uniform in the number of steps. Its target \(a_\star\) is the fixed reference parameter specified in N6; interpreting it as convergence to the paper's optimizer requires that identification and a corresponding frozen posterior reference. It retains explicit reference existence, moment and innovation premises; it does not claim convergence of the unrestricted Adam/preconditioned implementation.</p>''',
        ref("MainResults", "particle_oracle_parameter_bound", "parameterOutput_rms"))
    add("explicit-accuracy", "numerics", "new", "New result — Explicit choices for any target accuracy", r'''
<p>Let \(\varepsilon>0\) and \(R_0=\|X_0-y_0\|_{L^2}\). Under the preceding main bound, the following explicit conditions suffice for parameter RMS error at most \(\varepsilon\):</p>'''
        + eq(r'\begin{gathered}\frac{\lambda h n}{2}\ge\log\max\!\left\{1,\frac{5R_0}{\varepsilon}\right\},\qquad100V\le\lambda^2\varepsilon^2K,\\5LhG\le\lambda\varepsilon,\qquad400L^2W^2h\le9\lambda^2\varepsilon^2,\qquad25h\sigma^2\le\lambda\varepsilon^2.\end{gathered}')
        + r'''<p>Each of the five initialization, particle, drift, noise-modulus and oracle terms receives \(\varepsilon/5\). The conditions are division-free, including zero drift, noise or variance constants. The burn-in formula also covers zero initial error. The probabilistic/reference premises remain those of the main theorem.</p>''',
        ref("Accuracy", "burnin", "budget_le_epsilon"))
    add("tilted-density-decomposition", "source-contracts", "proved", "Source objective — Tilting adds the expected penalty", r'''
<p>For measurable \(\rho\ge0\) and \(R\ge0\), define \(\widetilde\rho=\rho e^{-R}\). If \(\rho\) is integrable, then \(\widetilde\rho\) is integrable and \(\int\widetilde\rho\le\int\rho\). When the tilted normalizer is positive, \(\log\int\widetilde\rho\le\log\int\rho\).</p>
<p>For \(q\ge0\), \(\rho>0\), with both terms on the right integrable, the literal density free energy satisfies</p>'''
        + eq(r'\int q\log\frac{q}{\rho e^{-R}}\,d\nu=\int q\log\frac q\rho\,d\nu+\int qR\,d\nu\ \ge\ \int q\log\frac q\rho\,d\nu.')
        + r'''<p>This proves the source's density-level penalty decomposition and evidence order. The identification of \(R\) with a conditional path-space KL and the path-law chain rule remain separate model obligations. No differentiation of integrals is used in this identity.</p>''',
        ref("SourceResults", "tilted_freeEnergy_decomposition", "tilted_freeEnergy_le", "tilted_evidence_le", "tilted_logEvidence_le"))
    result[-1]["source_reference"] = '<p class="statement-source">' + paper_reference(
        "papers/Latent_diffusion/main_aistats.tex", 88, 110, "eq:ptildedef and tilted objective") + ' · ' + paper_reference(
        "papers/Latent_diffusion/supp_aistats.tex", 12, 33, "eq_app:decomposed_obj") + '</p>'
    source_contracts = {"variational-domain", "flow-analytic-bridges", "density-normalization"}
    for panel in result:
        identifier = panel["id"]
        if identifier.startswith("source-"):
            panel["section"] = "assumptions"
        elif identifier in source_contracts:
            panel["section"] = "source-contracts"
        elif panel["category"] == "new":
            panel["section"] = "new-assumptions" if panel["section"] == "assumptions" else "new-theorems"
        if identifier in ("density-normalization", "marginal-optimizer"):
            panel["category"] = "proved"
        elif identifier == "continuous-energy-decay":
            panel["category"] = "proved"
    from latent_diffusion_regularity import REGULARITY_PANELS
    result.extend(dict(id="regularity-" + item["id"].lower(), section="source-regularity",
                       category="regularity", title=item["id"] + " — " + item["title"],
                       prose="<p>" + item["prose"] + "</p>", refs=item["refs"])
                  for item in REGULARITY_PANELS)
    return result


def premise(path, name, binder, sources, parsed):
    """Read an entire parenthesized theorem premise from its exact source."""
    decl = parsed[path][name]
    rows = sources[path].splitlines()
    start = next((n for n in range(decl["start"] - 1, decl["marker"])
                  if re.search(r'\(' + re.escape(binder) + r'\s*:', rows[n])), None)
    if start is None:
        raise ValueError(f"Missing premise {path}:{name}:{binder}")
    depth = 0
    for end in range(start, decl["marker"]):
        depth += rows[end].count("(") - rows[end].count(")")
        if depth == 0:
            return start + 1, end + 1
    raise ValueError(f"Unterminated premise {path}:{name}:{binder}")


def render_panel(panel, sources, parsed, math):
    category = panel["category"]
    labels = {"original": "Paper assumption / source result", "bridge": "Added analytic premise",
              "regularity": "Added source regularity — R hypothesis",
              "corrected": "Corrected source claim", "new": "New theory",
              "proved": "Proved on the stated domain", "conditional": "Proved with additional analytic premises"}
    formal = []
    for index, reference in enumerate(panel["refs"]):
        path, name, *binder = reference
        if path not in parsed or name not in parsed[path]:
            raise ValueError(f"Missing displayed Lean declaration: {path}:{name}")
        link_label = ("parent theorem proof" if binder else "complete proof"
                      if parsed[path][name]["kind"] in ("theorem", "lemma") else "definition and context")
        formal.append('<div class="formal-item"><h4><a href="'
                      + relative(proof_page(path), PAGE) + '#' + anchor(name) + '">'
                      + E(name) + ' · ' + link_label + '</a></h4>')
        if binder:
            start, end = premise(path, name, binder[0], sources, parsed)
            formal.append(code(path, start, end, sources, PAGE, "premise", name,
                               panel["id"] + "-" + str(index)))
        else:
            formal.append(exact_contract(path, name, sources, parsed))
        formal.append('</div>')
    formal_html = ''.join(formal)
    # A source theorem and its appendix restatement may cite the same proof.
    formal_html = re.sub(r'\b(id|data-copy)="([^"]+)"',
                         lambda match: f'{match[1]}="{panel["id"]}-{match[2]}"', formal_html)
    assumption = re.match(r"([ANR][1-7]) —", panel["title"])
    attrs = f' data-assumption-id="{assumption[1]}"' if assumption else ""
    status = panel.get("status", "")
    attrs += ' ' + panel.get("attrs", "")
    return (f'<article class="theorem-statement paired-statement category-{category}" '
            f'id="{panel["id"]}" data-category="{category}"{attrs}>'
            f'<span class="result-badge">{labels[category]}</span><h3>{E(panel["title"])}</h3>'
            + panel.get("source_reference", "") + status +
            '<div class="statement-pair"><div class="statement-math"><div class="pane-label">Mathematical statement</div>'
            + math(panel["prose"]) + '</div><aside class="statement-lean"><div class="pane-label">Exact Lean contract</div>'
            + (formal_html or '<p class="source-specification">This card records a correction to the printed specification. '
               'Its exact manuscript location is linked above.</p>')
            + '</aside></div>' + panel.get("printed_source", "") + '</article>')


def source_endpoint_refs(record):
    """Use the curated source proof endpoints, including the regular repairs."""
    result = []
    for reference in record.get("formal_declarations", []):
        path, name = reference["file"], reference["name"]
        result.append((path, name))
    return list(dict.fromkeys(result))


def render_source_result(record, sources, parsed, math):
    from latent_diffusion_paper import PAPER_RESULTS
    description = PAPER_RESULTS[record["id"]]
    refs = source_endpoint_refs(record)
    original_complete = record.get("original_statement_fully_reconstructed") is True
    corrected_complete = record.get("corrected_statement_fully_proved") is True
    complete = original_complete or corrected_complete
    formal_status = "proved" if complete else ("partial" if refs else "open")
    prose = description["statement"]
    added = record.get("added_assumptions", [])
    if added:
        prose += ('<p class="added-regularity"><strong>Added assumptions for this result:</strong> '
                  + ' · '.join('<a class="regularity-link" href="#regularity-' + E(identifier.lower()) + '">'
                               + E(identifier) + '</a>' for identifier in added) + '.</p>')
    if description.get("correction"):
        prose += '<div class="source-correction"><strong>Correction / required qualification.</strong>' + description["correction"] + '</div>'
    prose += '<p><strong>Formal scope.</strong> ' + description["scope"] + '</p>'
    # The supplemental formalization has its own exact, independently checked domain.
    counterpart = {
        "prop:ftildemins": ["variational-optimality"],
        "thm:exp_convg_informal": ["marginal-optimizer", "continuous-energy-decay"],
        "thm:exp_convg_appendix": ["continuous-energy-decay"],
    }.get(record["id"], [])
    for panel in panels():
        if panel["id"] in counterpart:
            prose += '<div class="formal-endpoint"><h4>Checked endpoint — ' + E(panel["title"]) + '</h4>' + panel["prose"] + '</div>'
    if record["id"] in ("thrm:error-bound", "thrm_app:error-bound"):
        prose += ('<p>The source proof uses actual full-batch Brownian dynamics, posterior initialization and the blue R moment/domain hypotheses. '
                  '<a href="#complete-numerical-budget">Theorem New 1</a> then gives the separate extension to a centered noisy oracle.</p>')
    panel = dict(id="paper-" + anchor(record["id"]), category="original", title=description["title"],
                 section="source-results", prose=prose, refs=refs,
                 attrs=f'data-source-result="{E(record["id"])}" data-formal-status="{formal_status}" '
                   f'data-original-complete="{str(original_complete).lower()}" '
                   f'data-corrected-complete="{str(corrected_complete).lower()}"',
                 source_reference='<p class="statement-source">' + paper_reference(record["source"],
                     record["start_line"], record["end_line"], record["id"]) + '</p>',
                 printed_source=exact_paper_statement(record))
    status = ("Proved: the original statement is reconstructed on its stated domain." if original_complete else
              "Proved corrected statement under the explicitly added blue R regularity hypotheses. The precise corrections to the printed source are stated below."
              if corrected_complete else
              "Partial formalization: the Lean code proves the stated endpoint or supporting component; the complete source statement remains unproved."
              if refs else "Open formalization: this source statement does not yet have a complete Lean proof.")
    panel["status"] = '<p class="formal-status"><strong>' + status + '</strong></p>'
    return render_panel(panel, sources, parsed, math)


def paper_document(path):
    page = paper_page(path)
    source = (ROOT / path).read_text()
    title = "Paper source — " + Path(path).name
    body = ('<div class="breadcrumb"><a href="' + relative(PAGE, page) + '">Latent diffusion</a> / Supplied paper</div>'
            '<header class="hero"><h1>' + E(title) + '</h1><p>Verbatim local source with stable line anchors. '
            'Line references on the statement page resolve here. This view contains no corrections to the manuscript.</p>'
            '<p><a href="' + relative(path, page) + '">Original TeX file</a> · SHA-256: <code>'
            + hashlib.sha256(source.encode()).hexdigest() + '</code></p></header><pre class="paper-source"><code>')
    body += '\n'.join(f'<span class="paper-source-line" id="L{number}"><a href="#L{number}" aria-label="Line {number}">{number:4}</a> '
                      + E(line) + '</span>' for number, line in enumerate(source.splitlines(), 1))
    body += '</code></pre>'
    from report_citations import citation_panel
    body += citation_panel(None, None, None, page)
    return shell(page, title, body).replace('</head>', '<style>.paper-source{font:13px/1.7 var(--font-code);white-space:pre-wrap;overflow-wrap:anywhere}'
                                           '.paper-source-line:target{background:#f5cf7555;outline:1px solid #c89a3c}'
                                           '.paper-source-line>a{color:var(--muted);text-decoration:none}</style></head>')


EXTRA_CSS = """
.latent-page .hero {max-width:1100px}.latent-page .section>p {max-width:1100px}
.latent-page .result-badge {display:inline-block;font:12px/1.5 var(--font-code);padding:5px 10px;border:1px solid var(--line)}
.latent-page .category-new {border-top-color:#a65d00}.latent-page .category-new>.result-badge {background:#fff0d8;color:#753c00}
.latent-page .category-original {border-top-color:#28734a}.latent-page .category-original>.result-badge {background:#e6f4e9;color:#205b3a}
.latent-page .category-regularity {border-top-color:#245fa3}.latent-page .category-regularity>.result-badge {background:#e5f0ff;color:#174b86}
.latent-page .category-bridge {border-top-color:#32718c}.latent-page .category-bridge>.result-badge {background:#eaf5fa;color:#164d64}
.latent-page .category-corrected {border-top-color:#a1364f}.latent-page .category-corrected>.result-badge {background:#fff0f3;color:#87283e}
.latent-page .statement-equation {overflow-x:auto}.latent-page .jump-nav{flex-wrap:wrap}
.latent-page .paper-tex{white-space:pre-wrap;overflow-wrap:anywhere;font:12px/1.65 var(--font-code);padding:18px;background:var(--white);border:1px solid var(--line)}
.latent-page .paper-reference{font:13px/1.6 var(--font-code);overflow-wrap:anywhere}
.latent-page .formal-status,.latent-page .formal-gap{padding:12px 16px;border-left:3px solid #32718c;background:var(--white)}
.latent-page .source-correction{border-left:3px solid #a1364f;padding:8px 16px;background:var(--white)}
.latent-page .added-regularity{border-left:3px solid #245fa3;padding:10px 16px;background:#e5f0ff;color:#174b86}
.latent-page .regularity-link{font-weight:700;color:inherit}
.latent-page .paper-contents{columns:2;column-gap:36px;margin:24px 0}.latent-page .paper-contents li{break-inside:avoid;margin:8px 0}
.latent-page .part-heading{margin-top:60px;padding-top:25px;border-top:3px solid var(--ink)}
.latent-page .new-contributions{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:20px;margin:24px 0}
.latent-page .new-contributions>div{border:1px solid var(--line);padding:16px;min-width:0}
@media(max-width:760px){.latent-page .paper-contents{columns:1}.latent-page .new-contributions{grid-template-columns:1fr}}
.reading-math .latent-page .statement-lean,.reading-lean .latent-page .statement-math{display:none}
.reading-math .latent-page .statement-pair,.reading-lean .latent-page .statement-pair{grid-template-columns:minmax(0,1fr)}
.reading-lean .latent-page .statement-lean{position:static;border:0;padding-left:0;max-height:none}
html[data-theme="dark"] .latent-page .category-new>.result-badge{background:#3c2e1f;color:#ffd19a}
html[data-theme="dark"] .latent-page .category-original>.result-badge{background:#1d3929;color:#aee2bd}
html[data-theme="dark"] .latent-page .category-regularity>.result-badge{background:#1c304f;color:#bad6ff}
html[data-theme="dark"] .latent-page .added-regularity{background:#1c304f;color:#bad6ff}
html[data-theme="dark"] .latent-page .category-bridge>.result-badge{background:#21343c;color:#b4def1}
html[data-theme="dark"] .latent-page .category-corrected>.result-badge{background:#3e2630;color:#ffbdcd}
"""


def overview(sources, parsed, math):
    from latent_diffusion_paper import PAPER_RESULTS, PAPER_CORRECTIONS
    audit = paper_audit()
    body = ('<div class="pbgso-overview latent-page"><header class="hero">'
            '<div class="eyebrow">Part I · Paper results and corrections &nbsp; / &nbsp; Part II · New theory</div>'
            '<h1>Training Latent Diffusion Models with Interacting Particle Algorithms</h1>'
            '<p class="subtitle">The paper’s statements first; additional assumptions and new theorems second. Mathematics and exact Lean code appear side by side.</p>'
            '<p>Source: Wang, Kuntz and Akyildiz, local manuscript. '
            '<a href="paper/main_aistats.html">Main text with line numbers</a> · '
            '<a href="paper/supp_aistats.html">Supplement with line numbers</a> · '
            '<a href="source_audit.md">Source audit and coverage</a> · '
            '<a href="source_inventory.json">Exact source inventory</a></p></header>'
            '<nav class="jump-nav" aria-label="Report contents"><a href="#assumptions">Paper assumptions</a>'
            '<a href="#source-regularity">Added regularity R1–R7</a><a href="#source-results">Paper results</a><a href="#source-corrections">Corrections</a>'
            '<a href="#new-assumptions">New assumptions</a><a href="#new-theorems">New theorems</a>'
            '<a href="#complete-numerical-budget">Main numerical bound</a>'
            '<a href="#verification">Check the statements</a></nav>'
            '<p class="formal-status"><strong>Formalization status.</strong> All 19 source result statements are stated below, '
            'including appendix restatements, with their corrected mathematical statements, precise source references and Lean proofs. '
            'The blue R1–R7 panels state the added regularity and domain hypotheses used to prove those corrections. '
            'The exact original TeX is retained in each card so a corrected theorem is never confused with the printed statement.</p>'
            '<p>Green identifies the paper’s original A1–A4. Blue identifies the added R regularity; rose identifies corrections. '
            'Orange is reserved for the new theory in Part II. Lean signatures are extracted from the current source; '
            'declaration links open complete proofs. “New” means added relative to this manuscript. '
            'Lean uses <code>m</code> or <code>rho</code> for λ; <code>N</code> in the cloud modules counts the paper’s total <code>M × N</code>.</p>'
            + toolbar())
    all_panels = panels()
    body += '<div class="part-heading"><h2>Part I — Results from the paper</h2></div>'
    setting = r'''<p>Write \(a=(\theta,\phi)\), \(U_m(a,z)=-\log\tilde p_a(x^m,z)\), \(Z_m(a)=\int e^{-U_m(a,z)}\,dz\), and \(\pi_a^m=Z_m(a)^{-1}e^{-U_m(a,\cdot)}dz\). The evidence and energy are</p>'''
    setting += eq(r'\ell(a)=\frac1M\sum_m\log Z_m(a),\qquad F(a,q)=-\ell(a)+\frac1M\sum_m\mathrm{KL}(q^m\|\pi_a^m).')
    setting += r'''<p>Here \(\ell\) and \(F\) abbreviate the paper's tilted evidence \(\widetilde\ell\) and energy \(\widetilde F\). The source cards below retain tildes. In the model-bias theorem in Part II, \(\ell\) explicitly denotes the original, untilted evidence.</p><p>The paper uses the normalized product distance \(d((a,q),(b,r))^2=\|a-b\|^2+M^{-1}\sum_m W_2(q^m,r^m)^2\), with \(M>0\). The law \(q^m\) is the latent posterior approximation for datum \(m\); \(N\) is the particle count per datum. The optimizer targets tilted evidence, not automatically the original likelihood.</p>'''
    for section, title in (("assumptions", "Paper assumptions — A1–A4"),
                           ("source-regularity", "Added regularity — R1–R7"),
                           ("source-contracts", "Actual density model and proved analytic chain")):
        body += '<section class="section" id="' + section + '"><h2>' + title + '</h2>'
        if section == "assumptions":
            body += math(setting)
        elif section == "source-regularity":
            body += ('<p class="regularity-provenance">These blue hypotheses are additions to the paper’s green A1–A4. '
                     'They state sufficient regularity, domain and initialization conditions for the corrected source proofs. '
                     'They contain no assumed entropy-dissipation identity, desired transport inequality or numerical error bound. '
                     'The orange N assumptions belong only to the later new theory.</p>')
        else:
            body += ('<p>The normalized finite-KL domain and actual density identity are defined below. '
                     'Classical flow records the differential equations and R regularity; its entropy calculus and transport inequalities are proved.</p>')
        selected = [p.copy() for p in all_panels if p["section"] == section]
        if section == "source-contracts":
            order = ["tilted-density-decomposition", "variational-domain", "density-normalization", "flow-analytic-bridges"]
            selected.sort(key=lambda p: order.index(p["id"]))
        for panel in selected:
            if section == "assumptions":
                record = audit["assumptions"][int(panel["title"][1]) - 1]
                panel["source_reference"] = '<p class="statement-source">' + paper_reference(
                    record["source"], record["start_line"], record["end_line"], record["id"]) + '</p>'
                panel["printed_source"] = exact_paper_statement(record)
            body += render_panel(panel, sources, parsed, math)
        body += '</section>'
    body += ('<section class="section" id="source-results"><h2>Paper results — all 19 source statements</h2>'
             '<p>Each card states the corrected source claim, identifies its R hypotheses and precise correction, and shows its Lean theorem. '
             'The exact original TeX is expandable for direct comparison.</p><ol class="paper-contents">')
    for record in audit["results"]:
        body += '<li><a href="#paper-' + anchor(record["id"]) + '">' + E(PAPER_RESULTS[record["id"]]["title"]) + '</a></li>'
    body += '</ol>'
    for record in audit["results"]:
        body += render_source_result(record, sources, parsed, math)
    body += '</section><section class="section" id="source-corrections"><h2>Corrections to the paper’s formulas and arguments</h2>'
    body += '<p>Each correction names the exact local source location. An algebraic repair and a completed proof of the corresponding flow or algorithm are separate claims.</p>'
    for correction in PAPER_CORRECTIONS:
        panel = dict(id=correction["id"], section="source-corrections", category="corrected",
                     title=correction["title"], prose=correction["prose"], refs=correction.get("refs", []))
        panel["source_reference"] = '<p class="statement-source">' + ' · '.join(
            paper_reference(r["file"], r["start_line"], r["end_line"], r["label"])
            for r in correction["references"]) + '</p>'
        panel["status"] = '<p class="formal-status">' + E(correction["status"]) + '</p>'
        body += render_panel(panel, sources, parsed, math)
    body += '</section>'
    body += ('<section class="section part-heading" id="new-theory" data-new-theory="true"><h2>Part II — New theory</h2>'
             '<p>The paper already gives a full-batch error rate with implicit constants. These additions make the force geometry, '
             'particle variance, discretization and oracle contributions explicit. Their hypotheses are listed first.</p>'
             '<div class="new-contributions"><div><strong>What changes for inference?</strong><p>The final bound separates initialization, '
             'particle count, step size and oracle noise, so each source of parameter error can be budgeted.</p></div>'
             '<div><strong>What changes for minibatches?</strong><p>Exact variance and scalar temperature calculations distinguish '
             'sampling error from a change of target caused by the printed noise scaling.</p></div>'
             '<div><strong>What changes for model bias?</strong><p>A one-sided evidence gap turns approximate tilted optimization '
             'into an explicit distance from the original model’s optimizer.</p></div></div>'
             '<section id="new-assumptions"><h3>New Assumptions — N1–N7</h3>'
             '<p>N1 is the force interface, derived from A3–A4 for the scaled cloud. N2 is the step restriction. '
             'N3–N4 describe alternative reference formulations; N5–N7 supply the probabilistic inputs for the main bound. '
             'Each theorem below names the subset it uses; these premises are not asserted to follow from A1–A4.</p>')
    for panel in all_panels:
        if panel["section"] == "new-assumptions":
            body += render_panel(panel, sources, parsed, math)
    body += '</section><section id="new-theorems"><h3>New Theorems — statements, contributions and Lean code</h3>'
    new_panels = [p for p in all_panels if p["section"] == "new-theorems"]
    new_panels.sort(key=lambda p: p["id"] != "complete-numerical-budget")
    contributions = {
        "complete-numerical-budget": "The paper gives an implicit full-batch error rate. This bound shows how much error comes from initialization, a finite particle cloud, finite time steps and a noisy gradient oracle, under the stated reference assumptions.",
        "batch-corrections": "These two scalar repairs restore the intended small-step temperature. They show that changing the batch size can change the target unless drift and noise are scaled consistently.",
        "tilted-model-bias": "The paper optimizes a tilted model. This result quantifies how close its approximate optimizer is to the original model's optimizer when a uniform evidence-gap bound is available.",
        "euler-contraction": "Two updates driven by the same noise move closer together. This is the stability mechanism that prevents small numerical errors from accumulating indefinitely.",
        "particle-normalized-geometry": "Adding more particles does not weaken contraction when the cloud norm averages their squared errors. The proof explains which geometry preserves the paper's original constants.",
        "robust-euler": "A persistent force error produces a fixed error floor. This separates errors in the implemented gradient from errors caused by discretizing time.",
        "integral-euler": "The local discretization error follows from the reference's integral dynamics and moment bounds. The resulting explicit step-size term explains the square-root rate used in the paper.",
        "stochastic-oracle": "Centered gradient noise accumulates in mean square. The explicit square-root-in-step-size error floor shows how reducing the step size controls this additional source of error.",
        "pointwise-probability-lift": "This connects regularity of the actual force on particle states to expected-error bounds for random states. It justifies applying the numerical argument on a real probability space.",
        "heterogeneous-average": "Different data can have different posterior laws. Zero cross moments still give inverse-square-root particle averaging, so identical distributions across data are unnecessary.",
        "finite-population-oracle": "The variance formula accounts for sampling data without replacement. It vanishes at full batch and exposes the batch-size factor needed to calibrate the oracle term.",
        "explicit-accuracy": "The implicit rate becomes concrete sufficient inequalities for particle count, step size and burn-in. Each of the five error terms receives one fifth of the requested tolerance.",
    }
    for number, panel in enumerate(new_panels, 1):
        panel = panel.copy()
        panel["title"] = "Theorem New " + str(number) + " — " + panel["title"].split(" — ", 1)[-1]
        panel["prose"] += '<p class="contribution"><strong>What this adds to the paper.</strong> ' + contributions[panel["id"]] + '</p>'
        body += render_panel(panel, sources, parsed, math)
    body += '</section></section>'
    body += ('<section class="section" id="verification"><h2>Check the displayed statements</h2>'
             '<p>The Lean panes contain full signatures and omit proof bodies. '
             'These commands check the available imported proofs, exact displayed code, source coverage and page ordering. '
             'The source audit separately records proof completion for corrected statements and fidelity to the exact printed statements.</p>'
             + commands("python3 scripts/verify-latent-diffusion.py --lean\npython3 docs/test_latent_diffusion_landing.py\npython3 docs/build_latent_diffusion.py --check", "verify-latent")
             + '<p><a href="statement_checks.lean">Statement checks</a> invoke the displayed Lean theorem endpoints as imported proof constants, without copying their proofs.</p>'
             + '<p>Proof modules: '
             + ' · '.join('<a href="' + relative(proof_page(path), PAGE) + '">' + E(path) + '</a>' for path in sources)
             + '</p></section></div>')
    from report_citations import citation_panel
    body += citation_panel(None, None, None, PAGE)
    document = shell(PAGE, "Latent diffusion: assumptions and checked results", body)
    return document.replace('<body data-theme-family="modern">', '<body data-theme-family="modern" class="pbgso-page">').replace(
        '</head>', '<link rel="stylesheet" href="' + relative("docs/assets/pbgso.css", PAGE) + '"><style>' + EXTRA_CSS + '</style></head>')


def module_document(path, sources, parsed):
    page = proof_page(path)
    title, summary = MODULES.get(Path(path).stem, (Path(path).stem, "Exact current Lean declarations."))
    body = ('<div class="breadcrumb"><a href="' + relative(PAGE, page) + '">Latent diffusion statements</a> / ' + E(path) + '</div>'
            '<header class="hero"><h1>' + E(title) + '</h1><p>' + E(summary) + '</p>'
            '<p>Each declaration below is read directly from the current source. Its complete signature specifies all inputs. '
            'Shared variables, typeclasses, imports and namespace scope are preserved in the complete module.</p></header>' + toolbar())
    for name, decl in parsed[path].items():
        doc = source_docstring(sources[path], decl["start"])
        body += ('<article class="proof-step" id="' + anchor(name) + '"><h2>' + E(name) + '</h2>'
                 '<p>' + E(doc or "Supporting declaration; the exact source below specifies its assumptions and mathematical role.") + '</p>'
                 + code(path, decl["start"], decl["end"], sources, page, "declaration", name) + '</article>')
    body += '<details class="source-section" id="complete-source"><summary>Complete Lean module and shared context</summary>'
    body += code(path, 1, len(sources[path].splitlines()), sources, page, "module") + '</details>'
    from report_citations import citation_panel
    body += citation_panel(None, None, None, page)
    return shell(page, title, body)


def inventory_document(sources, parsed):
    return {"schema_version": 2,
            "scope": "Syntactic source contracts, complete declarations, shared context, exact source hashes and main-page references. A successful Lean build is a separate check.",
            "panels": [{key: panel[key] for key in ("id", "section", "category", "title", "refs")} for panel in panels()],
            "paper_results": [{"id": record["id"], "source": record["source"],
                               "start_line": record["start_line"], "end_line": record["end_line"],
                               "original_statement_fully_reconstructed": record["original_statement_fully_reconstructed"],
                               "corrected_statement_fully_proved": record.get("corrected_statement_fully_proved", False),
                               "refs": source_endpoint_refs(record)} for record in paper_audit()["results"]],
            "modules": {path: {"source_sha256": hashlib.sha256(source.encode()).hexdigest(),
                               "shared_context": context_text(source, parsed[path]),
                               "declarations": {name: {"kind": decl["kind"], "lean_name": decl["lean_name"],
                                                        "start_line": decl["start"], "end_line": decl["end"],
                                                        "statement": header_text(source, decl),
                                                        "complete_declaration": "\n".join(source.splitlines()[decl["start"] - 1:decl["end"]])}
                                                for name, decl in parsed[path].items()}}
                        for path, source in sources.items()}}


def outputs():
    from latent_diffusion_paper import PAPER_CORRECTIONS
    sources, parsed = source_inventory()
    if shutil.which("node") is None:
        bundled = Path.home() / ".cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin"
        if (bundled / "node").is_file():
            os.environ["PATH"] = str(bundled) + os.pathsep + os.environ.get("PATH", "")
    # Collect the actual page's authored formulas, including source statements,
    # corrections and the shared setting. No runtime/network math is required.
    math = HELPERS.render_mathematics([overview(sources, parsed, lambda value: value)])
    result = {PAGE: overview(sources, parsed, math),
              INVENTORY: json.dumps(inventory_document(sources, parsed), ensure_ascii=False, indent=2) + "\n"}
    used = dict.fromkeys((reference[0], reference[1]) for panel in panels() for reference in panel["refs"])
    used.update(dict.fromkeys(reference for record in paper_audit()["results"] for reference in source_endpoint_refs(record)))
    used.update(dict.fromkeys(tuple(reference) for correction in PAPER_CORRECTIONS for reference in correction.get("refs", [])))
    checked = [(path, parsed[path][name]) for path, name in used
               if parsed[path][name]["kind"] in ("theorem", "lemma")]
    result[STATEMENT_CHECKS] = ("import LatentDiffusion\n\n"
                               "/- Generated by docs/build_latent_diffusion.py.\n"
                               "Every displayed result is invoked through its complete imported proof type.\n"
                               "No proof body is copied into this statement-checking file. -/\n\n"
                               "set_option linter.defProp false\n\n"
                               + "\n".join("-- " + path + ":" + str(decl["start"]) + "\n"
                                           "def check_" + re.sub(r"[^\w]", "_", decl["lean_name"]) + " := @" + decl["lean_name"] + "\n"
                                           for path, decl in checked))
    result.update({proof_page(path): module_document(path, sources, parsed) for path in sources})
    result.update({paper_page(path): paper_document(path) for path in paper_audit()["source"]["source_hashes"]
                   if path.endswith(".tex")})
    verify_outputs(result, sources, parsed)
    return result


def verify_outputs(result, sources, parsed):
    """Check source fidelity, statement-only panes, anchors and local resources."""
    from verify_site import Page
    from test_latent_diffusion_landing import validate_landing
    validate_landing(result[PAGE], paper_audit())
    html_pages = {}
    for path, value in result.items():
        if path.endswith(".html"):
            doc = Page()
            doc.feed(value)
            html_pages[path] = doc
            if len(doc.ids) != len(set(doc.ids)):
                raise ValueError("Duplicate HTML IDs: " + path)
            if "katex-error" in value:
                raise ValueError("Invalid rendered mathematics: " + path)
            for block in doc.blocks:
                source = block["data-source"]
                start, end = int(block["data-start"]), int(block["data-end"])
                expected = sources[source].splitlines()[start - 1:end]
                if block["data-role"] == "statement":
                    decl = parsed[source][block["data-declaration"]]
                    if (start, end) != (decl["start"], decl["marker"]):
                        raise ValueError("Truncated theorem header: " + source)
                    expected = header_lines(sources[source], decl)
                if block["lines"] != expected:
                    raise ValueError(f"Altered source excerpt: {path}:{source}:{start}-{end}")
                if path == PAGE and block["data-role"] not in ("statement", "premise", "contract"):
                    raise ValueError("Proof body on statement page: " + source)
    for path, doc in html_pages.items():
        for href in doc.links + doc.resources:
            parts = urlsplit(href)
            if parts.scheme or parts.netloc:
                if href in doc.resources:
                    raise ValueError("Network-dependent resource: " + href)
                continue
            destination = (ROOT / path).parent / unquote(parts.path) if parts.path else ROOT / path
            destination = destination.resolve()
            target = destination.relative_to(ROOT).as_posix()
            if target not in result and not destination.is_file():
                raise ValueError(f"Broken local link: {path}: {href}")
            if parts.fragment and destination.suffix == ".html":
                linked = html_pages.get(target)
                if linked is None:
                    linked = Page()
                    linked.feed(destination.read_text())
                if unquote(parts.fragment) not in linked.ids:
                    raise ValueError(f"Broken local anchor: {path}: {href}")



def authoring_inputs():
    sources, _ = source_inventory()
    return ["docs/build_latent_diffusion.py", "docs/latent_diffusion_paper.py", "docs/test_latent_diffusion_landing.py",
            "scripts/verify-latent-diffusion.py", AUDIT] + list(paper_audit()["source"]["source_hashes"]) + list(sources) + sorted(
        p.relative_to(ROOT).as_posix()
        for p in (ROOT / "LatentDiffusion").rglob("*.md"))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="verify generated files without writing")
    args = parser.parse_args()
    expected = outputs()
    if args.check:
        stale = [path for path, value in expected.items() if not (ROOT / path).is_file() or (ROOT / path).read_text() != value]
        if stale:
            raise SystemExit("Stale latent-diffusion exposition: " + ", ".join(stale))
        print(f"Latent-diffusion exposition matches its Lean sources ({len(expected)} files).")
    else:
        for path, value in expected.items():
            target = ROOT / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(value)
        print(f"Built latent-diffusion statements, proof pages and source inventory ({len(expected)} files).")


if __name__ == "__main__":
    main()
