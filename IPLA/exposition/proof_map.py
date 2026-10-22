"""Offline, source-linked roadmap of the formally proved IPLA theorem."""
from __future__ import annotations

import html
import json
import posixpath
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent

# This is a logical proof roadmap, rather than a graph of Lean import commands.
NODES = [
    dict(id="assumptions", x=355, y=24, kind="input",
         title="Joint potential + Gaussian noise",
         detail=r"\(m\)-strong convexity · \(L\)-Lipschitz gradient",
         file="IPLA/Model.lean", declaration="GaussianInnovations"),
    dict(id="geometry", x=25, y=210, kind="ipla",
         title="Lift and rescale the particles",
         detail=r"\(Nm,NL\) · dimension \(d_\theta+Nd_x\)",
         file="IPLA/Geometry.lean", declaration="potential_strongConvex"),
    dict(id="algorithm", x=25, y=360, kind="ipla",
         title="Identify the actual algorithm",
         detail=r"IPLA law = ULA law, step \(\gamma/N\)",
         file="IPLA/ULAAdapter.lean", declaration="laws_eq_ulaLawStep"),
    dict(id="gibbs", x=355, y=210, kind="ula",
         title="Gibbs normalization and moments",
         detail=r"Positive finite partition · finite \(L^2\) moments",
         file="UnadjustedLangevin/Gibbs.lean",
         declaration="isProbabilityMeasure_gibbsMeasure"),
    dict(id="mala", x=355, y=360, kind="ula",
         title="Exact Metropolis invariance",
         detail="Gaussian density + detailed balance",
         file="UnadjustedLangevin/MALAInvariance.lean",
         declaration="malaOneStep_gibbs_invariant"),
    dict(id="stationarity", x=355, y=510, kind="ula",
         title="Prove continuous Gibbs stationarity",
         detail="Vanishing rejection cost + Euler limit",
         file="UnadjustedLangevin/GibbsStationarity.lean",
         declaration="lp_langevin_gibbs_stationary"),
    dict(id="dalalyan", x=355, y=660, kind="ula",
         title="Dalalyan’s coupling estimate",
         detail=r"Contraction · local error · \(W_2\) infimum",
         file="UnadjustedLangevin/HilbertDalalyan.lean",
         declaration="dalalyan_small_step_of_integral_reference"),
    dict(id="canonical", x=355, y=810, kind="ula",
         title="Shared Gaussian ULA theorem",
         detail=r"Actual Gaussian chain · initial \(W_2\) derived",
         file="UnadjustedLangevin/GaussianULA.lean",
         declaration="dalalyan_of_gaussian_innovations"),
    dict(id="marginal", x=685, y=210, kind="concentration",
         title="Compute the parameter marginal",
         detail=r"\(\Pi_N\) projected to \(\theta\): density \(\propto\ell_y(\theta)^N\)",
         file="IPLA/MarginalConcentration.lean",
         declaration="gibbsTarget_parameter_marginal"),
    dict(id="log-concavity", x=685, y=360, kind="concentration",
         title="Derive marginal strong convexity",
         detail=r"Prékopa: \(F(\theta)=-\log\ell_y(\theta)\) is \(m\)-convex",
         file="IPLA/StrongLogConcavity.lean",
         declaration="marginalPotential_strongConvex"),
    dict(id="gibbs-moment", x=685, y=510, kind="ula",
         title="Shared Gibbs moment estimate",
         detail=r"Dimension \(d_\theta\) · curvature \(Nm\) · mode \(\theta_\star\)",
         file="UnadjustedLangevin/GibbsConcentration.lean",
         declaration="integral_sq_dist_gibbs_le_of_continuous_strongConvex_mode"),
    dict(id="concentration", x=685, y=810, kind="concentration",
         title="Prove the equilibrium radius",
         detail=r"Parameter RMS \(\le\sqrt{2d_\theta/(Nm)}\)",
         file="IPLA/Concentration.lean",
         declaration="gibbsTarget_parameter_concentration"),
    dict(id="projection", x=25, y=1000, kind="ula",
         title="Project the parameter and constants",
         detail=r"Norm \(\le1\) · exact dimension and step factors",
         file="UnadjustedLangevin/Projection.lean",
         declaration="projectedRMSReal_le_wasserstein2Real_add"),
    dict(id="theorem", x=355, y=1150, kind="final",
         title="General-dimension IPLA bound",
         detail=r"Independent \(d_\theta,d_x\) · zero dimensions included",
         file="IPLA/Theorem.lean", declaration="theorem1"),
]

EDGES = [
    ("assumptions", "geometry", "M 355 74 H 175 V 210"),
    ("assumptions", "gibbs", "M 505 124 V 210"),
    ("assumptions", "marginal", "M 655 74 H 835 V 210"),
    ("geometry", "algorithm", "M 175 310 V 360"),
    ("gibbs", "mala", "M 505 310 V 360"),
    ("mala", "stationarity", "M 505 460 V 510"),
    ("stationarity", "dalalyan", "M 505 610 V 660"),
    ("dalalyan", "canonical", "M 505 760 V 810"),
    ("geometry", "canonical", "M 325 260 H 340 V 860 H 355"),
    ("marginal", "log-concavity", "M 835 310 V 360"),
    ("log-concavity", "gibbs-moment", "M 835 460 V 510"),
    ("gibbs-moment", "concentration", "M 835 610 V 810"),
    ("marginal", "concentration", "M 985 260 H 1005 V 860 H 985"),
    ("algorithm", "projection", "M 175 460 V 1000"),
    ("canonical", "projection", "M 505 910 V 960 H 225 V 1000"),
    ("concentration", "projection", "M 835 910 V 980 H 280 V 1000"),
    ("projection", "theorem", "M 175 1100 V 1200 H 355"),
]

SVG_CSS = """
.proof-edge{fill:none;stroke:#7e929d;stroke-width:1.8;marker-end:url(#proof-arrow)}
.proof-node rect{fill:#fff;stroke:#b7c6ce;stroke-width:1.5}
.proof-node.ipla rect{fill:#f0f7ee;stroke:#86aa80}
.proof-node.ula rect{fill:#edf7fa;stroke:#82aebc}
.proof-node.concentration rect{fill:#f6f0fc;stroke:#ad94c1}
.proof-node.final rect{fill:#143747;stroke:#143747}
.proof-node text{font-family:system-ui,sans-serif;fill:#18313f}
.proof-node .node-title{font-size:15px;font-weight:650}
.proof-node .node-detail{font-size:11.5px;fill:#4f6674}
.proof-node .node-file{font:11.5px ui-monospace,monospace;fill:#006c7a;text-decoration:underline}
.proof-node.final text{fill:#fff}
.proof-node-label{height:100%;display:flex;flex-direction:column;justify-content:space-between;gap:3px;font:14px/1.25 system-ui,sans-serif;color:#18313f;pointer-events:none}
.proof-node-label .node-title{font-size:14px;overflow-wrap:anywhere}
.proof-node-label .node-detail{font-size:11.5px;line-height:1.4;color:#4f6674}
.proof-node-label .node-file{font:10.5px/1.3 ui-monospace,monospace;color:#006c7a;text-decoration:underline;overflow-wrap:anywhere}
.proof-node-label .katex{font-size:1em}
.proof-node.final .proof-node-label,.proof-node.final .node-detail,.proof-node.final .node-file{color:#fff}
.proof-node:hover rect,.proof-node:focus-visible rect{stroke:#00596b;stroke-width:3}
.proof-node:focus-visible{outline:none}
.proof-lane{font:600 12px system-ui,sans-serif;letter-spacing:1.1px;fill:#49606e}
"""


def lean_link(path, label=None, declaration=None):
    href = posixpath.relpath(path, "IPLA/exposition")
    target = (' data-declaration="' + html.escape(declaration, quote=True) + '"'
              if declaration else "")
    return ('<a href="' + html.escape(href, quote=True) +
            '" data-lean-source="' + html.escape(path, quote=True) + '"' + target + '>' +
            html.escape(label or path) + '</a>')


def diagram_svg(sources, math):
    files = dict(sources)
    ids = {node["id"] for node in NODES}
    for node in NODES:
        if node["file"] not in files:
            raise ValueError("Proof-map source is outside the theorem closure: " + node["file"])
        if not re.search(r"\b(?:theorem|def|structure|abbrev)\s+" +
                         re.escape(node["declaration"]) + r"\b", files[node["file"]]):
            raise ValueError("Missing proof-map declaration: " + str(node))
    if any(a not in ids or b not in ids for a, b, _ in EDGES):
        raise ValueError("Unknown proof-map endpoint")
    parts = [
        '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1030 1274" '
        'class="proof-svg" role="group" aria-labelledby="proof-map-title proof-map-description">',
        '<title id="proof-map-title">Proof of the general-dimension IPLA theorem</title>',
        '<desc id="proof-map-description">Fourteen linked boxes trace the joint assumptions '
        'through IPLA geometry, the shared ULA theorem and Gibbs stationarity, and '
        'marginal concentration. These branches meet in projection and exact scaling, '
        'then the final theorem. Every box opens an HTML proof page with its Lean source.</desc>',
        '<style>' + SVG_CSS + '</style>',
        '<defs><marker id="proof-arrow" viewBox="0 0 10 10" refX="9" refY="5" '
        'markerWidth="6" markerHeight="6" orient="auto-start-reverse">'
        '<path d="M 0 0 L 10 5 L 0 10 z" fill="#7e929d"/></marker></defs>',
        '<text class="proof-lane" x="25" y="181">IPLA GEOMETRY + LAWS</text>',
        '<text class="proof-lane" x="355" y="181">SHARED ULA PROOF</text>',
        '<text class="proof-lane" x="685" y="181">PARAMETER CONCENTRATION</text>',
    ]
    for start, end, route in EDGES:
        parts.append(f'<path class="proof-edge" data-from="{start}" data-to="{end}" d="{route}"/>')
    for node in NODES:
        x, y = node["x"], node["y"]
        href = posixpath.relpath("docs/modules/" + node["file"].removesuffix(".lean") + ".html", "IPLA/exposition")
        parts.append(
            '<a class="proof-node ' + node["kind"] + '" id="proof-' + node["id"] +
            '" href="' + html.escape(href, quote=True) + '" data-declaration="' +
            html.escape(node["declaration"], quote=True) + '" tabindex="0" '
            'aria-label="' + html.escape(node["title"] + ". Open " + node["file"], quote=True) +
            f'"><title>{html.escape(node["file"] + " · " + node["declaration"])}</title>'
            f'<rect x="{x}" y="{y}" width="300" height="112" rx="10"/>'
            f'<foreignObject x="{x+14}" y="{y+10}" width="272" height="92">'
            '<div xmlns="http://www.w3.org/1999/xhtml" class="proof-node-label">'
            f'<div class="node-title">{html.escape(node["title"])}</div>'
            f'<div class="node-detail">{html.escape(node["detail"])}</div>'
            f'<div class="node-file">{html.escape(Path(node["file"]).name)} ↗</div>'
            '</div></foreignObject></a>')
    return math("\n".join(parts) + "\n</svg>")


def proof_map_section(sources, math, katex_styles):
    svg = diagram_svg(sources, math)
    # Embed fonts in the downloadable SVG as well as in the enclosing HTML.
    (HERE / "proof-map.svg").write_text(svg.replace('<style>', '<style>'+katex_styles, 1))
    groups = [
        ("IPLA", "IPLA geometry and concentration"),
        ("UnadjustedLangevin", "Shared ULA"),
    ]
    catalog = []
    for prefix, label in groups:
        entries = [(p, s) for p, s in sources if p.startswith(prefix + "/")]
        catalog.append('<section><h4>' + html.escape(label) + '</h4><ul>')
        catalog.extend('<li>' + lean_link(path, Path(path).name) + '</li>' for path, _ in entries)
        catalog.append('</ul></section>')
    supplements = [
        ("IPLA/Dynamics.lean", "Physical θ and x updates"),
        ("IPLA/Scaling.lean", "Exact constants and step size"),
        ("UnadjustedLangevin/CanonicalULA.lean", "Shared law-level ULA estimate"),
        ("UnadjustedLangevin/MALACoupling.lean", "Rejection-cost coupling"),
        ("UnadjustedLangevin/EulerLimit.lean", "Euler convergence"),
        ("UnadjustedLangevin/GibbsScore.lean", "Gibbs score moment"),
        ("UnadjustedLangevin/CanonicalBrownian.lean", "Brownian source"),
        ("IPLA/PrekopaTensorization.lean", "Finite-dimensional Prékopa"),
        ("IPLA/Degenerate.lean", "Zero-dimensional cases"),
    ]
    extra_links = " · ".join(lean_link(path, label) for path, label in supplements)
    return (
        '<section id="proof-map" aria-labelledby="proof-map-heading">'
        '<h2 id="proof-map-heading">Proof map — follow the Lean files</h2>'
        '<p>Read downward from the joint assumptions. The blue boxes are the shared ULA '
        'results; the green and purple boxes supply the IPLA geometry and statistical '
        'marginal argument. Select any box to open its proof page and exact Lean source. '
        'The arrows describe the mathematical argument, rather than every import.</p>'
        '<div class="proof-legend"><span class="legend-ipla">IPLA geometry and laws</span>'
        '<span class="legend-ula">Shared ULA</span>'
        '<span class="legend-concentration">Parameter concentration</span></div>'
        '<figure class="proof-figure"><div class="proof-scroll" tabindex="0" '
        'aria-label="Scrollable, linked proof diagram">' + svg +
        '</div><figcaption>Boxes open the mathematical proof and Lean declarations; '
        'each proof page also links the .lean file. On narrow screens, scroll the diagram horizontally. '
        '<a href="proof-map.svg" target="_blank" rel="noopener">Open the SVG diagram</a>.'
        '</figcaption></figure>'
        '<p class="proof-support"><strong>Supporting files:</strong> ' + extra_links + '.</p>'
        '<p class="proof-note"><strong>The stationarity step is a proved limit argument.</strong> '
        'Exact MALA invariance, coupling bounds and the Euler limit establish the law of the '
        'continuous solution. Generator integration is documented separately below.</p>'
        '<details id="lean-files" class="source-library"><summary>Browse all ' +
        str(len(sources)) + ' Lean source files</summary><div class="source-groups">' +
        ''.join(catalog) + '</div></details></section>'
    )


def page_css():
    return """
.proof-legend{display:flex;flex-wrap:wrap;gap:10px;font-size:13px;margin:20px 0}
.proof-legend span{padding:4px 11px;border:1px solid;border-radius:20px}
.legend-ipla{background:#f0f7ee;border-color:#86aa80!important}
.legend-ula{background:#edf7fa;border-color:#82aebc!important}
.legend-concentration{background:#f6f0fc;border-color:#ad94c1!important}
.proof-figure{margin:0;border:1px solid #dce4e8;border-radius:12px;background:#fbfdfe;overflow:hidden}
.proof-scroll{overflow-x:auto;padding:15px}
.proof-svg{display:block;width:100%;min-width:840px;height:auto}
.proof-figure figcaption{padding:14px 20px;border-top:1px solid #dce4e8;color:#4f6674;font-size:13px}
.proof-support{font-size:14px;line-height:1.9}
.proof-note{background:#edf7fa;border-left:3px solid #82aebc;padding:14px 18px;font-size:15px}
.source-library{margin:22px 0;padding:16px 20px;border:1px solid #dce4e8;border-radius:8px}
.source-library summary{font-weight:600;cursor:pointer}
.source-groups{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:20px;margin-top:15px}
.source-groups h4{margin:6px 0;font-size:15px}
.source-groups ul{list-style:none;margin:0;padding:0}
.source-groups li{font:12px/1.9 ui-monospace,monospace;overflow-wrap:anywhere}
.lean-dialog{width:min(1100px,calc(100vw - 48px));max-height:86vh;padding:0;border:1px solid #748e9b;border-radius:12px;color:#18313f}
.lean-dialog::backdrop{background:rgb(10 29 41 / .65)}
.source-toolbar{display:flex;align-items:center;justify-content:space-between;gap:20px;padding:17px 22px;background:#f0f6f8;border-bottom:1px solid #dce4e8}
.source-toolbar h2{font:600 16px/1.4 ui-monospace,monospace;margin:0;padding:0;border:0;overflow-wrap:anywhere}
.source-actions{display:flex;align-items:center;gap:18px;white-space:nowrap;font-size:14px}
.source-actions button{border:1px solid #819ca8;border-radius:6px;background:#fff;color:#18313f;font:inherit;padding:7px 12px;cursor:pointer}
.source-actions button:focus-visible,a:focus-visible{outline:3px solid #007d91;outline-offset:4px}
.source-position{margin:0;padding:8px 22px;background:#fff;font-size:13px;color:#526875}
.source-code{margin:0;border-radius:0;max-height:65vh;overflow:auto;padding:20px 0;font:13px/1.65 ui-monospace,monospace;tab-size:2}
.source-line{display:block;padding:0 22px 0 0;min-width:max-content}
.source-line:before{content:attr(data-line);display:inline-block;width:4em;padding-right:1.5em;text-align:right;color:#8aa5b3;user-select:none}
.source-line.highlight{background:#294e60;box-shadow:inset 3px 0 #8ed8de}
@media(max-width:700px){.source-groups{grid-template-columns:1fr 1fr}.lean-dialog{width:calc(100vw - 20px);max-width:none}.source-toolbar{align-items:flex-start;padding:14px;gap:12px;flex-direction:column}.source-code{font-size:12px}.proof-scroll{padding:8px}}
@media print{.proof-svg{min-width:0}.proof-scroll{overflow:visible;padding:0}.proof-figure{break-inside:avoid}.lean-dialog{display:none}.source-library:not([open]){display:none}}
"""


def source_browser(sources):
    payload = json.dumps(dict(sources), ensure_ascii=False).replace("<", "\\u003c")
    return """
<dialog id="lean-source-dialog" class="lean-dialog" aria-labelledby="lean-source-title">
  <header class="source-toolbar">
    <h2 id="lean-source-title"></h2>
    <div class="source-actions"><a id="lean-source-raw" target="_blank" rel="noopener">Open .lean file ↗</a><button id="lean-source-close" type="button">Close</button></div>
  </header>
  <p id="lean-source-position" class="source-position"></p>
  <pre class="source-code" id="lean-source-code" tabindex="0" aria-label="Lean source with line numbers"><code id="lean-source-content"></code></pre>
</dialog>
<script id="lean-source-data" type="application/json">""" + payload + """</script>
<script>
(() => {
  const dialog = document.getElementById('lean-source-dialog');
  if (!dialog || typeof dialog.showModal !== 'function') return;
  const sources = JSON.parse(document.getElementById('lean-source-data').textContent);
  const content = document.getElementById('lean-source-content');
  const code = document.getElementById('lean-source-code');
  document.addEventListener('click', (event) => {
    const link = event.target.closest('a[data-lean-source]');
    if (!link || event.ctrlKey || event.metaKey || event.shiftKey || event.altKey) return;
    const path = link.dataset.leanSource;
    if (!(path in sources)) return;
    event.preventDefault();
    const declaration = link.dataset.declaration;
    const lines = sources[path].split('\\n');
    const first = declaration ? lines.findIndex(line =>
      ['theorem ', 'def ', 'structure ', 'abbrev '].some(kind => line.includes(kind + declaration))) : 0;
    content.replaceChildren();
    const fragment = document.createDocumentFragment();
    lines.forEach((line, index) => {
      const span = document.createElement('span');
      span.className = 'source-line' + (index === first ? ' highlight' : '');
      span.dataset.line = String(index + 1);
      span.textContent = line || ' ';
      fragment.appendChild(span);
    });
    content.appendChild(fragment);
    document.getElementById('lean-source-title').textContent = path;
    document.getElementById('lean-source-raw').href = link.getAttribute('href');
    document.getElementById('lean-source-position').textContent = declaration
      ? declaration + (first >= 0 ? ' · line ' + String(first + 1) : '')
      : 'Complete repository source · ' + String(lines.length) + ' lines';
    dialog.showModal();
    requestAnimationFrame(() => {
      const highlighted = content.querySelector('.highlight');
      code.scrollTop = highlighted ? Math.max(0, highlighted.offsetTop - code.offsetTop - 65) : 0;
      code.scrollLeft = 0;
    });
  });
  document.getElementById('lean-source-close').addEventListener('click', () => dialog.close());
  dialog.addEventListener('click', event => { if (event.target === dialog) dialog.close(); });
})();
</script>"""
