"""The mathematical dependencies of the IPLA parameter-error estimate."""
from __future__ import annotations

import html
import json
import posixpath
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent

# The arrows record mathematical dependencies between the stated results.
NODES = [
    dict(id="assumptions", x=355, y=24, kind="input",
         title="Joint potential and Gaussian innovations",
         detail=r"\(m\)-strong convexity and an \(L\)-Lipschitz gradient",
         file="IPLA/Model.lean", declaration="GaussianInnovations"),
    dict(id="geometry", x=25, y=210, kind="ipla",
         title="Scaled particle potential",
         detail=r"Curvature and gradient constants \(Nm,NL\); dimension \(d_\theta+Nd_x\)",
         file="IPLA/Geometry.lean", declaration="potential_strongConvex"),
    dict(id="algorithm", x=25, y=360, kind="ipla",
         title="Equality of particle and Euler laws",
         detail=r"IPLA and Gaussian Euler laws with step \(\gamma/N\)",
         file="IPLA/ULAAdapter.lean", declaration="laws_eq_ulaLawStep"),
    dict(id="gibbs", x=355, y=210, kind="ula",
         title="Gibbs normalization and second moments",
         detail=r"A positive finite partition and finite \(L^2\) moments",
         file="UnadjustedLangevin/Gibbs.lean",
         declaration="isProbabilityMeasure_gibbsMeasure"),
    dict(id="mala", x=355, y=360, kind="ula",
         title="Metropolis invariance of the Gibbs law",
         detail="Gaussian proposal density and detailed balance",
         file="UnadjustedLangevin/MALAInvariance.lean",
         declaration="malaOneStep_gibbs_invariant"),
    dict(id="stationarity", x=355, y=510, kind="ula",
         title="Stationarity of the Langevin law",
         detail="Vanishing rejection displacement and the Euler limit",
         file="UnadjustedLangevin/GibbsStationarity.lean",
         declaration="lp_langevin_gibbs_stationary"),
    dict(id="dalalyan", x=355, y=660, kind="ula",
         title="The synchronous coupling estimate",
         detail=r"Gradient contraction, local error, and the \(W_2\) infimum",
         file="UnadjustedLangevin/HilbertDalalyan.lean",
         declaration="dalalyan_small_step_of_integral_reference"),
    dict(id="canonical", x=355, y=810, kind="ula",
         title="Gaussian Euler transport convergence",
         detail=r"Independent Gaussian recursion and finite initial \(W_2\)",
         file="UnadjustedLangevin/GaussianULA.lean",
         declaration="dalalyan_of_gaussian_innovations"),
    dict(id="marginal", x=685, y=210, kind="concentration",
         title="The parameter Gibbs marginal",
         detail=r"Projection of \(\Pi_N\) onto \(\theta\) has density \(\propto\ell_y(\theta)^N\)",
         file="IPLA/MarginalConcentration.lean",
         declaration="gibbsTarget_parameter_marginal"),
    dict(id="log-concavity", x=685, y=360, kind="concentration",
         title="Strong convexity after latent integration",
         detail=r"Prékopa–Leindler gives \(F(\theta)=-\log\ell_y(\theta)\) with curvature \(m\)",
         file="IPLA/StrongLogConcavity.lean",
         declaration="marginalPotential_strongConvex"),
    dict(id="gibbs-moment", x=685, y=510, kind="ula",
         title="The Gibbs moment about its mode",
         detail=r"Dimension \(d_\theta\), curvature \(Nm\), and mode \(\theta_\star\)",
         file="UnadjustedLangevin/GibbsConcentration.lean",
         declaration="integral_sq_dist_gibbs_le_of_continuous_strongConvex_mode"),
    dict(id="concentration", x=685, y=810, kind="concentration",
         title="The equilibrium parameter radius",
         detail=r"The parameter root mean square is \(\le\sqrt{2d_\theta/(Nm)}\)",
         file="IPLA/Concentration.lean",
         declaration="gibbsTarget_parameter_concentration"),
    dict(id="projection", x=25, y=1000, kind="ula",
         title="Parameter projection of transport",
         detail=r"Projection norm \(\le1\) and the scaled dimension and step",
         file="UnadjustedLangevin/Projection.lean",
         declaration="projectedRMSReal_le_wasserstein2Real_add"),
    dict(id="theorem", x=355, y=1150, kind="final",
         title="The IPLA parameter-error estimate",
         detail=r"Arbitrary \(d_\theta,d_x\), including zero dimensions",
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
        '<desc id="proof-map-description">The joint assumptions imply the scaled-potential regularity, '
        'Gaussian Euler transport estimate, and parameter concentration. '
        'Parameter projection and the coordinate scaling combine these estimates '
        'in the final inequality. Each item links its mathematical proof and formal source.</desc>',
        '<style>' + SVG_CSS + '</style>',
        '<defs><marker id="proof-arrow" viewBox="0 0 10 10" refX="9" refY="5" '
        'markerWidth="6" markerHeight="6" orient="auto-start-reverse">'
        '<path d="M 0 0 L 10 5 L 0 10 z" fill="#7e929d"/></marker></defs>',
        '<text class="proof-lane" x="25" y="181">PARTICLE GEOMETRY AND LAWS</text>',
        '<text class="proof-lane" x="355" y="181">GAUSSIAN EULER ESTIMATES</text>',
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


def diagram_html(math):
    """Native HTML math remains readable and correctly positioned on iOS."""
    ordered = sorted(NODES, key=lambda node: (node['y'], node['x']))
    numbers = {node['id']: i for i, node in enumerate(ordered, 1)}
    by_id = {node['id']: node for node in ordered}
    rows = {y: i for i, y in enumerate(sorted({node['y'] for node in ordered}), 1)}
    columns = {25: 1, 355: 2, 685: 3}
    parts = ['<ol class="proof-card-grid" data-proof-grid>']
    for node in ordered:
        parents = [start for start, end, _ in EDGES if end == node['id']]
        href = posixpath.relpath('docs/modules/' + node['file'].removesuffix('.lean') + '.html', 'IPLA/exposition')
        parts.append(
            f'<li class="proof-card {node["kind"]}" id="proof-step-{node["id"]}" '
            f'data-node="{node["id"]}" data-parents="{" ".join(parents)}" '
            f'style="--proof-row:{rows[node["y"]]};--proof-col:{columns[node["x"]]}">'
            + f'<a class="proof-node" href="{html.escape(href, quote=True)}" '
            f'data-declaration="{html.escape(node["declaration"], quote=True)}" '
            f'aria-label="{html.escape(node["title"] + ". Open " + node["file"], quote=True)}">'
            '<div class="proof-node-label">'
            f'<div class="node-step">Step {numbers[node["id"]]:02}</div>'
            f'<div class="node-title">{math(html.escape(node["title"]))}</div>'
            f'<div class="node-detail">{math(html.escape(node["detail"]))}</div>'
            f'<div class="node-file">{html.escape(Path(node["file"]).name)} ↗</div></div></a>')
        if parents:
            parts.append('<div class="proof-card-parents"><span>Uses</span>')
            for parent in parents:
                title = html.escape(by_id[parent]['title'], quote=True)
                parts.append(f'<a href="#proof-step-{parent}" title="{title}" '
                             f'aria-label="Uses step {numbers[parent]}: {title}">{numbers[parent]:02}</a>')
            parts.append('</div>')
        parts.append('</li>')
    return ''.join(parts) + '</ol>'


def diagram_script():
    # Keep the archived document self-contained, including local file:// use.
    script = (Path(__file__).resolve().parents[2] / 'docs/assets/diagrams.js').read_text()
    return '<script>' + script + '</script>'


def proof_map_section(sources, math, katex_styles):
    svg = diagram_svg(sources, math)
    # Embed fonts in the downloadable SVG as well as in the enclosing HTML.
    (HERE / "proof-map.svg").write_text(svg.replace('<style>', '<style>'+katex_styles, 1))
    groups = [
        ("IPLA", "Particle geometry and concentration"),
        ("UnadjustedLangevin", "Gaussian Euler estimates"),
    ]
    catalog = []
    for prefix, label in groups:
        entries = [(p, s) for p, s in sources if p.startswith(prefix + "/")]
        catalog.append('<section><h4>' + html.escape(label) + '</h4><ul>')
        catalog.extend('<li>' + lean_link(path, Path(path).name) + '</li>' for path, _ in entries)
        catalog.append('</ul></section>')
    supplements = [
        ("IPLA/Dynamics.lean", "Physical parameter and latent updates"),
        ("IPLA/Scaling.lean", "Scaled constants and step restriction"),
        ("UnadjustedLangevin/CanonicalULA.lean", "Gaussian Euler transport estimate"),
        ("UnadjustedLangevin/MALACoupling.lean", "Metropolis rejection displacement"),
        ("UnadjustedLangevin/EulerLimit.lean", "Euler convergence"),
        ("UnadjustedLangevin/GibbsScore.lean", "Gibbs score second moment"),
        ("UnadjustedLangevin/CanonicalBrownian.lean", "Brownian source"),
        ("IPLA/PrekopaTensorization.lean", "Finite-dimensional Prékopa–Leindler"),
        ("IPLA/Degenerate.lean", "Zero-dimensional cases"),
    ]
    extra_links = " · ".join(lean_link(path, label) for path, label in supplements)
    return (
        '<section id="proof-map" aria-labelledby="proof-map-heading">'
        '<h2 id="proof-map-heading">Dependencies of the parameter-error estimate</h2>'
        '<p>The joint-potential and innovation assumptions imply the scaled particle '
        'geometry, the Gaussian Euler transport estimate, and the Gibbs parameter '
        'concentration. Projection combines the transport and concentration terms. '
        'Each link gives the corresponding proof and formal statement.</p>'
        '<div class="proof-legend"><span class="legend-ipla">IPLA geometry and laws</span>'
        '<span class="legend-ula">Gaussian Euler estimates</span>'
        '<span class="legend-concentration">Parameter concentration</span></div>'
        '<figure class="proof-figure"><div class="proof-scroll" data-proof-diagram role="group" '
        'aria-label="Linked proof diagram">' + diagram_html(math) +
        '</div><figcaption>Boxes open the mathematical proof and Lean declarations; '
        'each proof page also links the .lean file. The diagram reflows on smaller screens; '
        '“Uses” links identify the exact prerequisite steps. '
        '<a href="proof-map.svg" target="_blank" rel="noopener">Open the SVG diagram</a>.'
        '</figcaption></figure>'
        '<p class="proof-support"><strong>Supporting files:</strong> ' + extra_links + '.</p>'
        '<p class="proof-note"><strong>Stationarity follows by a limit of invariant adjusted chains.</strong> '
        'Metropolis invariance, the rejection-displacement comparison, and Euler convergence identify the law of the '
        'Langevin integral solution. The separate generator integration identity does not alone prove this stationarity.</p>'
        '<details id="lean-files" class="source-library"><summary>Browse all ' +
        str(len(sources)) + ' Lean source files</summary><div class="source-groups">' +
        ''.join(catalog) + '</div></details></section>' + diagram_script()
    )


def page_css():
    return """
.proof-legend{display:flex;flex-wrap:wrap;gap:10px;font-size:13px;margin:20px 0}
.proof-legend span{padding:4px 11px;border:1px solid;border-radius:20px}
.legend-ipla{background:#f0f7ee;border-color:#86aa80!important}
.legend-ula{background:#edf7fa;border-color:#82aebc!important}
.legend-concentration{background:#f6f0fc;border-color:#ad94c1!important}
.proof-figure{margin:0;border:1px solid #dce4e8;border-radius:12px;background:#fbfdfe;overflow:hidden}
.proof-scroll{position:relative;isolation:isolate;padding:20px;min-width:0}
.proof-card-grid{position:relative;z-index:1;display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:28px 20px;list-style:none;padding:0;margin:0}
.proof-card{position:relative;grid-row:var(--proof-row);grid-column:var(--proof-col);min-width:0;display:flex;flex-direction:column;border:1px solid var(--diagram-line,#b7c6ce);border-radius:9px;background:var(--diagram-node-bg,#fff);scroll-margin-top:24px}
.proof-card>.proof-node{display:block;flex:1;min-width:0;padding:16px;color:var(--diagram-node-ink,#18313f);text-decoration:none;border-radius:8px}
.proof-card>.proof-node:hover{background:var(--wash,#edf7fa)}
.proof-card .proof-node-label{display:flex;flex-direction:column;gap:9px;font:14px/1.5 system-ui,sans-serif;min-width:0}
.proof-card .node-step{font-size:10px;font-weight:700;letter-spacing:.09em;text-transform:uppercase;color:var(--diagram-muted,#4f6674)}
.proof-card .node-title{font-weight:650;overflow-wrap:anywhere}
.proof-card .node-detail{font-size:13px;line-height:1.6;color:var(--diagram-muted,#4f6674);overflow-wrap:anywhere}
.proof-card .node-file{font:11px/1.5 ui-monospace,monospace;color:var(--accent,#006c7a);overflow-wrap:anywhere}
.proof-card .katex{font-size:1em}
.proof-card-parents{display:flex;flex-wrap:wrap;align-items:center;gap:7px;padding:9px 16px;border-top:1px solid var(--diagram-line,#b7c6ce);font-size:11px;color:var(--diagram-muted,#4f6674)}
.proof-card-parents a{display:inline-flex;align-items:center;justify-content:center;min-width:32px;min-height:32px;border:1px solid var(--diagram-line,#b7c6ce);border-radius:4px;background:var(--diagram-node-bg,#fff);font-variant-numeric:tabular-nums;text-decoration:none}
.proof-card.ipla{border-top:3px solid #86aa80}.proof-card.ula{border-top:3px solid #82aebc}.proof-card.concentration{border-top:3px solid #ad94c1}.proof-card.final{border:2px solid var(--accent,#006c7a);background:var(--wash,#edf7fa)}
.proof-card:target{outline:3px solid var(--gold,#b47c30);outline-offset:4px}
@media(max-width:1000px){.proof-card-grid{grid-template-columns:repeat(2,minmax(0,1fr))}.proof-card{grid-row:auto;grid-column:auto}}
@media(max-width:600px){.proof-card-grid{grid-template-columns:minmax(0,1fr)}.proof-card .proof-node-label{font-size:15px}.proof-card .node-detail{font-size:14px}.proof-card .node-file{font-size:12px}}
@media(pointer:coarse){.proof-card-parents a{min-height:44px;min-width:44px}}
.proof-scroll>.diagram-connectors{position:absolute;inset:0;width:100%;height:100%;pointer-events:none;z-index:0;overflow:visible}
.proof-scroll .diagram-connector{fill:none;stroke:var(--diagram-muted,#63716b);stroke-width:1.6;stroke-linejoin:round;opacity:.9}
.proof-scroll .diagram-arrowhead{fill:var(--diagram-muted,#63716b)}
@media(max-width:600px){.proof-scroll>.diagram-connectors{display:none}}
@media print{.proof-scroll>.diagram-connectors{display:none}}
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
.archive-code-actions{display:flex;justify-content:flex-end;margin-top:1rem}.archive-code pre{margin-top:.5rem}.archive-copy,.source-actions button{border:1px solid #819ca8;border-radius:6px;background:#fff;color:#18313f;font:inherit;padding:7px 12px;cursor:pointer}
.archive-copy:focus-visible,.source-actions button:focus-visible,a:focus-visible{outline:3px solid #007d91;outline-offset:4px}
.archive-copy-status{position:fixed;bottom:1rem;left:50%;transform:translateX(-50%);z-index:20;background:#18313f;color:#fff;padding:.6rem 1rem;border-radius:5px;font:13px/1.5 system-ui,sans-serif}.archive-copy-status:empty{display:none}.source-copy-status{font-size:13px;margin:0;padding:0 22px}.source-copy-status:empty{display:none}.source-position{margin:0;padding:8px 22px;background:#fff;font-size:13px;color:#526875}
.source-code{margin:0;border-radius:0;max-height:65vh;overflow:auto;padding:20px 0;font:13px/1.65 ui-monospace,monospace;tab-size:2}
.source-line{display:block;padding:0 22px 0 0;min-width:max-content}
.source-line:before{content:attr(data-line);display:inline-block;width:4em;padding-right:1.5em;text-align:right;color:#8aa5b3;user-select:none}
.source-line.highlight{background:#294e60;box-shadow:inset 3px 0 #8ed8de}
@media(max-width:700px){.source-groups{grid-template-columns:1fr 1fr}.lean-dialog{width:calc(100vw - 20px);max-width:none}.source-toolbar{align-items:flex-start;padding:14px;gap:12px;flex-direction:column}.source-code{font-size:12px}.proof-scroll{padding:8px}}
@media print{.archive-code-actions,.archive-copy-status{display:none}.proof-svg{min-width:0}.proof-scroll{overflow:visible;padding:0}.proof-figure{break-inside:avoid}.lean-dialog{display:none}.source-library:not([open]){display:none}}
"""


def source_browser(sources):
    payload = json.dumps(dict(sources), ensure_ascii=False).replace("<", "\\u003c")
    return """
<dialog id="lean-source-dialog" class="lean-dialog" aria-labelledby="lean-source-title">
  <header class="source-toolbar">
    <h2 id="lean-source-title"></h2>
    <div class="source-actions"><button id="lean-source-copy" type="button">Copy file</button><a id="lean-source-raw" target="_blank" rel="noopener">Open .lean file ↗</a><button id="lean-source-close" type="button">Close</button></div>
  </header>
  <p id="lean-source-position" class="source-position"></p>
  <p id="lean-source-copy-status" class="source-copy-status" role="status" aria-live="polite"></p>
  <pre class="source-code" id="lean-source-code" tabindex="0" aria-label="Lean source with line numbers"><code id="lean-source-content"></code></pre>
</dialog>
<p id="lean-copy-status" class="archive-copy-status" role="status" aria-live="polite"></p>
<script id="lean-source-data" type="application/json">""" + payload + """</script>
<script>
(() => {
  const dialog = document.getElementById('lean-source-dialog');
  const sources = JSON.parse(document.getElementById('lean-source-data').textContent);
  const content = document.getElementById('lean-source-content');
  const code = document.getElementById('lean-source-code');
  let currentSource = null;
  let statusTimer;
  function fallbackCopy(text) {
    const active = document.activeElement;
    const selection = window.getSelection();
    const ranges = selection ? Array.from({ length: selection.rangeCount }, (_, i) => selection.getRangeAt(i).cloneRange()) : [];
    const area = document.createElement('textarea');
    area.value = text;
    area.readOnly = true;
    area.setAttribute('aria-label', 'Lean code to copy');
    Object.assign(area.style, { position: 'fixed', top: '0', left: '0', width: '1px', height: '1px', opacity: '0' });
    // A modal dialog makes the document body inert, so keep its fallback inside the dialog.
    (dialog && dialog.open ? dialog : document.body).appendChild(area);
    let copied = false;
    try {
      area.focus({ preventScroll: true });
      area.select();
      area.setSelectionRange(0, area.value.length);
      copied = typeof document.execCommand === 'function' && document.execCommand('copy');
    } finally {
      area.remove();
      if (active && typeof active.focus === 'function') active.focus({ preventScroll: true });
      if (selection) {
        selection.removeAllRanges();
        ranges.forEach(range => selection.addRange(range));
      }
    }
    return copied;
  }
  async function copyText(text, button) {
    let copied = false;
    try {
      if (navigator.clipboard && typeof navigator.clipboard.writeText === 'function') {
        try { await navigator.clipboard.writeText(text); copied = true; } catch (_) { /* File previews may need selection copying. */ }
      }
      if (!copied) copied = fallbackCopy(text);
    } catch (_) { /* Report copy restrictions without losing the displayed source. */ }
    const originalLabel = button.dataset.copyLabel || button.textContent;
    button.dataset.copyLabel = originalLabel;
    clearTimeout(button.copyResetTimer);
    button.textContent = copied ? 'Copied' : 'Copy unavailable';
    button.copyResetTimer = setTimeout(() => { button.textContent = originalLabel; }, 2500);
    const status = document.getElementById(dialog && dialog.open ? 'lean-source-copy-status' : 'lean-copy-status');
    clearTimeout(statusTimer);
    status.textContent = copied ? 'Code copied.' : 'Copy is unavailable in this browser. Open the source file to copy it.';
    statusTimer = setTimeout(() => { status.textContent = ''; }, 5000);
  }
  document.querySelectorAll('.archive-copy').forEach(button => {
    button.addEventListener('click', () => {
      const source = button.closest('.archive-code').querySelector('pre code');
      if (source) void copyText(source.textContent, button);
    });
  });
  if (!dialog || typeof dialog.showModal !== 'function') return;
  document.getElementById('lean-source-copy').addEventListener('click', event => {
    if (currentSource !== null) void copyText(currentSource, event.currentTarget);
  });
  document.addEventListener('click', (event) => {
    const link = event.target.closest('a[data-lean-source]');
    if (!link || event.ctrlKey || event.metaKey || event.shiftKey || event.altKey) return;
    const path = link.dataset.leanSource;
    if (!(path in sources)) return;
    event.preventDefault();
    currentSource = sources[path];
    document.getElementById('lean-source-copy-status').textContent = '';
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
