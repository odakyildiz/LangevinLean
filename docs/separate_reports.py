"""Proof reports for the two separately generated developments: PBGSO and latent diffusion.

Their pages have their own generators, but their reports follow the format of
the annotated libraries. Chapter 1 states the assumptions and main results
exactly as on the overview page, Chapter 2 gives the sequential mathematical
argument, and Chapter 3 proves the results behind the roadmap boxes. Every
statement, argument part and proof step is followed by the exact Lean
statement and an account of how the Lean proof follows it.
"""
from __future__ import annotations

import hashlib
import json
import re

from build_site import ROOT, latex_heading, latex_prose, latex_step_box, tex_escape
from report_citations import SEPARATE_REPORTS

TITLES = {'PBGSO': 'Particle-based Generalised Stochastic Optimisation',
          'LatentDiffusion': 'Training Latent Diffusion Models with Interacting Particle Algorithms'}


def inventory(library):
    if library == 'PBGSO':
        from build_pbgso import source_inventory
    else:
        from build_latent_diffusion import source_inventory
    return source_inventory()


def notes(library):
    path = ROOT / library / 'exposition/module_notes.json'
    return json.loads(path.read_text()) if path.is_file() else {}


def argument(library):
    path = ROOT / library / 'exposition/argument.json'
    data = json.loads(path.read_text()) if path.is_file() else {}
    return {'parts': data.get('parts', []), 'roadmap': data.get('roadmap', [])}


def statements(library, sources, parsed):
    """The assumptions and results of the overview, grouped into report sections."""
    if library == 'PBGSO':
        from pbgso_overview import overview_document
        rows = []
        overview_document(sources, parsed, lambda value: value, record=rows)
        groups = [('Setting and assumptions', [r for r in rows if r['kind'] != 'theorem' and not r['id'].startswith('numerical')]),
                  ('Main theorems of the paper', [r for r in rows if r['kind'] == 'theorem' and not r['id'].startswith('new')]),
                  ('Numerical setting and explicit constants', [r for r in rows if r['id'].startswith('numerical')]),
                  ('New discretisation bounds', [r for r in rows if r['kind'] == 'theorem' and r['id'].startswith('new')])]
        seen = {r['id'] for _, group in groups for r in group}
        missing = [r['id'] for r in rows if r['id'] not in seen]
        if missing:
            raise ValueError(f'PBGSO statements without a report section: {missing}')
        return [(heading, [(r['title'], r['content'], r['refs']) for r in group]) for heading, group in groups]
    from build_latent_diffusion import panels, paper_audit, source_endpoint_refs, result_label, source_status
    from latent_diffusion_paper import PAPER_RESULTS
    panel_list = panels()

    def section(name):
        return [(p['title'], p['prose'], [tuple(ref[:2]) for ref in p['refs']])
                for p in panel_list if p['section'] == name]
    results = []
    for record in paper_audit()['results']:
        entry = PAPER_RESULTS[record['id']]
        text = entry.get('statement', '')
        if entry.get('correction'):
            text += '<p><strong>Correction.</strong> ' + entry['correction'] + '</p>'
        text = '<p><strong>' + source_status(record) + '.</strong></p>' + text
        results.append((result_label(record) + ' — ' + entry['title'], text, source_endpoint_refs(record)))
    return [('Assumptions of the paper', section('assumptions')),
            ('Extra assumptions', section('source-regularity')),
            ('Density model and analytic chain', section('source-contracts')),
            ('Results of the paper in corrected form', results),
            ('Extra assumptions for the additional results', section('new-assumptions')),
            ('Additional results — not statements of the paper', section('new-theorems'))]


def paper_content(value):
    """Overview HTML as report prose: one layout per equation, notation notes moved to the Lean box."""
    value = re.sub(r'<div class="equation-mobile"[^>]*>.*?</div>', '', value, flags=re.S)
    lean, kept = [], []
    for paragraph in re.split(r'(?=<p\b)', value):
        formal = re.search(r'<code>|\bLean\b|\bMathlib\b|formal development', paragraph)
        (lean if formal else kept).append(paragraph)
    return ''.join(kept), ''.join(lean)


def report_revision(library):
    """Content revision: the authored inputs and the Lean sources they cite."""
    sources, parsed = inventory(library)
    authored = notes(library)
    overview_inputs = (['docs/pbgso_overview.py'] if library == 'PBGSO' else
                       ['docs/build_latent_diffusion.py', 'docs/latent_diffusion_paper.py',
                        'docs/latent_diffusion_regularity.py'])
    content = {'notes': authored, 'argument': argument(library),
               'overview': {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
                            for path in overview_inputs + ['docs/references.py', 'docs/separate_reports.py', 'docs/lean_latex.py']},
               'sources': {path: hashlib.sha256(source.encode()).hexdigest()
                           for path, source in sorted(sources.items())}}
    return hashlib.sha256(json.dumps(content, sort_keys=True, ensure_ascii=False).encode()).hexdigest()[:12]


def module_order(library, authored):
    """Roadmap modules in the order of the roadmap, then any further authored modules."""
    order = []
    nodes = argument(library)['roadmap'] or roadmap_nodes(library)
    for node in sorted(nodes, key=lambda node: (node['row'], node['col'])):
        if node['file'] in authored and node['file'] not in order:
            order.append(node['file'])
    return order + [path for path in authored if path not in order]


def roadmap_nodes(library):
    if library == 'PBGSO':
        from pbgso_overview import ROADMAP, APPENDIX_ROADMAP
        return ROADMAP + APPENDIX_ROADMAP
    return []


def tex_document(library):
    from full_proofs import _preamble, about_document, paper_references
    sources, parsed = inventory(library)
    authored = notes(library)
    parts = argument(library)['parts']
    nodes = argument(library)['roadmap'] or roadmap_nodes(library)
    if not parts or not nodes:
        raise ValueError(f'{library}: missing sequential argument or roadmap')
    for node in nodes:
        steps = authored.get(node['file'], {}).get('steps', [])
        explained = [step for step in steps if node['declaration'] in step['declarations']]
        if not explained or any(not step.get('body') or not step.get('lean') for step in explained):
            raise ValueError(f'{library}: roadmap target lacks mathematics and Lean correspondence: {node}')
    plan = {'report_number': SEPARATE_REPORTS[library]['number'], 'revision': report_revision(library)}
    document = [_preamble(TITLES[library], latex_heading, plan),
                about_document(library, bool(parts)), paper_references(library),
                r'\tableofcontents' + '\n' + r'\clearpage' + '\n' + r'\pagenumbering{arabic}' + '\n',
                r'\chapter{Assumptions and main results}' + '\n']
    for heading, items in statements(library, sources, parsed):
        if not items:
            continue
        document.append(r'\section{' + tex_escape(heading) + '}\n')
        for title, content, refs in items:
            prose, notation = paper_content(content)
            document.append(r'\subsection{' + latex_heading(title) + '}\n' + latex_prose(prose))
            document.append(latex_step_box(library, {'references': refs, 'lean': notation}, sources, parsed))
    if parts:
        document.append(r'\chapter{Mathematical argument}' + '\n')
        for part in parts:
            document.append(r'\section{' + latex_heading(part['title']) + '}\n' + latex_prose(part['body']))
            document.append(latex_step_box(library, {
                'references': [(r['file'], r['name']) for r in part.get('references', [])],
                'lean': part.get('lean', '')}, sources, parsed))
    if authored:
        document.append(r'\chapter{Supporting proofs}' + '\n'
                        'The following sections prove the results behind the boxes of the proof roadmap, '
                        'in roadmap order.\n\n')
        for path in module_order(library, authored):
            note = authored[path]
            document.append(r'\section{' + latex_heading(note['title']) + '}\n' + latex_prose(note['summary']))
            for step in note['steps']:
                document.append(r'\subsection{' + latex_heading(step['title']) + '}\n' + latex_prose(step['body']))
                document.append(latex_step_box(path, step, sources, parsed))
    document.append('\n' + r'\end{document}' + '\n')
    return ''.join(document)


def outputs():
    return {f'docs/latex/{library}/FullProof.tex': tex_document(library) for library in TITLES}


def plans():
    """Report identities for the bibliography files."""
    return {library: {'title': title, 'revision': report_revision(library),
                      'latex': f'docs/latex/{library}/FullProof.tex', 'pdf': f'docs/pdf/{library}/FullProof.pdf'}
            for library, title in TITLES.items()}


def authoring_inputs():
    return ['docs/separate_reports.py'] + [f'{library}/exposition/{name}' for library in TITLES
                                           for name in ('module_notes.json', 'argument.json')]
