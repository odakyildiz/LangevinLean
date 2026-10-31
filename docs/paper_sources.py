"""One presentation contract for paper labels, added hypotheses and proof status.

The source-specific records preserve the labels of the audited editions. A
result without an original paper label is never inserted into the paper ledger.
"""
from html import escape

from references import PAPERS


def source_metadata():
    from paper_sources_classical import PAPER_SOURCES as classical
    from paper_sources_kinetic import PAPER_SOURCES as kinetic
    return {**classical, **kinetic}


def source_citation(paper, location, url=None):
    record = PAPERS[paper]
    return ('<p class="source-citation">Source: <a href="' + escape(url or record['url'], quote=True)
            + '">' + escape(record['authors'] + ' (' + record['year'] + '), ' + location)
            + '</a>.</p>')


def result_metadata(library, name):
    data = source_metadata()[library]
    if name not in data['results']:
        raise ValueError(f'Missing paper correspondence: {library}:{name}')
    result = data['results'][name]
    if result['status'] not in {'proved', 'corrected', 'new', 'auxiliary'}:
        raise ValueError(f'Unknown paper proof status: {library}:{name}')
    if result['status'] in {'proved', 'corrected'} and not result.get('label'):
        raise ValueError(f'Missing original printed result label: {library}:{name}')
    return result


def proof_status(record):
    if record['status'] == 'corrected':
        return 'Corrected statement proved'
    if record['status'] == 'proved':
        return ('Paper result proved with extra assumptions' if record.get('extras')
                else 'Paper statement proved')
    return 'New result' if record['status'] == 'new' else 'Supporting result'


def result_notice(library, result, math):
    data = source_metadata()[library]
    record = result_metadata(library, result['name'])
    text = '<p class="paper-status" data-proof-status="' + record['status'] + '"><strong>'
    text += escape(proof_status(record)) + '.</strong> ' + math(record.get('note', '')) + '</p>'
    if record['status'] in {'proved', 'corrected'} or record.get('label', '').startswith('Algorithm '):
        text = source_citation(record.get('paper', data['paper']), record.get('location', record['label']),
                               record.get('url')) + text
    if record['status'] == 'new':
        text += '<p>This is not a numbered result of the source paper.</p>'
    elif record['status'] == 'auxiliary':
        text += '<p>This supporting identity is not a separate paper theorem.</p>'
    if record.get('extras'):
        text += ('<p class="added-assumption" data-assumption-kind="added">'
                 '<strong>Extra assumptions used:</strong> ' + ', '.join(
                     '<a href="#extra-a' + label.split('A')[-1] + '">' + escape(label) + '</a>'
                     for label in record['extras']) + '.</p>')
    return text


def correspondence_section(library, results, math):
    data = source_metadata()[library]
    body = ('<section class="section paper-correspondence" id="paper-correspondence">'
            '<h2>Paper correspondence</h2><p>The labels in the first column are the paper’s '
            'original labels. A corrected statement has a checked Lean proof, but its '
            'changed hypotheses or conclusion must not be read as the literal printed result.</p>')
    if data.get('scope'):
        body += math('<p>' + data['scope'] + '</p>')
    rows = []
    for index, result in enumerate(results, 1):
        record = result_metadata(library, result['name'])
        if record['status'] not in {'proved', 'corrected'}:
            continue
        paper = PAPERS[record.get('paper', data['paper'])]
        rows.append('<tr data-paper-result="' + escape(record['label'], quote=True) + '"><td><a href="'
                    + escape(record.get('url', paper['url']), quote=True) + '">'
                    + escape(record['label']) + '</a></td><td>' + escape(proof_status(record))
                    + '</td><td>' + math(record.get('note', '')) + '</td><td><a href="#result-'
                    + str(index) + '">Statement and Lean proof</a></td></tr>')
    if rows:
        body += ('<div class="table-wrap"><table><thead><tr><th>Paper result</th><th>Proof status</th>'
                 '<th>Difference from the paper</th><th>Formalized statement</th></tr></thead><tbody>'
                 + ''.join(rows) + '</tbody></table></div>')
    else:
        body += '<p>No numbered result of the source paper is claimed on this page. The results below are an extension.</p>'
    return body + '</section>'


def assumption_sections(library, math):
    data = source_metadata()[library]
    body = ('<section class="section" id="paper-assumptions"><h2>Assumptions from the paper</h2>'
            '<p>Original labels are retained. Unnumbered hypotheses are cited by their location in the paper.</p>')
    for index, record in enumerate(data['assumptions'], 1):
        label = record['label']
        title = ('<span class="paper-label">' + escape(label) + '</span>'
                 + (' — ' + escape(record['title']) if record.get('title') else ''))
        body += ('<article class="paper-assumption" id="paper-assumption-' + str(index)
                 + '" data-paper-assumption="' + escape(label, quote=True) + '"><h3>' + title + '</h3>'
                 + source_citation(record.get('paper', data['paper']), record.get('location', label), record.get('url'))
                 + math(record['body']) + '</article>')
    body += '</section><section class="section" id="extra-assumptions"><h2>Extra assumptions</h2>'
    extras = data.get('extras', [])
    for index, record in enumerate(extras, 1):
        if record['label'] != f'Extra A{index}':
            raise ValueError(f'Nonsequential extra assumption label: {library}:{record["label"]}')
        title = record['label'] + (' — ' + record['title'] if record.get('title') else '')
        body += ('<article class="added-assumption" data-assumption-kind="added" data-extra-assumption="'
                 + escape(record['label'], quote=True) + '" id="extra-a' + str(index) + '"><h3>'
                 + escape(title) + '</h3><p>Added in this formalization; not an assumption of the paper at the cited location.</p>'
                 + math(record['body']) + '</article>')
    if not extras:
        body += '<p>No extra assumptions are imposed on the paper statements listed above.</p>'
    return body + '</section>'
