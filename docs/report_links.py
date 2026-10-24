"""Resolve authored result citations against the reports' actual section plan.

No section numbers are authored by hand. A declaration identifies its proof
subsection; the same inventory drives LaTeX headings, HTML links and validation.
"""
from __future__ import annotations

from collections import defaultdict
import html
from html.parser import HTMLParser
import re

from report_citations import REPORTS, PROJECT_URL, report_owner


CITE = re.compile(r'<cite\b([^>]*)>\s*</cite>')


class _Attributes(HTMLParser):
    def handle_starttag(self, tag, attrs):
        self.attrs = dict(attrs)


def citation_target(match):
    parser = _Attributes()
    parser.feed('<cite' + match[1] + '>')
    attrs = parser.attrs
    if not attrs.get('data-report-ref'):
        raise ValueError('A report citation needs a target proof')
    return attrs['data-report-ref'], attrs.get('data-report-declaration')


def step_label(path, index):
    return 'report-step-' + re.sub(r'[^A-Za-z0-9-]', '-', path) + '-' + str(index)


class ReportCatalog:
    def __init__(self, plans, notes, sources, parsed):
        from build_site import HELPERS, imports

        self.plans, self.notes = plans, notes
        self.locations, self.declarations = {}, {}
        self.step_uses = {}
        self.section_uses = {}
        for library, plan in plans.items():
            for path, detail in plan['module_details'].items():
                self.locations[path] = dict(library=library, path=path, **detail)
                for index, step in enumerate(detail['steps'], 1):
                    for name in step['declarations']:
                        self.declarations[path, name] = dict(
                            library=library, path=path, index=index, **step)

        # The formal proof names provide a conservative, declaration-specific
        # use index. Ambiguous names are never guessed. Every direct earlier
        # prerequisite is additionally cited at the beginning of its section.
        masked = {path: list(HELPERS.mask_comments(text.splitlines()))
                  for path, text in sources.items() if path in self.locations}
        namespace_at, opens_at, qualified = {}, {}, defaultdict(list)
        for path, lines in masked.items():
            scopes, opened = [], []
            for line_no, line in enumerate(lines, 1):
                namespace_at[path, line_no] = '.'.join(
                    name for kind, name in scopes if kind == 'namespace')
                opens_at[path, line_no] = tuple(opened)
                scope = re.match(r'^\s*(namespace|section)\b\s*([\w.]*)', line)
                if scope:
                    scopes.append((scope[1], scope[2]))
                elif re.match(r'^\s*end(?:\s+[\w.]+)?\s*$', line) and scopes:
                    scopes.pop()
                opening = re.match(r'^\s*open\s+(?!scoped\b)([\w. ]+)', line)
                if opening:
                    opened.extend(opening[1].split())
            for name, declaration in parsed.get(path, {}).items():
                prefix = namespace_at.get((path, declaration['start']), '')
                full = '.'.join(part for part in (prefix, name) if part)
                qualified[full].append((path, name))
        short = defaultdict(list)
        for pair in self.declarations:
            short[pair[1].split('.')[-1]].append(pair)

        closure_cache = {}

        def closure(path):
            if path not in closure_cache:
                result = {path}
                for dependency in imports(sources[path]):
                    if dependency in self.locations:
                        result.update(closure(dependency))
                closure_cache[path] = result
            return closure_cache[path]

        for path in self.locations:
            library = self.locations[path]['library']
            self.section_uses[path] = [dependency for dependency in imports(sources[path])
                                       if dependency in self.locations
                                       and report_owner(dependency) != library]
            available = closure(path)
            for index, step in enumerate(notes[path]['steps'], 1):
                used = set()
                for name in step['declarations']:
                    declaration = parsed[path][name]
                    text = '\n'.join(masked[path][declaration['start']-1:declaration['end']])
                    namespace = namespace_at.get((path, declaration['start']), '')
                    prefixes = ['.'.join(namespace.split('.')[:i])
                                for i in range(len(namespace.split('.')), -1, -1)]
                    for token in set(re.findall(r"\b[A-Za-z_][\w']*(?:\.[\w']+)*", text)):
                        if len(token) < 5:
                            continue
                        candidates = []
                        for prefix in prefixes + list(opens_at.get((path, declaration['start']), ())):
                            full = '.'.join(part for part in (prefix, token) if part)
                            matches = [pair for pair in qualified.get(full, ()) if pair[0] in available]
                            if matches:
                                candidates = matches
                                break
                        if not candidates:
                            candidates = [pair for pair in short.get(token, ()) if pair[0] in available]
                        if len(candidates) == 1 and report_owner(candidates[0][0]) != library:
                            used.add(candidates[0])
                self.step_uses[path, index] = sorted(used, key=lambda pair: (
                    list(plans).index(report_owner(pair[0])), self.location(*pair)['section']))

    def location(self, path, declaration=None):
        try:
            return self.declarations[path, declaration] if declaration else self.locations[path]
        except KeyError:
            raise ValueError(f'Unknown precise report citation: {path}: {declaration}') from None

    def url(self, location):
        return (PROJECT_URL + self.plans[location['library']]['pdf']
                + '#nameddest=' + location['anchor'])

    def html_citation(self, path, declaration=None, page=None):
        location = self.location(path, declaration)
        library = location['library']
        if page:
            from build_site import relative
            url = relative(self.plans[library]['pdf'], page) + '#nameddest=' + location['anchor']
        else:
            url = self.url(location)
        text = REPORTS[library]['short'] + ', Section ' + location['section']
        return ('<a class="report-citation" data-report="' + library
                + '" data-report-section="' + location['section']
                + '" href="' + html.escape(url, quote=True) + '" title="'
                + html.escape(location['title'], quote=True) + '">'
                + html.escape(text) + '</a>')

    def tex_citation(self, path, declaration=None, current=None):
        location = self.location(path, declaration)
        if current == location['library']:
            label = (step_label(path, location['index']) if declaration
                     else 'proof-module-' + re.sub(r'[^A-Za-z0-9-]', '-', path))
            return r'Section~\ref{' + label + '}'
        return (r'\cite[Section~' + location['section'] + ']{'
                + REPORTS[location['library']]['key'] + '}')

    def resolve_html(self, value, page):
        return CITE.sub(lambda match: self.html_citation(*citation_target(match), page=page), value)

    def latex_prose(self, value, current=None):
        from full_proofs import mathematical_prose
        from build_site import latex_prose
        references = []

        def protect(match):
            references.append(self.tex_citation(*citation_target(match), current=current))
            return f'REPORTREFERENCEPLACEHOLDER{len(references)-1}END'

        result = latex_prose(mathematical_prose(CITE.sub(protect, value)))
        return re.sub(r'REPORTREFERENCEPLACEHOLDER(\d+)END',
                      lambda match: references[int(match[1])], result)

    def html_dependencies(self, path, index=None, page=None):
        refs = ([(dependency, None) for dependency in self.section_uses.get(path, ())]
                if index is None else self.step_uses.get((path, index), ()))
        if not refs:
            return ''
        references = self._unique_locations(refs)
        return ('<p class="report-prerequisites">Earlier results used here: '
                + '; '.join(self.html_citation(*pair, page=page) for pair in references) + '.</p>')

    def tex_dependencies(self, path, index=None, current=None):
        refs = ([(dependency, None) for dependency in self.section_uses.get(path, ())]
                if index is None else self.step_uses.get((path, index), ()))
        if not refs:
            return ''
        references = self._unique_locations(refs)
        return ('\n\nEarlier results used here: '
                + '; '.join(self.tex_citation(*pair, current=current) for pair in references) + '.\n')

    def _unique_locations(self, refs):
        result, seen = [], set()
        for pair in refs:
            location = self.location(*pair)
            key = location['library'], location['section']
            if key not in seen:
                seen.add(key)
                result.append(pair)
        return result

    def bibliography(self, document):
        """Self-contained TeX bibliography, matching the downloadable .bib keys."""
        from build_site import tex_escape
        keys = {key.strip() for group in re.findall(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}', document)
                for key in group.split(',')}
        if not keys:
            return ''
        parts = ['\n' + r'\begin{thebibliography}{ULA-LSI}' + '\n']
        for library, plan in self.plans.items():
            report = REPORTS[library]
            if report['key'] not in keys:
                continue
            parts.append(r'\bibitem[' + report['short'] + ']{' + report['key'] + '}\n'
                         + r'LangevinLean Project. \emph{' + tex_escape(plan['title']) + '}. '
                         + report['number'] + ', 2026. Draft report, content revision '
                         + plan['revision'] + '. '
                         + r'\url{' + PROJECT_URL + plan['pdf'] + '}.\n')
        parts.append(r'\end{thebibliography}' + '\n')
        return ''.join(parts)
