"""Consolidated mathematical proof volumes for the homepage developments.

The theorem statements and proof prose remain authored inputs. Each supporting proof belongs to one report. Later reports cite its precise
section instead of reproducing earlier reports. The source dependency closure
is retained in the inventory for reproducibility.
"""
from __future__ import annotations

import hashlib
import json
import re
from html.parser import HTMLParser


from report_citations import REPORT_ORDER, REPORTS, report_owner

VOLUMES = REPORT_ORDER


def _digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def _configuration_roots(config):
    roots = [result["file"] for result in config["results"]]
    roots += [reference["file"]
              for part in config.get("proof", [])
              for reference in part.get("references", [])]
    roots += [node["file"] for node in config.get("diagram", [])]
    for target, _ in config.get("extra", []):
        target = target.split("#", 1)[0].split("?", 1)[0]
        if target.startswith("docs/modules/") and target.endswith(".html"):
            path = target.removeprefix("docs/modules/").removesuffix(".html") + ".lean"
            if path != "IPLA/Standalone.lean":
                roots.append(path)
    return list(dict.fromkeys(roots))


def _volume_plans(configurations, notes, sources):
    """Assign every shared proof to one report, before assigning section numbers.

    The union is important: a helper first needed by a particle report still
    belongs in its earlier ULA report, so every citation has a real destination.
    """
    from build_site import imports

    libraries = [library for library in VOLUMES if library in configurations]
    roots = {library: _configuration_roots(configurations[library]) for library in libraries}
    order, visited, active, external = [], set(), set(), set()

    def visit(path):
        if path in visited:
            return
        if path in active:
            raise ValueError(f"Cyclic local proof dependency: {path}")
        if path not in sources:
            external.add(path.removesuffix(".lean").replace("/", "."))
            return
        if path not in notes:
            raise ValueError(f"Missing authored mathematical proof: {path}")
        active.add(path)
        for dependency in imports(sources[path]):
            visit(dependency)
        active.remove(path)
        visited.add(path)
        order.append(path)

    for library in libraries:
        for root in roots[library]:
            if root not in sources:
                raise ValueError(f"Missing local theorem or proof-map module: {root}")
            visit(root)
    # Publish the additional mathematical lemmas in the atlas as well, so a
    # proof page never supplies a citation to a report that omits its result.
    # Aggregate imports, audit pages and the generated standalone bundle have
    # no declarations of their own and are not mathematical report sections.
    for path, note in notes.items():
        if path != 'IPLA/Standalone.lean' and any(step['declarations'] for step in note['steps']):
            visit(path)
    owners = {path: report_owner(path) for path in order}
    if any(owner not in libraries for owner in owners.values()):
        raise ValueError("A mathematical proof has no report owner")
    rank = {library: i for i, library in enumerate(libraries)}
    plans = {}
    for library in libraries:
        config = configurations[library]
        owned = [path for path in order if owners[path] == library]
        closure = set()

        def collect(path):
            if path in closure or path not in sources:
                return
            closure.add(path)
            for dependency in imports(sources[path]):
                collect(dependency)

        for path in owned + roots[library]:
            collect(path)
        borrowed = [path for path in order if path in closure and owners[path] != library]
        dependencies = [earlier for earlier in libraries
                        if any(owners[path] == earlier for path in borrowed)]
        if any(rank[earlier] >= rank[library] for earlier in dependencies):
            raise ValueError(f"Report {library} refers forward to {dependencies}")
        details = {}
        for section_index, path in enumerate(owned, 1):
            note = notes[path]
            section = f"3.{section_index}"
            details[path] = {
                "title": note["title"], "section": section,
                "anchor": "section." + section,
                "source_sha256": _digest(sources[path]),
                "summary_sha256": _digest(note["summary"]),
                "proof_steps": len(note["steps"]),
                "declarations": [name for step in note["steps"] for name in step["declarations"]],
                "steps": [{"title": step["title"], "section": f"{section}.{i}",
                           "anchor": f"subsection.{section}.{i}",
                           "body_sha256": _digest(step["body"]),
                           "declarations": step["declarations"]}
                          for i, step in enumerate(note["steps"], 1)],
            }
        results = []
        for i, result in enumerate(config["results"], 1):
            if result["name"] not in details[result["file"]]["declarations"]:
                raise ValueError(f"Missing main theorem proof: {library}: {result['name']}")
            results.append(dict(configuration=library, file=result["file"],
                                name=result["name"], title=result["title"], section=f"1.{i}"))
        content = {"title": config["title"], "results": config["results"],
                   "proof": config.get("proof", []), "modules": details,
                   "earlier_reports": {earlier: plans[earlier]["revision"] for earlier in dependencies}}
        revision = _digest(json.dumps(content, sort_keys=True, ensure_ascii=False))[:12]
        report_external = sorted({dependency.removesuffix('.lean').replace('/', '.')
                                  for path in closure for dependency in imports(sources[path])
                                  if dependency not in sources})
        plans[library] = {
            "title": config["title"], "revision": revision,
            "report_number": REPORTS[library]["number"],
            "latex": f"docs/latex/{library}/FullProof.tex",
            "pdf": f"docs/pdf/{library}/FullProof.pdf",
            "configurations": [library], "roots": roots[library],
            "modules": owned, "module_details": details, "results": results,
            "referenced_modules": borrowed, "earlier_reports": dependencies,
            "external_imports": report_external,
        }
    return plans


def full_proof_inventory(configurations, notes, sources):
    """Return reproducible coverage and source fingerprints for every volume."""
    return _volume_plans(configurations, notes, sources)


def _preamble(title, heading, report=None):
    return "\n".join([
        r"\documentclass[11pt,a4paper]{report}",
        r"\usepackage{fontspec,amsmath,amssymb,amsthm,microtype,xcolor}",
        r"\setmainfont{lmroman10-regular.otf}[BoldFont=lmroman10-bold.otf,ItalicFont=lmroman10-italic.otf,BoldItalicFont=lmroman10-bolditalic.otf]",
        r"\usepackage[margin=25mm]{geometry}",
        r"\usepackage[unicode,hidelinks]{hyperref}",
        r"\hypersetup{pdfauthor={LangevinLean Project},bookmarksdepth=2}",
        r"\setlength{\emergencystretch}{3em}",
        r"\setlength{\parskip}{0.4em}",
        r"\setlength{\parindent}{0pt}",
        r"\setcounter{tocdepth}{1}",
        r"\makeatletter",
        r"\renewcommand*\l@section{\@dottedtocline{1}{1.5em}{3.8em}}",
        r"\renewcommand*\@pnumwidth{2.5em}",
        r"\renewcommand*\@tocrmarg{3.5em}",
        r"\makeatother",
        r"\setcounter{secnumdepth}{2}",
        r"\allowdisplaybreaks[2]",
        r"\raggedbottom",
        r"\title{" + heading(title) + r"\\[0.6em]\large Mathematical proofs}",
        r"\author{LangevinLean Project}",
        (r"\date{Draft report " + report['report_number'] + r"\\[0.4em]\small Content revision "
         + report['revision'] + "}" if report else r"\date{}"),
        r"\begin{document}",
        r"\pagenumbering{roman}",
        r"\maketitle",
    ]) + "\n"


def _module_label(path):
    return "proof-module-" + re.sub(r"[^A-Za-z0-9-]", "-", path)


class _MathematicalProse(HTMLParser):
    """Keep authored mathematics, omitting explicitly marked source commentary.

    Math is protected before parsing: a less-than sign in TeX is not an HTML
    tag. Never guess whether a sentence is dispensable from words it contains.
    Mixed mathematical/implementation passages must be separated by the author.
    """
    def __init__(self):
        super().__init__(convert_charrefs=False)
        self.output = []
        self.omitted = 0

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if self.omitted:
            if tag not in ('br', 'hr', 'img', 'input', 'meta', 'link'):
                self.omitted += 1
        elif 'formal-note' in attrs.get('class', '').split():
            self.omitted = 1
        else:
            self.output.append(self.get_starttag_text())

    def handle_startendtag(self, tag, attrs):
        if not self.omitted:
            self.output.append(self.get_starttag_text())

    def handle_endtag(self, tag):
        if self.omitted:
            self.omitted -= 1
        else:
            self.output.append('</' + tag + '>')

    def handle_data(self, data):
        if not self.omitted:
            self.output.append(data)

    def handle_entityref(self, name):
        self.handle_data('&' + name + ';')

    def handle_charref(self, name):
        self.handle_data('&#' + name + ';')


def mathematical_prose(value):
    """Return the paper-facing HTML without deleting any unmarked proof prose."""
    from build_site import HELPERS
    formulas = []

    def protect(match):
        formulas.append(match[0])
        return f'PAPERMATHPLACEHOLDER{len(formulas)-1}END'

    parser = _MathematicalProse()
    parser.feed(HELPERS.TEX.sub(protect, value))
    parser.close()
    if parser.omitted:
        raise ValueError('Unclosed formal-note element; refusing to omit subsequent proof prose')
    result = ''.join(parser.output)
    return re.sub(r'PAPERMATHPLACEHOLDER(\d+)END',
                  lambda match: formulas[int(match[1])], result)


def paper_prose(value):
    from build_site import latex_prose
    return latex_prose(mathematical_prose(value))


def paper_references(library):
    """Bibliographic information, without the website's implementation audit."""
    from build_site import tex_escape
    from references import DEVELOPMENTS, PAPERS
    parts = [r'\section*{Literature and scope}' + '\n']
    if library in ('IPLA', 'IPLA/LSI', 'ProximalLangevin', 'KineticLangevin'):
        scope = {
            'IPLA': 'The result allows different parameter and latent dimensions. '
                    'That extension is unpublished. The entropy extension is presented in a separate report.',
            'IPLA/LSI': 'The particle entropy argument presented here is unpublished; '
                        'the cited works provide its sampling and functional-inequality background.',
            'ProximalLangevin': 'The algorithms are from the cited paper. The corrected bounds '
                               'and proofs here are unpublished. They establish the results stated '
                               'below; some rates and constants printed in the paper are not proved here.',
            'KineticLangevin': 'The exposition follows the cited kinetic-sampling paper, with '
                              'corrections to the continuous prefactor and the second-order comparison. '
                              'The exact fourth Gaussian moment is retained. Continuous solutions '
                              'are continuous in mean square on finite time intervals.',
        }[library]
        parts.append(tex_escape(scope) + '\n\n')
    parts.append(r'\begin{enumerate}' + '\n')
    for identifier in DEVELOPMENTS[library]['papers']:
        paper = PAPERS[identifier]
        parts.append(r'\item ' + tex_escape(paper['authors']) + ' (' + paper['year'] + '). '
                     + r'\emph{' + tex_escape(paper['title']) + '}. '
                     + tex_escape(paper['venue']) + '. '
                     + r'\url{' + paper['url'] + '}.\n')
    parts.append(r'\end{enumerate}' + '\n')
    return ''.join(parts)


def full_proof_documents(configurations, notes, sources, catalog=None):
    """Build one mathematical proof document for each homepage entry."""
    from build_site import latex_heading, tex_escape

    from report_links import ReportCatalog, step_label
    if catalog is None:
        from build_site import declarations
        parsed = {path: declarations(text) for path, text in sources.items()
                  if path != 'IPLA/Standalone.lean'}
        catalog = ReportCatalog(_volume_plans(configurations, notes, sources), notes, sources, parsed)
    outputs = {}
    for library, plan in catalog.plans.items():
        prose = lambda value: catalog.latex_prose(value, current=library)
        document = [_preamble(plan["title"], latex_heading, plan)]
        argument_summary = ('Chapter 2 gives their proofs. '
                            if configurations[library].get('proof')
                            else 'Chapter 2 describes the proof organization. ')
        document += [
            r"\chapter*{About this document}" + "\n",
            r"\addcontentsline{toc}{chapter}{About this document}" + "\n",
            "Chapter 1 states the assumptions and convergence estimates. "
            + argument_summary + "Chapter 3 proves the supporting "
            "lemmas, in an order in which each lemma precedes its applications.\n\n"
            "Prepared by the LangevinLean Project with AI assistance, these notes form "
            "part of an ongoing effort to formalize Langevin algorithms comprehensively. "
            "This is draft work and may contain mistakes.\n\n",
            paper_references(library),
            _earlier_report_notice(plan, catalog),
            r"\tableofcontents" + "\n" + r"\clearpage" + "\n",
            r"\pagenumbering{arabic}" + "\n",
        ]
        for key in plan["configurations"]:
            config = configurations[key]
            extension = key != library
            if extension:
                document.append(r"\chapter{Unpublished entropy extension}" + "\n")
                document.append(paper_references(key))
            else:
                document.append(r"\chapter{Assumptions and main results}" + "\n")
            for result in config["results"]:
                document.append(r"\section{" + latex_heading(result["title"]) + "}\n")
                document.append(prose(result["body"]))
                document.append("\n" + r"{\small\color{gray}Supporting proof: "
                                + r"Section~\ref{" + _module_label(result["file"]) + r"}.\par}" + "\n")
            if config.get("proof"):
                document.append((r"\section{Mathematical argument}" if extension
                                 else r"\chapter{Mathematical argument}") + "\n")
                for part in config["proof"]:
                    level = "subsection" if extension else "section"
                    document.append("\\" + level + "{" + latex_heading(part["title"]) + "}\n")
                    document.append(prose(part["body"]))
            elif config.get("diagram"):
                document.append((r"\section{Proof organization}" if extension
                                 else r"\chapter{Proof organization}") + "\n")
                document.append("The supporting proofs below establish the following steps.\n"
                                + r"\begin{enumerate}" + "\n")
                for node in sorted(config["diagram"], key=lambda node: (node["row"], node["col"])):
                    document.append(r"\item \textbf{" + tex_escape(node["title"]) + "}. "
                                    + prose(node["detail"]) + r" See Section~\ref{"
                                    + _module_label(node["file"]) + "}.\n")
                document.append(r"\end{enumerate}" + "\n")
        document += [r"\chapter{Supporting proofs}" + "\n",
                     "The following sections give the definitions and prove the lemmas "
                     "used in the convergence arguments.\n\n"]
        for path in plan["modules"]:
            note = notes[path]
            document.append(r"\section{" + latex_heading(note["title"]) + "}\n")
            document.append(r"\label{" + _module_label(path) + "}\n")
            document.append(prose(note["summary"]))
            document.append(catalog.tex_dependencies(path, current=library))
            for index, step in enumerate(note["steps"], 1):
                document.append(r"\subsection{" + latex_heading(step["title"]) + "}\n")
                document.append(r"\label{" + step_label(path, index) + "}\n")
                document.append(prose(step["body"]))
                document.append(catalog.tex_dependencies(path, index=index, current=library))
        document.append(catalog.bibliography(''.join(document)))
        document.append("\n" + r"\end{document}" + "\n")
        outputs[plan["latex"]] = "".join(document)
    return outputs


def _earlier_report_notice(plan, catalog):
    """Name the earlier reports once; use-site citations carry exact sections."""
    if not plan['earlier_reports']:
        return ''
    keys = ','.join(REPORTS[library]['key'] for library in plan['earlier_reports'])
    return ('Results from the earlier reports '
            + r'\cite{' + keys + '} '
            + 'are used below. Each application cites the section containing the required result.\n\n')
