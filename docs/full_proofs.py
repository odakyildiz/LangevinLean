"""Consolidated mathematical proof volumes for the homepage developments.

The theorem statements and proof prose remain authored inputs. Each volume
includes their complete local import closure once, in dependency order; the
generated Lean-only standalone bundle is represented by its original modules.
"""
from __future__ import annotations

import hashlib
import re
from html.parser import HTMLParser


VOLUMES = (
    "UnadjustedLangevin",
    "UnadjustedLangevin/LSI",
    "IPLA",
    "ProximalLangevin",
    "KineticLangevin",
    "KIPLMC",
    "AverageLMC",
)


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
    from build_site import imports

    plans = {}
    for library in VOLUMES:
        if library not in configurations:
            continue
        included = [library]
        if library == "IPLA" and "IPLA/LSI" in configurations:
            included.append("IPLA/LSI")
        roots = list(dict.fromkeys(path for key in included
                                   for path in _configuration_roots(configurations[key])))
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

        for root in roots:
            if root not in sources:
                raise ValueError(f"Missing local theorem or proof-map module: {root}")
            visit(root)
        results = []
        for key in included:
            for result in configurations[key]["results"]:
                explained = {name for step in notes[result["file"]]["steps"]
                             for name in step["declarations"]}
                if result["name"] not in explained:
                    raise ValueError(f"Missing main theorem proof: {key}: {result['name']}")
                results.append(dict(configuration=key, file=result["file"],
                                    name=result["name"], title=result["title"]))
        details = {}
        for path in order:
            note = notes[path]
            details[path] = {
                "title": note["title"],
                "source_sha256": _digest(sources[path]),
                "summary_sha256": _digest(note["summary"]),
                "proof_steps": len(note["steps"]),
                "declarations": [name for step in note["steps"]
                                 for name in step["declarations"]],
                "steps": [{"title": step["title"], "body_sha256": _digest(step["body"]),
                           "declarations": step["declarations"]}
                          for step in note["steps"]],
            }
        plans[library] = {
            "title": configurations[library]["title"],
            "latex": f"docs/latex/{library}/FullProof.tex",
            "pdf": f"docs/pdf/{library}/FullProof.pdf",
            "configurations": included,
            "roots": roots,
            "modules": order,
            "module_details": details,
            "results": results,
            "external_imports": sorted(external),
        }
    return plans


def full_proof_inventory(configurations, notes, sources):
    """Return reproducible coverage and source fingerprints for every volume."""
    return _volume_plans(configurations, notes, sources)


def _preamble(title, heading):
    return "\n".join([
        r"\documentclass[11pt,a4paper]{report}",
        r"\usepackage{fontspec,amsmath,amssymb,amsthm,microtype,xcolor}",
        r"\setmainfont{lmroman10-regular.otf}[BoldFont=lmroman10-bold.otf,ItalicFont=lmroman10-italic.otf,BoldItalicFont=lmroman10-bolditalic.otf]",
        r"\usepackage[margin=25mm]{geometry}",
        r"\usepackage[unicode,hidelinks]{hyperref}",
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
        r"\author{Omer Deniz Akyildiz\\[0.4em]\normalsize Prepared with AI assistance}",
        r"\date{}",
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
                    'That extension, and the entropy extension included in this volume, are unpublished.',
            'IPLA/LSI': 'The particle entropy argument presented here is unpublished; '
                        'the cited works provide its sampling and functional-inequality background.',
            'ProximalLangevin': 'The algorithms are from the cited paper. The corrected bounds '
                               'and proofs here are unpublished and cover only the results explicitly '
                               'stated below; the printed rates and constants are not all recovered.',
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


def full_proof_documents(configurations, notes, sources):
    """Build one mathematical proof document for each homepage entry."""
    from build_site import latex_heading, tex_escape

    outputs = {}
    for library, plan in _volume_plans(configurations, notes, sources).items():
        document = [_preamble(plan["title"], latex_heading)]
        document += [
            r"\chapter*{About this document}" + "\n",
            r"\addcontentsline{toc}{chapter}{About this document}" + "\n",
            "These draft notes present the assumptions, convergence theorems and "
            "detailed mathematical proofs for this development. The supporting "
            "arguments are arranged so that prerequisites precede their applications. "
            "They use ordinary mathematical notation throughout.\n\n"
            "Prepared by Omer Deniz Akyildiz with AI assistance, these notes form "
            "part of an ongoing effort to formalize Langevin algorithms comprehensively. "
            "This is draft work and may contain mistakes.\n\n",
            paper_references(library),
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
                document.append(paper_prose(result["body"]))
                document.append("\n" + r"{\small\color{gray}Supporting proof: "
                                + r"Section~\ref{" + _module_label(result["file"]) + r"}.\par}" + "\n")
            if config.get("proof"):
                document.append((r"\section{Mathematical argument}" if extension
                                 else r"\chapter{Mathematical argument}") + "\n")
                for part in config["proof"]:
                    level = "subsection" if extension else "section"
                    document.append("\\" + level + "{" + latex_heading(part["title"]) + "}\n")
                    document.append(paper_prose(part["body"]))
            elif config.get("diagram"):
                document.append(r"\section{Proof organization}" + "\n")
                document.append("The supporting proofs below establish the following steps.\n"
                                + r"\begin{enumerate}" + "\n")
                for node in sorted(config["diagram"], key=lambda node: (node["row"], node["col"])):
                    document.append(r"\item \textbf{" + tex_escape(node["title"]) + "}. "
                                    + paper_prose(node["detail"]) + r" See Section~\ref{"
                                    + _module_label(node["file"]) + "}.\n")
                document.append(r"\end{enumerate}" + "\n")
        document += [r"\chapter{Supporting proofs}" + "\n",
                     "We now supply the detailed supporting arguments. Each section "
                     "introduces the objects and estimates needed by the results that "
                     "follow it.\n\n"]
        for path in plan["modules"]:
            note = notes[path]
            document.append(r"\section{" + latex_heading(note["title"]) + "}\n")
            document.append(r"\label{" + _module_label(path) + "}\n")
            document.append(paper_prose(note["summary"]))
            for step in note["steps"]:
                document.append(r"\subsection{" + latex_heading(step["title"]) + "}\n")
                document.append(paper_prose(step["body"]))
        document.append("\n" + r"\end{document}" + "\n")
        outputs[plan["latex"]] = "".join(document)
    return outputs
