"""Consolidated mathematical proof volumes for the homepage developments.

The theorem statements and proof prose remain authored inputs. Each volume
includes their complete local import closure once, in dependency order; the
generated Lean-only standalone bundle is represented by its original modules.
"""
from __future__ import annotations

import hashlib
import html
import re


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
        r"\setmonofont{lmmono10-regular.otf}[Scale=MatchLowercase]",
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
        r"\author{LangevinLean}",
        r"\date{}",
        r"\begin{document}",
        r"\pagenumbering{roman}",
        r"\maketitle",
    ]) + "\n"


def _module_label(path):
    return "proof-module-" + re.sub(r"[^A-Za-z0-9-]", "-", path)


def full_proof_documents(configurations, notes, sources):
    """Build one mathematical proof document for each homepage entry."""
    from build_site import latex_code, latex_heading, latex_prose, tex_escape
    from references import reference_notice

    outputs = {}
    for library, plan in _volume_plans(configurations, notes, sources).items():
        document = [_preamble(plan["title"], latex_heading)]
        document += [
            r"\chapter*{About this document}" + "\n",
            r"\addcontentsline{toc}{chapter}{About this document}" + "\n",
            "This volume collects the theorem statements, mathematical arguments and "
            "supporting proofs for this development. Every locally authored proof "
            "module required by the displayed results, proof roadmap and linked "
            "extensions is included once, in dependency order. Foundational results "
            "from Mathlib are used as standard mathematical results.\n\n",
            latex_prose("<p>" + html.escape(configurations[library]["status"]) + "</p>"),
            latex_prose(reference_notice(library)),
            r"\tableofcontents" + "\n" + r"\clearpage" + "\n",
            r"\pagenumbering{arabic}" + "\n",
        ]
        for key in plan["configurations"]:
            config = configurations[key]
            extension = key != library
            if extension:
                document.append(r"\chapter{Unpublished entropy extension}" + "\n")
                document.append(latex_prose(reference_notice(key)))
                document.append(latex_prose("<p>" + html.escape(config["status"]) + "</p>"))
            else:
                document.append(r"\chapter{Assumptions and main results}" + "\n")
            if config.get("formal_note"):
                document.append(latex_prose("<p>" + config["formal_note"] + "</p>"))
            for result in config["results"]:
                document.append(r"\section{" + latex_heading(result["title"]) + "}\n")
                document.append(latex_prose(result["body"]))
                document.append("\n" + r"{\small\color{gray}Supporting proof: "
                                + r"Section~\ref{" + _module_label(result["file"]) + r"}.\par}" + "\n")
            if config.get("proof"):
                document.append((r"\section{Mathematical argument}" if extension
                                 else r"\chapter{Mathematical argument}") + "\n")
                for part in config["proof"]:
                    level = "subsection" if extension else "section"
                    document.append("\\" + level + "{" + latex_heading(part["title"]) + "}\n")
                    document.append(latex_prose(part["body"]))
                    if part.get("note"):
                        document.append(latex_prose("<p><strong>Scope.</strong> " + part["note"] + "</p>"))
            elif config.get("diagram"):
                document.append(r"\section{Proof organization}" + "\n")
                document.append("The supporting proofs below establish the following steps.\n"
                                + r"\begin{enumerate}" + "\n")
                for node in sorted(config["diagram"], key=lambda node: (node["row"], node["col"])):
                    document.append(r"\item \textbf{" + tex_escape(node["title"]) + "}. "
                                    + latex_prose(node["detail"]) + r" See Section~\ref{"
                                    + _module_label(node["file"]) + "}.\n")
                document.append(r"\end{enumerate}" + "\n")
        document += [r"\chapter{Supporting proofs}" + "\n",
                     "The following mathematical arguments are reproduced in full "
                     "from the authored exposition of the local proof dependencies. "
                     "Each module appears after its local imports.\n\n"]
        for path in plan["modules"]:
            note = notes[path]
            document.append(r"\section{" + latex_heading(note["title"]) + "}\n")
            document.append(r"\label{" + _module_label(path) + "}\n")
            document.append(r"{\small\color{gray}Source module: " + latex_code(path) + r".\par}" + "\n")
            document.append(latex_prose(note["summary"]))
            for step in note["steps"]:
                document.append(r"\subsection{" + latex_heading(step["title"]) + "}\n")
                document.append(latex_prose(step["body"]))
        document.append("\n" + r"\end{document}" + "\n")
        outputs[plan["latex"]] = "".join(document)
    return outputs
