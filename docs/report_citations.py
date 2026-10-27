"""Shared report identities and downloadable citations for the proof atlas.

This module deliberately knows nothing about the site or report builders.  They
provide the authored title and the deterministic content revision of each report.
"""
from __future__ import annotations

import hashlib
from html import escape
import os
from pathlib import Path
from collections.abc import Mapping


REPORT_ORDER = (
    "UnadjustedLangevin",
    "UnadjustedLangevin/LSI",
    "IPLA",
    "IPLA/LSI",
    "ProximalLangevin",
    "KineticLangevin",
    "KIPLMC",
    "AverageLMC",
)

REPORTS = {
    "AverageLMC": dict(key="LangevinLean2026AverageLMC", short="Average LMC", number="LL-09"),
    "UnadjustedLangevin": dict(key="LangevinLean2026ULASC", short="ULA-SC", number="LL-01"),
    "UnadjustedLangevin/LSI": dict(key="LangevinLean2026ULALSI", short="ULA-LSI", number="LL-02"),
    "IPLA": dict(key="LangevinLean2026IPLA", short="IPLA-SC", number="LL-03"),
    "IPLA/LSI": dict(key="LangevinLean2026IPLALSI", short="IPLA-LSI", number="LL-04"),
    "ProximalLangevin": dict(key="LangevinLean2026Proximal", short="Proximal", number="LL-05"),
    "KineticLangevin": dict(key="LangevinLean2026Kinetic", short="Kinetic", number="LL-06"),
    "KIPLMC": dict(key="LangevinLean2026KIPLMC", short="KIPLMC", number="LL-07"),
}

PROJECT_URL = "https://odakyildiz.github.io/LangevinLean/"
ROOT = Path(__file__).resolve().parents[1]


def report_owner(path):
    """Return the most specific report for a local source path, if known."""
    path = str(path).replace("\\", "/")
    for library in sorted(REPORT_ORDER, key=len, reverse=True):
        if path == library + ".lean" or path.startswith(library + "/"):
            return library
    return None


def _bibtext(value):
    """Escape field text while preserving Unicode names and punctuation."""
    substitutions = {
        "\\": r"\textbackslash{}", "{": r"\{", "}": r"\}",
        "&": r"\&", "%": r"\%", "#": r"\#", "_": r"\_",
    }
    return "".join(substitutions.get(character, character)
                   for character in str(value)).replace("\n", " ")


def bibliography_entry(library, title, revision):
    """Return a corporate-author BibTeX entry for one versioned report."""
    report = REPORTS[library]
    url = PROJECT_URL + f"docs/pdf/{library}/FullProof.pdf"
    note = "Draft mathematical proof report; content revision " + str(revision)
    return "\n".join([
        "@techreport{" + report["key"] + ",",
        "  author = {{LangevinLean Project}},",
        "  title = {{" + _bibtext(title) + "}},",
        "  institution = {LangevinLean Project},",
        "  number = {" + report["number"] + "},",
        "  year = {2026},",
        "  url = {" + url + "},",
        "  note = {" + _bibtext(note) + "}",
        "}", "",
    ])


def project_bibtex():
    """Return the project-level entry used by the main page."""
    return "\n".join([
        "@misc{LangevinLeanProject2026,",
        "  author = {{LangevinLean Project}},",
        "  title = {{LangevinLean: Formalized Langevin Algorithms}},",
        "  year = {2026},",
        "  url = {" + PROJECT_URL + "},",
        "  note = {Draft mathematical expositions and formally checked proofs}",
        "}", "",
    ])


def _relative(target, page):
    return Path(os.path.relpath(ROOT / target, (ROOT / page).parent)).as_posix()


def _section_reference(section, pdf_url):
    """Accept plain text, a (text, URL) pair, or a section metadata mapping."""
    if isinstance(section, Mapping):
        text = section.get("text")
        if not text:
            number, title = section.get("number", section.get("section")), section.get("title")
            text = "Section " + str(number) if number is not None else ""
            if title:
                text += (": " if text else "") + str(title)
        href = section.get("href") or section.get("url")
        if not href and section.get("anchor"):
            href = pdf_url + "#nameddest=" + str(section["anchor"])
    elif isinstance(section, (tuple, list)) and len(section) == 2:
        text, href = section
    else:
        text, href = section, None
    text = escape(str(text))
    if href:
        text = '<a href="' + escape(str(href), quote=True) + '">' + text + '</a>'
    return '<p class="small">Precise report location: ' + text + '.</p>'


def citation_panel(library, title, revision, page, section=None):
    """Render a keyboard-accessible BibTeX panel using the shared copy control.

    ``section`` may be readable text, ``(text, href)``, or a mapping with
    ``text`` (alternatively ``number``/``title``) and ``href`` or PDF ``anchor``.
    The project page passes ``library=None`` and does not need a revision.
    """
    if library is None:
        entry, target = project_bibtex(), "docs/bib/project.bib"
        summary = "Cite the LangevinLean Project"
        links = '<a href="' + PROJECT_URL + '">Project website</a>'
        pdf_url = None
    else:
        entry = bibliography_entry(library, title, revision)
        target = f"docs/bib/{library}.bib"
        summary = "Cite this report (BibTeX)"
        pdf_url = _relative(f"docs/pdf/{library}/FullProof.pdf", page)
        links = '<a href="' + escape(pdf_url, quote=True) + '">Mathematical proof report (PDF)</a>'
    identity = "|".join((str(page), str(library), str(section)))
    identifier = "report-bibtex-" + hashlib.sha256(identity.encode()).hexdigest()[:12]
    return (
        '<details class="section citation-panel" aria-label="Bibliographic citation">'
        '<summary>' + escape(summary) + '</summary>'
        + (_section_reference(section, pdf_url) if section is not None else "")
        + '<p>' + links + ' · <a href="' + escape(_relative(target, page), quote=True)
        + '" download>Download BibTeX</a></p>'
        + '<button class="copy" type="button" data-copy="' + identifier
        + '" aria-label="Copy BibTeX citation">Copy BibTeX</button>'
        + '<pre class="commands"><code id="' + identifier + '">' + escape(entry)
        + '</code></pre></details>'
    )


def bib_outputs(plans):
    """Return the individual, combined, and project-level BibTeX artifacts."""
    outputs, entries = {}, []
    for library in REPORT_ORDER:
        if library not in plans:
            continue
        plan = plans[library]
        revision = plan.get("revision", plan.get("content_revision"))
        if revision is None:
            raise ValueError("Missing content revision for report " + library)
        entry = bibliography_entry(library, plan["title"], revision)
        outputs[f"docs/bib/{library}.bib"] = entry
        entries.append(entry)
    outputs["docs/bib/all-reports.bib"] = "\n".join(entries)
    outputs["docs/bib/project.bib"] = project_bibtex()
    return outputs
