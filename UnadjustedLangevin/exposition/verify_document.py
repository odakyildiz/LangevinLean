#!/usr/bin/env python3
"""Check every displayed Lean line and local link in the generated document."""
from __future__ import annotations
import hashlib
import json
from html.parser import HTMLParser
from pathlib import Path
from build_document import OUT, ROOT, HERE, ENTRY_POINTS, load_document


class Document(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.ids, self.links, self.excerpts, self.scripts = [], [], [], {}
        self.pre = self.line = self.script = None
        self.line_depth = 0
        self.complete_proofs = 0
        self.declarations = 0
        self.external_resources = []
        self.beginner_notes = {"setup":0,"statement":0,"proof":0}

    def handle_starttag(self, tag, attributes):
        attrs = dict(attributes)
        if "id" in attrs:
            self.ids.append(attrs["id"])
        if tag == "a" and attrs.get("href", "").startswith("#"):
            self.links.append(attrs["href"][1:])
        if tag in ("script", "link", "img", "iframe"):
            if url := attrs.get("src", attrs.get("href", "")):
                self.external_resources.append(url)
        if tag == "article" and attrs.get("class") == "declaration":
            self.declarations += 1
        if tag == "details" and attrs.get("class") == "full-proof":
            assert "open" in attrs, "Repeated proofs should be initially visible"
            self.complete_proofs += 1
        if tag == "details" and attrs.get("class") == "lean-note":
            self.beginner_notes[attrs["data-note-kind"]] += 1
        if tag == "script":
            self.script = attrs.get("id", "inline-script")
            self.scripts[self.script] = ""
        if tag == "pre" and attrs.get("class") == "lean-code":
            self.pre = {**attrs, "lines": []}
        if self.pre is not None and tag == "span":
            if attrs.get("class") == "line-text":
                self.line, self.line_depth = "", 1
            elif self.line is not None:
                self.line_depth += 1

    def handle_endtag(self, tag):
        if tag == "script":
            self.script = None
        if tag == "span" and self.line is not None:
            self.line_depth -= 1
            if self.line_depth == 0:
                self.pre["lines"].append(self.line)
                self.line = None
        if tag == "pre" and self.pre is not None:
            self.excerpts.append(self.pre)
            self.pre = None

    def handle_data(self, data):
        if self.script is not None:
            self.scripts[self.script] += data
        if self.line is not None:
            self.line += data


def verify():
    sections, sources = load_document()  # Also checks every proof-body range.
    text = OUT.read_text()
    assert text.startswith('<!doctype html>'), "Output is an HTML fragment instead of a complete document"
    doc = Document()
    doc.feed(text)
    assert len(doc.ids) == len(set(doc.ids)), "Duplicate HTML ids"
    missing = set(doc.links)-set(doc.ids)
    assert not missing, f"Broken internal links: {missing}"
    assert not doc.external_resources, f"External resources: {doc.external_resources}"
    assert 'url(fonts/' not in text and 'url(http' not in text, "Nonembedded fonts"
    assert 'katex-error' not in text, "Failed mathematical rendering"
    embedded = json.loads(doc.scripts["lean-sources"])
    assert embedded == sources, "Embedded sources differ from repository files"
    manifest = json.loads(doc.scripts["source-manifest"])
    assert manifest["sources"] == {p:hashlib.sha256(v.encode()).hexdigest() for p,v in sources.items()}
    for block in doc.excerpts:
        path = block["data-source"]
        start, end = int(block["data-start"]), int(block["data-end"])
        expected = sources[path].splitlines()[start-1:end]
        assert block["lines"] == expected, f"Altered source excerpt {path}:{start}-{end}"
    expected_count = sum(len(s["declarations"]) for s in sections)
    assert doc.declarations == doc.complete_proofs == manifest["declarations"] == expected_count
    assert sum(b["data-role"] == "full-proof" for b in doc.excerpts) == expected_count
    assert sum(b["data-role"] == "module" for b in doc.excerpts) == len(sources)
    expected_steps = sum(len(d["steps"]) for s in sections for d in s["declarations"])
    assert doc.beginner_notes == dict(setup=len(sections),statement=expected_count,proof=expected_steps)
    assert 'id="lean-unicode"' in text and 'id="lean-affine-map"' in text
    assert text.index('id="main-theorem"') < text.index('id="lean-beginner-guide"')
    assert 'id="main-reference-assumptions"' in text
    shared = next(s for s in sections if s["file"] == "UnadjustedLangevin/HilbertDalalyan.lean")
    wrappers = next(s for s in sections if s["file"] == "UnadjustedLangevin/L2Convergence.lean")
    assert {d["name"] for d in shared["declarations"]} >= {
        "lpChain", "L2Reference", "l2_reference_bound",
        "dalalyan_small_step_of_integral_reference", "dalalyan_large_step_of_integral_reference"}
    assert any(d["name"] == "hilbert_lpChain_eq_lpUlaChain" for d in wrappers["declarations"])
    assert "Exact Lean statements of the canonical results" in text
    assert 'data-source="UnadjustedLangevin/CanonicalULA.lean"' in text
    assert "Gibbs invariance and the complete coupling-family construction remain open" not in text
    assert '<style>' in text and 'class="katex' in text, "Missing styles or prerendered mathematics"
    main = text.split('<section class="main-theorem"',1)[1].split('</section>',1)[0]
    assert main.count('class="katex') > 20, "Main theorem mathematics is not prerendered"
    assert '\\(' not in main and '\\[' not in main, "Unrendered TeX delimiters in the main theorem"
    for name,target in ENTRY_POINTS.items():
        entry = (HERE/name).read_text()
        assert f'content="0;url={target}"' in entry, f"Wrong entry-point redirect: {name}"
        assert f'href="{target}"' in entry, f"Missing fallback link: {name}"
        assert '\\(' not in entry and '\\[' not in entry, f"Raw mathematical template in public entry point: {name}"
        destination = HERE/target.split('#')[0]
        assert destination.is_file(), f"Missing entry-point target: {name}"
        if '#' in target:
            assert target.split('#',1)[1] in doc.ids, f"Broken entry-point anchor: {name}"
    print(f"Verified {doc.declarations} complete proofs, {sum(doc.beginner_notes.values())} beginner notes, {len(doc.excerpts)} exact source listings, {len(doc.links)} internal links, {len(sources)} embedded files; no external resources.")


if __name__ == "__main__":
    verify()
