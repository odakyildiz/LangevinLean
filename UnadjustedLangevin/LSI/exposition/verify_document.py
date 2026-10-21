#!/usr/bin/env python3
"""Check the LSI page's exact proof excerpts, complete sources, math and links."""
from __future__ import annotations

import hashlib
import json
import re
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urlsplit

from build_document import HERE, OUT, ROOT, load_inputs


class Document(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.ids, self.links, self.resources = [], [], []
        self.excerpts, self.scripts = [], {}
        self.classes = {}
        self.pre = self.line = self.script = None
        self.line_depth = 0
        self.style_depth = self.pre_depth = 0
        self.prose = []

    def handle_starttag(self, tag, attributes):
        attrs = dict(attributes)
        if identifier := attrs.get("id"):
            self.ids.append(identifier)
        for name in attrs.get("class", "").split():
            self.classes[name] = self.classes.get(name, 0) + 1
        if tag == "a" and "href" in attrs:
            self.links.append(attrs["href"])
        if tag in ("script", "link", "img", "iframe", "video", "audio"):
            if url := attrs.get("src", attrs.get("href", "")):
                self.resources.append(url)
        if tag == "style":
            self.style_depth += 1
        if tag == "script":
            self.script = attrs.get("id", "inline-script")
            self.scripts[self.script] = ""
        if tag == "pre":
            self.pre_depth += 1
            if attrs.get("class") == "lean-code":
                self.pre = {**attrs, "lines": []}
        if self.pre is not None and tag == "span":
            if attrs.get("class") == "line-text":
                self.line, self.line_depth = "", 1
            elif self.line is not None:
                self.line_depth += 1

    def handle_endtag(self, tag):
        if tag == "style":
            self.style_depth -= 1
        if tag == "script":
            self.script = None
        if tag == "span" and self.line is not None:
            self.line_depth -= 1
            if self.line_depth == 0:
                self.pre["lines"].append(self.line)
                self.line = None
        if tag == "pre":
            self.pre_depth -= 1
            if self.pre is not None:
                self.excerpts.append(self.pre)
                self.pre = None

    def handle_data(self, data):
        if self.script is not None:
            self.scripts[self.script] += data
        if self.line is not None:
            self.line += data
        if self.script is None and not self.style_depth and not self.pre_depth:
            self.prose.append(data)


def verify():
    content, audit, sources, parsed, represented = load_inputs()
    text = OUT.read_text()
    assert text.startswith('<!doctype html>'), "Not a complete HTML page"
    doc = Document()
    doc.feed(text)
    assert len(doc.ids) == len(set(doc.ids)), "Duplicate HTML identifiers"
    identifiers = set(doc.ids)
    for href in doc.links:
        link = urlsplit(href)
        if link.scheme or link.netloc:
            assert link.scheme in ("https", "http"), f"Unexpected link scheme: {href}"
            continue
        if not link.path:
            assert unquote(link.fragment) in identifiers, f"Broken section/line link: {href}"
        else:
            target = (HERE / unquote(link.path)).resolve()
            assert target.is_relative_to(ROOT) and target.is_file(), f"Broken repository link: {href}"
    assert not doc.resources, f"External page dependencies: {doc.resources}"
    assert 'url(fonts/' not in text and 'url(http' not in text, "Fonts are not embedded"
    assert 'katex-error' not in text, "Failed mathematical rendering"
    assert not re.search(r'\\[\[(]', ''.join(doc.prose)), "Unrendered math delimiters"
    assert 'Conditional Lean formalization.' in ''.join(doc.prose), "Missing conditional status"
    assert json.loads(doc.scripts["lean-sources"]) == sources, "Embedded source differs from repository"
    manifest = json.loads(doc.scripts["source-manifest"])
    assert manifest == json.loads((HERE / 'source_manifest.json').read_text()), "Manifest differs from page"
    assert manifest["sources"] == {
        path: hashlib.sha256(source.encode()).hexdigest() for path, source in sources.items()
    }, "Stale source hashes"
    for path, digest in manifest["inputs"].items():
        assert hashlib.sha256((HERE / path).read_bytes()).hexdigest() == digest, f"Stale input: {path}"
    excerpted = set()
    module_paths = []
    for block in doc.excerpts:
        path = block["data-source"]
        start, end = int(block["data-start"]), int(block["data-end"])
        assert block["lines"] == sources[path].splitlines()[start - 1:end], f"Altered source: {path}:{start}"
        if block["data-role"] == "declaration":
            name = block["data-declaration"]
            declaration = parsed[path][name]
            assert (start, end) == (declaration["start"], declaration["end"]), f"Truncated declaration: {name}"
            excerpted.add((path, name))
        else:
            assert start == 1 and end == len(sources[path].splitlines()), f"Truncated module: {path}"
            module_paths.append(path)
    assert excerpted == represented, "Missing proof excerpt"
    assert set(module_paths) == set(sources) and len(module_paths) == len(sources), "Missing/duplicate module"
    assert manifest["explained_declarations"] == len(represented)
    assert manifest["sections"] == len(content["sections"])
    steps = sum(len(section["steps"]) for section in content["sections"])
    assert manifest["steps"] == doc.classes["proof-step"] == steps
    assert len(audit["checks"]) == len([identifier for identifier in doc.ids if identifier.startswith('audit-')])
    for key in ["reading-mode", "toggle-proofs", "print-document", "source-search", "action-status"]:
        assert key in identifiers, f"Missing page control: {key}"
    print(f"Verified {len(content['sections'])} chapters, {steps} proof steps, "
          f"{len(represented)} complete explained declarations, {len(sources)} embedded files, "
          f"{len(doc.links)} links, and {len(audit['checks'])} reference checks; "
          "all source lines exact and all resources offline.")


if __name__ == "__main__":
    verify()
