#!/usr/bin/env python3
"""Reader-facing coverage and ordering checks for the latent-diffusion page.

The source verifier checks exact TeX inventory, Lean declarations, hashes and
regeneration.  These independent checks catch a different failure: a valid
catalogue that hides paper results, merges added premises into paper assumptions,
or presents new theory before the paper and its corrections.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from html import escape
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import unittest


ROOT = Path(__file__).resolve().parents[1]
PAGE = ROOT / "LatentDiffusion/exposition/index.html"
AUDIT = ROOT / "LatentDiffusion/exposition/reference_audit.json"
NEW_THEOREMS = {
    "batch-corrections", "tilted-model-bias", "euler-contraction",
    "particle-normalized-geometry", "robust-euler", "integral-euler",
    "stochastic-oracle", "pointwise-probability-lift", "heterogeneous-average",
    "finite-population-oracle", "complete-numerical-budget", "explicit-accuracy",
}
VOID = {"area", "base", "br", "col", "embed", "hr", "img", "input", "link",
        "meta", "param", "source", "track", "wbr"}


@dataclass
class Element:
    tag: str
    attrs: dict[str, str]
    order: int
    children: list[Element | str] = field(default_factory=list)
    parent: Element | None = None

    def elements(self):
        for child in self.children:
            if isinstance(child, Element):
                yield child
                yield from child.elements()

    def text(self):
        return "".join(child.text() if isinstance(child, Element) else child
                       for child in self.children)

    def has_class(self, value):
        return value in self.attrs.get("class", "").split()

    def contains(self, child):
        while child is not None:
            if child is self:
                return True
            child = child.parent
        return False


class Document(HTMLParser):
    def __init__(self, source):
        super().__init__(convert_charrefs=True)
        self.root = Element("document", {}, -1)
        self.stack = [self.root]
        self.counter = 0
        self.feed(source)

    def handle_starttag(self, tag, attrs):
        node = Element(tag, dict(attrs), self.counter, parent=self.stack[-1])
        self.counter += 1
        self.stack[-1].children.append(node)
        if tag not in VOID:
            self.stack.append(node)

    def handle_startendtag(self, tag, attrs):
        self.handle_starttag(tag, attrs)
        if tag not in VOID:
            self.stack.pop()

    def handle_endtag(self, tag):
        for position in range(len(self.stack) - 1, 0, -1):
            if self.stack[position].tag == tag:
                del self.stack[position:]
                return

    def handle_data(self, data):
        self.stack[-1].children.append(data)


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def normalized(text):
    return " ".join(text.split())


def validate_landing(source, audit):
    """Validate the page without importing its generator or trusting its panels."""
    document = Document(source)
    nodes = list(document.root.elements())

    def unique(identifier):
        matches = [node for node in nodes if node.attrs.get("id") == identifier]
        require(len(matches) == 1, f"Expected one landing section/card: {identifier}")
        return matches[0]

    assumptions = unique("assumptions")
    contracts = unique("source-contracts")
    paper = unique("source-results")
    new = unique("new-theory")
    new_assumptions = unique("new-assumptions")
    new_theorems = unique("new-theorems")
    require(assumptions.order < contracts.order < paper.order < new.order,
            "Paper assumptions, formalization premises and source results must precede new theory")
    require(new.attrs.get("data-new-theory") == "true",
            "The new-theory block must be explicitly identified")
    require(new.contains(new_assumptions) and new.contains(new_theorems),
            "New Assumptions and New Theorems must be inside New theory")
    require(new_assumptions.order < new_theorems.order,
            "New Assumptions must precede New Theorems")
    for section, heading in ((new_assumptions, "New Assumptions"),
                             (new_theorems, "New Theorems")):
        headings = [node.text() for node in section.elements()
                    if node.tag in {"h2", "h3"}]
        require(any(heading.lower() in text.lower() for text in headings),
                f"Missing explicit heading: {heading}")

    source_assumption_ids = []
    for node in assumptions.elements():
        if node.tag in {"h3", "h4"}:
            match = re.match(r"\s*(A\d+)\b", node.text())
            if match:
                source_assumption_ids.append(match[1])
        require(not node.attrs.get("data-assumption-id", "").startswith("N"),
                "New assumptions cannot appear among paper assumptions")
        if node.tag in {"h3", "h4"}:
            require(not re.match(r"\s*(?:N\d+|V1|C1)\b", node.text()),
                    "Added domains and analytic bridges need their own section")
    require(source_assumption_ids == ["A1", "A2", "A3", "A4"],
            "The source-assumptions section must state A1–A4 explicitly and in order")

    required_assumptions = {f"N{i}" for i in range(1, 8)}
    numerical_assumptions = [node for node in nodes
                             if node.attrs.get("data-assumption-id") in required_assumptions]
    require(len(numerical_assumptions) == 7 and
            {node.attrs["data-assumption-id"] for node in numerical_assumptions} == required_assumptions,
            "New Assumptions must include N1–N7 exactly once")
    for node in numerical_assumptions:
        require(new_assumptions.contains(node),
                f"{node.attrs['data-assumption-id']} lies outside New Assumptions")
        require(any(child.tag == "pre" for child in node.elements()),
                f"{node.attrs['data-assumption-id']} is missing its exact Lean premise")

    records = {record["id"]: record for record in audit["results"]}
    require(len(records) == 19, "The source ledger must retain all 19 paper results")
    cards = [node for node in nodes if "data-source-result" in node.attrs]
    require(len(cards) == len(records) and
            {node.attrs["data-source-result"] for node in cards} == set(records),
            "The landing page must state all 19 source results exactly once")
    for card in cards:
        identifier = card.attrs["data-source-result"]
        record = records[identifier]
        require(paper.contains(card), f"Source result is outside the source section: {identifier}")
        descendants = list(card.elements())
        references = [node for node in [card] + descendants
                      if node.attrs.get("data-source-path") == record["source"] and
                      node.attrs.get("data-source-start") == str(record["start_line"]) and
                      node.attrs.get("data-source-end") == str(record["end_line"])]
        require(references, f"Missing precise manuscript reference for {identifier}")
        exact_tex = normalized(record["exact_tex"])
        require(any(node.tag == "details" and exact_tex in normalized(node.text())
                    for node in descendants),
                f"Missing exact printed source statement for {identifier}")
        status = card.attrs.get("data-formal-status", "").strip()
        require(status, f"Missing explicit formal status for {identifier}")
        visible = normalized(card.text())
        require(re.search(r"\b(formali[sz]|proved|checked|unproved|open|partial|conditional|reconstruct|refut|correct)",
                          visible, re.I),
                f"Missing reader-facing formalization status for {identifier}")
        require(any(node.has_class("statement-math") for node in descendants),
                f"A source citation cannot replace the mathematical statement: {identifier}")
        if status in {"open", "partial", "conditional", "refuted"}:
            require(not re.search(r"(?:^|[.!?]\s+)(?:This (?:result|theorem|statement) is )?"
                                  r"(?:fully reconstructed|fully formalized|proved without added assumptions)\b",
                                  visible, re.I),
                    f"A source result with unresolved premises claims full reconstruction: {identifier}")

    for node in nodes:
        if node.has_class("category-new"):
            require(new.contains(node), "A new-theory card occurs before the new-theory block")
    for identifier in NEW_THEOREMS:
        card = unique(identifier)
        require(new_theorems.contains(card), f"New theorem lies outside New Theorems: {identifier}")
        descendants = list(card.elements())
        require(any(node.has_class("statement-math") for node in descendants) and
                any(node.has_class("statement-lean") for node in descendants) and
                any(node.tag == "pre" for node in descendants),
                f"New theorem needs mathematics and exact Lean together: {identifier}")
    for node in nodes:
        if node.has_class("statement-math"):
            require(not re.search(r"\b(?:TODO|TBD|PLACEHOLDER)\b", node.text()),
                    "Reader-facing mathematical statement contains an authoring placeholder")


class LandingContractTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.audit = json.loads(AUDIT.read_text())

    def fixture(self):
        def pair(prose):
            return ('<div class="statement-pair"><div class="statement-math">' + prose +
                    '</div><aside class="statement-lean"><pre data-role="statement">'
                    'theorem example : 0 ≤ 1</pre></aside></div>')

        paper = []
        for record in self.audit["results"]:
            paper.append('<article data-source-result="' + escape(record["id"]) +
                         '" data-formal-status="partial">' + pair(
                             '<p>Formal status: the stated conclusion is conditional on explicit analytic premises.</p>') +
                         '<a data-source-path="' + record["source"] +
                         '" data-source-start="' + str(record["start_line"]) +
                         '" data-source-end="' + str(record["end_line"]) + '">Source</a>' +
                         '<details><summary>Exact printed source</summary><pre>' +
                         escape(record["exact_tex"]) + '</pre></details></article>')
        assumptions = ''.join(f'<article><h3>A{i} — Source condition</h3></article>'
                              for i in range(1, 5))
        new_assumptions = ''.join(f'<article data-assumption-id="N{i}" class="category-new">' +
                                 pair('The explicit primitive force premise.') + '</article>'
                                 for i in range(1, 8))
        new_theorems = ''.join(f'<article id="{identifier}" class="category-new">' +
                              pair('The quantitative conclusion and its contribution to the paper.') + '</article>'
                              for identifier in sorted(NEW_THEOREMS))
        return ('<main><section id="assumptions">' + assumptions + '</section>' +
                '<section id="source-contracts"><h2>Additional formalization premises</h2></section>' +
                '<section id="source-results">' + ''.join(paper) + '</section>' +
                '<section id="new-theory" data-new-theory="true">' +
                '<section id="new-assumptions"><h2>New Assumptions</h2>' + new_assumptions + '</section>' +
                '<section id="new-theorems"><h2>New Theorems</h2>' + new_theorems + '</section>' +
                '</section></main>')

    def check(self, source):
        validate_landing(source, self.audit)

    def test_generated_page_meets_reader_contract(self):
        self.check(PAGE.read_text())

    def test_complete_source_first_fixture_passes(self):
        self.check(self.fixture())

    def test_missing_main_error_theorem_is_rejected(self):
        with self.assertRaisesRegex(AssertionError, "all 19"):
            self.check(self.fixture().replace('data-source-result="thrm:error-bound"', ''))

    def test_missing_supplementary_lemma_is_rejected(self):
        with self.assertRaisesRegex(AssertionError, "all 19"):
            self.check(self.fixture().replace('data-source-result="lem:temporal_discretization"', ''))

    def test_duplicate_source_result_is_rejected(self):
        with self.assertRaisesRegex(AssertionError, "all 19"):
            self.check(self.fixture().replace('data-source-result="lem:temporal_discretization"',
                                             'data-source-result="thrm:error-bound"'))

    def test_source_line_ranges_cannot_be_inexact(self):
        with self.assertRaisesRegex(AssertionError, "precise manuscript"):
            self.check(self.fixture().replace('data-source-start="208"', 'data-source-start="207"'))

    def test_source_links_do_not_replace_exact_printed_statements(self):
        source = self.fixture()
        source = source.replace(escape(self.audit["results"][0]["exact_tex"]), 'Read the source file.', 1)
        with self.assertRaisesRegex(AssertionError, "exact printed source"):
            self.check(source)

    def test_source_cards_cannot_hide_their_formalization_status(self):
        with self.assertRaisesRegex(AssertionError, "formal status"):
            self.check(self.fixture().replace('data-formal-status="partial"', '', 1))

    def test_partial_result_cannot_claim_full_reconstruction(self):
        with self.assertRaisesRegex(AssertionError, "claims full reconstruction"):
            self.check(self.fixture().replace('Formal status: the stated conclusion is conditional',
                                             'Fully reconstructed. Formal status: the conclusion is conditional', 1))

    def test_new_theory_cannot_precede_paper_results(self):
        source = self.fixture().replace('id="source-results"', 'id="swap"')
        source = source.replace('id="new-theory"', 'id="source-results"')
        source = source.replace('id="swap"', 'id="new-theory"')
        with self.assertRaisesRegex(AssertionError, "must precede"):
            self.check(source)

    def test_added_assumptions_cannot_be_presented_as_paper_assumptions(self):
        with self.assertRaisesRegex(AssertionError, "own section"):
            self.check(self.fixture().replace('A4 — Source condition', 'N1 — Added force condition'))

    def test_new_assumptions_must_be_separate_and_complete(self):
        with self.assertRaisesRegex(AssertionError, "N1–N7"):
            self.check(self.fixture().replace('data-assumption-id="N7"', ''))

    def test_exact_lean_cannot_be_replaced_by_a_proof_link(self):
        source = self.fixture().replace('<pre data-role="statement">theorem example : 0 ≤ 1</pre>',
                                        '<a href="proof.html">Read Lean</a>')
        with self.assertRaisesRegex(AssertionError, "exact Lean"):
            self.check(source)

    def test_new_theorems_require_their_own_explicit_heading(self):
        with self.assertRaisesRegex(AssertionError, "explicit heading"):
            self.check(self.fixture().replace('<h2>New Theorems</h2>', '<h2>Further details</h2>'))

    def test_authoring_placeholders_are_rejected(self):
        with self.assertRaisesRegex(AssertionError, "placeholder"):
            self.check(self.fixture().replace('The quantitative conclusion', 'TODO quantitative conclusion', 1))


if __name__ == "__main__":
    unittest.main()
