"""Build and import-test a deck using the installed Anki application's own backend.

On this Mac:
  PYTHONPATH=/Applications/Anki.app/Contents/Resources/app_packages \
    /opt/homebrew/bin/python3.13 GradientDescent/exposition/Flashcards/build_deck.py

All collections used here live in temporary directories. The user's collection
is never opened. Equations use Anki's built-in MathJax, without external assets.
"""
import csv
import hashlib
import html
import json
import re
import tempfile
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from html.parser import HTMLParser

from anki.collection import Collection
from anki.import_export_pb2 import ExportAnkiPackageOptions, ExportLimit, ImportAnkiPackageRequest

HERE = Path(__file__).resolve().parent
LEAN = HERE.parent.parent
NAME = "Gradient Descent - Math and Lean"
FIELDS = ["ID", "Module", "Topic", "Kind", "Prompt", "Answer", "Takeaway", "Source", "FrontCode", "BackCode"]
QA = Path("/private/tmp/gradient-descent-anki-qa")
QA.mkdir(exist_ok=True)


class Text(HTMLParser):
    def __init__(self):
        super().__init__()
        self.bits = []

    def handle_data(self, data):
        self.bits.append(data)


def plain(s):
    p = Text()
    p.feed(s)
    return " ".join(p.bits)


def protect_math(s):
    # HTML must not consume a less-than sign or an aligned-environment '&'.
    def protect(m):
        return html.escape(html.unescape(m[0]), quote=False)
    return re.sub(r"\\\(.*?\\\)|\\\[.*?\\\]", protect, s, flags=re.S)


KEYWORDS = {"theorem", "lemma", "def", "variable", "fun", "by", "have", "let", "with", "zero", "succ", "calc"}
TACTICS = {"rw", "rwa", "simp", "simpa", "exact", "apply", "intro", "obtain", "refine", "constructor", "change", "dsimp", "linarith", "nlinarith", "ring", "positivity", "rfl", "convert", "ext", "funext", "norm_num", "field_simp", "module", "abel", "induction"}


def highlight(line):
    return "".join('<span class="' + ("kw" if p in KEYWORDS else "tactic") + '">' + html.escape(p) + '</span>'
                   if p in KEYWORDS | TACTICS else html.escape(p)
                   for p in re.split(r"(\b[A-Za-z_]+\b)", line))


def snippet(c):
    lines = (LEAN / c["file"]).read_text().splitlines()
    start, end = c["start"], c["end"]
    assert 1 <= start <= end <= len(lines), c
    spans = ['<span class="code-line"><span class="line-number">' + str(i) +
             '</span><span class="code-text">' + highlight(lines[i - 1]) + '</span></span>'
             for i in range(start, end + 1)]
    label = html.escape(c["file"]) + ":" + str(start) + "-" + str(end)
    return '<div class="snippet-source">' + label + '</div><pre class="lean-code"><code>' + "".join(spans) + '</code></pre>'


def main():
    cards = []
    for file in ["cards_foundations.json", "cards_strong.json", "cards_smooth.json", "cards_rates.json"]:
        cards.extend(json.loads((HERE / file).read_text())["cards"])
    cards.sort(key=lambda c: c["module"][:2])  # stable authored order within a module
    assert len({c["id"] for c in cards}) == len(cards), "Duplicate stable card IDs"
    assert len({plain(c["front"]) for c in cards}) == len(cards), "Duplicate questions"
    for c in cards:
        assert c["front"].strip() and c["answer"].strip() and c["takeaway"].strip(), c["id"]
        for k in ["front", "answer"]:
            for left, right in [(r"\(", r"\)"), (r"\[", r"\]")]:
                assert c[k].count(left) == c[k].count(right), (c["id"], k, left)
        for r in c["refs"]:
            lines = (LEAN / r["file"]).read_text().splitlines()
            assert 1 <= r["start"] <= r["end"] <= len(lines), (c["id"], r)

    output = HERE / "GradientDescent_Math_and_Lean.apkg"
    rendered = []
    rows = []
    with tempfile.TemporaryDirectory(prefix="gd-anki-build-", dir="/private/tmp") as tmp:
        col = Collection(str(Path(tmp) / "collection.anki2"))
        root = col.decks.id(NAME)
        model = col.models.new("Gradient Descent - Atomic Review")
        for name in FIELDS:
            col.models.add_field(model, col.models.new_field(name))
        template = col.models.new_template("Recall")
        template["qfmt"] = (HERE / "front.html").read_text()
        template["afmt"] = (HERE / "back.html").read_text()
        col.models.add_template(model, template)
        model["css"] = (HERE / "card_style.css").read_text()
        model["sortf"] = 0
        col.models.add(model)
        for n, c in enumerate(cards, 1):
            deck_id = col.decks.id(NAME + "::" + c["module"])
            note = col.new_note(model)
            note.guid = hashlib.sha256(("gd-review-v1:" + c["id"]).encode()).hexdigest()[:20]
            source = "; ".join(r["file"] + ":" + str(r["start"]) + "-" + str(r["end"]) for r in c["refs"])
            if not source:
                source = "GradientDescent.pdf, opening Lean dictionary and common setting."
            else:
                source += ". Matching source blocks are explained in GradientDescent.pdf."
            values = [f"GD {n:03d} / {len(cards)}", c["module"], c["topic"], c["kind"],
                      protect_math(c["front"]), protect_math(c["answer"]), html.escape(c["takeaway"]),
                      html.escape(source), "", ""]
            if c.get("code"):
                values[8 if c["code"]["side"] == "front" else 9] = snippet(c["code"])
            for field, value in zip(FIELDS, values):
                note[field] = value
            note.tags = ["GradientDescent", "GD::" + c["module"][:2], "GD::" + c["kind"]]
            col.add_note(note, deck_id)
            card = note.cards()[0]
            rendered.append(dict(id=c["id"], index=n, module=c["module"], kind=c["kind"],
                                 topic=c["topic"], question=card.question(), answer=card.answer()))
            rows.append(values + [" ".join(note.tags)])
        total = col.export_anki_package(
            out_path=str(output),
            options=ExportAnkiPackageOptions(with_scheduling=False, with_deck_configs=False,
                                            with_media=False, legacy=True),
            limit=ExportLimit(deck_id=root))
        assert total == len(cards), (total, len(cards))
        col.close()

    # Test with Anki's real importer, without touching the user's collection.
    with tempfile.TemporaryDirectory(prefix="gd-anki-import-", dir="/private/tmp") as tmp:
        col = Collection(str(Path(tmp) / "collection.anki2"))
        col.import_anki_package(ImportAnkiPackageRequest(package_path=str(output)))
        imported = col.find_cards('deck:"' + NAME + '"')
        assert len(imported) == len(cards), (len(imported), len(cards))
        assert len(col.find_cards('deck:"' + NAME + '" is:new')) == len(cards)
        assert len(col.find_cards('deck:"' + NAME + '" is:suspended')) == 0
        for cid in imported:
            card = col.get_card(cid)
            note = card.note()
            assert note["Prompt"] and note["Answer"]
            assert "<main" in card.question() and "Remember" in card.answer()
        col.import_anki_package(ImportAnkiPackageRequest(package_path=str(output)))
        assert len(col.find_cards('deck:"' + NAME + '"')) == len(cards), "Reimport duplicated cards"
        col.close()

    (QA / "rendered_cards.json").write_text(json.dumps(rendered, ensure_ascii=False))
    # A source/editing backup; the APKG is the complete styled deck to import.
    with (HERE / "cards.tsv").open("w", newline="") as f:
        f.write("#separator:Tab\n#html:true\n#notetype:Gradient Descent - Atomic Review\n")
        f.write("#columns:" + "\t".join(FIELDS + ["Tags"]) + "\n#tags column:11\n")
        writer = csv.writer(f, delimiter="\t", lineterminator="\n")
        writer.writerows(rows)
    manifest = dict(created_utc=datetime.now(timezone.utc).isoformat(), total_cards=len(cards),
                    modules=dict(Counter(c["module"] for c in cards)),
                    kinds=dict(Counter(c["kind"] for c in cards)),
                    source_sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in LEAN.glob("*.lean")},
                    package_sha256=hashlib.sha256(output.read_bytes()).hexdigest(),
                    import_test="Anki native backend: all new, none suspended; repeated import produces no duplicates",
                    cards=[dict(id=c["id"], refs=c["refs"], code=c.get("code")) for c in cards])
    (HERE / "deck_manifest.json").write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({k:manifest[k] for k in ["total_cards", "modules", "kinds", "import_test"]}, indent=2))
    print("Saved", output)


if __name__ == "__main__":
    main()
