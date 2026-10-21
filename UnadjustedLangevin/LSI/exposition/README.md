# LSI proof page

Open [index.html](index.html) directly in a browser. The complete page works
offline, including mathematical typesetting and fonts, exact Lean proofs,
source search, and copying or saving the embedded source files. Its contents
are also linked from the repository homepage and the strongly convex ULA page.

The mathematical explanations are authored in `chapters.json`. Every LSI
definition and theorem is paired with its complete declaration, read directly
from the Lean files. `reference_audit.json` records the comparison with
Vempala–Wibisono (2019), including the scalar proof variation and the unproved
analytic bridges. Both the introduction and the theorem discussion retain the
conditional status of the current formalization.

Regenerate and verify from the repository root:

```sh
python3 -B UnadjustedLangevin/LSI/exposition/build_document.py
python3 -B UnadjustedLangevin/LSI/exposition/verify_document.py
```

Building uses Python 3, Node.js, and the existing vendored KaTeX from the ULA
exposition. No network connection or package installation is needed. `page.css`
and `page.js` supply the responsive layout and reading/source controls.

The builder rejects missing declaration explanations and malformed formulas.
The verifier compares every displayed source line and embedded file with the
repository, verifies the source and authoring-input hashes, checks every local
link, and rejects external resource dependencies. These integrity checks do
not prove analytic hypotheses that remain explicit in the Lean theorem.

Compile the proofs and run their kernel dependency audit separately:

```sh
lake build UnadjustedLangevin IPLA +UnadjustedLangevin.LSI.Check
lake env lean UnadjustedLangevin/LSI/Check.lean
```
