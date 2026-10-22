# ULA-LSI proof pages

[index.html](index.html) states the unconditional actual-law theorem, gives its
mathematical proof and Lean statement, provides the proof diagram, and offers a
LaTeX download. [proof.html](proof.html) is the detailed source-by-source archive,
including every LSI declaration and its full proof. Mathematical typesetting,
fonts, source search and embedded sources work offline.

The final theorem is `ULA.LSI.ula_kl_bound` in
[UnconditionalTheorem.lean](../UnconditionalTheorem.lean). Its assumptions are
LSI for the normalized Gibbs target, a differentiable potential with Lipschitz
gradient, positive constants, the stated step restriction and finite initial KL.
The density construction, score moments, compatibility, actual weak equation,
noncompact bounded-log limit, initial entropy endpoint and recurrence are
proved in its dependency chain. Earlier conditional path interfaces remain
shown with their displayed hypotheses.

`chapters.json` contains the mathematical explanations and stable historical
anchors. Completed module chapters use the same detailed authored notes as the
standalone module pages. `reference_audit.json` records agreement with the
published normalization and constants, plus the documented proof variations:
direct entropy-to-score moments, bounded-test compatibility, spacetime entropy
calculus, and the initial entropy upper envelope.

Regenerate and verify locally from the repository root:

```sh
python3 -B UnadjustedLangevin/LSI/exposition/build_document.py
python3 -B UnadjustedLangevin/LSI/exposition/verify_document.py
python3 -B docs/build_site.py
python3 -B docs/verify_site.py
```

The builders use Python 3, Node.js and the repository's vendored KaTeX. No
network access or package installation is needed for exposition generation.
The builder rejects missing declaration explanations and malformed formulas.
The verifiers compare all source excerpts and embedded files with the
repository, check input/output hashes and local links, and reject external
resource dependencies.

Compile the Lean development and inspect the kernel dependency audit:

```sh
lake build UnadjustedLangevin IPLA +UnadjustedLangevin.LSI.Check
lake env lean UnadjustedLangevin/LSI/Check.lean
```

All verification is local. No GitHub workflows are used, and publication is a
separate manual action after review on `main`.
