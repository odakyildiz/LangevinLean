# ULA-LSI proof pages

[index.html](index.html) states the convergence theorem for the Gaussian ULA distributions, gives its
mathematical proof and Lean statement, provides the proof diagram, and offers a
LaTeX download. [proof.html](proof.html) is the detailed source-by-source archive,
including every LSI declaration and its full proof. Mathematical typesetting,
fonts, source search and embedded sources work offline.

The final theorem is `ULA.LSI.ula_kl_bound` in
[UnconditionalTheorem.lean](../UnconditionalTheorem.lean). Its assumptions are
LSI for the normalized Gibbs target, a differentiable potential with Lipschitz
gradient, positive constants, the stated step restriction and finite initial KL.
The proof constructs the positive-time density, bounds its score moments,
derives the inequality between the LSI and smoothness constants, and proves
the weak equation and entropy derivative. Bounded approximations to the
logarithm justify the entropy calculation on the whole space. An upper bound
on entropy at small positive times supplies the initial value for integration;
a discrete recurrence then gives the stated bound. The earlier conditional
results are displayed with their own hypotheses.

`chapters.json` contains the mathematical explanations and stable historical
anchors. Completed module chapters use the same detailed authored notes as the
standalone module pages. `reference_audit.json` records agreement with the
published normalization and constants, plus the documented proof variations:
the score moment derived from the entropy variational inequality, the proof
of compatibility using bounded test functions, the integration of entropy
production over time and space, and the entropy bound at the initial time.

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
