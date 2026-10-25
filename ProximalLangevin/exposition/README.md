# Proximal algorithms proof page

Open [index.html](index.html) for the common proximal overview: standalone MYIPLA,
PIPGLA and MYPGD statements beside Lean, verification commands, a clickable proof
diagram, and every supporting module. Each module page has a mathematical proof
beside complete Lean declarations and a downloadable LaTeX exposition. The authored
proofs are in `module_notes.json`; [the shared guide](../../docs/README.md) explains
coverage and regeneration.

The extended reference audit is at [proof.html](proof.html). Formula typesetting, fonts and the
complete local Lean dependency sources are embedded for offline reading.
The page states the proved theorems and corrected estimates, the scalar
recurrence results, and the paper's claims that remain unproved.

The reference is the full supplied **arXiv:2406.14292v3** PDF. The audit records
v3 page and statement numbers; errors already fixed between v1 and v3 are
identified as historical, rather than attributed to the current reference.
The article itself is not copied into the repository.

Regenerate after changing Lean sources or page explanations:

```sh
python3 ProximalLangevin/exposition/build_document.py
python3 ProximalLangevin/exposition/verify_document.py
python3 docs/build_site.py
python3 docs/verify_site.py
```

Regeneration needs Python 3 and Node.js, using the repository's vendored
KaTeX assets. Verification checks exact embedded source text, declaration
coverage, source hashes, internal and relative links, formula errors and
offline resources. Lean compilation checks the mathematical proofs; the documentation verifier
checks their correspondence with the displayed source.
