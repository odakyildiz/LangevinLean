# Proximal algorithms proof page

Open [index.html](index.html) in a browser. Formula typesetting, fonts and the
complete local Lean dependency sources are embedded for offline reading.
The page separates proved theorems, corrected replacements, scalar results
and the paper's remaining unformalized claims.

The reference is the full supplied **arXiv:2406.14292v3** PDF. The audit records
v3 page and statement numbers; errors already fixed between v1 and v3 are
identified as historical, rather than attributed to the current reference.
The article itself is not copied into the repository.

Regenerate after changing Lean sources or page explanations:

```sh
python3 ProximalLangevin/exposition/build_document.py
python3 ProximalLangevin/exposition/verify_document.py
```

Regeneration needs Python 3 and Node.js, using the repository's vendored
KaTeX assets. Verification checks exact embedded source text, declaration
coverage, source hashes, internal and relative links, formula errors and
offline resources. It does not turn the unproved paper claims into theorems.
