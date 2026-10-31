"""Shared mathematical text handling for headings, comments and notation checks."""
from __future__ import annotations

import html
import re
from html.parser import HTMLParser

TEX = re.compile(r"\\\[(.*?)\\\]|\\\((.*?)\\\)", re.S)
SYMBOLS = {
    "α": r"\alpha", "β": r"\beta", "γ": r"\gamma", "δ": r"\delta",
    "ε": r"\varepsilon", "ζ": r"\zeta", "η": r"\eta", "θ": r"\theta",
    "ι": r"\iota", "κ": r"\kappa", "λ": r"\lambda", "μ": r"\mu",
    "ν": r"\nu", "ξ": r"\xi", "π": r"\pi", "ρ": r"\rho",
    "σ": r"\sigma", "τ": r"\tau", "υ": r"\upsilon", "φ": r"\varphi",
    "χ": r"\chi", "ψ": r"\psi", "ω": r"\omega", "Γ": r"\Gamma",
    "Δ": r"\Delta", "Θ": r"\Theta", "Λ": r"\Lambda", "Ξ": r"\Xi",
    "Π": r"\Pi", "Σ": r"\Sigma", "Φ": r"\Phi", "Ψ": r"\Psi",
    "Ω": r"\Omega", "ℝ": r"\mathbb R", "ℕ": r"\mathbb N",
    "ℤ": r"\mathbb Z", "ℂ": r"\mathbb C", "∞": r"\infty",
    "≤": r"\le", "≥": r"\ge", "≠": r"\ne", "∈": r"\in",
    "∉": r"\notin", "∇": r"\nabla", "∂": r"\partial",
    "∫": r"\int", "∑": r"\sum", "∏": r"\prod", "√": r"\sqrt{}",
    "∀": r"\forall", "∃": r"\exists", "⊂": r"\subset",
    "⊆": r"\subseteq", "⊗": r"\otimes", "⟨": r"\langle",
    "⟩": r"\rangle", "‖": r"\Vert", "−": "-", "×": r"\times",
}
SUPER = dict(zip("⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻ⁿ", "0123456789+-n"))
SUB = dict(zip("₀₁₂₃₄₅₆₇₈₉", "0123456789"))
RAW_MATH = re.compile(
    r"[α-ωΑ-Ωℝℕℤℂ∞≤≥≠∈∉∇∂∫∑∏√∀∃⊂⊆⊗‖¹²³⁴⁵⁶⁷⁸⁹₀-₉ᵢⱼₖₗₘₙₚᵣₛₜᵤᵥₓᵦᵧᵨᵩᵪ]"
    r"|\b(?:L[12p]|C[0-4]|W2|Mav|Mrms|MDelta|M_infinity|M_av|M_rms|Lpsi|LF|Lb|Lsigma|rO|rS)\b"
    r"|(?<![\w/])[A-Za-z0-9()]+\s*(?:<=|>=|=|<|>|\^)\s*[A-Za-z0-9({\\]"
    r"|\b[A-Za-z]\s*[+*/-]\s*(?:[A-Za-z]|\d+)\b"
    r"|\b[A-Za-z]_[A-Za-z0-9]+\b"
    r"|\b[A-Za-z]\([A-Za-z0-9 ,+*/-]+\)"
    r"|\b(?:sqrt|exp|log|sin|cos|abs|min|max)\s*\("
    r"|\bsqrt-[A-Z]\b"
    r"|\b(?:factor|coefficient|constant|rate|radius|variance|exponent|probability)\s+(?:of\s+)?\d+(?:\.\d+)?\b"
    r"|\b(?:variance|constant|rate|operator|particle|parameter|dimension|time|approximations of)\s+[B-HJ-Zb-z]\b"
    r"|\\(?:\(|\[|frac\b|sqrt\b|alpha\b|beta\b|gamma\b)"
)


def authored_strings(value):
    """Collect prose and headings without relying on an incomplete field list."""
    if isinstance(value, str):
        yield value
    elif isinstance(value, dict):
        for item in value.values():
            yield from authored_strings(item)
    elif isinstance(value, (list, tuple)):
        for item in value:
            yield from authored_strings(item)


def plain_math_text(value):
    """Readable text for PDF bookmarks, browser titles and accessibility labels.

    Visible mathematical headings are rendered separately with KaTeX/LaTeX.
    Metadata cannot contain those rendered elements or TeX control sequences.
    """
    def plain(match):
        text = html.unescape(match[1] if match[1] is not None else match[2])
        text = re.sub(r"\\(?:mathbb|mathcal|mathrm|mathbf|mathsf|operatorname|text)\s*\{([^{}]*)\}", r"\1", text)
        text = re.sub(r"\\(?:mathbb|mathcal|mathrm|mathbf|mathsf)\s+([A-Za-z])", r"\1", text)
        text = re.sub(r"\\frac\{([^{}]*)\}\{([^{}]*)\}", r"(\1)/(\2)", text)
        text = re.sub(r"\\sqrt\{([^{}]*)\}", r"√(\1)", text)
        for character, command in sorted(SYMBOLS.items(), key=lambda pair: -len(pair[1])):
            if command.startswith("\\") and " " not in command and "{" not in command:
                text = re.sub(re.escape(command) + r"(?![A-Za-z])", lambda _: character, text)
        text = re.sub(r"\\(?:left|right|displaystyle|textstyle)\b", "", text)
        text = re.sub(r"\\(?:lVert|rVert|Vert)\b", "‖", text)
        text = re.sub(r"\\(?:langle|rangle)\b", lambda m: "⟨" if m[0] == r"\langle" else "⟩", text)
        for marker, table in [("^", SUPER), ("_", SUB)]:
            inverse = {value: key for key, value in table.items()}
            text = re.sub(re.escape(marker) + r"\{?([0-9+n-]+)\}?",
                          lambda m: "".join(inverse.get(c, c) for c in m[1]), text)
        text = re.sub(r"\\[,;!: ]", " ", text)
        text = re.sub(r"\\([A-Za-z]+)", r"\1", text)
        return text.replace("{", "").replace("}", "").replace("_", "").strip()
    return TEX.sub(plain, value)


def _unicode_tex(value):
    result = []
    for character in value:
        if character in SUPER:
            result.append("^{" + SUPER[character] + "}")
        elif character in SUB:
            result.append("_{" + SUB[character] + "}")
        else:
            result.append(SYMBOLS.get(character, character) + (" " if character in SYMBOLS and SYMBOLS[character].startswith("\\") else ""))
    return "".join(result).strip()


def _comment_notation(value):
    """Format unambiguous notation in extracted comments, never in Lean source."""
    parts = re.split(r"(\\\[.*?\\\]|\\\(.*?\\\))", value, flags=re.S)
    for index in range(0, len(parts), 2):
        text = parts[index]
        explicit = {
            "K=sigma/sqrt(2)": r"\(K=\sigma/\sqrt{2}\)",
            "sqrt(2)": r"\(\sqrt{2}\)",
            "R0=0": r"\(R_0=0\)", "z=0": r"\(z=0\)",
            "T=0": r"\(T=0\)", "t=0": r"\(t=0\)",
            "K=M*N": r"\(K=MN\)", "V/K²": r"\(V/K^2\)",
            "C^{1,2}": r"\(C^{1,2}\)",
            "r=q+εb<1": r"\(r=q+\varepsilon b<1\)",
            "h√h": r"\(h\sqrt h\)",
            "T_t(Y_t)": r"\(T_t(Y_t)\)", "T_t": r"\(T_t\)",
            "2 sqrt(V₀/(M*N))/m": r"\(\frac2m\sqrt{\frac{V_0}{MN}}\)",
            "1/sqrt(K)": r"\(1/\sqrt{K}\)",
            "sqrt(2 dz)": r"\(\sqrt{2d_z}\)", "K>0": r"\(K>0\)",
            "u'=v, v'=-u-v": r"\(u'=v,\;v'=-u-v\)",
            "[[a,-c/2],[-c/2,b]]": r"\(\begin{pmatrix}a&-c/2\\-c/2&b\end{pmatrix}\)",
            "n+1": r"\(n+1\)", "u-v": r"\(u-v\)", "V/N": r"\(V/N\)",
            "A/B": r"\(A\)/\(B\)", "B-A-B": r"\(B\!-\!A\!-\!B\)",
            "F/G": r"\(F\)/\(G\)",
            "sqrt(2(delta+epsilon)/rho)": r"\(\sqrt{2(\delta+\varepsilon)/\rho}\)",
            "1/sqrt(N)": r"\(1/\sqrt N\)",
            "reciprocal-sqrt(K)": r"\(K^{-1/2}\)",
            "sqrt(h)": r"\(\sqrt h\)", "sqrt(K)": r"\(\sqrt K\)",
            "sqrt(2/K)": r"\(\sqrt{2/K}\)", "sqrt-N": r"\(\sqrt N\)",
            "sqrt(2 rho)": r"\(\sqrt{2\rho}\)",
            "O(h sqrt(h))": r"\(O(h\sqrt h)\)",
            "min(time,stop)": r"\(\min\{\mathrm{time},\mathrm{stop}\}\)",
            "min(t,τ)": r"\(\min\{t,\tau\}\)",
            "per-copy second moment V": r"per-copy second moment \(V\)",
            "V is the exact sum": r"\(V\) is the exact sum",
            "each of N particles": r"each of \(N\) particles",
            "X may carry": r"\(X\) may carry",
            "eigenvalues of DT": r"eigenvalues of \(DT\)",
            "divergence of T-id": r"divergence of \(T-\mathrm{id}\)",
            "first n observations": r"first \(n\) observations",
            "before n; n is the terminal time": r"before \(n\); \(n\) is the terminal time",
            "approximations of U": r"approximations of \(U\)",
            "K matrix": r"\(K\) matrix", "K matrices": r"\(K\) matrices",
            "finite-particle M-MFPO": r"finite-particle \(\mathrm{M\!-\!MFPO}\)",
        }
        pattern = re.compile("|".join(re.escape(source) for source in
                                     sorted(explicit, key=len, reverse=True)))
        text = pattern.sub(lambda match: explicit[match[0]], text)
        text = re.sub(r"\bparticle i\b", lambda _: r"particle \(i\)", text)
        text = re.sub(r"\breference copy i\b", lambda _: r"reference copy \(i\)", text)
        text = re.sub(r"\bcoefficient sigma\b", lambda _: r"coefficient \(\sigma\)", text)
        text = re.sub(r"\brate(?=[α-ω])", "rate ", text)
        text = re.sub(r"\b([LC])([01234p∞¹²³])(?!\w)",
                      lambda m: r"\(" + m[1] + "^{" + (r"\infty" if m[2] == "∞" else SUPER.get(m[2], m[2])) + r"}\)", text)
        text = re.sub(r"\bP₂\b", r"\\(\\mathcal P_2\\)", text)
        text = re.sub(r"(?<![A-Za-z\\])(?:[A-Za-z]?[¹²³⁴⁵⁶⁷⁸⁹₀-₉]+|[α-ωΑ-Ωℝℕℤℂ∞≤≥≠∈∉∇∂∫∑∏√∀∃⊂⊆⊗‖])",
                      lambda m: r"\(" + _unicode_tex(m[0]) + r"\)", text)
        parts[index] = text
    return "".join(parts)


def display_docstring(value):
    """Format comment prose while preserving literal Lean identifiers/snippets."""
    tick = chr(96)
    pieces = re.split(f"({tick}[^{tick}]+{tick})", value)
    output = []
    for piece in pieces:
        if piece.startswith(tick) and piece.endswith(tick):
            token = piece[1:-1]
            greek = {name: "\\" + command for name, command in {
                "alpha": "alpha", "beta": "beta", "gamma": "gamma",
                "delta": "delta", "epsilon": "varepsilon", "theta": "theta",
                "kappa": "kappa", "lambda": "lambda", "mu": "mu", "nu": "nu",
                "pi": "pi", "rho": "rho", "sigma": "sigma", "phi": "phi",
            }.items()}
            if token in greek:
                output.append(r"\(" + greek[token] + r"\)")
                continue
            words = re.findall(r"[A-Za-z]+", token)
            simple_expression = (bool(re.search(r"[=<>+*/^≤≥]", token))
                                 and all(len(word) <= 2 or word in {"sqrt", "sigma"} for word in words)
                                 and not re.search(r":=|->|→|↦|\bby\b", token))
            if (re.fullmatch(r"[A-Za-zα-ωΑ-Ω]", token)
                    or re.fullmatch(r"[LC][01234p∞¹²³]|P₂", token)
                    or re.fullmatch(r"sqrt\s*\([0-9A-Za-z +*/-]+\)", token)
                    or simple_expression):
                token = re.sub(r"^sqrt\s*\((.*)\)$", r"\\sqrt{\1}", token)
                token = re.sub(r"\bsqrt\s*\(([^()]*)\)", r"\\sqrt{\1}", token)
                token = re.sub(r"\bsigma\b", r"\\sigma ", token)
                token = re.sub(r"\bR0\b", "R_0", token)
                token = token.replace("*", r"\,")
                token = re.sub(r"^([LC])([01234p∞¹²³])$", lambda m: m[1] + "^{" + (r"\infty" if m[2] == "∞" else SUPER.get(m[2], m[2])) + "}", token)
                token = r"\mathcal P_2" if token == "P₂" else _unicode_tex(token)
                output.append(r"\(" + html.escape(token) + r"\)")
            else:
                output.append("<code>" + html.escape(token) + "</code>")
        else:
            output.append(html.escape(_comment_notation(piece)))
    return "".join(output)


def render_prose_math(value, math):
    """Typeset visible HTML text without touching attributes or source listings."""
    tag = re.compile(r"""</?[A-Za-z][^>"']*(?:(?:"[^"]*"|'[^']*')[^>"']*)*>""", re.S)
    protected = {"pre", "code", "script", "style", "textarea", "title", "annotation"}
    depth = 0
    result = []
    index = 0
    while index < len(value):
        if value[index] == "<" and (match := tag.match(value, index)):
            markup = match[0]
            name = re.match(r"</?([A-Za-z]+)", markup)[1].lower()
            if name in protected:
                depth += -1 if markup.startswith("</") else 1
            if not depth:
                markup = re.sub(r'((?<![\w-])(?:title|aria-label)=")([^"]*)"',
                                lambda m: m[1] + html.escape(plain_math_text(html.unescape(m[2])), quote=True) + '"',
                                markup)
            result.append(markup)
            index = match.end()
        elif not depth and (match := TEX.match(value, index)):
            result.append(math(match[0]))
            index = match.end()
        else:
            result.append(value[index])
            index += 1
    return "".join(result)


class VisibleProse(HTMLParser):
    """Collect prose while excluding typeset maths, source listings and scripts."""
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.stack = []
        self.passages = []

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        classes = set(attrs.get("class", "").split())
        skip = (any(self.stack) or tag in {"script", "style", "pre", "code", "textarea", "title", "svg"}
                or bool(classes & {"katex", "lean-pane", "code-meta", "diagram-node-file", "paper-label"}))
        if tag not in {"br", "hr", "img", "input", "meta", "link", "source", "wbr"}:
            self.stack.append(skip)

    def handle_endtag(self, tag):
        if tag not in {"br", "hr", "img", "input", "meta", "link", "source", "wbr"} and self.stack:
            self.stack.pop()

    def handle_data(self, value):
        if not any(self.stack) and value.strip():
            self.passages.append(value)
