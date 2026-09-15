#!/usr/bin/env python3
"""ASCII sanitization for Agda sources included via listings on arXiv (pdfLaTeX).

The arXiv AutoTeX pipeline runs pdfLaTeX, which chokes on arbitrary UTF-8 inside
`lstinputlisting` files. We therefore render the logical/mathematical operators to
readable ASCII and drop anything still non-ASCII to `?` rather than break the build.
"""

from __future__ import annotations

import unicodedata

# Order matters: longer / composite replacements first where needed.
UNICODE_REPLACEMENTS: tuple[tuple[str, str], ...] = (
    ("⋢", " sqsubneq "),
    ("⊑\u0338", " sqsubneq "),
    ("⁻¹", "^-1"),
    ("⟶", " --> "),
    ("⟷", " <-> "),
    ("⟨", "<"),
    ("⟩", ">"),
    ("↦", " |-> "),
    ("⊢", " |- "),
    ("⊨", " |= "),
    ("⊬", " |/- "),
    ("⊭", " |/= "),
    ("□", "[] "),
    ("◇", "<> "),
    ("∼", "~"),
    ("⋀", " /\\ "),
    ("⋁", " \\/ "),
    ("∀", "forall "),
    ("∃", "exists "),
    ("¬", "not "),
    ("∧", " /\\ "),
    ("∨", " \\/ "),
    ("↔", " <-> "),
    ("→", " -> "),
    ("←", " <- "),
    ("⇒", " => "),
    ("⊥", "False"),
    ("∈", " in "),
    ("∉", " notin "),
    ("∪", " U "),
    ("∩", " I "),
    ("⊆", " subseteq "),
    ("⊇", " supseteq "),
    ("∅", "{}"),
    ("≠", " != "),
    ("≢", " != "),
    ("≡", " == "),
    ("≤", " <= "),
    ("≥", " >= "),
    ("≅", " ~= "),
    ("≪", " << "),
    ("⊑", " sqsub "),
    ("⊔", " sqsup "),
    ("⊓", " sqcap "),
    ("⊤", " top "),
    ("⊣", " dashv "),
    ("↟", " Up "),
    ("⇄", " <=> "),
    ("⨆", " bigcup "),
    ("𝕆", " O "),
    ("∞", " inf "),
    ("′", "'"),
    ("ḡ", "g"),
    ("̄", ""),
    ("̸", ""),
    ("↑", ""),
    ("↓", ""),
    ("↥", ""),
    ("▸", " |> "),
    ("∘", " comp "),
    ("·", "*"),
    ("×", " x "),
    ("§", "S"),
    ("—", "--"),
    ("–", "-"),
    ("…", "..."),
    ("Γ", "Gamma"),
    ("Δ", "Delta"),
    ("Θ", "Theta"),
    ("Σ", "Sigma"),
    ("Η", "Eta"),
    ("Κ", "Kappa"),
    ("φ", "phi"),
    ("ψ", "psi"),
    ("χ", "chi"),
    ("σ", "sigma"),
    ("τ", "tau"),
    ("α", "a"),
    ("β", "b"),
    ("λ", "fun "),
    ("ℕ", "Nat"),
    ("ℤ", "Int"),
    ("₀", "_0"),
    ("₁", "_1"),
    ("₂", "_2"),
    ("₃", "_3"),
    ("ₙ", "_n"),
    ("ₚ", "_p"),
    ("ᵢ", "_i"),
    ("₊", "_+"),
    ("⁺", "^+"),
    ("⁻", "^-"),
    ("¹", "1"),
    ("│", "|"),
    ("─", "-"),
    ("━", "-"),
    ("├", "+"),
    ("┤", "+"),
    ("┬", "+"),
    ("┴", "+"),
    ("┼", "+"),
    ("┌", "+"),
    ("┐", "+"),
    ("└", "+"),
    ("┘", "+"),
    ("║", "|"),
    ("═", "="),
    ("╔", "+"),
    ("╗", "+"),
    ("╚", "+"),
    ("╝", "+"),
    ("╠", "+"),
    ("╣", "+"),
    ("•", "*"),
    ("▪", "*"),
    ("▶", ">"),
    ("◀", "<"),
)


def sanitize_for_arxiv(text: str) -> str:
    out = text
    for src, dst in UNICODE_REPLACEMENTS:
        out = out.replace(src, dst)
    out = unicodedata.normalize("NFD", out)
    out = "".join(c for c in out if unicodedata.category(c) != "Mn")
    return "".join(ch if ord(ch) < 128 else "?" for ch in out)


def chunk_line_ranges(line_count: int, chunk_size: int = 350) -> list[tuple[int, int]]:
    if line_count <= chunk_size:
        return [(1, line_count)]
    ranges: list[tuple[int, int]] = []
    start = 1
    while start <= line_count:
        end = min(start + chunk_size - 1, line_count)
        ranges.append((start, end))
        start = end + 1
    return ranges
