#!/usr/bin/env python3
"""ASCII sanitization for Lean sources included via listings on arXiv (pdfLaTeX).

The arXiv AutoTeX pipeline runs pdfLaTeX, which chokes on arbitrary UTF-8 inside
`lstinputlisting` files. We therefore render the logical/mathematical operators to
readable ASCII and drop anything still non-ASCII to `?` rather than break the build.
"""

from __future__ import annotations

# Order matters: longer / composite replacements first where needed.
LEAN_UNICODE_REPLACEMENTS: tuple[tuple[str, str], ...] = (
    # multi-codepoint-ish first
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
    # modal / hybrid operators
    ("□", "[] "),
    ("◇", "<> "),
    ("∼", "~"),
    ("⋀", " /\\ "),
    ("⋁", " \\/ "),
    # logical connectives / quantifiers
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
    # set theory
    ("∈", " in "),
    ("∉", " notin "),
    ("∪", " U "),
    ("∩", " I "),
    ("⊆", " subseteq "),
    ("⊇", " supseteq "),
    ("∅", "{}"),
    # relations
    ("≠", " != "),
    ("≤", " <= "),
    ("≥", " >= "),
    ("≅", " ~= "),
    # arrows / misc operators
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
    # Greek letters (identifiers in Lean source)
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
    # double-struck / blackboard
    ("ℕ", "Nat"),
    ("ℤ", "Int"),
    # sub/superscripts
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
    # box drawing (set-builder bars and ASCII-art flowcharts in fenced blocks)
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


def sanitize_lean_for_arxiv(text: str) -> str:
    out = text
    for src, dst in LEAN_UNICODE_REPLACEMENTS:
        out = out.replace(src, dst)
    # Drop any remaining non-ASCII (comments / docstrings) rather than break pdfLaTeX.
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
