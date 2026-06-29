#!/usr/bin/env python3
"""Append complete Lean source to arxiv.md → arxiv_with_code.md (build artifact)."""

from __future__ import annotations

from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Library files in dependency order (matches Scott1972.lean import order).
FILES = [
    "Scott1972.lean",
    "Scott1972/ContinuousLattice/Injective.lean",
    "Scott1972/ContinuousLattice/WayBelow.lean",
    "Scott1972/ContinuousLattice/Specialization.lean",
    "Scott1972/ContinuousLattice/ScottMaps.lean",
    "Scott1972/ContinuousLattice/MilnerCorrection.lean",
    "Scott1972/ContinuousLattice/Constructions.lean",
    "Scott1972/ContinuousLattice/FunctionSpaces.lean",
    "Scott1972/ContinuousLattice/Theorem212.lean",
    "Scott1972/ContinuousLattice/InverseLimits.lean",
    "Scott1972/ContinuousLattice/FunctionSpaceTower.lean",
]

FILE_ROLES: dict[str, str] = {
    "Scott1972.lean": "Root import graph",
    "Scott1972/ContinuousLattice/Injective.lean": "Scott §1",
    "Scott1972/ContinuousLattice/WayBelow.lean": "Scott §2",
    "Scott1972/ContinuousLattice/Specialization.lean": "Scott §2",
    "Scott1972/ContinuousLattice/ScottMaps.lean": "Scott §2",
    "Scott1972/ContinuousLattice/MilnerCorrection.lean": "March 1972 correction",
    "Scott1972/ContinuousLattice/Constructions.lean": "Scott §2.8–2.12",
    "Scott1972/ContinuousLattice/FunctionSpaces.lean": "Scott §3",
    "Scott1972/ContinuousLattice/Theorem212.lean": "Theorem 2.12",
    "Scott1972/ContinuousLattice/InverseLimits.lean": "Scott §4",
    "Scott1972/ContinuousLattice/FunctionSpaceTower.lean": "Theorem 4.4",
}


def paper_title(arxiv_text: str) -> str:
    first = arxiv_text.splitlines()[0] if arxiv_text else "# Scott 1972"
    if first.startswith("# "):
        return first[2:].strip()
    return first.strip()


def narrative_body(arxiv_text: str) -> str:
    body = arxiv_text
    if body.startswith("# "):
        idx = body.find("\n---\n")
        if idx != -1:
            body = body[idx + len("\n---\n") :]
        else:
            body = body[body.find("\n") + 1 :]
    return body.rstrip()


def main() -> None:
    arxiv_path = ROOT / "arxiv.md"
    arxiv = arxiv_path.read_text()
    title = paper_title(arxiv)
    body = narrative_body(arxiv)

    parts: list[str] = []
    parts.append(
        "<!-- AUTO-GENERATED: run scripts/generate_arxiv_with_code.sh to refresh -->\n"
        "<!-- AGENTS: do not read or grep this file. Use arxiv.md; see .cursorignore -->\n"
    )
    parts.append(f"# {title} — full narrative + complete Lean source\n\n")
    parts.append(
        "> **Generated artifact — not for agents.** Inventory and narrative live in "
        "[`arxiv.md`](arxiv.md). Regenerate with `scripts/generate_arxiv_with_code.sh`. "
        "This file is stale whenever it is older than `arxiv.md` or any listed `.lean` file.\n\n"
    )
    parts.append(
        f"*Generated {date.today().isoformat()} from `arxiv.md` and all library "
        "`.lean` files in dependency order (`Scott1972.lean`).*\n\n"
    )
    parts.append(
        "**Review copy.** The narrative body matches [`arxiv.md`](arxiv.md) "
        "(excluding the title block through the first `---`). "
        "This file appends **Appendix A: Complete Lean source** with every line "
        "of the formalization inlined below.\n\n"
    )
    parts.append("---\n\n")
    parts.append("## Document map\n\n")
    parts.append("| Part | Contents |\n")
    parts.append("| --- | --- |\n")
    parts.append("| **§1–§6** | Full `arxiv.md` narrative |\n")
    parts.append("| **Appendix A** | Complete Lean 4 source, one subsection per file |\n\n")
    parts.append("### Appendix A — file index\n\n")

    total_lines = 0
    for f in FILES:
        n = len((ROOT / f).read_text().splitlines())
        total_lines += n
        parts.append(f"- [`{f}`](#{f.replace('/', '').replace('.', '').lower()}) — {n} lines\n")

    parts.append(f"\n**Total:** {len(FILES)} files, {total_lines} lines of Lean.\n\n")
    parts.append("---\n\n")
    parts.append("# Narrative (from arxiv.md)\n\n")
    parts.append(body)
    parts.append("\n\n---\n\n")
    parts.append("# Appendix A: Complete Lean source\n\n")
    parts.append("| Role | File |\n")
    parts.append("| --- | --- |\n")
    for f in FILES:
        parts.append(f"| {FILE_ROLES[f]} | `{f}` |\n")
    parts.append(
        "\nPrimary source (OCR plain text): [`sources/ScottContinLatt1972.md`]"
        "(sources/ScottContinLatt1972.md) — transcription of **[Sco72]** for use in the "
        "Lean development (see §2).\n\n"
    )
    parts.append(
        "Files appear in `Scott1972.lean` import order. "
        "Each block is a verbatim copy of the repository file at generation time.\n\n"
    )

    for f in FILES:
        content = (ROOT / f).read_text().rstrip() + "\n"
        # Nested ``` in docstrings would break markdown lean fences in arxiv_with_code.md.
        content = content.replace("```", "'''")
        n = len(content.splitlines())
        parts.append(f"## `{f}`\n\n")
        parts.append(f"*{n} lines.*\n\n")
        parts.append("```lean\n")
        parts.append(content)
        parts.append("```\n\n")

    out = ROOT / "arxiv_with_code.md"
    out.write_text("".join(parts))
    print(f"Wrote {out} ({len(out.read_text().splitlines())} lines)")


if __name__ == "__main__":
    main()
