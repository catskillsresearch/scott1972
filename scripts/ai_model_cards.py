"""Model-card registry for the AI-assisted development acknowledgements block.

Injected into `arxiv_with_code.md` / `arxiv.tex` by `build_arxiv_tex.py` at:
  <!-- AI_MODEL_TOOL_BULLETS --> … <!-- /AI_MODEL_TOOL_BULLETS -->
  <!-- AI_MODEL_REFERENCES --> … <!-- /AI_MODEL_REFERENCES -->
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class ModelCard:
    label: str
    cite_key: str
    tool_note: str
    reference: str


MODEL_CARDS: tuple[ModelCard, ...] = (
    ModelCard(
        label="Cursor",
        cite_key="Cur26",
        tool_note=(
            "agent-assisted editing in the Cursor IDE: formalizing Scott's 1972 "
            "continuous-lattice layer in Lean 4 / mathlib, `lake build` repair, vision-OCR "
            "transcription, drafting this narrative (`arxiv.md`), and tracking the formalized "
            "inventory. Generated Lean was provisional until it compiled under the pinned "
            "toolchain."
        ),
        reference=(
            "Anysphere, Inc. *Cursor: AI-native code editor and agent environment*. "
            "<https://cursor.com> (accessed 2026)."
        ),
    ),
    ModelCard(
        label="Cursor Composer 2.5 Fast",
        cite_key="Cmp25",
        tool_note=(
            "routine multi-step work: module scaffolding, dependency-ordered wiring of "
            "`Scott1972/ContinuousLattice/`, documentation and Mermaid blueprints, and medium "
            "proof obligations where the strategy was already fixed. Per its model card, "
            "Composer 2.5 is optimized for codebase navigation rather than open-ended "
            "topological proof design; the Milner-block results (2.9–2.11, full 3.3) were not "
            "delegated to it alone."
        ),
        reference=(
            "Anysphere, Inc. *Composer 2.5*. Model announcement and documentation, "
            "<https://cursor.com/blog/composer-2-5>; model card as integrated in Cursor, "
            "<https://cursor.com/docs/models> (accessed 2026)."
        ),
    ),
    ModelCard(
        label="Anthropic Claude Sonnet 5 (medium reasoning)",
        cite_key="Son26",
        tool_note=(
            "day-to-day formalization and proof-engineering in Cursor at the medium reasoning "
            "tier: inventory and narrative maintenance, module wiring, and medium-complexity "
            "Lean obligations where the proof strategy was already fixed. Per its model card, "
            "Sonnet 5 Medium balances cost and capability for agentic coding at moderate "
            "reasoning depth."
        ),
        reference=(
            "Anthropic. *Claude Sonnet 5* (medium reasoning variant). System card, "
            "<https://www.anthropic.com/claude-sonnet-5-system-card>; model documentation as "
            "integrated in Cursor, <https://cursor.com/docs/models> (accessed 2026)."
        ),
    ),
    ModelCard(
        label="Anthropic Claude Opus 4.8 (high reasoning)",
        cite_key="Ant26",
        tool_note=(
            "selective use for the heaviest proof work (Propositions 2.9–2.11, Theorem 2.12, "
            "Theorem 3.3, Propositions 3.8–3.10, Theorem 4.4). Every emitted proof term was "
            "checked by the Lean kernel."
        ),
        reference=(
            "Anthropic. *Claude Opus 4.8* (high thinking/reasoning variant). System card and "
            "announcement, <https://www.anthropic.com/news/claude-opus-4-8>; model documentation "
            "as integrated in Cursor, <https://cursor.com/docs/models/claude-opus-4-8> "
            "(accessed 2026)."
        ),
    ),
    ModelCard(
        label="Google Gemini 3.5 Flash",
        cite_key="Gem25",
        tool_note=(
            "exploratory passes on Scott's typographic conventions (ambient vs subspace joins "
            "in the Milner correction) and scope decisions."
        ),
        reference=(
            "Google DeepMind. *Gemini 3.5 Flash*. Technical documentation and model cards. "
            "<https://ai.google.dev/gemini-api/docs/models> (accessed 2026)."
        ),
    ),
)

TOOL_BULLETS_BEGIN = "<!-- AI_MODEL_TOOL_BULLETS -->"
TOOL_BULLETS_END = "<!-- /AI_MODEL_TOOL_BULLETS -->"
REFERENCES_BEGIN = "<!-- AI_MODEL_REFERENCES -->"
REFERENCES_END = "<!-- /AI_MODEL_REFERENCES -->"


def render_tool_bullets() -> str:
    return "\n".join(
        f"- **{card.label}** **[{card.cite_key}]** — {card.tool_note}" for card in MODEL_CARDS
    )


def render_model_references() -> str:
    return "\n".join(f"- **[{card.cite_key}]** {card.reference}" for card in MODEL_CARDS)


def inject_model_cards(text: str) -> str:
    """Expand acknowledgement markers; pass through unchanged if markers absent."""
    tool_block = f"{TOOL_BULLETS_BEGIN}\n{render_tool_bullets()}\n{TOOL_BULLETS_END}"
    ref_block = f"{REFERENCES_BEGIN}\n{render_model_references()}\n{REFERENCES_END}"

    if TOOL_BULLETS_BEGIN not in text:
        raise RuntimeError(
            f"missing {TOOL_BULLETS_BEGIN} in narrative; add markers to arxiv.md Acknowledgments"
        )
    if REFERENCES_BEGIN not in text:
        raise RuntimeError(
            f"missing {REFERENCES_BEGIN} in narrative; add markers to arxiv.md References"
        )

    text = _replace_between(text, TOOL_BULLETS_BEGIN, TOOL_BULLETS_END, render_tool_bullets())
    text = _replace_between(text, REFERENCES_BEGIN, REFERENCES_END, render_model_references())
    return text


def _replace_between(text: str, begin: str, end: str, body: str) -> str:
    start = text.index(begin)
    stop = text.index(end, start)
    stop_end = stop + len(end)
    inner_start = start + len(begin)
    # Preserve one leading newline after begin marker when present.
    if inner_start < stop and text[inner_start : inner_start + 1] == "\n":
        inner_start += 1
    if inner_start < stop and text[stop - 1 : stop] == "\n":
        stop -= 1
    return text[:start] + begin + "\n" + body + "\n" + end + text[stop_end:]
