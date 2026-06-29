#!/usr/bin/env python3
r"""Convert arxiv_with_code.md to arxiv.tex (arXiv-ready).

Pipeline:
  1. Drop the GitHub-only navigation preamble (auto-gen note, document map, file index).
  2. Lift the `## Abstract` section into a LaTeX \begin{abstract}.
  3. Demote the Appendix-A structural headings so LaTeX numbers everything once, then
     insert \\appendix before the combined Lean-source appendix.
  4. Strip manual section numbers (any depth, e.g. `1.`, `1.3`, `5.1`) so LaTeX does
     the numbering and we never get duplicates like "5.1 5.1".
  5. Replace fenced code with \\lstinputlisting blocks (ASCII-sanitized for arXiv pdfLaTeX).
  5b. Render ```mermaid blocks to vector PDFs via mermaid-cli (mmdc).
  6. pandoc → LaTeX, then splice the listing/math/figure placeholders back in.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
import textwrap
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))
from lean_listing_sanitize import chunk_line_ranges, sanitize_lean_for_arxiv

SRC = ROOT / "arxiv_with_code.md"
OUT = ROOT / "arxiv.tex"
PREAMBLE = SCRIPTS / "tex_preamble_arxiv.tex"
LISTINGS_DIR = ROOT / "lean-listings"
FIGURES_DIR = ROOT / "figures"
PUPPETEER_CONFIG = SCRIPTS / "puppeteer-config.json"
LISTING_CHUNK_LINES = 400

AUTHOR = "Lars Warren Ericson"
COMPANY = "Catskills Research Company"
GITHUB_URL = r"https://github.com/catskillsresearch/scott1972"
ORCID = "0000-0001-8299-9361"
EMAIL = "lars.ericson@catskillsresearch.com"


def find_chrome() -> str | None:
    env = os.environ.get("PUPPETEER_EXECUTABLE_PATH")
    if env and Path(env).exists():
        return env
    for name in ("google-chrome", "google-chrome-stable", "chromium", "chromium-browser"):
        path = shutil.which(name)
        if path:
            return path
    return None


def render_mermaid(code: str, idx: int) -> str:
    FIGURES_DIR.mkdir(parents=True, exist_ok=True)
    mmd_path = FIGURES_DIR / f"figure-{idx:03d}.mmd"
    pdf_path = FIGURES_DIR / f"figure-{idx:03d}.pdf"
    mmd_path.write_text(code.strip() + "\n", encoding="utf-8")

    mmdc = shutil.which("mmdc")
    if not mmdc:
        raise RuntimeError(
            "mermaid-cli (mmdc) not found; install with "
            "`npm install -g @mermaid-js/mermaid-cli`"
        )
    env = os.environ.copy()
    chrome = find_chrome()
    if chrome:
        env["PUPPETEER_EXECUTABLE_PATH"] = chrome
    cmd = [mmdc, "-i", str(mmd_path), "-o", str(pdf_path), "--pdfFit", "-b", "transparent"]
    if PUPPETEER_CONFIG.is_file():
        cmd += ["-p", str(PUPPETEER_CONFIG)]
    proc = subprocess.run(cmd, env=env, capture_output=True, text=True, check=False)
    if proc.returncode != 0 or not pdf_path.is_file():
        sys.stderr.write(proc.stdout + "\n" + proc.stderr + "\n")
        raise RuntimeError(f"mmdc failed to render figure {idx}")
    return pdf_path.relative_to(ROOT).as_posix()


def extract_title() -> str:
    first = (ROOT / "arxiv.md").read_text(encoding="utf-8").splitlines()[0]
    title = first[2:].strip() if first.startswith("# ") else first.strip()
    title = re.sub(r"\*([^*]+)\*", r"\\emph{\1}", title)
    return title


TITLE = extract_title()

GITHUB_INLINE_MATH = re.compile(r"\$`([^`\n]+?)`\$")
HTML_COMMENT = re.compile(r"<!--.*?-->", re.DOTALL)
FENCE_RE = re.compile(r"^```([^\n]*)\n(.*?)^```\s*$", re.MULTILINE | re.DOTALL)
MANUAL_SECTION_NUM = re.compile(r"^(#{1,6})[ \t]+\d+(?:\.\d+)*\.?[ \t]+", re.MULTILINE)
NARRATIVE_MARKER = "# Narrative (from arxiv.md)"
LEAN_MODULE_RE = re.compile(r"^###\s+(Scott1972(?:\.lean|/[^\s{]+))\s*$", re.MULTILINE)


def github_math_to_tex(text: str) -> str:
    return GITHUB_INLINE_MATH.sub(r"$\1$", text)


def strip_html_comments(text: str) -> str:
    return HTML_COMMENT.sub("", text)


def strip_manual_section_numbers(text: str) -> str:
    return MANUAL_SECTION_NUM.sub(r"\1 ", text)


def drop_github_nav(text: str) -> str:
    idx = text.find(NARRATIVE_MARKER)
    if idx == -1:
        return text
    return text[idx + len(NARRATIVE_MARKER) :].lstrip("\n")


def normalize_appendix_headings(text: str) -> str:
    text = re.sub(
        r"^#\s+Appendix A: Complete Lean source\s*$",
        "## Complete Lean source",
        text,
        flags=re.MULTILINE,
    )
    text = re.sub(
        r"^##\s+`(Scott1972(?:\.lean|/[^`]+))`\s*$",
        r"### \1",
        text,
        flags=re.MULTILINE,
    )
    return text


def extract_abstract(text: str) -> tuple[str, str]:
    m = re.search(r"^##\s+Abstract\s*\n(.*?)(?=^##\s)", text, re.DOTALL | re.MULTILINE)
    if not m:
        return "", text
    abstract_md = m.group(1).strip()
    body = text[: m.start()] + text[m.end() :]
    return abstract_md, body


def write_listing(code: str, listing_name: str) -> tuple[str, int]:
    LISTINGS_DIR.mkdir(parents=True, exist_ok=True)
    source = sanitize_lean_for_arxiv(code.rstrip("\n"))
    listing_path = LISTINGS_DIR / listing_name
    listing_path.write_text(source + "\n", encoding="utf-8")
    rel_path = listing_path.relative_to(ROOT).as_posix()
    return rel_path, (len(source.splitlines()) if source else 0)


def lean_block_latex(code: str, listing_name: str) -> str:
    rel_path, line_count = write_listing(code, listing_name)
    ranges = chunk_line_ranges(line_count, LISTING_CHUNK_LINES)

    parts: list[str] = []
    for first, last in ranges:
        if first == 1 and last == line_count:
            parts.append(
                "\\vspace{0.5\\baselineskip}\n"
                "\\noindent\\textcolor{green!40!black}{\\textbf{Lean 4 source}}"
                "\\par\\vspace{0.25\\baselineskip}\n"
                f"\\lstinputlisting[style=leanbox]{{{rel_path}}}\n"
                "\\vspace{0.5\\baselineskip}\n\n"
            )
        else:
            parts.append(
                f"\\noindent\\textcolor{{green!40!black}}{{\\textbf{{Lean 4 source "
                f"(lines {first}--{last})}}}}\\par\\vspace{{0.25\\baselineskip}}\n"
                f"\\lstinputlisting[style=leanbox,firstline={first},lastline={last}]"
                f"{{{rel_path}}}\n\n"
            )
    return "".join(parts)


def extract_lean_titles(text: str) -> dict[str, str]:
    titles: dict[str, str] = {}
    lean_starts = [m.start() for m in re.finditer(r"^```lean\s*$", text, re.MULTILINE)]
    for idx, pos in enumerate(lean_starts):
        prefix = text[:pos].rstrip("\n")
        module = None
        for line in reversed(prefix.splitlines()[-4:]):
            m = re.match(r"^###\s+(Scott1972(?:\.lean|/[^\s{]+))", line.strip())
            if m:
                module = m.group(1)
                break
        titles[f"LEANINCLUDE{idx:03d}"] = module or f"module-{idx + 1}"
    return titles


def replace_fences(text: str) -> tuple[str, dict[str, str]]:
    lean_titles = extract_lean_titles(text)
    placeholders: dict[str, str] = {}
    lean_idx = 0
    other_idx = 0

    def repl(match: re.Match[str]) -> str:
        nonlocal lean_idx, other_idx
        lang = match.group(1).strip().lower()
        body = match.group(2)
        if lang == "lean":
            key = f"LEANINCLUDE{lean_idx:03d}"
            module = lean_titles.get(key, f"module-{lean_idx}")
            lean_idx += 1
            safe_name = module.replace("/", "-")
            if not safe_name.endswith(".lean"):
                safe_name += ".lean"
            placeholders[key] = lean_block_latex(body, safe_name)
            return f"\n\n{key}\n\n"
        if lang == "math":
            key = f"MATHINCLUDE{other_idx:03d}"
            other_idx += 1
            placeholders[key] = f"\\[\n{body.strip()}\n\\]\n"
            return f"\n\n{key}\n\n"
        if lang == "mermaid":
            key = f"FIGINCLUDE{other_idx:03d}"
            rel_path = render_mermaid(body, other_idx)
            other_idx += 1
            placeholders[key] = (
                "\\begin{center}\n"
                f"\\includegraphics[max width=\\linewidth,"
                f"max totalheight=0.85\\textheight,keepaspectratio]{{{rel_path}}}\n"
                "\\end{center}\n"
            )
            return f"\n\n{key}\n\n"
        key = f"CODEINCLUDE{other_idx:03d}"
        rel_path, _ = write_listing(body, f"snippet-{other_idx:03d}.txt")
        other_idx += 1
        placeholders[key] = f"\\lstinputlisting[style=leanbox]{{{rel_path}}}\n"
        return f"\n\n{key}\n\n"

    converted = FENCE_RE.sub(repl, text)
    return converted, placeholders


def pandoc_to_latex(markdown: str, shift: bool = True) -> str:
    cmd = [
        "pandoc",
        "-f",
        "markdown+tex_math_dollars+raw_tex+smart",
        "-t",
        "latex",
        "--wrap=none",
    ]
    if shift:
        cmd += ["--shift-heading-level-by=-1"]
    proc = subprocess.run(cmd, input=markdown, text=True, capture_output=True, check=False)
    if proc.returncode != 0:
        print(proc.stderr, file=sys.stderr)
        raise RuntimeError("pandoc failed")
    return proc.stdout


def inject_placeholders(latex: str, placeholders: dict[str, str]) -> str:
    out = latex
    for key, value in placeholders.items():
        patterns = [
            key,
            f"\\emph{{{key}}}",
            f"\\text{{{key}}}",
            f"\\passthrough{{\\lstinline!{key}!}}",
        ]
        for pat in patterns:
            if pat in out:
                out = out.replace(pat, value)
                break
        else:
            out = out.replace(key, value)
    return out


def cleanup_pandoc_latex(latex: str) -> str:
    latex = latex.replace("\\pandocbounded{", "{")
    latex = re.sub(r"\\tightlist\n", "", latex)
    for cmd in ("section", "subsection", "subsubsection", "paragraph"):
        latex = re.sub(
            rf"(\\{cmd}\{{)\d+(?:\.\d+)*\.?\s+",
            r"\1",
            latex,
        )
    latex = re.sub(
        r"\\section\{Appendix A\. Lean source index\}",
        "",
        latex,
    )
    latex = re.sub(
        r"\\section\{Appendix A: Complete Lean source\}",
        r"\\section{Complete Lean source}",
        latex,
    )
    latex = re.sub(r"\n{3,}", "\n\n", latex)
    return latex


def insert_appendix_command(latex: str) -> str:
    marker = r"\section{Complete Lean source}"
    if marker not in latex:
        raise RuntimeError(f"missing {marker!r} in LaTeX output")
    return latex.replace(marker, r"\appendix" + "\n" + marker, 1)


def cleanup_abstract_latex(latex: str) -> str:
    """Keep the abstract pdfLaTeX/arXiv-safe: ASCII plus standard LaTeX escapes."""
    latex = latex.replace("\\pandocbounded{", "{")
    latex = latex.replace("\\textbf{{[}", "\\textbf{[")
    latex = latex.replace("\\texttt{{[}", "\\texttt{[")
    latex = latex.replace("{]}}", "]}")
    latex = re.sub(r"\\begin\{center\}\\rule\{.*?\}\\end\{center\}\s*", "", latex, flags=re.DOTALL)
    return latex


def build_title_page(abstract_latex: str) -> str:
    return textwrap.dedent(
        f"""
        \\title{{\\textbf{{{TITLE}}}}}

        \\author[1]{{\\textbf{{{AUTHOR}}}}}
        \\affil[1]{{{COMPANY}}}
        \\affil[1]{{\\url{{{GITHUB_URL}}}}}
        \\affil[1]{{\\texttt{{{EMAIL}}}}}

        \\date{{\\today}}

        \\begin{{document}}

        \\maketitle

        \\begin{{center}}
          \\small
          \\textbf{{ORCID:}} {ORCID} \\\\
          \\textbf{{Primary Category:}} cs.LO (Logic in Computer Science) \\\\
          \\textbf{{Secondary Category:}} math.LO (Logic)
        \\end{{center}}

        \\begin{{abstract}}
        {abstract_latex.strip()}
        \\end{{abstract}}
        """
    ).strip()


def main() -> int:
    if not SRC.is_file():
        print(f"error: missing {SRC}; run scripts/generate_arxiv_with_code.sh first", file=sys.stderr)
        return 1
    if not PREAMBLE.is_file():
        print(f"error: missing {PREAMBLE}", file=sys.stderr)
        return 1

    for d in (LISTINGS_DIR, FIGURES_DIR):
        if d.exists():
            for path in d.iterdir():
                if path.is_file():
                    path.unlink()
        d.mkdir(parents=True, exist_ok=True)

    raw = SRC.read_text(encoding="utf-8")
    body = drop_github_nav(raw)
    body = strip_html_comments(body)
    body = normalize_appendix_headings(body)
    abstract_md, body = extract_abstract(body)
    body = strip_manual_section_numbers(body)
    body = github_math_to_tex(body)
    body, placeholders = replace_fences(body)

    latex_body = pandoc_to_latex(body, shift=True)
    latex_body = inject_placeholders(latex_body, placeholders)
    latex_body = cleanup_pandoc_latex(latex_body)
    latex_body = insert_appendix_command(latex_body)

    abstract_latex = pandoc_to_latex(github_math_to_tex(abstract_md), shift=False) if abstract_md else ""
    abstract_latex = cleanup_abstract_latex(abstract_latex)

    preamble = PREAMBLE.read_text(encoding="utf-8")
    title_page = build_title_page(abstract_latex)
    document = preamble + "\n\n" + title_page + "\n\n" + latex_body + "\n\n\\end{document}\n"
    OUT.write_text(document, encoding="utf-8")
    n_listings = sum(1 for p in LISTINGS_DIR.iterdir() if p.is_file())
    n_figures = sum(1 for p in FIGURES_DIR.glob("*.pdf"))
    print(
        f"wrote {OUT.relative_to(ROOT)} ({OUT.stat().st_size:,} bytes, "
        f"{n_listings} listings, {n_figures} mermaid figures)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
