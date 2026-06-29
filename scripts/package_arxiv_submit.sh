#!/usr/bin/env bash
# Build arxiv.tex and zip everything arXiv needs to compile it (pdfLaTeX).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

TEX="arxiv.tex"
LISTINGS_DIR="lean-listings"
FIGURES_DIR="figures"
OUT_DIR="dist"
ZIP="${OUT_DIR}/arxiv_submit.zip"

if [[ "${1:-}" != "--skip-tex-build" ]]; then
  echo "==> Regenerating arxiv_with_code.md, arxiv.tex, listings, and figures"
  bash scripts/build_arxiv_tex.sh
fi

missing=0
if [[ ! -f "$TEX" ]]; then
  echo "error: missing $TEX" >&2
  missing=1
fi
if [[ ! -d "$LISTINGS_DIR" ]]; then
  echo "error: missing $LISTINGS_DIR" >&2
  missing=1
fi
lean_count="$(find "$LISTINGS_DIR" -maxdepth 1 -type f 2>/dev/null | wc -l)"
if [[ "$lean_count" -eq 0 ]]; then
  echo "error: no listing files in $LISTINGS_DIR" >&2
  missing=1
fi
fig_count="$(find "$FIGURES_DIR" -maxdepth 1 -name '*.pdf' 2>/dev/null | wc -l)"
if [[ "$fig_count" -eq 0 ]]; then
  echo "error: no mermaid figure PDFs in $FIGURES_DIR" >&2
  missing=1
fi
if [[ "$missing" -ne 0 ]]; then
  exit 1
fi

mkdir -p "$OUT_DIR"
rm -f "$ZIP"

echo "==> Writing 00README.json (mark listing files as include so arXiv does not drop them)"
python3 - <<'PY'
import json
from pathlib import Path

sources = [{"filename": "arxiv.tex", "usage": "toplevel"}]
for path in sorted(p for p in Path("lean-listings").iterdir() if p.is_file()):
    sources.append({"filename": path.as_posix(), "usage": "include"})
for path in sorted(Path("figures").glob("*.pdf")):
    sources.append({"filename": path.as_posix(), "usage": "include"})
readme = {"process": {"compiler": "pdflatex"}, "sources": sources}
Path("00README.json").write_text(json.dumps(readme, indent=2) + "\n")
print(f"  {len(sources)} sources")
PY

echo "==> Packaging"
zip -r "$ZIP" \
  00README.json \
  "$TEX" \
  "$LISTINGS_DIR" \
  "$FIGURES_DIR"/*.pdf

echo "wrote $ZIP ($(du -h "$ZIP" | cut -f1))"
echo "Contents:"
zipinfo -1 "$ZIP" | sed 's/^/  /' | head -40
echo
echo "Upload $ZIP to arXiv (pdfLaTeX; UTF-8 Lean listings render via the listings literate"
echo "table; mermaid diagrams ship as pre-rendered figures/*.pdf since AutoTeX cannot run mmdc)."
echo "On arXiv Add Files: Delete All before uploading (uploads merge, they do not replace)."
echo "On arXiv Review Files: if any lean-listings/*.lean or figures/*.pdf are marked for"
echo "deletion, UNCHECK them."
