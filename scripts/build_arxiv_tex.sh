#!/usr/bin/env bash
# Regenerate arxiv_with_code.md and build arxiv.tex (gitignored build artifacts).
set -euo pipefail
cd "$(dirname "$0")/.."

echo "==> Regenerating arxiv_with_code.md"
bash scripts/generate_arxiv_with_code.sh

echo "==> Building arxiv.tex + lean-listings/ + figures/"
python3 scripts/build_arxiv_tex.py
