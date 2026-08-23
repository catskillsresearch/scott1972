#!/usr/bin/env bash
# Reproduce the repository-side mechanical checks needed before Palomar submission.
set -euo pipefail
cd "$(dirname "$0")/.."

step() {
  printf '\n== %s ==\n' "$1"
}

step "Validate Comparator configuration"
python3 - <<'PY'
import json

with open("comparator.json", encoding="utf-8") as f:
    cfg = json.load(f)

required = ("challenge_module", "solution_module", "theorem_names",
            "definition_names", "permitted_axioms")
missing = [key for key in required if key not in cfg]
if missing:
    raise SystemExit(f"Missing comparator keys: {', '.join(missing)}")

names = cfg["theorem_names"] + cfg["definition_names"]
duplicates = sorted({name for name in names if names.count(name) > 1})
if duplicates:
    raise SystemExit(f"Duplicate Comparator names: {', '.join(duplicates)}")
print(f"OK: {len(cfg['theorem_names'])} theorem targets and "
      f"{len(cfg['definition_names'])} definition targets.")
PY

step "Build Lean project"
lake build

step "Compare Challenge/Solution types and definition values"
PALOMAR_QUIET=1 bash scripts/compare_challenge_solution_types.sh

step "Reject proof holes in Solution sources"
if rg -n --glob '*.lean' \
    '(^|:=|by)[[:space:]]+sorry([[:space:];]|$)|^[[:space:]]*sorry([[:space:];]|$)' \
    Scott1972 Solution.lean; then
  echo "FAIL: Solution proof sources contain sorry."
  exit 1
fi
echo "OK: Solution proof sources contain no sorry."

step "Check permitted theorem axioms"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
python3 - "$tmp/Axioms.lean" <<'PY'
import json
import sys

with open("comparator.json", encoding="utf-8") as f:
    cfg = json.load(f)
with open(sys.argv[1], "w", encoding="utf-8") as out:
    out.write(f"import {cfg['solution_module']}\n")
    for name in cfg["theorem_names"]:
        out.write(f"#print axioms {name}\n")
PY
lake env lean "$tmp/Axioms.lean" >"$tmp/axioms.txt"
python3 - "$tmp/axioms.txt" <<'PY'
import json
import re
import sys

with open("comparator.json", encoding="utf-8") as f:
    cfg = json.load(f)
allowed = set(cfg["permitted_axioms"])
text = open(sys.argv[1], encoding="utf-8").read()
reports = re.findall(
    r"^'(.+)' depends on axioms: \[([^\]]*)\]$", text, re.MULTILINE
)
reported = {name for name, _ in reports}
expected = set(cfg["theorem_names"])
if reported != expected:
    missing = sorted(expected - reported)
    extra = sorted(reported - expected)
    raise SystemExit(f"Axiom report mismatch; missing={missing}, extra={extra}")
for name, raw in reports:
    used = {item.strip() for item in raw.split(",") if item.strip()}
    forbidden = sorted(used - allowed)
    if forbidden:
        raise SystemExit(f"{name} uses forbidden axioms: {', '.join(forbidden)}")
print(f"OK: all theorem targets use only {sorted(allowed)}.")
PY

step "Check patch formatting"
git diff --check
echo "OK: Palomar preflight passed."
