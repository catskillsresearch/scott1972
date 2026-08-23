#!/usr/bin/env bash
# Diff Challenge vs Solution types for every comparator.json name.
# Palomar Comparator looks up those names in two lean4export environments
# and compares ConstantVal (name, levelParams, type) with pp.all-level
# fidelity: instance names in the type are part of the type. A green
# `lake build` does not imply a match.
#
# Gotchas this script is meant to catch:
# - instance-path mismatch (e.g. ConditionallyCompletePartialOrder.toSupSet
#   vs ScottMap.instSupSet)
# - pretty-printer hiding a module prefix (`Challenge.Foo` vs `Foo`)
# - a `def` listed under theorem_names (Comparator then throws
#   "constant kind don't match")
set -euo pipefail
cd "$(dirname "$0")/.."

mapfile -t NAMES < <(python3 - <<'PY'
import json
cfg = json.load(open("comparator.json"))
for n in cfg["theorem_names"] + cfg.get("definition_names", []):
    print(n)
PY
)

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

write_lean() {
  local module="$1" out="$2"
  {
    echo "import ${module}"
    echo "set_option pp.all true"
    echo "set_option pp.explicit true"
    echo "set_option pp.universes true"
    echo "set_option pp.fullNames true"
    echo "set_option pp.funBinderTypes true"
    for n in "${NAMES[@]}"; do
      echo "#check ${n}"
    done
  } >"${out}"
}

write_lean Challenge "${tmp}/ChallengeTypes.lean"
write_lean Solution "${tmp}/SolutionTypes.lean"

lake env lean "${tmp}/ChallengeTypes.lean" 2>/dev/null \
  | grep -vE 'LEAN_PATH|trace:|warning:|declaration uses' \
  >"${tmp}/challenge.txt" || true
lake env lean "${tmp}/SolutionTypes.lean" 2>/dev/null \
  | grep -vE 'LEAN_PATH|trace:|warning:|declaration uses' \
  >"${tmp}/solution.txt" || true

# Drop universe-name noise (u_1 vs u_4) so instance-name mismatches stand out.
# Do not strip Challenge./_challenge prefixes: those are Palomar failures.
normalize() {
  sed -E 's/\.\{u_[0-9]+(,[ ]*u_[0-9]+)*\}//g; s/u_[0-9]+/u/g'
}

normalize <"${tmp}/challenge.txt" >"${tmp}/challenge.norm"
normalize <"${tmp}/solution.txt" >"${tmp}/solution.norm"

echo "== Challenge (pp.all + pp.fullNames, universes normalized) =="
cat "${tmp}/challenge.norm"
echo
echo "== Solution (pp.all + pp.fullNames, universes normalized) =="
cat "${tmp}/solution.norm"
echo
if diff -u "${tmp}/challenge.norm" "${tmp}/solution.norm"; then
  echo "OK: Challenge and Solution names/types match (after universe-name normalize)."
else
  echo "FAIL: type/instance/name mismatch — Palomar Comparator will reject this."
  exit 1
fi
