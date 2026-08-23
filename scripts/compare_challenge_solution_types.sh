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
# - a structure listed under definition_names (Comparator then throws
#   "Challenge constant is not a definition")
# - universe parameter names (`IsContinuousLattice.{u_3}` vs `.{u_2}`):
#   Comparator BEqs ConstantVal.levelParams, so auto-generated `u_n`
#   names must agree. Pin compared decls to `Type u` / `Type v`.
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

# Palomar Comparator BEqs ConstantVal.levelParams, so `.{u_3}` vs `.{u_2}`
# is a rejection. Do not strip universe names. A secondary stripped view is
# printed only to make instance-path mismatches easier to read.
normalize_instances() {
  sed -E 's/\.\{u_[0-9]+(,[ ]*u_[0-9]+)*\}//g; s/u_[0-9]+/u/g'
}

echo "== Challenge (pp.all + pp.fullNames) =="
cat "${tmp}/challenge.txt"
echo
echo "== Solution (pp.all + pp.fullNames) =="
cat "${tmp}/solution.txt"
echo
if diff -u "${tmp}/challenge.txt" "${tmp}/solution.txt"; then
  echo "OK: Challenge and Solution names, universes, and types match."
else
  echo "FAIL: type/universe/instance/name mismatch — Palomar Comparator will reject this."
  echo
  echo "== Universe-stripped hint (instance paths only) =="
  normalize_instances <"${tmp}/challenge.txt" >"${tmp}/challenge.norm"
  normalize_instances <"${tmp}/solution.txt" >"${tmp}/solution.norm"
  diff -u "${tmp}/challenge.norm" "${tmp}/solution.norm" || true
  exit 1
fi
