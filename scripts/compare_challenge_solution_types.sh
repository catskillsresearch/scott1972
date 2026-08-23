#!/usr/bin/env bash
# Diff Challenge vs Solution types for every comparator.json name.
# Palomar Comparator looks up those names in two lean4export environments
# and compares ConstantVal (name, levelParams, type, and definition value)
# with pp.all-level fidelity. Instance names in types and values are part of
# the comparison. A green `lake build` does not imply a match.
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

mapfile -t DEFINITION_NAMES < <(python3 - <<'PY'
import json
cfg = json.load(open("comparator.json"))
for n in cfg.get("definition_names", []):
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
  >"${tmp}/challenge.txt"
lake env lean "${tmp}/SolutionTypes.lean" 2>/dev/null \
  | grep -vE 'LEAN_PATH|trace:|warning:|declaration uses' \
  >"${tmp}/solution.txt"

# Palomar Comparator BEqs ConstantVal.levelParams, so `.{u_3}` vs `.{u_2}`
# is a rejection. Do not strip universe names. A secondary stripped view is
# printed only to make instance-path mismatches easier to read.
normalize_instances() {
  sed -E 's/\.\{u_[0-9]+(,[ ]*u_[0-9]+)*\}//g; s/u_[0-9]+/u/g'
}

if [[ "${PALOMAR_QUIET:-0}" != 1 ]]; then
  echo "== Challenge (pp.all + pp.fullNames) =="
  cat "${tmp}/challenge.txt"
  echo
  echo "== Solution (pp.all + pp.fullNames) =="
  cat "${tmp}/solution.txt"
  echo
fi
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

# These declarations occur transitively in theorem_4_4 and are intentionally
# not definition holes: their bodies lock the advertised pointwise lattice,
# coordinatewise inverse-limit lattice, and recursive projection tower.
LOCKED_DEFINITIONS=(
  Scott1972.ContinuousLattice.ScottMap.le
  Scott1972.ContinuousLattice.ScottMap.instPartialOrder
  Scott1972.ContinuousLattice.ScottMap.sSupMaps
  Scott1972.ContinuousLattice.ScottMap.instSupSet
  Scott1972.ContinuousLattice.ScottMap.instCompleteLattice
  Scott1972.ContinuousLattice.functionSpaceInclFun
  Scott1972.ContinuousLattice.functionSpaceRetrFun
  Scott1972.ContinuousLattice.functionSpaceProjection
  Scott1972.ContinuousLattice.towerProj
  Scott1972.ContinuousLattice.inverseLimitLE
  Scott1972.ContinuousLattice.inverseLimitLT
  Scott1972.ContinuousLattice.inverseLimitPartialOrder
  Scott1972.ContinuousLattice.inverseLimitSInfCoe
  Scott1972.ContinuousLattice.instInfSetInverseLimit
  Scott1972.ContinuousLattice.instCompleteLattice
)

# Every `definition_names` value is compared by Palomar. `LOCKED_DEFINITIONS`
# adds concrete definitions reached transitively through theorem types and
# instances. Deduplicate while preserving order.
mapfile -t BODY_NAMES < <(
  printf '%s\n' "${DEFINITION_NAMES[@]}" "${LOCKED_DEFINITIONS[@]}" |
    awk '!seen[$0]++'
)

write_definition_dump() {
  local module="$1" out="$2"
  {
    echo "import ${module}"
    echo "set_option pp.all true"
    echo "set_option pp.explicit true"
    echo "set_option pp.universes true"
    echo "set_option pp.fullNames true"
    echo "set_option pp.funBinderTypes true"
    for n in "${BODY_NAMES[@]}"; do
      echo "#print ${n}"
    done
  } >"${out}"
}

write_definition_dump Challenge "${tmp}/ChallengeDefinitions.lean"
write_definition_dump Solution "${tmp}/SolutionDefinitions.lean"
lake env lean "${tmp}/ChallengeDefinitions.lean" 2>/dev/null \
  | grep -vE 'LEAN_PATH|trace:|warning:|declaration uses' \
  >"${tmp}/challenge-definitions.txt"
lake env lean "${tmp}/SolutionDefinitions.lean" 2>/dev/null \
  | grep -vE 'LEAN_PATH|trace:|warning:|declaration uses' \
  >"${tmp}/solution-definitions.txt"

# Inline structure proofs elaborate to private constants such as
# `instPartialOrder._proof_4`. Their generated values can differ between the
# modules even when the source proposition is identical. Require every proof
# boundary in a locked value to be a stable, named theorem target instead.
if grep -nE '\._proof_[0-9]+' \
    "${tmp}/challenge-definitions.txt" "${tmp}/solution-definitions.txt"; then
  echo "FAIL: a locked definition depends on an anonymous generated proof."
  echo "Move the field proof to a named theorem and add it to theorem_names."
  exit 1
fi

if diff -u "${tmp}/challenge-definitions.txt" "${tmp}/solution-definitions.txt"; then
  echo "OK: compared and transitively locked definition values match."
else
  echo "FAIL: a compared or transitively locked definition value differs."
  echo "Palomar Comparator will reject the mismatching constant."
  exit 1
fi
