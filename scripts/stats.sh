#!/usr/bin/env bash
# Project stats + import-DAG-root invariant for cflibs-formal.
#
# - Prints per-module named-result (theorem/lemma) and definition counts, and totals — so the
#   counts in CONTEXT.md are derived, not hand-estimated.
# - Verifies the import DAG is rooted at Boltzmann: the root imports no CflibsFormal module.
#   (Acyclicity itself is guaranteed by Lean — cyclic imports fail to compile — so the build is
#   the acyclicity gate; visualize the full graph with `lake exe graph cflibs-imports.dot`.)
#
# Exits non-zero only if the import-root invariant is violated, so it is a usable CI gate.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== Named results (theorem/lemma) and definitions per module =="
total_results=0
total_defs=0
while IFS= read -r f; do
  n=$(grep -cE '^(theorem|lemma) ' "$f" || true)
  d=$(grep -cE '^(noncomputable def|def) ' "$f" || true)
  printf '  %-46s %3d results  %3d defs\n' "${f#CflibsFormal/}" "$n" "$d"
  total_results=$((total_results + n))
  total_defs=$((total_defs + d))
done < <(find CflibsFormal -name '*.lean' | sort)
printf '  %-46s %3d results  %3d defs\n' "TOTAL" "$total_results" "$total_defs"

echo ""
echo "== Import DAG root invariant =="
root="CflibsFormal/Boltzmann.lean"
if grep -qE '^import CflibsFormal' "$root"; then
  echo "FAIL: the DAG root $root imports a CflibsFormal module:"
  grep -nE '^import CflibsFormal' "$root"
  exit 1
fi
echo "OK: root $root imports no CflibsFormal module; acyclicity is guaranteed by the Lean build."
