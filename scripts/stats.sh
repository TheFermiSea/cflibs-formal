#!/usr/bin/env bash
# Project stats + import-hygiene invariant for cflibs-formal.
#
# - Prints per-module named-result (theorem/lemma, including attributed ones like `@[simp] theorem`)
#   and definition counts and totals, over the git-tracked sources only — so CONTEXT.md's counts
#   are derived, not hand-estimated, and stray/untracked scratch files cannot pollute them.
# - Import hygiene: asserts every CflibsFormal module imports only `Mathlib` or other `CflibsFormal`
#   modules (no surprise external dependency), and prints the base modules (those importing no
#   CflibsFormal module). Acyclicity itself is guaranteed by the Lean build (cyclic imports fail to
#   compile); visualize the full graph with `lake exe graph cflibs-imports.dot`.
#
# Exits non-zero if the import-hygiene invariant is violated, so it is a usable CI gate.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== Named results (theorem/lemma) and definitions per module =="
total_results=0
total_defs=0
while IFS= read -r f; do
  read -r n d < <(awk '
    /^(@\[[^]]*\][ \t]*)?(theorem|lemma) / { r++ }
    /^(noncomputable[ \t]+)?def /          { x++ }
    END { print r + 0, x + 0 }' "$f")
  printf '  %-46s %3d results  %3d defs\n' "${f#CflibsFormal/}" "$n" "$d"
  total_results=$((total_results + n))
  total_defs=$((total_defs + d))
done < <(git ls-files 'CflibsFormal/*.lean' | sort)
printf '  %-46s %3d results  %3d defs\n' "TOTAL" "$total_results" "$total_defs"

echo ""
echo "== Import hygiene =="
bad=0
while IFS= read -r f; do
  if grep -nE '^import ' "$f" | grep -qvE '^[0-9]+:import (Mathlib|CflibsFormal)\b'; then
    echo "FAIL: $f imports a non-Mathlib / non-CflibsFormal module:"
    grep -nE '^import ' "$f" | grep -vE '^[0-9]+:import (Mathlib|CflibsFormal)\b'
    bad=1
  fi
done < <(git ls-files 'CflibsFormal/*.lean')
if [ "$bad" -ne 0 ]; then exit 1; fi
echo "OK: every module imports only Mathlib / CflibsFormal (acyclicity guaranteed by the build)."
echo "Base modules (import no CflibsFormal module):"
while IFS= read -r f; do
  grep -qE '^import CflibsFormal' "$f" || echo "  ${f#CflibsFormal/}"
done < <(git ls-files 'CflibsFormal/*.lean' | sort)
