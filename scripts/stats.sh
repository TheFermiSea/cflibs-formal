#!/usr/bin/env bash
# Project stats + import-hygiene invariant for cflibs-formal.
#
# - Prints per-module named-result (theorem/lemma, including attributed ones like `@[simp] theorem`)
#   and definition counts and totals, over the git-tracked sources only — so CONTEXT.md's counts
#   are derived, not hand-estimated, and stray/untracked scratch files cannot pollute them.
# - Source hygiene (scripts/source_hygiene.py): every import in the root file, in each CflibsFormal
#   module and in upstream/ names only `Mathlib` / `CflibsFormal` (read token by token, so
#   same-line, indented and `public import` forms are seen); every module is imported by the root
#   (no orphan); and no `sorry` / `admit` / `native_decide` / `axiom` / kernel-bypass token occurs
#   outside comments (this also covers `example`s, which the axiom audit cannot see).
#   Then prints the base modules (those importing no CflibsFormal module). Acyclicity itself is
#   guaranteed by the Lean build (cyclic imports fail to compile); visualize the full graph with
#   `lake exe graph cflibs-imports.dot`.
#
# Exits non-zero if a hygiene invariant is violated, so it is a usable CI gate.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== Named results (theorem/lemma) and definitions per module =="
total_results=0
total_defs=0
while IFS= read -r f; do
  # Count only lines that start OUTSIDE a comment: a docstring line that happens to begin with
  # the word "theorem" (prose) is not a declaration. `depth` tracks nested `/- ... -/` blocks
  # (docstrings `/-- ... -/` included); a `--` line comment ends the scan of its line.
  read -r n d < <(awk '
    depth == 0 && /^(@\[[^]]*\][ \t]*)?(theorem|lemma) / { r++ }
    depth == 0 && /^(noncomputable[ \t]+)?def /          { x++ }
    {
      s = $0; i = 1; len = length(s)
      while (i <= len) {
        two = substr(s, i, 2)
        if (two == "/-") { depth++; i += 2; continue }
        if (depth > 0 && two == "-/") { depth--; i += 2; continue }
        if (depth == 0 && two == "--") break
        i++
      }
    }
    END { print r + 0, x + 0 }' "$f")
  printf '  %-46s %3d results  %3d defs\n' "${f#CflibsFormal/}" "$n" "$d"
  total_results=$((total_results + n))
  total_defs=$((total_defs + d))
done < <(git ls-files 'CflibsFormal/*.lean' | sort)
printf '  %-46s %3d results  %3d defs\n' "TOTAL" "$total_results" "$total_defs"

echo ""
echo "== Source hygiene (imports, orphan modules, proof escape hatches) =="
python3 scripts/source_hygiene.py
echo "Base modules (import no CflibsFormal module):"
while IFS= read -r f; do
  grep -qE '^import CflibsFormal' "$f" || echo "  ${f#CflibsFormal/}"
done < <(git ls-files 'CflibsFormal/*.lean' | sort)
