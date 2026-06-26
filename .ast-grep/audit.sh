#!/usr/bin/env bash
# Structural ast-grep audit of the Lean sources — a fast, comment/string-aware complement to the
# authoritative gates (`lake exe axiom-audit`, `runLinter`). Matches by tree-sitter NODE KIND, so it
# never false-positives on the words "axiom"/"sorry" appearing in docstrings or comments (which a
# plain `rg` would). Exits non-zero if any rule fires.
#
# Setup once: ./.ast-grep/build-parser.sh   (builds .ast-grep/parser/lean.so)
set -euo pipefail
cd "$(dirname "$0")/.."

if [ ! -f .ast-grep/parser/lean.so ]; then
  echo "ast-grep Lean parser not built. Run: ./.ast-grep/build-parser.sh" >&2
  exit 2
fi

echo "== ast-grep structural audit (rules in .ast-grep/rules) =="
# `ast-grep scan` reads sgconfig.yml (custom 'lean' language + ruleDirs) and exits non-zero on
# error-severity matches.
ast-grep scan "${1:-CflibsFormal}"
echo "OK: no structural violations (axiom / sorry / unsound-tactic nodes)."
