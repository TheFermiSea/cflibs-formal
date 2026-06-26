#!/usr/bin/env bash
# Build the Lean tree-sitter parser for ast-grep into .ast-grep/parser/lean.so.
#
# Grammar: wvhulle/tree-sitter-lean @ 16f43e0 (v0.3.0) — it models imports, `/- -/` block comments,
# and Lean's layout, so it actually parses mathlib-style files (the older tree-sitter-lean4 0.0.6
# grammar whole-file-ERRORs on `import Mathlib`/block comments and is unusable here).
#
# ABI: regenerated at **14**. ast-grep 0.41 cannot load the grammar's default ABI-15 build; ABI 14
# is the compatible target (and the resolved-conflict v0.3.0 grammar generates a lean ~6 MB
# parser.c, vs the 0.0.6 grammar's 104 MB).
set -euo pipefail
cd "$(dirname "$0")/.."

GRAMMAR_REPO="https://github.com/wvhulle/tree-sitter-lean"
GRAMMAR_SHA="16f43e0194ea339a572abf4eec604ffbd8d5594e"
TS_CLI_VERSION="0.22.6"  # defaults to ABI 14

WORK="$(mktemp -d)"; trap 'rm -rf "$WORK"' EXIT

echo "[1/4] install tree-sitter CLI ${TS_CLI_VERSION} (ABI-14 default) ..."
npm install --silent --prefix "$WORK/ts" "tree-sitter-cli@${TS_CLI_VERSION}" >/dev/null 2>&1
TS="$WORK/ts/node_modules/.bin/tree-sitter"

echo "[2/4] clone grammar @ ${GRAMMAR_SHA:0:8} ..."
git clone --quiet "$GRAMMAR_REPO" "$WORK/g"
git -C "$WORK/g" checkout --quiet "$GRAMMAR_SHA"

echo "[3/4] generate parser.c at ABI 14 ..."
( cd "$WORK/g" && "$TS" generate --abi 14 >/dev/null 2>&1 )

echo "[4/4] compile -> .ast-grep/parser/lean.so (cc -O0; the parse tables are data) ..."
mkdir -p .ast-grep/parser
cc -O0 -shared -fPIC -I "$WORK/g/src" \
  "$WORK/g/src/parser.c" "$WORK/g/src/scanner.c" \
  -o .ast-grep/parser/lean.so

echo "done: $(ls -la .ast-grep/parser/lean.so | awk '{print $5}') bytes"
