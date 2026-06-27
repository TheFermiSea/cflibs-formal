#!/usr/bin/env bash
# Regenerate the auto documentation (docs/module-reference.md, docs/theorem-catalog.md) from the
# Lean source. Run after adding/removing modules or named results. The docs-sync CI gate runs this
# into a temp dir and diffs against the committed copies (mirroring the oracle regression gate), so
# the auto docs cannot silently drift from the spec.
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 scripts/gen_docs.py
