#!/usr/bin/env bash
# Regenerate the auto documentation (docs/module-reference.md, docs/theorem-catalog.md) from the
# Lean source, applying the curated scope tags in docs/scope-tags.tsv. Run after adding/removing
# modules or named results. EXITS NON-ZERO if any result lacks a scope tag (or a tag is stale/
# invalid) — so the docs-sync CI gate fails until every result is classified. Together with the
# git-diff drift check in CI, the auto docs cannot silently drift from the spec.
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 scripts/gen_docs.py
