#!/usr/bin/env bash
# Regenerate the auto documentation (docs/module-reference.md, docs/theorem-catalog.md) from the
# Lean source, applying the curated scope tags in docs/scope-tags.tsv. Run after adding/removing
# modules or named results. EXITS NON-ZERO if any result lacks a scope tag (or a tag is stale/
# invalid/duplicated) — so the docs-sync CI gate fails until every result is classified. Together
# with the git-diff drift check in CI, the auto docs cannot silently drift from the spec.
#
# Published scope tags (owner decision 2026-09-24, docs/conventions.md section 8) need the kernel
# environment, so they are computed by `lake exe scope-check --write` into docs/scope-published.tsv
# and only rendered here; this script fails if that file is missing or out of step with the TSV.
# After changing docs/scope-tags.tsv: `lake exe scope-check --write && scripts/gen-docs.sh`.
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 scripts/gen_docs.py
