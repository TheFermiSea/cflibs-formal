# Working rules and verification protocol

[Handbook](README.md)

## Before editing

1. Read `AGENTS.md`, `CONTEXT.md`, the affected source docstrings, and scope/citation rows.
2. Record `git status`, base commit, `lean-toolchain`, and `lake-manifest.json` hash. Preserve user
   work; use a dedicated branch/worktree when the starting checkout contains unrelated changes.
3. Identify the declaration consumers, not just module imports. Include umbrella exports, examples,
   certificates, oracle generator, upstream seed, documentation references, and Python mirrors.
4. Write the exact intent: move, rename, proof substitution, representation change, scientific
   correction, or new theorem. Separate these categories when their evidence differs.
5. Record the existing theorem types, attributes, key non-vacuity witnesses, and expected fixtures.
6. Confirm the scope of the change permits finishing the affected verification gates. Do not change
   pins or silently lower heartbeat/memory settings to mask a broken proof dependency.

## Rules for edits

- Keep public names and types during initial file moves. Use thin import shims for old module paths.
- Keep one canonical physical definition. An `Alt` estimator must reuse it, not copy it.
- Preserve comments that explain assumptions, counterexamples, and reference conventions.
- Keep `[simp]`, instances, notation, and local scopes under explicit review. Check representative
  caller proofs after changing them; broad automation can conceal a different dependency.
- Extract helpers only if the abstraction has a clear consumer and improves understanding.
- Treat signature strengthening, scope promotion, changed normalization, or new constants as
  scientific/API work, even when the proof becomes shorter.
- Update curated scope keys with source moves. Regenerate generated references; never edit them to
  hide missing rows. Review the generated diff for lost declarations and false moves.
- Keep the original axiom allowlist. Missing proofs become documented obligations, not axioms.
- Do not execute old research engines merely because they are tracked. Determine status and callers
  first; known-invalid historical material belongs with its errata.
- Do not combine a dependency upgrade with a domain reorganization.

## Core gate commands

Run this sequence after the relevant sources have built. These are current commands, not new tools.
Use unique log/fixture files per worktree if multiple sessions run concurrently.

```bash
lake build
lake exe axiom-audit --root CflibsFormal
lake exe scope-check
lake exe runLinter CflibsFormal
./scripts/stats.sh
./scripts/gen-docs.sh
lake build SahaUpstream
lake exe axiom-audit --root SahaUpstream
```

Inspect exit codes and full summaries. `lake build` may reuse valid cached artifacts; it is not by
itself evidence of clean recompilation of every source. Record what rebuilt. For a broad move or
retirement, use a fresh build output directory/worktree with the same pinned dependencies to expose
stale artifacts. Do not run `lake update` or wipe a shared dependency cache for this purpose.

Oracle comparison, in a shell that stops on failure:

```bash
set -euo pipefail
fixture_file=$(mktemp /tmp/cflibs-formal-fixtures.XXXXXX)
lake exe oracle-fixtures > "$fixture_file"
diff -u oracle/fixtures.json "$fixture_file"
python3 oracle/check_fixtures.py
rm "$fixture_file"
```

A mismatch is a stop condition until explained; never accept regenerated fixtures as the explanation.

For committed changes:

```bash
scripts/kernel-replay.sh --changed origin/main
```

**Important:** this compares the selected base with **HEAD**, not the working tree. Choose an
explicit baseline for a stack of migration commits. Before committing, or when checking renamed
modules, use an explicit list of built modules. Example of existing modules:

```bash
KERNEL_REPLAY_JOBS=2 scripts/kernel-replay.sh \
  CflibsFormal.Boltzmann CflibsFormal.ForwardMap
```

For migration, substitute all affected new modules and changed consumers; inspect the printed list.
Deleted files have no replay target: validate replacement import coverage and perform a fresh build.
Replay a broad audited module set or the existing `--all` sweep for final broad retirement. The
script bounds workers and pins one Lean thread per worker; do not invoke unbounded/no-argument
`leanchecker` or treat an empty changed set as proof replay.

## Documentation and statement review

1. Review `git diff --check` and the generated reference diff.
2. Check relative links and every current source path in the change.
3. Compare expected module/declaration sets to the actual root and topic targets. A passing default
   target does not prove a forgotten module was built.
4. Run `scripts/check-scope-consistency.sh` as the complementary module-level advisory; distinguish
   its warnings from the authoritative declaration-level `scope-check` result.
5. Run citation checks for touched scientific claims and open primary sources for new claims.
   Existing UNVERIFIED entries remain unresolved; do not promote them from a DOI alone.
6. Review the assumption ledger and jointly satisfiable witness. Inspect for tautological bridges
   that take the sought scientific conclusion as a hypothesis.
7. Record any baseline warnings separately from newly introduced failures.

## Commit and landing

Commit a coherent, reviewed unit with its gate record. The project requests a `Claude-Session:`
trailer; use a real applicable identifier or transparently mark it not applicable for another tool.
Never invent a session identity. Push to the verified existing repository remote under its current
workflow. Do not publish private documentation elsewhere or contact upstream maintainers without
separate authorization. Preserve unrelated branches, worktrees, and stashes.
