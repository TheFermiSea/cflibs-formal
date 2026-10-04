# Proof-queue archive (2026-09-24 to 2026-09-28)

A dated, read-only snapshot of the proof-queue records behind the frontier results landed in PRs #8
and #9. Before this snapshot these files existed only outside version control, on the machine that
runs the queue. They are kept because they are the only record of each target's proof route,
rejected routes, non-vacuity witnesses and verification verdict.

This is a log, not a source of truth. The landed Lean declarations, `docs/scope-tags.tsv` and the
theorem cards in `docs/theorems/` supersede anything here; several notes (for example parts of
`staging/2026-09-27/FOLLOWUPS.md`) were already stale when archived.

| Directory | What it holds |
|---|---|
| `staging/2026-09-24/` | Statement files, planning dossiers and audit notes for the first frontier batch (FT-01 to FT-18 and F02-M6), including the hand-land and manifest folders |
| `staging/2026-09-27/` | The second batch (FT-08, FT-14, FT-19, FT-20), `FOLLOWUPS.md` and the hand-land proofs |
| `results/<target>/` | Each queue-verified target: `PROOF.lean`, the audited `statement.lean` and `verdict.json` from `tools/openprover/queue/verify.py` |
| `parked/<target>/` | The five targets still open after repeated attempts (FT08-log, FT13-log, FT14-conv, FT17-tendsto, F07): statement, dossier and `target.json` |

**Scrubbing (decision D23).** Before committing, absolute paths were replaced with placeholders
(`<openprover>`, `<cflibs-formal>`, `<CF-LIBS-improved>`, `<scratch>`, `<home>`), machine names and
addresses with `<node>`, `<host>` and `<ip>`, and the JSON fields `node`, `run_dir`, `planner_usd`,
`slot` and `pid` were removed, as were text lines mentioning planner cost. Planner-comparison pilot
entries were left out. CF-LIBS-improved backlog and review-round ids were replaced with
`[backlog-id]` (a `G1`/`G2` round prefix before such an id was dropped). Nothing else was edited. `MANIFEST.sha256` lists every archived file with its
SHA-256 as committed.

**Added 2026-10-04.** `results/FT08-log-sahaFactor-hasDerivAt-beta/` and
`results/FT13-log-selfAbsorptionFactor-lipschitz/`: both targets were verified on that date (attempts 7
and 11) and landed as `SahaStability.log_sahaFactor_hasDerivAt_beta` and
`EscapeFactor.log_selfAbsorptionFactor_lipschitz`. Their `parked/` entries are kept as the earlier
record. In these two verdicts `plan.carried` names the earlier attempt whose compiled Lean items the
verified attempt started from.

The `.lean` files here are records, not library code: they sit outside every `lean_lib` root and are
never built.
