# Continuous proof queue

A supervisor on ai-proxy that keeps the three infer-0x Qwen3.8-27B endpoints busy with audited
statements, re-verifies every claimed proof, and never lands anything itself (spec 04 §10.4, D14).

## Pieces

| file | role |
|---|---|
| `supervisor.py` | the loop: health-checks nodes, claims targets, runs OpenProver, verifies, requeues or parks |
| `verify.py` | independent re-verification of one candidate against its audited statement file |
| `openprover-queue.service` | systemd unit (`User=brian`) for ai-proxy |

Installed state (outside the repo, survives branch switches):

```
~/.local/share/openprover/
  venv/        openprover==1.0.1 from requirements.lock + tools/openprover/patch_local_alias.py
  lean-main/   git worktree of origin/main; .lake/packages symlinked to the main checkout's
  leanproj/    symlinks into lean-main (OpenProver writes OpenProver-<id>/ here)
  bin/         deployed copies of supervisor.py and verify.py (the unit runs these)
  fleet.json   the three nodes, port 8081
  queue/{pending,running,done,parked}/<id>/   target.json + statement.lean + dossier.md
  runs/<id>-<n>/ and runs/<id>-<n>.log        OpenProver run records
  results/<id>/  PROOF.lean + statement.lean + verdict.json for every verified target
  status.json, supervisor.log
```

## Adding a target

Only statements that have passed a Mode B statement audit (`lean-statement-audit`) go in. A target
is a directory in `queue/pending/`:

```
statement.lean   the audited file: imports, local definitions, the theorem with one `sorry`
dossier.md       what the planner reads (goal, definitions, known lemmas, pitfalls)
target.json      {"theorem": "Fully.Qualified.name", "max_tokens": 150000, "max_attempts": 2,
                  "note": "where this came from"}
```

Defaults: `planner` `sonnet` (Claude CLI; D8), `worker` `qwen38-local`. The supervisor picks it up
within 30 s. A verified proof is only a *candidate for landing*: open a PR by hand (Copilot review
is billed per PR and per push; batch).

## What "verified" means

`verify.py` passes a candidate only if it has no `sorry`/`admit`/`native_decide`/`axiom`/
`implemented_by`/`extern`/`unsafe`/kernel-skip options, imports nothing the audited file does not,
keeps every audited definition and the theorem signature verbatim, has the same fully elaborated
type for the theorem (`pp.all`, which catches shadowed names), compiles cleanly and depends only on
`propext`, `Classical.choice`, `Quot.sound`. Falsified on 2026-09-23: it passes the three C3 proofs
and rejects the `sorry` statement, a statement with its conclusion deleted, an added import of the
answer module, and a shadowed definition (the last caught only by the elaborated-type check).
OpenProver reporting `proved` with no passing candidate is logged as a FINDING.

## Operating it

```bash
cat ~/.local/share/openprover/status.json          # what is running where
tail -f ~/.local/share/openprover/supervisor.log
sudo systemctl restart openprover-queue            # kills running proofs; they are requeued
cp tools/openprover/queue/*.py ~/.local/share/openprover/bin/   # deploy a change, then restart
```

A node whose `/health` fails is restarted once (`systemctl restart llm-server@qwen38` over ssh)
and skipped for 30 minutes if it stays down. Each run is capped by its token budget and a 9 h
wall-clock guard; after `max_attempts` unverified runs a target is parked with its run records.
The Claude planner is the only paid part (subscription quota): C3 runs cost ~$2.5–8 nominal per
target, so a busy day on three nodes is on the order of $50–100 nominal.
