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

Defaults: `planner` `opus` (Opus 5.5 via the Claude CLI, effort `high`; owner 2026-09-25,
revising D8's Sonnet), `worker` `qwen38-local`. The supervisor picks it up
within 30 s. Optional planner keys:
- `effort`: Claude planner effort, default `high`. OpenProver's own default for `opus` was `max`;
  the patch removes that because the owner ruled it out on cost.
- `advisor`: e.g. `"opus"`. It is attached with `--settings` only on planner steps 1,
  1+`advisor_every`, 1+2×`advisor_every`, … up to `advisor_max` per run (defaults 5 and 3).
  Retries, phase-2 and discussion calls never get it. No automated run uses Fable 5.1 (owner,
  2026-09-25).
- `history_budget`: chars of planner history, default 120000 for every planner. That is Claude's
  auto value; Qwen's auto value is ~39k, so a comparison would otherwise be unmatched.
- `pilot: true`: exempts the target from the daily-cap fallback below.

Each attempt's planner configuration is written to `runs/<id>-<n>.planner.json`, the start log
line, `status.json` and, for verified targets, `verdict.json`.

**Daily cap.** When the Claude planner spend of the last 24 h reaches
`OPENPROVER_DAILY_PLANNER_USD` (default 60, list-price equivalent, advisor included, summed from
every step's `meta.toml`), new non-pilot attempts are planned by `qwen38-local` with no advisor. The
loop keeps running on local models. `status.json` shows `planner_usd_24h`.

A verified proof is only a *candidate for landing*: open a PR by hand (Copilot review
is billed per PR and per push; batch).

## What "verified" means

`verify.py` passes a candidate only if: (1) its text has no escape hatch or metaprogramming
(`sorry`, `sorryAx`, `admit`, `native_decide`, `axiom`, `implemented_by`, `extern`, `unsafe`,
kernel-skip options, `#`-commands, `run_cmd`/`run_elab`, `elab`/`macro`/`syntax`, `initialize`,
`addDecl`/`doCheck`/`Environment`, `set_option` other than heartbeat/recursion limits); (2) it
imports nothing the audited file does not; (3) it keeps every audited definition and the theorem
signature verbatim; (4) it compiles as its own module and **`leanchecker` replays every
declaration through the kernel**; (5) a probe file written by the verifier, importing the compiled
candidate, reads the theorem's axioms (subset of `propext`, `Classical.choice`, `Quot.sound`) and
its `pp.all` elaborated type (identical to the audited statement's, read the same way) between
per-run random markers.

The pre-2026-09-24 version parsed axioms and types from the candidate's own stdout and never ran
the kernel; the deep audit (RF-07) forged three proofs of `(2:ℕ)+2=5` that it accepted. They are
kept in `falsification/`, and `falsification/run.py <lean-project> [cand:stmt:thm ...]` asserts that
each fails through the full verifier AND through the kernel/probe layers alone (text layer
bypassed), and that every genuine proof passed on the command line still passes. Run it after any
change to `verify.py`. On 2026-09-24 it passed with the three C3 proofs and F02 as genuine
controls (~4 min; kernel replay ~15 s per candidate). OpenProver reporting `proved` with no passing
candidate is logged as a FINDING only if OpenProver itself accepted a PROOF.lean. OpenProver's
`[result] proved` means only that PROOF.md exists (`cli.py`), e.g. when the token budget runs out
after an informal proof: F07 attempt 5 (2026-09-24) reported `proved` with no Lean file at all, and was correctly
not verified.

## Operating it

```bash
cat ~/.local/share/openprover/status.json          # what is running where
tail -f ~/.local/share/openprover/supervisor.log
sudo systemctl restart openprover-queue            # kills running proofs; they are requeued
cp tools/openprover/queue/*.py ~/.local/share/openprover/bin/   # deploy a change, then restart
```

A node whose `/health` fails is restarted once (`systemctl restart llm-server@qwen38` over ssh)
and skipped for 30 minutes if it stays down; the same check runs on nodes with a job in flight
(two failed polls → restart → otherwise terminate the run, requeue it uncharged). Five consecutive
failed planner calls terminate the run uncharged and pause all dispatch for 30 minutes: the Claude
planner shares the owner's subscription quota with interactive sessions and workflows, and at the
limit OpenProver otherwise loops through instantly failing steps (292 of them on 2026-09-24).
Each attempt is capped at `max_planner_usd` (default $30 nominal).
Root cause of the mid-run node deaths before 2026-09-24: the cluster SLURM prolog killed
llama-server on every job start (fixed; spec 04 §10.4). Each run is capped by its token budget and a 9 h
wall-clock guard; after `max_attempts` unverified runs a target is parked with its run records.
The Claude planner is the only paid part (subscription quota). Until 2026-09-25 each headless
`claude -p` planner call inherited the owner's Fable advisor from `~/.claude/settings.json`
(`advisorModel`), and the advisor was 77% of the planner's $263 nominal over 2026-09-20..25 (~6% of
the account's usage in that window). The key was removed on 2026-09-25, which leaves ~$0.3 of
Sonnet per planner step. `--settings '{"advisorModel": null}'` does not turn the advisor off; only
removing the key, or `--setting-sources project,local`, does (checked with a probe that asks the
model to call the advisor). At full load (3 nodes, ~19 planner steps/h) the measured list-price cost
per planner step was: Sonnet alone ~$0.20-0.27; Opus 5.5 at the same token counts ~$0.51; an Opus
5.5 advisor consultation ~$0.49, because it re-reads ~95k tokens with no cache; a Fable
consultation $1.23. A 2026-09-25 four-arm pilot (Sonnet; Opus 5.5 high; Sonnet + gated Opus advisor; Qwen)
was cut short on quota: its Claude arms were cancelled after one target each. On F07 (all three
exhausted the 300k-token budget unproved) Sonnet cost $2.44 over 14 steps, Opus 5.5 $2.95 over 11
(half Sonnet's planner output, so more budget left to the workers) and Sonnet + advisor $3.02. The
owner then chose Opus 5.5 as the default planner under the daily cap.
