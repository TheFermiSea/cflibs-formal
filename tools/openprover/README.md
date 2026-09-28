# OpenProver as the cflibs-formal proof Worker harness

Decision D7 (`docs/spec/README.md`); design in `docs/spec/04-autoformalization-framework.md` §10.

- Upstream: `openprover` 1.0.1 (MIT, Kripner & Straka, arXiv 2607.09217). Not vendored as source;
  installed into a scratch venv and patched by `patch_local_alias.py`.
- The patch adds a second worker alias, `qwen38-local`, for the Qwen3.8-27B control arm on infer-01
  (`run-qwen38`, port 8081; the served model id is the GGUF path because that launcher has no
  `--alias`). Invoke with `--worker-model qwen38-local --provider-url http://10.0.0.26:8081`.
- The patch adds one worker alias, `leanstral-local`, bound to the OpenAI-compatible llama.cpp
  endpoint on the infer-0x fleet (`/usr/local/bin/run-leanstral`, `--alias leanstral`, port 8082).
  The planner stays on the Claude CLI (the owner's subscription).
- The same patch fixes the planner client for Claude Code CLI >= 2.1 (2.1.278 here): `claude -p
  --output-format json` now returns a list of messages whose last element is the `type: result`
  object; unpatched 1.0.1 crashes with `'list' object has no attribute 'get'` on the first planner
  step (observed 2026-09-20). It also passes `--strict-mcp-config` with an empty server map to the
  planner so the user's global MCP servers are not started for every planner call.

OpenProver writes an `OpenProver-<id>/` scratch directory *inside* `--lean-project` and its run
log under `runs/` *relative to the cwd*. Neither belongs in the repository, so point both at a scratch
Lean project that shares the repo's build: a directory holding symlinks to the repo's `lakefile.toml`,
`lean-toolchain`, `lake-manifest.json` and `.lake` (verified 2026-09-20: `lake env lean` from that
directory typechecks against the repo's oleans without rebuilding).

```sh
python3 -m venv /tmp/opvenv && /tmp/opvenv/bin/pip install openprover==1.0.1
/tmp/opvenv/bin/python tools/openprover/patch_local_alias.py
R=/home/brian/code/cflibs-formal; P=/tmp/op/leanproj; mkdir -p "$P"
for f in lakefile.toml lean-toolchain lake-manifest.json .lake; do ln -sfn "$R/$f" "$P/$f"; done
/tmp/opvenv/bin/openprover /tmp/op/runs/<name> --headless --autonomous \
  --planner-model sonnet --worker-model leanstral-local \
  --provider-url http://10.0.0.27:8082 \
  --lean-project "$P" --lean-theorem <statement-only .lean file> --theorem <dossier .md> \
  --answer-reserve 16384 --max-time 2h
```

First run with `--lean-project` (which auto-enables the worker tools) installs `lean-explore`,
CPU `torch` and `sentence-transformers` into the venv (~1 GB) and fetches the Lean Explore index plus
the Qwen3-Embedding-0.6B model into `~/.lean_explore` (3.0 GB, version 20260714 on 2026-09-20);
this took about 15 minutes and is not counted against `--max-time`. Budget 5 GB of disk before the
first run. Headless stdout is block-buffered when redirected; read `<run_dir>/trace.log` instead.

`fleet/run-leanstral.infer-02` and `fleet/run-leanstral.infer-03` are copies of the launchers installed
as `/usr/local/bin/run-leanstral` on the two Worker nodes (Q6_K on both; `-t 30`, `-fa off`,
`-ncmoe 36`, thinking forced). Install with `cp` + `chmod 755`, then `/root/verify-node.sh`.

A Worker node is only usable while nothing else runs on it: the fleet's CI runners (`ghrunner`)
collapse decode from ~11–14 tok/s to ~1.5 tok/s at `-t 36`; the launchers run `-t 30` for that
reason, and a run's log should record `pgrep -u ghrunner -f pytest` at start and end.

The Worker endpoint runs with `--chat-template-kwargs '{"reasoning_effort":"high"}'` because
`HFClient` sends no per-request template kwargs and Leanstral's template defaults to no thinking.

`--provider-url` takes the server root, **not** `.../v1`: `HFClient` probes `<url>/health` and posts to
`<url>/v1/chat/completions`, so a `/v1` suffix yields HTTP 404 on every worker call (observed
2026-09-20). The headless TUI in 1.0.1 also lacks `_sync_step_log_line`, which crashes the first
spawn; the patch adds a no-op.

Two worker-loop rules were added to the patch after the 2026-09-21 dry run: a **search-loop
breaker** (after two consecutive turns whose only tool calls were `lean_search`, the next turn is
offered `lean_verify` only and told to write the file) and a **turn cap** (`WORKER_MAX_TURNS = 12`,
routed through the existing forced-output path). On the server side every Leanstral launcher
carries `--reasoning-budget 16384` (8192 until 2026-09-22; now equal to the Qwen control's) so a turn
always ends in an answer or a tool call; pair it with `--answer-reserve 24576`.

Three more patches since 2026-09-22 (spec 04 §10.4): **per-model sampling** (`MODEL_SAMPLING` in
`llm/hf.py`: Leanstral gets its card's temperature 1.0 with top-p 1, top-k off, min-p 0; other models
keep OpenProver's 0.6/0.95); **Worker usage summed over all turns** (1.0.1 reported only the last
turn, so `--max-tokens` budgets undercounted); and the patch script's idempotency guard now also
recognises a first pattern that later patches extended. The Leanstral launchers serve Mistral's
1.5 chat template via `--chat-template-file`, not the GGUF's embedded 2603 one, which rejects a user
message after a tool result; the llama.cpp-compatible copy is
`fleet/leanstral-1.5.chat_template.llamacpp.jinja`.

`--answer-reserve` (24576 with the 16k reasoning budget; 12288 was used before any budget) is mandatory with Leanstral: the flag is also the per-call `max_tokens` for
OpenAI-style workers, and the default 4096 is consumed by thinking alone (every failed smoke-test turn
ended `finish_reason: length` at 4096 completion tokens with empty content).

The patch also raises the worker/verifier HTTP timeout from 600 s to 1800 s: at ~12 tok/s with
thinking on, a verifier pass can exceed 10 minutes, and smoke test 2 lost both verifier passes to the
600 s limit while its Lean proof had already passed `lean_verify`.

Never point the endpoint at a global proxy or shell rc: the base URL lives only in this command /
the saved `run_config.toml` of a run (global rule: per-tool base URLs only).
Worker output is accepted only after `lake exe axiom-audit` and kernel replay (`docs/spec/05` §4).

Continuous operation: `queue/` holds the supervisor that runs this harness against a queue of
audited statements on all three nodes, with independent re-verification of every proof
(`queue/README.md`).
