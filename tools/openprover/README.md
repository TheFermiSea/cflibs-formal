# OpenProver as the cflibs-formal proof Worker harness

Decision D7 (`docs/spec/README.md`); design in `docs/spec/04-autoformalization-framework.md` §10.

- Upstream: `openprover` 1.0.1 (MIT, Kripner & Straka, arXiv 2607.09217). Not vendored as source;
  installed into a scratch venv and patched by `patch_local_alias.py`.
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
  --max-time 2h
```

First run with `--lean-project` (which auto-enables the worker tools) installs `lean-explore`,
CPU `torch` and `sentence-transformers` into the venv (~1 GB) and fetches the Lean Explore index plus
the Qwen3-Embedding-0.6B model into `~/.lean_explore` (3.0 GB, version 20260714 on 2026-09-20);
this took about 15 minutes and is not counted against `--max-time`. Budget 5 GB of disk before the
first run. Headless stdout is block-buffered when redirected; read `<run_dir>/trace.log` instead.

The Worker endpoint runs with `--chat-template-kwargs '{"reasoning_effort":"high"}'` because
`HFClient` sends no per-request template kwargs and Leanstral's template defaults to no thinking.

`--provider-url` takes the server root, **not** `.../v1`: `HFClient` probes `<url>/health` and posts to
`<url>/v1/chat/completions`, so a `/v1` suffix yields HTTP 404 on every worker call (observed
2026-09-20). The headless TUI in 1.0.1 also lacks `_sync_step_log_line`, which crashes the first
spawn; the patch adds a no-op.

Never point the endpoint at a global proxy or shell rc: the base URL lives only in this command /
the saved `run_config.toml` of a run (global rule: per-tool base URLs only).
Worker output is accepted only after `lake exe axiom-audit` and kernel replay (`docs/spec/05` §4).
