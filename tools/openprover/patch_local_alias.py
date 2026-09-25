#!/usr/bin/env python3
"""Add a `leanstral-local` worker alias to an installed openprover==1.0.1, and make its Claude
planner client work with Claude Code CLI >= 2.1 (whose `--output-format json` returns a list of
messages ending in a `type: result` element, not a single result object) without loading the
user's global MCP servers.

OpenProver hard-codes its model aliases (cli.py) and the context-length table (llm/hf.py); the
`leanstral` alias it ships routes to Mistral's hosted API. This patch adds `leanstral-local`,
an OpenAI-compatible HFClient target served by llama.cpp on the infer-0x fleet
(docs/spec/04 §10.4). Idempotent: re-running on a patched install is a no-op.

Usage:  <venv>/bin/python tools/openprover/patch_local_alias.py
"""
import importlib, pathlib, sys

ALIAS, SERVED_NAME, CTX = "leanstral-local", "leanstral", 65536

def patch(path: pathlib.Path, pairs):
    s = path.read_text()
    # The first `old` disappears once patched; its `new` may not survive verbatim, because later
    # patches (the qwen alias) extend the same lines.
    if pairs[0][1] in s or pairs[0][0] not in s:
        print(f"already patched: {path}"); return
    for old, new in pairs:
        assert s.count(old) == 1, f"{path}: pattern not found or not unique: {old[:60]!r}"
        s = s.replace(old, new)
    path.write_text(s); print(f"patched: {path}")

cli = pathlib.Path(importlib.import_module("openprover.cli").__file__)
hf = pathlib.Path(importlib.import_module("openprover.llm.hf").__file__)
cl = pathlib.Path(importlib.import_module("openprover.llm.claude").__file__)
hl = pathlib.Path(importlib.import_module("openprover.tui.headless").__file__)
pr = pathlib.Path(importlib.import_module("openprover.prover").__file__)

patch(cli, [
    ('    model_choices = ["sonnet", "opus", "minimax-m2.5", "leanstral"]',
     f'    model_choices = ["sonnet", "opus", "minimax-m2.5", "leanstral", "{ALIAS}"]'),
    ('    HF_MODEL_MAP = {\n        "minimax-m2.5": "MiniMaxAI/MiniMax-M2.5",\n    }',
     f'    HF_MODEL_MAP = {{\n        "minimax-m2.5": "MiniMaxAI/MiniMax-M2.5",\n        "{ALIAS}": "{SERVED_NAME}",  # llama-server --alias {SERVED_NAME} on the infer-0x fleet\n    }}'),
    ('    VLLM_MODELS = {"minimax-m2.5"}  # served via vLLM (standard OpenAI API)',
     f'    VLLM_MODELS = {{"minimax-m2.5", "{ALIAS}"}}  # standard OpenAI API with tool calls (vLLM or llama-server --jinja)'),
    ('    non_claude_models = {"minimax-m2.5", "leanstral"}',
     f'    non_claude_models = {{"minimax-m2.5", "leanstral", "{ALIAS}"}}'),
    ('    MODEL_DISPLAY = {"sonnet": "sonnet 4.6", "opus": "opus 4.6", "leanstral": "leanstral"}',
     f'    MODEL_DISPLAY = {{"sonnet": "sonnet 4.6", "opus": "opus 4.6", "leanstral": "leanstral", "{ALIAS}": "Leanstral 1.5 (local llama.cpp)"}}'),
])
patch(hf, [
    ('MODEL_CONTEXT_LENGTHS = {\n    "MiniMaxAI/MiniMax-M2.5": 196608,\n}',
     f'MODEL_CONTEXT_LENGTHS = {{\n    "MiniMaxAI/MiniMax-M2.5": 196608,\n    "{SERVED_NAME}": {CTX},  # Leanstral 1.5 Q6_K via llama-server -c {CTX} (run-leanstral)\n}}'),
])
patch(cl, [
    ('        try:\n            raw = json.loads(stdout)\n        except json.JSONDecodeError:',
     '        try:\n            raw = json.loads(stdout)\n            if isinstance(raw, list):  # Claude Code CLI >= 2.1: list of messages, last is the result\n                raw = next(x for x in reversed(raw) if isinstance(x, dict) and x.get("type") == "result")\n        except json.JSONDecodeError:'),
    ('        else:\n            cmd.extend(["--tools", ""])\n        if json_schema:',
     '        else:\n            cmd.extend(["--tools", "", "--strict-mcp-config", "--mcp-config", \'{"mcpServers":{}}\'])  # do not start the user\'s global MCP servers\n        if json_schema:'),
])
patch(hl, [
    ('    def cleanup(self):\n        pass\n',
     '    def cleanup(self):\n        pass\n\n    def _sync_step_log_line(self, step_idx: int):\n        pass  # prover.py calls this on spawn; 1.0.1 only implements it on the curses TUI\n'),
])
# Worker/verifier HTTP calls: 1.0.1 hard-codes urlopen(timeout=600) at four sites. A local MoE at
# ~12 tok/s with reasoning_effort=high routinely needs more than 10 minutes per call (smoke test 2
# lost both of its verifier passes to this timeout), so raise all of them to 30 minutes.
_t = hf.read_text()
if "timeout=1800" in _t:
    print(f"already patched (timeouts): {hf}")
else:
    assert _t.count("urlopen(req, timeout=600)") == 4, "expected four 600 s urlopen sites in hf.py"
    hf.write_text(_t.replace("urlopen(req, timeout=600)", "urlopen(req, timeout=1800)  # was 600; local Worker at ~12 tok/s"))
    print(f"patched (timeouts): {hf}")
# Worker loop rules (from the 2026-09-21 dry run): (a) a search-loop breaker — after two consecutive
# turns whose only tool calls were lean_search, the next turn is offered lean_verify only and told
# so (Frontier 07: 63 searches, zero verifications in 4 h); (b) a hard cap on Worker turns, reusing
# the existing "context nearly full — wrapping up" path (DRY07 ran eleven turns).
patch(pr, [
    ('        call_idx = 0\n        conversation_id = None  # Mistral stateful conversation\n',
     '        call_idx = 0\n        conversation_id = None  # Mistral stateful conversation\n'
     '        search_only_streak = 0  # cflibs patch: consecutive turns that only called lean_search\n'
     '        WORKER_MAX_TURNS = 12  # cflibs patch: hard cap on worker turns\n'),
    ('                if msg_chars > max_input_chars:\n                    logger.warning(\n                        "[%s] context nearly full (%d chars > %d limit) — forcing output",',
     '                if msg_chars > max_input_chars or call_idx >= WORKER_MAX_TURNS:\n                    logger.warning(\n                        "[%s] context nearly full or turn cap (%d chars > %d limit) — forcing output",'),
    ('                resp = self.worker_llm.chat(\n                    messages=messages,\n                    tools=WORKER_TOOLS,\n                    label=f"{worker_id}_turn_{call_idx}",',
     '                if search_only_streak >= 2:  # cflibs patch: break the search loop\n'
     '                    logger.info("[%s] %d search-only turns — withholding lean_search", worker_id, search_only_streak)\n'
     '                    messages.append({"role": "user", "content": (\n'
     '                        "You have searched twice without verifying anything. Stop searching. "\n'
     '                        "Write the complete Lean 4 file now, using the lemma names you already found, "\n'
     '                        "and call lean_verify on it. lean_search is unavailable this turn.")})\n'
     '                    turn_tools = [t for t in WORKER_TOOLS if t.get("function", {}).get("name") != "lean_search"]\n'
     '                else:\n'
     '                    turn_tools = WORKER_TOOLS\n'
     '                resp = self.worker_llm.chat(\n                    messages=messages,\n                    tools=turn_tools,\n                    label=f"{worker_id}_turn_{call_idx}",'),
    ('                    assistant_msg["tool_calls"] = resp["tool_calls"]\n                    messages.append(assistant_msg)\n',
     '                    assistant_msg["tool_calls"] = resp["tool_calls"]\n                    messages.append(assistant_msg)\n'
     '                    _names = {tc["function"]["name"] for tc in resp["tool_calls"]}  # cflibs patch\n'
     '                    search_only_streak = search_only_streak + 1 if _names == {"lean_search"} else 0\n'),
])
# Second local worker alias for the control arm (D11): Qwen3.8-27B Q6_K on infer-01 (run-qwen38, port
# 8081, no --alias, so the served model id is the GGUF path). Context entry kept conservative.
QALIAS, QSERVED, QCTX = "qwen38-local", "/mnt/models/Qwen3.8-27B/Qwen3.8-27B-Q6_K.gguf", 65536
_c = cli.read_text()
if QALIAS in _c:
    print(f"already patched (qwen alias): {cli}")
else:
    reps = [
        (f'"leanstral", "{ALIAS}"]', f'"leanstral", "{ALIAS}", "{QALIAS}"]'),
        (f'        "{ALIAS}": "{SERVED_NAME}",  # llama-server --alias {SERVED_NAME} on the infer-0x fleet\n',
         f'        "{ALIAS}": "{SERVED_NAME}",  # llama-server --alias {SERVED_NAME} on the infer-0x fleet\n        "{QALIAS}": "{QSERVED}",  # run-qwen38 on infer-01 (control arm)\n'),
        (f'VLLM_MODELS = {{"minimax-m2.5", "{ALIAS}"}}', f'VLLM_MODELS = {{"minimax-m2.5", "{ALIAS}", "{QALIAS}"}}'),
        (f'non_claude_models = {{"minimax-m2.5", "leanstral", "{ALIAS}"}}', f'non_claude_models = {{"minimax-m2.5", "leanstral", "{ALIAS}", "{QALIAS}"}}'),
        (f'"{ALIAS}": "Leanstral 1.5 (local llama.cpp)"}}', f'"{ALIAS}": "Leanstral 1.5 (local llama.cpp)", "{QALIAS}": "Qwen3.8-27B (local llama.cpp)"}}'),
    ]
    for o, n in reps:
        assert _c.count(o) == 1, f"qwen alias: pattern not found or not unique: {o[:60]!r}"
        _c = _c.replace(o, n)
    cli.write_text(_c); print(f"patched (qwen alias): {cli}")
_h = hf.read_text()
if QSERVED in _h:
    print(f"already patched (qwen ctx): {hf}")
else:
    o = f'    "{SERVED_NAME}": {CTX},  # Leanstral 1.5 Q6_K via llama-server -c {CTX} (run-leanstral)\n'
    assert _h.count(o) == 1
    hf.write_text(_h.replace(o, o + f'    "{QSERVED}": {QCTX},  # Qwen3.8-27B Q6_K, run-qwen38 -c 131072 (4 unified slots); conservative\n'))
    print(f"patched (qwen ctx): {hf}")

# Per-model sampling (2026-09-22). HFClient hard-codes temperature 0.6 / top_p 0.95 at all three request
# sites -- Qwen3-family thinking-mode settings. Mistral's Leanstral card recommends temperature 1.0 and
# its reference client sends nothing else (vLLM defaults: top_p 1, top_k off, min_p 0); llama-server's
# own defaults (top_k 40, min_p 0.05) would otherwise apply, so they are sent explicitly. Models not in
# the table keep OpenProver's original values, so the Qwen control arm is unchanged.
_h = hf.read_text()
if "def _sampling(" in _h:
    print(f"already patched (sampling): {hf}")
else:
    anchor = "# Per-read timeout for streaming responses (seconds)."
    assert _h.count(anchor) == 1
    _h = _h.replace(anchor, '''MODEL_SAMPLING = {
    "leanstral": {"temperature": 1.0, "top_p": 1.0, "top_k": 0, "min_p": 0.0},  # Mistral model card
}


def _sampling(model: str) -> dict:
    return MODEL_SAMPLING.get(model, {"temperature": 0.6, "top_p": 0.95})


''' + anchor)
    n = 0
    for ind in (" " * 16, " " * 12):
        old = f'{ind}"temperature": 0.6,\n{ind}"top_p": 0.95,\n'
        n += _h.count(old)
        _h = _h.replace(old, f'{ind}**_sampling(self.model),\n')
    assert n == 3, f"sampling: expected 3 request sites, found {n}"
    hf.write_text(_h); print(f"patched (sampling): {hf}")

# Budget accounting (2026-09-22). _run_worker_multi_turn returns only the LAST turn's `raw`, so
# _track_output_tokens (and step meta.toml) saw one turn of a 12-turn worker: --max-tokens budgets
# silently undercounted Worker output. Sum usage over every turn and return it in `raw["usage"]`.
_p = pr.read_text()
if "total_out_tokens" in _p:
    print(f"already patched (usage sum): {pr}")
else:
    o = '        total_cost = 0.0\n        total_duration = 0\n        call_idx = 0\n'
    assert _p.count(o) == 1
    _p = _p.replace(o, '        total_cost = 0.0\n        total_duration = 0\n'
                       '        total_out_tokens = total_in_tokens = 0  # cflibs patch: usage over all turns\n'
                       '        call_idx = 0\n')
    a = _p.index("    def _run_worker_multi_turn(")
    b = _p.index("\n    def ", a + 10)
    head, body, tail = _p[:a], _p[a:b], _p[b:]
    n = 0
    for ind in (" " * 20, " " * 16):
        o = f'\n{ind}total_duration += resp["duration_ms"]\n'  # leading \n: 16 spaces is a suffix of 20
        n += body.count(o)
        body = body.replace(o, o + f'{ind}_u = (resp.get("raw") or {{}}).get("usage") or {{}}  # cflibs patch\n'
                              f'{ind}total_out_tokens += _u.get("completion_tokens", 0) or 0\n'
                              f'{ind}total_in_tokens += _u.get("prompt_tokens", 0) or 0\n')
    assert n == 3, f"usage sum: expected 3 accumulation sites, found {n}"
    _p = head + body + tail
    o = '                "duration_ms": total_duration,\n                "raw": resp["raw"],\n'
    assert _p.count(o) == 1
    _p = _p.replace(o, '                "duration_ms": total_duration,\n'
                       '                "raw": {**(resp["raw"] or {}), "usage": {"prompt_tokens": total_in_tokens,\n'
                       '                        "completion_tokens": total_out_tokens}},  # cflibs patch\n')
    pr.write_text(_p); print(f"patched (usage sum): {pr}")

# Planner error visibility (2026-09-25). On a non-zero exit the Claude CLI puts its reason (e.g. a
# usage-limit message) in stdout as JSON, not stderr, so every overnight planner failure logged as
# "Claude CLI failed (exit 1): " with nothing after it (95 abort/requeue cycles, cause unknown).
_c = cl.read_text()
if "cflibs patch: include stdout" in _c:
    print(f"already patched (planner error text): {cl}")
else:
    o = '            raise RuntimeError(f"Claude CLI failed (exit {proc.returncode}): {stderr[:500]}")'
    assert _c.count(o) == 1, "planner error text: pattern not found or not unique"
    cl.write_text(_c.replace(o, '            raise RuntimeError(f"Claude CLI failed (exit {proc.returncode}): "  # cflibs patch: include stdout\n'
                                 '                               f"{stderr[:300]} | stdout: {stdout[-400:]}")'))
    print(f"patched (planner error text): {cl}")

# Planner effort (2026-09-25). 1.0.1 auto-selects effort "max" whenever `opus` is used and rejects
# --effort unless BOTH planner and worker are Claude models, so an Opus planner with a local worker
# always ran at max. The owner ruled max out on cost: default to "high", and accept --effort when
# at least one of the two models is Claude (it only reaches LLMClient, via CLAUDE_CODE_EFFORT_LEVEL).
patch(cli, [
    ('            effective_effort = "max" if any(m == "opus" for m in claude_models_used) else "high"',
     '            effective_effort = "high"  # cflibs patch: never auto-select max (owner, 2026-09-25)'),
    ('        if non_claude:\n            parser.error(\n                f"--effort is only supported',
     '        if len(non_claude) == 2:  # cflibs patch: effort applies to whichever model is Claude\n'
     '            parser.error(\n                f"--effort is only supported'),
])
# Gated advisor (2026-09-25). The Claude CLI attaches an advisor to every call when the user
# settings name one, and has no per-call cap; unattended, the inherited advisor was 77% of planner
# spend. The owner's settings no longer name one. When OPENPROVER_ADVISOR_MODEL is set (by the
# queue supervisor), attach it with --settings only to first-attempt planner steps 1, 1+EVERY,
# 1+2*EVERY, ... up to MAX per process; parse retries, phase-2 and discussion calls never get it.
_c = cl.read_text()
if "def _advisor_for(" in _c:
    print(f"already patched (gated advisor): {cl}")
else:
    anchor = "from ._base import Interrupted, archive\n"
    assert _c.count(anchor) == 1, "gated advisor: import anchor not found"
    _c = _c.replace(anchor, anchor + '''
_ADVISOR_USED = [0]  # cflibs patch: advisor consultations attached by this process


def _advisor_for(label: str) -> str | None:
    """cflibs patch: the advisor model to attach to this call, or None."""
    model = os.environ.get("OPENPROVER_ADVISOR_MODEL")
    m = re.fullmatch(r"planner_step_(\\d+)", label or "")
    if not model or not m:
        return None
    every = int(os.environ.get("OPENPROVER_ADVISOR_EVERY", "5"))
    cap = int(os.environ.get("OPENPROVER_ADVISOR_MAX", "3"))
    if (int(m.group(1)) - 1) % every or _ADVISOR_USED[0] >= cap:
        return None
    _ADVISOR_USED[0] += 1
    return model
''')
    o = '        if json_schema:\n            cmd.extend(["--json-schema", json.dumps(json_schema)])\n'
    assert _c.count(o) == 1, "gated advisor: cmd anchor not found or not unique"
    _c = _c.replace(o, o + '        _adv = _advisor_for(label)  # cflibs patch: gated advisor\n'
                           '        if _adv:\n'
                           '            cmd.extend(["--settings", json.dumps({"advisorModel": _adv})])\n'
                           '            logger.info("[%s] advisor %s attached", label, _adv)\n')
    cl.write_text(_c); print(f"patched (gated advisor): {cl}")

# Local planner, truncated reply (2026-09-25). When a planner reply is cut off, prover.py retries
# with call(..., no_thinking=True), which HFClient.call does not accept: the first Qwen-planned run
# (PILOT-Q-F07) died with TypeError on step 1. Accept it and ask the chat template not to think.
_h = hf.read_text()
if "no_thinking: bool = False,  # cflibs patch" in _h:
    print(f"already patched (local planner no_thinking): {hf}")
else:
    o = '        max_tokens: int | None = None,\n    ) -> dict:\n        """Make an LLM call via HTTP and archive it.'
    assert _h.count(o) == 1, "no_thinking: call() signature not found or not unique"
    _h = _h.replace(o, '        max_tokens: int | None = None,\n'
                       '        no_thinking: bool = False,  # cflibs patch: prover.py phase-2 retry passes it\n'
                       '    ) -> dict:\n        """Make an LLM call via HTTP and archive it.')
    o = ('                "max_tokens": effective_max_tokens,\n                **_sampling(self.model),\n'
         '                "stream": bool(stream_callback),\n            }\n')
    assert _h.count(o) == 1, "no_thinking: vLLM payload in call() not found or not unique"
    _h = _h.replace(o, o + '            if no_thinking:  # cflibs patch: llama-server --jinja passes these to the template\n'
                           '                payload["chat_template_kwargs"] = {"enable_thinking": False}\n')
    hf.write_text(_h); print(f"patched (local planner no_thinking): {hf}")
